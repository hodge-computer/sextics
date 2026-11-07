/* Dictionary-native packed restart driver for the pinned msolve 0.11.0 core.
 * GPL-2.0-or-later.  No external flat basis export is allocated.
 */
#include "data.h"
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/resource.h>
#include <unistd.h>
static void hc_safe_boundary(bs_t *, md_t *, uint64_t);
static int hc_restore_native_state(bs_t **,md_t **,mat_t **,md_t *,bs_t *,len_t);
static const char *hc_state_input=NULL;
static uint64_t hc_resume_round=0;
#include "gb.c"

typedef struct {
    uint32_t flags,n,p,order,elim;
    uint64_t ngens,nmon,terms,noriginal;
} hc_header;
typedef struct {
    uint64_t n,terms;
    int32_t *lengths,*exponents,*coefficients;
} hc_original;
static hc_original hc_orig={0};
static const char *hc_checkpoint_path=NULL;
static double hc_started=0,hc_budget=0;
static uint64_t hc_round_budget=0;
static volatile sig_atomic_t hc_checkpoint_requested=0;
static FILE *hc_fingerprint_stream=NULL;
static uint64_t hc_fingerprint=UINT64_C(14695981039346656037),hc_input_fingerprint=0,hc_output_fingerprint=0;
static uint64_t hc_output_bytes=0,hc_output_synced=0,hc_output_advised=0;
static void hc_write_native_state(const char *,bs_t *,md_t *,uint64_t);
static void hc_fingerprint_add(const void *data,size_t count) {
    const uint8_t *p=data;for(size_t i=0;i<count;++i){hc_fingerprint^=p[i];hc_fingerprint*=UINT64_C(1099511628211);}
}
static void hc_checkpoint_signal(int signum) {
    (void)signum;hc_checkpoint_requested=1;
}

static void hc_die(const char *message) {
    fprintf(stderr,"[driver] %s: %s\n",message,strerror(errno));exit(2);
}
static void *hc_alloc(uint64_t count,size_t item) {
    if(item && count>SIZE_MAX/item){errno=EOVERFLOW;hc_die("allocation size overflow");}
    void *p=malloc((size_t)(count?count:1)*item);
    if(!p)hc_die("allocation failed");return p;
}
static void hc_read(FILE *f,void *p,size_t size,size_t count) {
    if(fread(p,size,count,f)!=count){errno=EINVAL;hc_die("truncated packed input");}
    if(f==hc_fingerprint_stream)hc_fingerprint_add(p,size*count);
}
static void hc_write(FILE *f,const void *p,size_t size,size_t count) {
    if(fwrite(p,size,count,f)!=count)hc_die("packed write failed");
    if(f==hc_fingerprint_stream){
        hc_fingerprint_add(p,size*count);hc_output_bytes+=size*count;
        if(hc_output_bytes-hc_output_synced>=UINT64_C(64)*1024*1024){
            if(fflush(f)||fdatasync(fileno(f)))hc_die("sync bounded packed output");
            uint64_t clean=hc_output_bytes&~UINT64_C(4095);
            int rc=posix_fadvise(fileno(f),(off_t)hc_output_advised,(off_t)(clean-hc_output_advised),POSIX_FADV_DONTNEED);
            if(rc){errno=rc;hc_die("release completed packed output cache");}
            hc_output_synced=hc_output_bytes;hc_output_advised=clean;
        }
    }
}
static hc_header hc_read_header(FILE *f) {
    char magic[8];uint32_t a[6];uint64_t b[4];hc_header h;
    hc_read(f,magic,1,8);hc_read(f,a,4,6);hc_read(f,b,8,4);
    if(memcmp(magic,"HCF4PK01",8)||a[0]!=1||!a[2]||a[3]<2||a[3]>INT32_MAX||a[4]!=0||a[5]>=a[2]
            ||b[0]>INT32_MAX||b[1]>UINT32_MAX||b[3]>b[0]){errno=EINVAL;hc_die("invalid packed header");}
    h=(hc_header){a[1],a[2],a[3],a[4],a[5],b[0],b[1],b[2],b[3]};return h;
}
static void hc_write_header(FILE *f,hc_header h) {
    uint32_t a[6]={1,h.flags,h.n,h.p,h.order,h.elim};
    uint64_t b[4]={h.ngens,h.nmon,h.terms,h.noriginal};
    hc_write(f,"HCF4PK01",1,8);hc_write(f,a,4,6);hc_write(f,b,8,4);
}
static uint32_t hc_coefficient(const bs_t *bs,const md_t *md,const hm_t *row,len_t j) {
    const len_t at=row[COEFFS];
    if(md->ff_bits==8)return bs->cf_8[at][j];
    if(md->ff_bits==16)return bs->cf_16[at][j];
    if(md->ff_bits==32)return bs->cf_32[at][j];
    errno=EINVAL;hc_die("rational coefficients unsupported");return 0;
}
static hi_t hc_find_exponent(const ht_t *ht,const exp_t *e) {
    val_t h=0;for(len_t j=0;j<ht->evl;++j)h+=ht->rn[j]*e[j];
    hi_t pos=h,mask=(hi_t)(ht->hsz-1);
    for(hl_t k=0;k<ht->hsz;++k){pos=(pos+(hi_t)k)&mask;hi_t at=ht->hmap[pos];
        if(!at)return 0;
        if(ht->hd[at].val==h&&!memcmp(ht->ev[at],e,ht->evl*sizeof(exp_t)))return at;
    }return 0;
}
static void hc_encode(const ht_t *ht,const int32_t *source,exp_t *e) {
    memset(e,0,ht->evl*sizeof(exp_t));uint32_t left=0,right=0;
    for(len_t j=0;j<ht->nv;++j){len_t at=j+1+(ht->ebl&&j>=ht->ebl-1);
        e[at]=(exp_t)source[j];if(ht->ebl&&at>ht->ebl)right+=e[at];else left+=e[at];}
    if(left>UINT16_MAX||right>UINT16_MAX){errno=EOVERFLOW;hc_die("degree exceeds native exponent width");}
    e[0]=(exp_t)left;if(ht->ebl)e[ht->ebl]=(exp_t)right;
}
static void hc_stream_basis(const char *path,bs_t *bs,md_t *md,int complete) {
    hc_rc_report(complete?"complete":"checkpoint");
    ht_t *ht=bs->ht;const uint64_t nr=complete?bs->lml:bs->ld;
    uint64_t rows=complete?0:hc_orig.n,terms=complete?0:hc_orig.terms;int unit_ideal=0;
    for(hl_t k=1;k<ht->eld;++k)ht->hd[k].idx=0;
    for(uint64_t i=0;i<nr;++i){hm_t *row=bs->hm[complete?bs->lmps[i]:i];if(!row)continue;
        ++rows;terms+=row[LENGTH];
        if(row[LENGTH]&&ht->hd[row[OFFSET]].deg==0)unit_ideal=1;
        for(len_t j=0;j<row[LENGTH];++j){hi_t k=row[OFFSET+j];
            if(!k||k>=ht->eld){errno=EINVAL;hc_die("invalid live monomial reference");}ht->hd[k].idx=1;}}
    uint64_t *original_keys=hc_alloc(complete?0:hc_orig.terms,sizeof(uint64_t));
    uint64_t *extra_refs=hc_alloc(complete?0:hc_orig.terms,sizeof(uint64_t));uint64_t extras=0;
    exp_t *scratch=hc_alloc(ht->evl,sizeof(exp_t));
    if(!complete)for(uint64_t i=0;i<hc_orig.terms;++i){
        hc_encode(ht,hc_orig.exponents+i*ht->nv,scratch);hi_t at=hc_find_exponent(ht,scratch);
        if(at){ht->hd[at].idx=1;original_keys[i]=at;}
        else {uint64_t k=0;for(;k<extras;++k)
                if(!memcmp(hc_orig.exponents+i*ht->nv,hc_orig.exponents+extra_refs[k]*ht->nv,ht->nv*sizeof(int32_t)))break;
            if(k==extras)extra_refs[extras++]=i;original_keys[i]=(UINT64_C(1)<<63)|k;}
    }
    uint64_t live=0;for(hl_t k=1;k<ht->eld;++k)if(ht->hd[k].idx)ht->hd[k].idx=(ind_t)++live;
    if(live+extras>UINT32_MAX){errno=EOVERFLOW;hc_die("packed monomial ID overflow");}
    hc_header header={(uint32_t)(complete?1:0),(uint32_t)ht->nv,md->fc,0,(uint32_t)(ht->ebl?ht->ebl-1:0),
                      rows,live+extras,terms,complete?rows:hc_orig.n};
    size_t plen=strlen(path)+40;char *temporary=hc_alloc(plen,1);snprintf(temporary,plen,"%s.tmp.%ld",path,(long)getpid());
    FILE *f=fopen(temporary,"wb");if(!f)hc_die("open packed output");setvbuf(f,NULL,_IOFBF,1<<20);hc_fingerprint_stream=f;hc_fingerprint=UINT64_C(14695981039346656037);
    hc_output_bytes=hc_output_synced=hc_output_advised=0;hc_write_header(f,header);
    uint16_t *vector=hc_alloc(ht->nv,sizeof(uint16_t));
    for(hl_t k=1;k<ht->eld;++k)if(ht->hd[k].idx){
        for(len_t j=0;j<ht->nv;++j)vector[j]=ht->ev[k][j+1+(ht->ebl&&j>=ht->ebl-1)];
        hc_write(f,vector,2,ht->nv);}
    for(uint64_t i=0;i<extras;++i){for(len_t j=0;j<ht->nv;++j)vector[j]=(uint16_t)hc_orig.exponents[extra_refs[i]*ht->nv+j];
        hc_write(f,vector,2,ht->nv);}
    uint64_t pos=0;
    if(!complete)for(uint64_t i=0;i<hc_orig.n;++i){uint64_t len=(uint64_t)hc_orig.lengths[i];hc_write(f,&len,8,1);
        for(uint64_t j=0;j<len;++j,++pos){uint64_t key=original_keys[pos];
            uint32_t pair[2]={(uint32_t)((key>>63)?live+(key&~(UINT64_C(1)<<63)):ht->hd[key].idx-1),(uint32_t)hc_orig.coefficients[pos]};
            hc_write(f,pair,4,2);}}
    for(uint64_t i=0;i<nr;++i){hm_t *row=bs->hm[complete?bs->lmps[i]:i];if(!row)continue;
        uint64_t len=row[LENGTH];hc_write(f,&len,8,1);
        for(len_t j=0;j<row[LENGTH];++j){uint32_t pair[2]={ht->hd[row[OFFSET+j]].idx-1,hc_coefficient(bs,md,row,j)};hc_write(f,pair,4,2);}}
    hc_output_fingerprint=hc_fingerprint;hc_fingerprint_stream=NULL;
    if(fflush(f)||fsync(fileno(f)))hc_die("sync packed output");
    int advise=posix_fadvise(fileno(f),0,0,POSIX_FADV_DONTNEED);if(advise){errno=advise;hc_die("release packed output cache");}
    if(fclose(f)||rename(temporary,path))hc_die("commit packed output");
    struct rusage usage;getrusage(RUSAGE_SELF,&usage);
    printf("{\"status\":\"%s\",\"complete\":%s,\"unit_ideal\":%s,\"variables\":%u,\"prime\":%u,\"generators\":%llu,\"monomials\":%llu,\"terms\":%llu,\"original_generators\":%llu,\"seconds\":%.6f,\"peak_rss_kib\":%ld}\n",
           complete?"COMPLETE":"CHECKPOINT",complete?"true":"false",unit_ideal?"true":"false",header.n,header.p,
           (unsigned long long)rows,(unsigned long long)header.nmon,(unsigned long long)terms,
           (unsigned long long)header.noriginal,realtime()-hc_started,usage.ru_maxrss);fflush(stdout);
    free(original_keys);free(extra_refs);free(scratch);free(vector);free(temporary);
}
static void hc_safe_boundary(bs_t *bs,md_t *md,uint64_t round) {
    if(md->trace_level!=NO_TRACER||!md->fc||md->use_signatures)return;
    hc_rc_report("next_round");
    if(round==hc_resume_round+1||round%10==0){uint8_t *seen=calloc(bs->ht->nv,1);if(!seen)hc_die("progress allocation");uint32_t count=0;uint64_t rows=0;int unit=0;
        for(bl_t i=0;i<bs->ld;++i)if(bs->hm[i]){++rows;const exp_t *e=bs->ht->ev[bs->hm[i][OFFSET]];len_t at=0,number=0;
            for(len_t j=0;j<bs->ht->nv;++j)if(e[j+1+(bs->ht->ebl&&j>=bs->ht->ebl-1)]){at=j;++number;}
            if(!number)unit=1;
            if(number==1&&!seen[at]){seen[at]=1;++count;}}
        fprintf(stderr,"[progress] completed_rounds=%llu rows=%llu pure_power_variables=%u/%u unit_ideal=%d primary=%lu secondary_capacity=%lu elapsed=%.3f\n",
                (unsigned long long)(round-1),(unsigned long long)rows,count,bs->ht->nv,unit,(unsigned long)bs->ht->eld,(unsigned long)md->ht->esz,realtime()-hc_started);
        fflush(stderr);free(seen);}
    if(hc_checkpoint_path&&(hc_checkpoint_requested||(hc_budget>0&&realtime()-hc_started>=hc_budget)||(hc_round_budget&&round-1-hc_resume_round>=hc_round_budget))){
        hc_stream_basis(hc_checkpoint_path,bs,md,0);hc_write_native_state(hc_checkpoint_path,bs,md,round-1);exit(75);}
}


/* Only the original input-generator prefix is expanded.  Derived rows retain
 * the compact native (monomial-id, field-coefficient) representation throughout.
 * A disposable constant configures upstream field/order metadata; it is removed
 * before any true generator or F4 update is imported. */
static void *hc_resize(void *p,uint64_t count,size_t item) {
    if(item&&count>SIZE_MAX/item){errno=EOVERFLOW;hc_die("resize size overflow");}
    void *q=realloc(p,(size_t)(count?count:1)*item);
    if(!q)hc_die("resize failed");return q;
}
static void hc_set_coefficient(bs_t *bs,const md_t *md,len_t i,len_t j,uint32_t c) {
    if(md->ff_bits==8)bs->cf_8[i][j]=(cf8_t)c;
    else if(md->ff_bits==16)bs->cf_16[i][j]=(cf16_t)c;
    else bs->cf_32[i][j]=(cf32_t)c;
}
static void hc_sort_packed_row(bs_t *bs,const md_t *md,len_t i) {
    ht_t *ht=bs->ht;hm_t *row=bs->hm[i],*m=row+OFFSET;len_t n=row[LENGTH];int sorted=1;
    for(len_t j=1;j<n;++j){hm_t *a=m+j-1,*b=m+j;
        int cmp=initial_gens_cmp(&a,&b,ht);
        if(!cmp){errno=EINVAL;hc_die("duplicate monomial in packed row");}
        if(cmp>0){sorted=0;break;}}
    if(sorted)return;
    /* Same permutation-cycle method as upstream sort_terms_ff_*, with its
     * variable-length stack array moved to a checked heap allocation. */
    hm_t **permutation=hc_alloc(n,sizeof(hm_t*));
    for(len_t j=0;j<n;++j)permutation[j]=m+j;
    sort_r(permutation,n,sizeof(hm_t*),initial_gens_cmp,ht);
    for(len_t j=1;j<n;++j)if(*permutation[j-1]==*permutation[j]){
        errno=EINVAL;hc_die("duplicate monomial in packed row");}
    for(len_t j=0;j<n;++j)if(j!=(len_t)(permutation[j]-m)){
        uint32_t c=hc_coefficient(bs,md,row,j);hm_t mon=m[j];len_t k=j,l;
        while(j!=(l=(len_t)(permutation[k]-m))){
            hc_set_coefficient(bs,md,i,k,hc_coefficient(bs,md,row,l));
            m[k]=m[l];permutation[k]=m+k;k=l;
        }
        hc_set_coefficient(bs,md,i,k,c);m[k]=mon;permutation[k]=m+k;
    }
    free(permutation);
}
static void hc_import_dictionary(FILE *f,hc_header h,bs_t **bsp,ht_t **htp,md_t **mdp,
                                 int pairs,int reset,int info,int threads) {
    int32_t one=1,*zero=calloc(h.n,sizeof(int32_t));if(!zero)hc_die("bootstrap exponent allocation");
    int ok=initialize_gba_input_data(bsp,htp,mdp,&one,zero,&one,h.p,0,h.elim,h.n,1,0,14,threads,pairs,reset,2,0,1,0,0,0);
    free(zero);if(ok!=1){errno=EINVAL;hc_die("native metadata bootstrap failed");}
    bs_t *bs=*bsp;ht_t *ht=*htp;md_t *md=*mdp;
    free_basis_elements(bs);bs->constant=0;bs->mltdeg=0;clean_hash_table(ht);
    check_enlarge_basis(bs,(len_t)h.ngens,md);
    hi_t *ids=hc_alloc(h.nmon,sizeof(hi_t));
    uint16_t *packed=hc_alloc(h.n,sizeof(uint16_t));
    int32_t *decoded=hc_alloc(h.n,sizeof(int32_t));exp_t *exponent=hc_alloc(ht->evl,sizeof(exp_t));
    for(uint64_t i=0;i<h.nmon;++i){
        hc_read(f,packed,2,h.n);uint32_t total=0;
        for(uint32_t j=0;j<h.n;++j){decoded[j]=packed[j];total+=packed[j];}
        if(total>UINT16_MAX){errno=EOVERFLOW;hc_die("input degree exceeds native width");}
        while(1>=ht->esz-ht->eld)enlarge_hash_table(ht);
        hc_encode(ht,decoded,exponent);hl_t before=ht->eld;ids[i]=insert_in_hash_table(exponent,ht);
        if(ht->eld==before){errno=EINVAL;hc_die("duplicate packed dictionary exponent");}
    }
    free(packed);free(decoded);free(exponent);
    hc_orig=(hc_original){h.noriginal,0,hc_alloc(h.noriginal,sizeof(int32_t)),NULL,NULL};
    uint32_t *buffer=hc_alloc(2*16384,sizeof(uint32_t));uint64_t pos=0;len_t valid=0;
    for(uint64_t i=0;i<h.ngens;++i){uint64_t len;hc_read(f,&len,8,1);
        if(len>INT32_MAX||len>h.terms-pos){errno=EINVAL;hc_die("invalid packed row length");}
        uint64_t original_offset=hc_orig.terms;
        if(i<h.noriginal){hc_orig.lengths[i]=(int32_t)len;hc_orig.terms+=len;
            hc_orig.exponents=hc_resize(hc_orig.exponents,hc_orig.terms,(size_t)h.n*sizeof(int32_t));
            hc_orig.coefficients=hc_resize(hc_orig.coefficients,hc_orig.terms,sizeof(int32_t));}
        if(!len)continue;
        hm_t *row=hc_alloc(len+OFFSET,sizeof(hm_t));memset(row,0,OFFSET*sizeof(hm_t));
        row[COEFFS]=valid;row[PRELOOP]=len%UNROLL;row[LENGTH]=(len_t)len;bs->hm[valid]=row;bs->red[valid]=0;
        if(md->ff_bits==8)bs->cf_8[valid]=hc_alloc(len,sizeof(cf8_t));
        else if(md->ff_bits==16)bs->cf_16[valid]=hc_alloc(len,sizeof(cf16_t));
        else bs->cf_32[valid]=hc_alloc(len,sizeof(cf32_t));
        for(uint64_t start=0;start<len;){uint64_t count=len-start<16384?len-start:16384;
            hc_read(f,buffer,8,(size_t)count);
            for(uint64_t j=0;j<count;++j){uint32_t id=buffer[2*j],c=buffer[2*j+1];
                if(id>=h.nmon||!c||c>=h.p){errno=EINVAL;hc_die("invalid packed term");}
                hi_t at=ids[id];row[OFFSET+start+j]=at;hc_set_coefficient(bs,md,valid,(len_t)(start+j),c);
                if(i<h.noriginal){uint64_t out=original_offset+start+j;hc_orig.coefficients[out]=(int32_t)c;
                    for(uint32_t k=0;k<h.n;++k)hc_orig.exponents[out*h.n+k]=ht->ev[at][k+1+(ht->ebl&&k>=ht->ebl-1)];}
            }start+=count;
        }
        pos+=len;hc_sort_packed_row(bs,md,valid);++valid;
    }
    free(ids);free(buffer);
    if(pos!=h.terms||fgetc(f)!=EOF){errno=EINVAL;hc_die("packed term count or trailing data mismatch");}
    md->ngens_input=(int32_t)h.ngens;md->ngens_invalid=(int32_t)(h.ngens-valid);md->ngens=(int32_t)valid;
    md->init_bs_sz=bs->sz;md->homogeneous=0;bs->ld=valid;
    /* Exactly the upstream import_input_data degree/homogeneity calculation. */
    if(md->nev){for(len_t i=0;i<valid;++i){hm_t *row=bs->hm[i];deg_t deg=ht->hd[row[OFFSET]].deg;
        for(len_t j=1;j<row[LENGTH];++j)if(deg<ht->hd[row[OFFSET+j]].deg){deg=ht->hd[row[OFFSET+j]].deg;md->homogeneous=1;}
        row[DEG]=deg;}}
    else for(len_t i=0;i<valid;++i)bs->hm[i][DEG]=ht->hd[bs->hm[i][OFFSET]].deg;
    if(!md->homogeneous){int homogeneous=1;
        for(len_t i=0;i<valid&&homogeneous;++i){hm_t *row=bs->hm[i];deg_t deg=ht->hd[row[OFFSET]].deg;
            for(len_t j=1;j<row[LENGTH];++j)if(deg!=ht->hd[row[OFFSET+j]].deg){homogeneous=0;break;}}
        md->homogeneous=homogeneous;
    }
    if(!valid){errno=EINVAL;hc_die("no nonzero packed input generators");}
    calculate_divmask(ht);
    if(!hc_state_input){sort_r(bs->hm,bs->ld,sizeof(hm_t*),initial_input_cmp,ht);normalize_initial_basis(bs,md->fc);}
    md->info_level=info<0?0:info>2?2:info;print_initial_statistics(VERBSTREAM,md);
}


/* Native-boundary sidecar format v1.  The fixed-width header and row/pair
 * records are little-endian.  md_t is an ABI-specific, pointer-cleared snapshot
 * of numeric configuration and statistics for the pinned native core.  The
 * packed basis remains independently usable as an ideal-preserving generating
 * set.  FNV-1a binds the two files against accidental mismatch; it is not a
 * cryptographic integrity certificate.  Distribution receipts additionally use
 * SHA256.  Only signature-free finite-field NO_TRACER boundaries are accepted. */
static void hc_write_native_state(const char *basis_path,bs_t *bs,md_t *md,uint64_t rounds) {
    if(md->trace_level!=NO_TRACER||md->use_signatures||!md->fc||bs->lo!=bs->ld){errno=EINVAL;hc_die("unsupported native state boundary");}
    for(bl_t i=0;i<bs->ld;++i)if(!bs->hm[i]){errno=EINVAL;hc_die("native state requires dense live row indices");}
    size_t size=strlen(basis_path)+64;char *path=hc_alloc(size,1),*temp=hc_alloc(size,1);
    snprintf(path,size,"%s.state",basis_path);snprintf(temp,size,"%s.tmp.%ld",path,(long)getpid());
    FILE *f=fopen(temp,"wb");if(!f)hc_die("open native state sidecar");setvbuf(f,NULL,_IOFBF,1<<20);
    uint32_t a[12]={1,sizeof(md_t),(uint32_t)bs->ht->nv,md->fc,(uint32_t)(bs->ht->ebl?bs->ht->ebl-1:0),
        bs->ld,bs->lo,bs->lml,bs->constant,(uint32_t)bs->mltdeg,md->ps->ld,0};
    uint64_t b[3]={hc_output_fingerprint,rounds,hc_orig.n};
    hc_write(f,"HCF4ST01",1,8);hc_write(f,a,4,12);hc_write(f,b,8,3);
    md_t stored=*md;stored.tr=NULL;stored.ht=NULL;stored.hcm=NULL;stored.ps=NULL;hc_write(f,&stored,sizeof(stored),1);
    for(bl_t i=0;i<bs->ld;++i){int32_t row[2]={(int32_t)bs->red[i],(int32_t)bs->hm[i][DEG]};hc_write(f,row,4,2);}
    hc_write(f,bs->lmps,4,bs->lml);
    uint16_t *e=hc_alloc(bs->ht->nv,sizeof(uint16_t));
    for(len_t i=0;i<md->ps->ld;++i){spair_t pair=md->ps->p[i];
        if(pair.gen1>=bs->ld||pair.gen2>=bs->ld||!pair.lcm||pair.lcm>=bs->ht->eld){errno=EINVAL;hc_die("invalid pending pair at state boundary");}
        uint32_t q[4]={pair.gen1,pair.gen2,(uint32_t)pair.deg,(uint32_t)pair.type};hc_write(f,q,4,4);
        for(len_t j=0;j<bs->ht->nv;++j)e[j]=bs->ht->ev[pair.lcm][j+1+(bs->ht->ebl&&j>=bs->ht->ebl-1)];
        hc_write(f,e,2,bs->ht->nv);
    }
    free(e);if(fflush(f)||fsync(fileno(f))||fclose(f)||rename(temp,path))hc_die("commit native state sidecar");
    fprintf(stderr,"[state] saved completed_rounds=%llu pending_pairs=%u basis_rows=%u packed_fingerprint=%016llx path=%s\n",
            (unsigned long long)rounds,md->ps->ld,bs->ld,(unsigned long long)hc_output_fingerprint,path);fflush(stderr);
    free(path);free(temp);
}
static int hc_restore_native_state(bs_t **bsp,md_t **mdp,mat_t **matp,md_t *gmd,bs_t *bs,len_t fc) {
    FILE *f=fopen(hc_state_input,"rb");if(!f)hc_die("open native state sidecar");setvbuf(f,NULL,_IOFBF,1<<20);
    char magic[8];uint32_t a[12];uint64_t b[3];md_t stored;
    hc_read(f,magic,1,8);hc_read(f,a,4,12);hc_read(f,b,8,3);
    if(memcmp(magic,"HCF4ST01",8)||a[0]!=1||a[1]!=sizeof(md_t)||a[2]!=bs->ht->nv||a[3]!=fc
            ||a[4]!=(uint32_t)gmd->nev||a[6]!=a[5]||a[7]>a[5]||a[8]||!a[10]
            ||b[0]!=hc_input_fingerprint||b[2]!=hc_orig.n){errno=EINVAL;hc_die("native state ABI, basis fingerprint, or dimensions mismatch");}
    hc_read(f,&stored,sizeof(stored),1);
    if(stored.tr||stored.ht||stored.hcm||stored.ps||stored.fc!=fc||stored.trace_level!=NO_TRACER||stored.use_signatures
            ||stored.nvars!=gmd->nvars||stored.nev!=gmd->nev||stored.mo!=gmd->mo||stored.ff_bits!=gmd->ff_bits
            ||stored.laopt!=gmd->laopt){errno=EINVAL;hc_die("unsupported native metadata snapshot");}
    len_t prefix=0;for(uint64_t i=0;i<hc_orig.n;++i)prefix+=hc_orig.lengths[i]>0;
    if(bs->ld!=prefix+a[5]){errno=EINVAL;hc_die("packed row count does not match native state");}
    for(len_t i=0;i<prefix;++i){free(bs->hm[i]);
        if(gmd->ff_bits==8)free(bs->cf_8[i]);else if(gmd->ff_bits==16)free(bs->cf_16[i]);else free(bs->cf_32[i]);}
    memmove(bs->hm,bs->hm+prefix,(size_t)a[5]*sizeof(hm_t*));
    if(gmd->ff_bits==8)memmove(bs->cf_8,bs->cf_8+prefix,(size_t)a[5]*sizeof(cf8_t*));
    else if(gmd->ff_bits==16)memmove(bs->cf_16,bs->cf_16+prefix,(size_t)a[5]*sizeof(cf16_t*));
    else memmove(bs->cf_32,bs->cf_32+prefix,(size_t)a[5]*sizeof(cf32_t*));
    bs->ld=a[5];bs->lo=a[6];bs->lml=a[7];bs->constant=a[8];bs->mltdeg=(deg_t)a[9];
    md_t *md=hc_alloc(1,sizeof(md_t));*md=stored;
    md->mnsel=gmd->mnsel;md->reset_ht=gmd->reset_ht;md->info_level=gmd->info_level;md->nthrds=gmd->nthrds;
    md->reduce_gb=gmd->reduce_gb;md->gen_pbm_file=gmd->gen_pbm_file;md->init_hts=gmd->init_hts;
    md->init_bs_sz=bs->sz;md->hcm=hc_alloc(1,sizeof(hi_t));md->ps=initialize_pairset();
    if(a[10]==UINT32_MAX){errno=EOVERFLOW;hc_die("pair queue too large");}
    check_enlarge_pairset(md->ps,a[10]+1);md->ps->ld=a[10];
    for(bl_t i=0;i<bs->ld;++i){int32_t row[2];hc_read(f,row,4,2);
        if(row[0]<0||row[0]>2||row[1]<0){errno=EINVAL;hc_die("invalid native row metadata");}
        bs->red[i]=(int8_t)row[0];bs->hm[i][DEG]=(deg_t)row[1];bs->hm[i][COEFFS]=i;
    }
    hc_read(f,bs->lmps,4,bs->lml);
    uint16_t *packed=hc_alloc(bs->ht->nv,sizeof(uint16_t));int32_t *decoded=hc_alloc(bs->ht->nv,sizeof(int32_t));
    exp_t *exponent=hc_alloc(bs->ht->evl,sizeof(exp_t));
    for(len_t i=0;i<md->ps->ld;++i){uint32_t q[4];hc_read(f,q,4,4);hc_read(f,packed,2,bs->ht->nv);
        if(q[0]>=bs->ld||q[1]>=bs->ld||q[2]>INT32_MAX||q[3]>GEN_PAIR){errno=EINVAL;hc_die("invalid restored pair metadata");}
        const exp_t *left=bs->ht->ev[bs->hm[q[0]][OFFSET]],*right=bs->ht->ev[bs->hm[q[1]][OFFSET]];
        for(len_t j=0;j<bs->ht->nv;++j){len_t k=j+1+(bs->ht->ebl&&j>=bs->ht->ebl-1);
            if(packed[j]!=(left[k]>right[k]?left[k]:right[k])){errno=EINVAL;hc_die("restored pair LCM does not match its generators");}
            decoded[j]=packed[j];}
        hc_encode(bs->ht,decoded,exponent);while(1>=bs->ht->esz-bs->ht->eld)enlarge_hash_table(bs->ht);
        hi_t monomial=insert_in_hash_table(exponent,bs->ht);
        md->ps->p[i]=(spair_t){.lcm=monomial,.gen1=q[0],.gen2=q[1],.deg=(deg_t)q[2],.type=(spt_t)q[3]};
    }
    free(packed);free(decoded);free(exponent);
    if(fgetc(f)!=EOF){errno=EINVAL;hc_die("trailing native state data");}fclose(f);
    calculate_divmask(bs->ht);
    for(bl_t i=0;i<bs->lml;++i){if(bs->lmps[i]>=bs->ld||bs->red[bs->lmps[i]]){errno=EINVAL;hc_die("invalid restored leading-monomial list");}
        bs->lm[i]=bs->ht->hd[bs->hm[bs->lmps[i]][OFFSET]].sdm;}
    md->ht=initialize_secondary_hash_table(bs->ht,md);
    mat_t *mat=calloc(1,sizeof(mat_t));if(!mat)hc_die("restored matrix allocation");
    hc_resume_round=b[1];*bsp=bs;*mdp=md;*matp=mat;
    fprintf(stderr,"[state] restored completed_rounds=%llu pending_pairs=%u basis_rows=%u; initial pair generation skipped\n",
            (unsigned long long)hc_resume_round,md->ps->ld,bs->ld);fflush(stderr);
    return 0;
}

int main(int argc,char **argv) {
    const char *input=NULL,*output=NULL;int pairs=64,reset=1,info=1,import_only=0,threads=1;uint32_t endian=1;
    struct sigaction action={0};action.sa_handler=hc_checkpoint_signal;sigemptyset(&action.sa_mask);
    if(sigaction(SIGUSR1,&action,NULL))hc_die("install checkpoint signal handler");
    if(*(uint8_t*)&endian!=1){errno=ENOTSUP;hc_die("little-endian host required");}
    for(int i=1;i<argc;++i){if(i+1>=argc){errno=EINVAL;hc_die("option requires a value");}
        const char *key=argv[i],*value=argv[++i];
        if(!strcmp(key,"--input"))input=value;else if(!strcmp(key,"--output"))output=value;
        else if(!strcmp(key,"--checkpoint"))hc_checkpoint_path=value;else if(!strcmp(key,"--seconds"))hc_budget=strtod(value,NULL);
        else if(!strcmp(key,"--resume-state"))hc_state_input=value;
        else if(!strcmp(key,"--reducer-cache"))hc_rc_enabled=atoi(value);
        else if(!strcmp(key,"--threads"))threads=atoi(value);
        else if(!strcmp(key,"--import-only"))import_only=atoi(value);
        else if(!strcmp(key,"--round-budget"))hc_round_budget=strtoull(value,NULL,10);
        else if(!strcmp(key,"--pairs"))pairs=atoi(value);else if(!strcmp(key,"--reset"))reset=atoi(value);else if(!strcmp(key,"--info"))info=atoi(value);
        else{errno=EINVAL;hc_die("unknown option");}}
    if(!input||!output||((hc_budget>0||hc_round_budget)&&!hc_checkpoint_path)){errno=EINVAL;hc_die("input, output and any budget checkpoint path are required");}
    if(hc_rc_enabled!=0&&hc_rc_enabled!=1){errno=EINVAL;hc_die("--reducer-cache must be0 or1");}
    if(threads<1||threads>8){errno=EINVAL;hc_die("--threads must be between1 and8 for this tested driver");}
#ifndef _OPENMP
#error This driver requires OpenMP support.
#endif
    omp_set_dynamic(0);int actual_threads=0;
#pragma omp parallel num_threads(threads)
    {
#pragma omp single
        actual_threads=omp_get_num_threads();
    }
    if(actual_threads!=threads){errno=ENOTSUP;hc_die("runtime did not provide the requested OpenMP team");}
    fprintf(stderr,"[parallel] requested_threads=%d actual_threads=%d dynamic=%d md_abi_bytes=%zu\n",threads,actual_threads,omp_get_dynamic(),sizeof(md_t));
#if defined(__x86_64__) && defined(__GNUC__)
    __builtin_cpu_init();fprintf(stderr,"[native] runtime_avx2=%d runtime_avx512f=%d\n",!!__builtin_cpu_supports("avx2"),!!__builtin_cpu_supports("avx512f"));
#endif
    FILE *f=fopen(input,"rb");if(!f)hc_die("open packed input");
    hc_fingerprint_stream=f;hc_fingerprint=UINT64_C(14695981039346656037);hc_header h=hc_read_header(f);
    bs_t *bs=NULL;ht_t *ht=NULL;md_t *md=NULL;
    double imported_at=realtime();
    hc_import_dictionary(f,h,&bs,&ht,&md,pairs,reset,info,threads);hc_input_fingerprint=hc_fingerprint;hc_fingerprint_stream=NULL;
    int advise=posix_fadvise(fileno(f),0,0,POSIX_FADV_DONTNEED);if(advise){errno=advise;hc_die("release packed input cache");}fclose(f);
    hc_started=realtime();
    struct rusage import_usage;getrusage(RUSAGE_SELF,&import_usage);
    fprintf(stderr,"[import] mode=dictionary-native generators=%llu monomials=%llu terms=%llu original_terms=%llu seconds=%.6f peak_rss_kib=%ld\n",
            (unsigned long long)h.ngens,(unsigned long long)h.nmon,(unsigned long long)h.terms,
            (unsigned long long)hc_orig.terms,hc_started-imported_at,import_usage.ru_maxrss);
    if(import_only){
        printf("{\"status\":\"IMPORT_ONLY\",\"complete\":false,\"generators\":%llu,\"monomials\":%llu,\"terms\":%llu,\"peak_rss_kib\":%ld}\n",
               (unsigned long long)h.ngens,(unsigned long long)h.nmon,(unsigned long long)h.terms,import_usage.ru_maxrss);
        free_shared_hash_data(ht);free_basis(&bs);free(md);free(hc_orig.lengths);free(hc_orig.exponents);free(hc_orig.coefficients);return 0;
    }
    int error=0;bs=core_f4(bs,md,&error,h.p);if(error){errno=EINVAL;hc_die("native F4 error");}
    hc_stream_basis(output,bs,md,1);
    free_shared_hash_data(ht);free_basis(&bs);free(md);free(hc_orig.lengths);free(hc_orig.exponents);free(hc_orig.coefficients);
    return 0;
}
