/* Independent storage-invariant checks for the actual compaction helper.
 * Build against the pinned msolve data.h and a GMP header, then run with
 * address/undefined-behavior sanitizers.  This is not a Groebner certificate.
 */
#include "data.h"
#include <assert.h>
#include <time.h>
#define VERBSTREAM stderr
static double realtime(void) {
    struct timespec t; clock_gettime(CLOCK_MONOTONIC,&t);
    return t.tv_sec + 1e-9*t.tv_nsec;
}
static inline sdm_t generate_short_divmask(const exp_t *a,const ht_t *ht) {
    uint32_t result=0; len_t ctr=0;
    for (len_t i=0;i<ht->ndv;++i)
        for (len_t j=0;j<ht->bpv;++j,++ctr)
            if ((sdm_t)a[ht->dv[i]]>=ht->dm[ctr]) result|=(1u<<ctr);
    return result;
}
#include "compact_hash.c"

static uint32_t hash(const ht_t *ht,const exp_t *e) {
    uint32_t h=0;
    for (len_t j=0;j<ht->evl;++j) h+=ht->rn[j]*e[j];
    return h;
}
static hi_t lookup(const ht_t *ht,const exp_t *e) {
    hi_t pos=hash(ht,e),mask=(hi_t)(ht->hsz-1);
    for (hl_t i=0;i<ht->hsz;++i) {
        pos=(pos+(hi_t)i)&mask;
        hi_t k=ht->hmap[pos];
        if (!k) return 0;
        if (ht->hd[k].val==hash(ht,e) && !memcmp(ht->ev[k],e,ht->evl*sizeof(exp_t))) return k;
    }
    abort();
}
static void case_run(hl_t capacity,hl_t load,int dense,int empty,int block) {
    ht_t ht={0}; bs_t bs={0}; md_t md={0}; ps_t ps={0};
    ht.nv=6; ht.ebl=block?3:0; ht.evl=ht.nv+1+(block!=0);
    ht.esz=capacity; ht.eld=load; ht.hsz=2*capacity;
    ht.ev=calloc(capacity,sizeof(exp_t*));
    exp_t *base=calloc(capacity*ht.evl,sizeof(exp_t));
    for (hl_t k=0;k<capacity;++k) ht.ev[k]=base+k*ht.evl;
    ht.hd=calloc(capacity,sizeof(hd_t));ht.hmap=calloc(ht.hsz,sizeof(hi_t));
    ht.rn=calloc(ht.evl,sizeof(val_t));
    for (len_t j=0;j<ht.evl;++j) ht.rn[j]=0x9e3779b9u*(j+1);
    ht.ndv=2;ht.bpv=8;ht.dv=calloc(2,sizeof(len_t));ht.dm=calloc(16,sizeof(sdm_t));
    ht.dv[0]=1;ht.dv[1]=ht.evl-1;
    for (len_t j=0;j<16;++j)ht.dm[j]=1+j%8;
    for (hl_t k=1;k<load;++k) {
        hl_t q=k;
        for (len_t j=1;j<ht.evl;++j)if(j!=ht.ebl){ht.ev[k][j]=q%19;q/=19;}
        for (len_t j=1;j<ht.evl;++j)if(j!=ht.ebl)ht.ev[k][block&&j>ht.ebl?ht.ebl:0]+=ht.ev[k][j];
        ht.hd[k].val=hash(&ht,ht.ev[k]);ht.hd[k].sdm=generate_short_divmask(ht.ev[k],&ht);
        ht.hd[k].deg=ht.ev[k][0]+(block?ht.ev[k][ht.ebl]:0);
        ht.hd[k].idx=12345; /* stale scratch data must not influence marking */
    }
    bs.ht=&ht;bs.ld=dense?1:12;bs.hm=calloc(bs.ld,sizeof(hm_t*));
    bs.red=calloc(bs.ld,sizeof(int8_t));
    size_t count=0;
    for (len_t i=0;i<bs.ld;++i) {
        if(empty||(!dense&&i%5==0))continue;
        len_t n=dense?(len_t)(load-1):17;
        bs.hm[i]=calloc(OFFSET+n,sizeof(hm_t));bs.hm[i][LENGTH]=n;bs.hm[i][COEFFS]=i;
        bs.red[i]=i%3; /* include every non-null row, even redundancy marker2 */
        for (len_t j=0;j<n;++j) {
            hl_t k=dense?j+1:1+(((i*47+j*13)%101)*97)%(load-1);
            bs.hm[i][OFFSET+j]=(hm_t)k;++count;
        }
    }
    ps.ld=empty?0:31;ps.p=calloc(ps.ld,sizeof(spair_t));
    for(len_t i=0;i<ps.ld;++i){ps.p[i].lcm=1+((i*73+11)%(load-1));++count;}
    md.ps=&ps;md.info_level=0;
    exp_t *snapshot=calloc((count?count:1)*ht.evl,sizeof(exp_t));
    unsigned char *live=calloc(load,1);size_t at=0;
    for(len_t i=0;i<bs.ld;++i)if(bs.hm[i])for(len_t j=OFFSET;j<OFFSET+bs.hm[i][LENGTH];++j){
        hi_t k=bs.hm[i][j];live[k]=1;memcpy(snapshot+at++*ht.evl,ht.ev[k],ht.evl*sizeof(exp_t));
    }
    for(len_t i=0;i<ps.ld;++i){hi_t k=ps.p[i].lcm;live[k]=1;memcpy(snapshot+at++*ht.evl,ht.ev[k],ht.evl*sizeof(exp_t));}
    hl_t expected=1;for(hl_t k=1;k<load;++k)expected+=live[k]!=0;
    hc_compact_basis_hash_table(&bs,&md);
    assert(ht.eld==expected);assert(md.num_rht==1);at=0;
    for(len_t i=0;i<bs.ld;++i)if(bs.hm[i])for(len_t j=OFFSET;j<OFFSET+bs.hm[i][LENGTH];++j){
        hi_t k=bs.hm[i][j];const exp_t *before=snapshot+at++*ht.evl;
        assert(!memcmp(before,ht.ev[k],ht.evl*sizeof(exp_t)));assert(lookup(&ht,before)==k);
    }
    for(len_t i=0;i<ps.ld;++i){hi_t k=ps.p[i].lcm;const exp_t *before=snapshot+at++*ht.evl;
        assert(!memcmp(before,ht.ev[k],ht.evl*sizeof(exp_t)));assert(lookup(&ht,before)==k);}
    for(hl_t k=1;k<ht.eld;++k){assert(ht.hd[k].val==hash(&ht,ht.ev[k]));
        assert(ht.hd[k].sdm==generate_short_divmask(ht.ev[k],&ht));
        assert(ht.hd[k].deg==ht.ev[k][0]+(block?ht.ev[k][ht.ebl]:0));assert(ht.hd[k].idx==0);}
    for(hl_t k=0;k<ht.esz;++k)assert(ht.ev[k]==ht.ev[0]+k*ht.evl);
    hl_t first_capacity=ht.esz;hc_compact_basis_hash_table(&bs,&md);
    assert(ht.eld==expected);assert(ht.esz==first_capacity);assert(md.num_rht==2);
    printf("PASS capacity=%lu load=%lu retained=%lu new_capacity=%lu dense=%d empty=%d block=%d\n",
           (unsigned long)capacity,(unsigned long)load,(unsigned long)expected,(unsigned long)ht.esz,dense,empty,block);
    for(len_t i=0;i<bs.ld;++i)free(bs.hm[i]);free(bs.hm);free(bs.red);free(ps.p);
    free(snapshot);free(live);free(ht.ev[0]);free(ht.ev);free(ht.hd);free(ht.hmap);free(ht.rn);free(ht.dv);free(ht.dm);
}
int main(void) {
    case_run(16384,12001,0,0,0);case_run(16384,12001,0,0,1);
    case_run(16384,12001,1,0,0);case_run(16384,12001,1,0,1);
    case_run(16384,12001,0,1,0);case_run(256,190,1,0,0);
    return 0;
}
