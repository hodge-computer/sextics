/* Independent sparse-row storage fixtures for selective_columns.c.
 * Uses ordinary quadratic-probe reference hash tables; checks the actual helper.
 * This does not replace completed-basis comparison with the original solver.
 */
#include "data.h"
#include <assert.h>
#define VERBSTREAM stderr

static uint32_t hash_value(const ht_t *ht,const exp_t *e) {
    uint32_t h=0;for(len_t j=0;j<ht->evl;++j)h+=ht->rn[j]*e[j];return h;
}
static void rehash(ht_t *ht) {
    memset(ht->hmap,0,ht->hsz*sizeof(hi_t));
    for(hl_t k=1;k<ht->eld;++k){hi_t pos=ht->hd[k].val;
        for(hl_t i=0;i<ht->hsz;++i){pos=(pos+(hi_t)i)&(hi_t)(ht->hsz-1);
            if(!ht->hmap[pos]){ht->hmap[pos]=(hi_t)k;break;}}
    }
}
static void enlarge_hash_table(ht_t *ht) {
    hl_t old=ht->esz;ht->esz*=2;ht->hsz*=2;
    exp_t *base=realloc(ht->ev[0],ht->esz*ht->evl*sizeof(exp_t));assert(base);
    ht->ev=realloc(ht->ev,ht->esz*sizeof(exp_t*));assert(ht->ev);
    for(hl_t k=0;k<ht->esz;++k)ht->ev[k]=base+k*ht->evl;
    ht->hd=realloc(ht->hd,ht->esz*sizeof(hd_t));assert(ht->hd);
    memset(ht->hd+old,0,(ht->esz-old)*sizeof(hd_t));
    ht->hmap=realloc(ht->hmap,ht->hsz*sizeof(hi_t));assert(ht->hmap);rehash(ht);
}
static hi_t lookup(const exp_t *e,const ht_t *ht) {
    hi_t pos=hash_value(ht,e);
    for(hl_t i=0;i<ht->hsz;++i){pos=(pos+(hi_t)i)&(hi_t)(ht->hsz-1);hi_t k=ht->hmap[pos];
        if(!k)return 0;
        if(ht->hd[k].val==hash_value(ht,e)&&!memcmp(e,ht->ev[k],ht->evl*sizeof(exp_t)))return k;
    }abort();
}
static inline hi_t insert_in_hash_table(const exp_t *e,ht_t *ht) {
    hi_t existing=lookup(e,ht);if(existing)return existing;
    assert(ht->eld<ht->esz);hi_t k=(hi_t)ht->eld++,pos=hash_value(ht,e);
    memcpy(ht->ev[k],e,ht->evl*sizeof(exp_t));ht->hd[k].val=pos;
    ht->hd[k].deg=e[0];
    for(hl_t i=0;i<ht->hsz;++i){pos=(pos+(hi_t)i)&(hi_t)(ht->hsz-1);
        if(!ht->hmap[pos]){ht->hmap[pos]=k;return k;}}
    abort();
}
#include "selective_columns.c"

static ht_t make_table(hl_t capacity) {
    ht_t ht={0};ht.evl=5;ht.nv=4;ht.esz=capacity;ht.hsz=2*capacity;ht.eld=1;
    ht.ev=calloc(capacity,sizeof(exp_t*));exp_t *base=calloc(capacity*ht.evl,sizeof(exp_t));
    for(hl_t k=0;k<capacity;++k)ht.ev[k]=base+k*ht.evl;
    ht.hd=calloc(capacity,sizeof(hd_t));ht.hmap=calloc(ht.hsz,sizeof(hi_t));
    ht.rn=calloc(ht.evl,sizeof(val_t));for(len_t j=0;j<ht.evl;++j)ht.rn[j]=0x9e3779b9u*(j+1);
    return ht;
}
static void destroy_table(ht_t *ht){free(ht->ev[0]);free(ht->ev);free(ht->hd);free(ht->hmap);free(ht->rn);}
static void fill_source(ht_t *ht,len_t count) {
    for(len_t k=0;k<count;++k){exp_t e[5]={0};len_t q=k;
        for(int j=1;j<5;++j){e[j]=q%19;e[0]+=e[j];q/=19;}
        assert(insert_in_hash_table(e,ht)==k+1);
    }
}
static void run_case(len_t columns,len_t start,int dense,int empty,int initially_present) {
    hl_t cap=16;while(cap<=columns)cap*=2;
    ht_t source=make_table(cap),primary=make_table(16);fill_source(&source,columns);
    hi_t *hcm=calloc(columns?columns:1,sizeof(hi_t));
    hi_t *before=calloc(columns?columns:1,sizeof(hi_t));
    for(len_t i=0;i<columns;++i)hcm[i]=before[i]=i+1;
    if(initially_present)for(len_t i=0;i<columns&&i<7;++i)insert_in_hash_table(source.ev[hcm[i]],&primary);
    hl_t initial_load=primary.eld;mat_t mat={0};md_t md={0};
    mat.ncl=start;mat.nc=columns;mat.ncr=columns-start;mat.np=empty?0:(dense?1:5);
    mat.tr=calloc(mat.np,sizeof(hm_t*));unsigned char *used=calloc(columns?columns:1,1);
    len_t expected=0;size_t refs=0;
    for(len_t k=0;k<mat.np;++k){len_t n=dense?columns-start:17;mat.tr[k]=calloc(OFFSET+n,sizeof(hm_t));
        mat.tr[k][LENGTH]=n;
        for(len_t j=0;j<n;++j){hi_t col=dense?start+j:start+((k*13+j*7)%(columns-start));
            mat.tr[k][OFFSET+j]=col;if(!used[col]){used[col]=1;++expected;}++refs;}
    }
    hm_t *row_snapshot=calloc(refs?refs:1,sizeof(hm_t));size_t pos=0;
    for(len_t k=0;k<mat.np;++k)for(len_t j=OFFSET;j<OFFSET+mat.tr[k][LENGTH];++j)row_snapshot[pos++]=mat.tr[k][j];
    uint64_t old_candidates=hc_used_column_candidates,old_selected=hc_used_column_selected;
    hc_switch_used_columns_to_basis_hash_table(hcm,&primary,&mat,&source,&md);
    assert(hc_used_column_candidates-old_candidates==columns-start);
    assert(hc_used_column_selected-old_selected==expected);
    hl_t expected_load=initial_load;
    for(len_t i=0;i<columns;++i){
        if(used[i]){
            assert(!memcmp(primary.ev[hcm[i]],source.ev[before[i]],source.evl*sizeof(exp_t)));
            assert(lookup(source.ev[before[i]],&primary)==hcm[i]);
            if(!(initially_present&&i<7))++expected_load;
        }else{assert(hcm[i]==before[i]);if(!(initially_present&&i<7))assert(lookup(source.ev[before[i]],&primary)==0);}
    }
    assert(primary.eld==expected_load);pos=0;
    for(len_t k=0;k<mat.np;++k)for(len_t j=OFFSET;j<OFFSET+mat.tr[k][LENGTH];++j){
        assert(mat.tr[k][j]==row_snapshot[pos++]);hi_t col=mat.tr[k][j];
        assert(!memcmp(primary.ev[hcm[col]],source.ev[before[col]],source.evl*sizeof(exp_t)));
    }
    printf("PASS columns=%u reducer_columns=%u surviving_unique=%u primary_added=%lu dense=%d empty=%d initially_present=%d\n",
           columns,start,expected,(unsigned long)(primary.eld-initial_load),dense,empty,initially_present);
    for(len_t k=0;k<mat.np;++k)free(mat.tr[k]);free(mat.tr);free(hcm);free(before);free(used);free(row_snapshot);
    destroy_table(&source);destroy_table(&primary);
}
int main(void) {
    run_case(2000,17,0,0,0);run_case(2000,0,0,0,1);run_case(100,13,1,0,1);
    run_case(17,0,0,0,1);run_case(2000,100,0,1,1);run_case(0,0,0,1,0);
    return 0;
}
