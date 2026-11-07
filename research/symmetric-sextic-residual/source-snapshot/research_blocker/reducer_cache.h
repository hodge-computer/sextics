/* Exact bounded first-divisor cache for the ordinary msolve 0.11.0 F4 path.
 * GPL-2.0-or-later.  Added 2026-11-07; see reducer_cache_REPLAY.txt.
 * No hash equality is trusted without comparison of the full exponent vector.
 */
#ifndef HC_REDUCER_CACHE_H
#define HC_REDUCER_CACHE_H
#include <stdint.h>
#include <string.h>
#include <time.h>

#define HC_RC_LOG2 18u
#define HC_RC_SLOTS (UINT32_C(1)<<HC_RC_LOG2)
#define HC_RC_NONE UINT32_MAX
static int hc_rc_enabled=1,hc_rc_active=0;
static double hc_rc_now(void){struct timespec t;if(clock_gettime(CLOCK_MONOTONIC,&t))abort();return (double)t.tv_sec+(double)t.tv_nsec*1e-9;}
typedef struct {uint32_t generation,winner;val_t hash;} hc_rc_entry;
static hc_rc_entry *hc_rc_entries=NULL;
static exp_t *hc_rc_keys=NULL,*hc_rc_heads=NULL;
static bl_t *hc_rc_old_indices=NULL;
static uint32_t *hc_rc_position=NULL;
static uint64_t hc_rc_position_capacity=0,hc_rc_head_capacity=0,hc_rc_allocated=0;
static len_t hc_rc_evl=0,hc_rc_old_lml=0;
static bl_t hc_rc_old_ld=0;
static uint32_t hc_rc_positive_generation=1,hc_rc_negative_generation=1;
static uint64_t hc_rc_queries=0,hc_rc_positive_hits=0,hc_rc_negative_hits=0,hc_rc_misses=0;
static uint64_t hc_rc_linear_entries=0,hc_rc_saved_entries=0,hc_rc_candidate_checks=0;
static uint64_t hc_rc_monotone_phases=0,hc_rc_reset_phases=0,hc_rc_appended=0,hc_rc_deleted=0,hc_rc_audited=0;
static uint64_t hc_rc_materialized_rows=0,hc_rc_materialized_terms=0;
static double hc_rc_lookup_seconds=0,hc_rc_materialize_seconds=0,hc_rc_prepare_seconds=0;
static void *hc_rc_allocate(uint64_t n,size_t size){
    if(size&&n>SIZE_MAX/size){fprintf(stderr,"[reducer] allocation overflow\n");abort();}
    void *p=malloc((size_t)(n?n:1)*size);if(!p){fprintf(stderr,"[reducer] allocation failed\n");abort();}return p;
}
static void hc_rc_bump(uint32_t *generation){
    ++*generation;if(!*generation){memset(hc_rc_entries,0,HC_RC_SLOTS*sizeof(hc_rc_entry));
        hc_rc_positive_generation=hc_rc_negative_generation=1;}
}
static void hc_rc_prepare(const bs_t *bs,const md_t *md){
    double started=hc_rc_now();hc_rc_active=0;
    if(!hc_rc_enabled||md->trace_level!=NO_TRACER||!md->fc||md->use_signatures||md->in_final_reduction_step){
        hc_rc_prepare_seconds+=hc_rc_now()-started;return;}
    const ht_t *ht=bs->ht;int first=hc_rc_evl!=ht->evl||!hc_rc_entries;
    if(first){
        free(hc_rc_entries);free(hc_rc_keys);free(hc_rc_heads);free(hc_rc_old_indices);free(hc_rc_position);
        hc_rc_entries=calloc(HC_RC_SLOTS,sizeof(hc_rc_entry));if(!hc_rc_entries)abort();
        hc_rc_keys=hc_rc_allocate(HC_RC_SLOTS,(size_t)ht->evl*sizeof(exp_t));
        hc_rc_heads=NULL;hc_rc_old_indices=NULL;hc_rc_position=NULL;
        hc_rc_position_capacity=hc_rc_head_capacity=0;hc_rc_old_lml=0;hc_rc_old_ld=0;hc_rc_evl=ht->evl;
        hc_rc_positive_generation=hc_rc_negative_generation=1;
    }
    if(hc_rc_position_capacity<bs->ld){uint64_t cap=hc_rc_position_capacity?hc_rc_position_capacity:256;
        while(cap<bs->ld)cap*=2;
        uint32_t *map=calloc(cap,sizeof(uint32_t));if(!map)abort();
        if(hc_rc_position_capacity)memcpy(map,hc_rc_position,hc_rc_position_capacity*sizeof(uint32_t));
        free(hc_rc_position);hc_rc_position=map;hc_rc_position_capacity=cap;
    }
    int monotone=!first&&bs->ld>=hc_rc_old_ld,new_suffix=0;uint32_t last_old=0;len_t added=0,survivors=0;
    for(len_t j=0;j<bs->lml;++j){bl_t idx=bs->lmps[j];
        if(idx>=bs->ld||!bs->hm[idx]||bs->red[idx]||(j&&idx<=bs->lmps[j-1])){
            hc_rc_bump(&hc_rc_positive_generation);hc_rc_bump(&hc_rc_negative_generation);
            hc_rc_old_lml=0;hc_rc_old_ld=0;memset(hc_rc_position,0,hc_rc_position_capacity*sizeof(uint32_t));
            hc_rc_prepare_seconds+=hc_rc_now()-started;return;
        }
        uint32_t oldpos=hc_rc_position[idx];
        if(oldpos){
            ++survivors;
            if(new_suffix||oldpos<=last_old||oldpos>hc_rc_old_lml
                ||memcmp(hc_rc_heads+(uint64_t)(oldpos-1)*ht->evl,ht->ev[bs->hm[idx][OFFSET]],ht->evl*sizeof(exp_t)))monotone=0;
            last_old=oldpos;
        }else{
            new_suffix=1;++added;if(idx<hc_rc_old_ld)monotone=0;
        }
    }
    if(monotone){++hc_rc_monotone_phases;
        if(added)hc_rc_bump(&hc_rc_negative_generation);
    }else{
        ++hc_rc_reset_phases;hc_rc_bump(&hc_rc_positive_generation);hc_rc_bump(&hc_rc_negative_generation);
    }
    hc_rc_appended+=added;hc_rc_deleted+=hc_rc_old_lml>=survivors?hc_rc_old_lml-survivors:0;
    for(len_t j=0;j<hc_rc_old_lml;++j)hc_rc_position[hc_rc_old_indices[j]]=0;
    if(hc_rc_head_capacity<bs->lml){uint64_t cap=hc_rc_head_capacity?hc_rc_head_capacity:256;
        while(cap<bs->lml)cap*=2;
        free(hc_rc_heads);free(hc_rc_old_indices);hc_rc_heads=hc_rc_allocate(cap,(size_t)ht->evl*sizeof(exp_t));
        hc_rc_old_indices=hc_rc_allocate(cap,sizeof(bl_t));hc_rc_head_capacity=cap;
    }
    for(len_t j=0;j<bs->lml;++j){bl_t idx=bs->lmps[j];hc_rc_position[idx]=j+1;hc_rc_old_indices[j]=idx;
        memcpy(hc_rc_heads+(uint64_t)j*ht->evl,ht->ev[bs->hm[idx][OFFSET]],ht->evl*sizeof(exp_t));}
    hc_rc_old_lml=bs->lml;hc_rc_old_ld=bs->ld;hc_rc_active=1;
    hc_rc_allocated=HC_RC_SLOTS*(sizeof(hc_rc_entry)+(uint64_t)ht->evl*sizeof(exp_t))
        +hc_rc_position_capacity*sizeof(uint32_t)+hc_rc_head_capacity*(sizeof(bl_t)+(uint64_t)ht->evl*sizeof(exp_t));
    hc_rc_prepare_seconds+=hc_rc_now()-started;
}
static len_t hc_rc_linear(const bs_t *bs,const exp_t *e,sdm_t ns,exp_t *difference){
    const ht_t *ht=bs->ht;
    for(len_t i=0;i<bs->lml;++i){++hc_rc_linear_entries;if(bs->lm[i]&ns)continue;
        const exp_t *f=ht->ev[bs->hm[bs->lmps[i]][OFFSET]];len_t k;
        for(k=0;k<ht->evl;++k){if(e[k]<f[k])break;difference[k]=(exp_t)(e[k]-f[k]);}
        if(k==ht->evl)return i;
    }return bs->lml;
}
#ifdef HC_REDUCER_CACHE_AUDIT
/* Independent copy of the upstream first-divisor control flow. */
static len_t hc_rc_reference(const bs_t *bs,const exp_t *e,sdm_t ns){
    len_t i=0,k;const ht_t *ht=bs->ht;
start:
    while(i<bs->lml&&(bs->lm[i]&ns))++i;
    if(i<bs->lml){const exp_t *f=ht->ev[bs->hm[bs->lmps[i]][OFFSET]];
        for(k=0;k<ht->evl;++k)if(e[k]<f[k]){++i;goto start;}}
    return i;
}
#endif
static len_t hc_rc_find(const bs_t *bs,const ht_t *sht,hm_t m,exp_t *difference){
    ++hc_rc_queries;const exp_t *e=sht->ev[m];const hd_t hd=sht->hd[m];
    uint32_t x=hd.val;x^=x>>16;x*=UINT32_C(0x7feb352d);x^=x>>15;
    uint32_t slot=x&(HC_RC_SLOTS-1);hc_rc_entry *entry=NULL;len_t answer=bs->lml;int hit=0;
    if(hc_rc_active){entry=hc_rc_entries+slot;
        uint32_t generation=entry->winner==HC_RC_NONE?hc_rc_negative_generation:hc_rc_positive_generation;
        if(entry->generation==generation&&entry->hash==hd.val
            &&!memcmp(hc_rc_keys+(uint64_t)slot*hc_rc_evl,e,hc_rc_evl*sizeof(exp_t))){
            if(entry->winner==HC_RC_NONE){hit=1;++hc_rc_negative_hits;hc_rc_saved_entries+=bs->lml;}
            else if(entry->winner<bs->ld&&hc_rc_position[entry->winner]&&!bs->red[entry->winner]&&bs->hm[entry->winner]){
                ++hc_rc_candidate_checks;const exp_t *f=bs->ht->ev[bs->hm[entry->winner][OFFSET]];len_t k;
                for(k=0;k<hc_rc_evl;++k){if(e[k]<f[k])break;difference[k]=(exp_t)(e[k]-f[k]);}
                if(k==hc_rc_evl){answer=hc_rc_position[entry->winner]-1;hit=1;++hc_rc_positive_hits;hc_rc_saved_entries+=answer+1;}
            }
        }
    }
    if(!hit){++hc_rc_misses;answer=hc_rc_linear(bs,e,~hd.sdm,difference);
        if(entry){entry->winner=answer<bs->lml?bs->lmps[answer]:HC_RC_NONE;
            entry->generation=answer<bs->lml?hc_rc_positive_generation:hc_rc_negative_generation;
            entry->hash=hd.val;memcpy(hc_rc_keys+(uint64_t)slot*hc_rc_evl,e,hc_rc_evl*sizeof(exp_t));}
    }
#ifdef HC_REDUCER_CACHE_AUDIT
    ++hc_rc_audited;if(answer!=hc_rc_reference(bs,e,~hd.sdm)){
        fprintf(stderr,"[reducer] exact first-divisor audit mismatch\n");abort();}
#endif
    return answer;
}
static void hc_rc_report(const char *boundary){
    static uint64_t previous_queries=0,previous_positive=0,previous_negative=0,previous_scans=0,previous_saved=0;
    static double previous_lookup=0,previous_materialize=0,previous_prepare=0;
    if(hc_rc_queries==previous_queries)return;
    fprintf(stderr,"[reducer] boundary=%s enabled=%d queries=%llu positive_hits=%llu negative_hits=%llu scanned_entries=%llu avoided_entries=%llu lookup_seconds=%.6f materialize_seconds=%.6f prepare_seconds=%.6f cache_bytes=%llu total_queries=%llu total_positive_hits=%llu total_negative_hits=%llu total_scanned_entries=%llu total_avoided_entries=%llu materialized_rows=%llu materialized_terms=%llu monotone_phases=%llu reset_phases=%llu audited=%llu\n",
        boundary,hc_rc_enabled,(unsigned long long)(hc_rc_queries-previous_queries),(unsigned long long)(hc_rc_positive_hits-previous_positive),
        (unsigned long long)(hc_rc_negative_hits-previous_negative),(unsigned long long)(hc_rc_linear_entries-previous_scans),
        (unsigned long long)(hc_rc_saved_entries-previous_saved),hc_rc_lookup_seconds-previous_lookup,
        hc_rc_materialize_seconds-previous_materialize,hc_rc_prepare_seconds-previous_prepare,(unsigned long long)hc_rc_allocated,
        (unsigned long long)hc_rc_queries,(unsigned long long)hc_rc_positive_hits,(unsigned long long)hc_rc_negative_hits,
        (unsigned long long)hc_rc_linear_entries,(unsigned long long)hc_rc_saved_entries,(unsigned long long)hc_rc_materialized_rows,
        (unsigned long long)hc_rc_materialized_terms,(unsigned long long)hc_rc_monotone_phases,(unsigned long long)hc_rc_reset_phases,(unsigned long long)hc_rc_audited);
    fflush(stderr);previous_queries=hc_rc_queries;previous_positive=hc_rc_positive_hits;previous_negative=hc_rc_negative_hits;
    previous_scans=hc_rc_linear_entries;previous_saved=hc_rc_saved_entries;previous_lookup=hc_rc_lookup_seconds;
    previous_materialize=hc_rc_materialize_seconds;previous_prepare=hc_rc_prepare_seconds;
}
#endif
