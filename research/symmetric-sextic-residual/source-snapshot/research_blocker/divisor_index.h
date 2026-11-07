/* Exact bounded active-leading-monomial divisor index, GPL-2.0-or-later.
 * Ordinary finite-field NO_TRACER DRL only; every other path scans normally.
 */
#ifndef HC_DIVISOR_INDEX_H
#define HC_DIVISOR_INDEX_H
#include <stdint.h>
#include <string.h>
#include <time.h>
#define HC_DI_LIMIT UINT64_C(256)
static int hc_di_enabled=1,hc_di_active=0;
typedef struct {uint32_t position;val_t hash;} hc_di_entry;
static hc_di_entry *hc_di_table=NULL;
static uint64_t hc_di_capacity=0,hc_di_queries=0,hc_di_indexed=0,hc_di_fallback=0;
static uint64_t hc_di_candidates=0,hc_di_probes=0,hc_di_equality=0,hc_di_rechecks=0;
static uint64_t hc_di_scans=0,hc_di_avoided=0,hc_di_max_product=0,hc_di_product_overflows=0,hc_di_audited=0;
static uint64_t hc_di_rows=0,hc_di_terms=0;
static double hc_di_lookup_seconds=0,hc_di_materialize_seconds=0,hc_di_prepare_seconds=0;
static double hc_di_now(void){struct timespec t;if(clock_gettime(CLOCK_MONOTONIC,&t))abort();return (double)t.tv_sec+(double)t.tv_nsec*1e-9;}
static uint32_t hc_di_mix(val_t h){uint32_t x=h;x^=x>>16;x*=UINT32_C(0x7feb352d);x^=x>>15;return x;}
static void hc_di_prepare(const bs_t *bs,const md_t *md){
    double started=hc_di_now();hc_di_active=0;
    if(!hc_di_enabled||!md->fc||md->trace_level!=NO_TRACER||md->use_signatures||md->in_final_reduction_step||md->mo!=0||bs->ht->ebl||bs->ht->evl!=bs->ht->nv+1){
        hc_di_prepare_seconds+=hc_di_now()-started;return;}
    uint64_t capacity=16;while(capacity<2*(uint64_t)bs->lml)capacity*=2;
    if(capacity>hc_di_capacity){hc_di_entry *table=calloc(capacity,sizeof(hc_di_entry));
        if(!table){hc_di_prepare_seconds+=hc_di_now()-started;return;}
        free(hc_di_table);hc_di_table=table;hc_di_capacity=capacity;
    }else memset(hc_di_table,0,hc_di_capacity*sizeof(hc_di_entry));
    for(len_t i=0;i<bs->lml;++i){bl_t idx=bs->lmps[i];
        if(idx>=bs->ld||!bs->hm[idx]||bs->red[idx]){hc_di_prepare_seconds+=hc_di_now()-started;return;}
        val_t hash=bs->ht->hd[bs->hm[idx][OFFSET]].val;uint64_t at=hc_di_mix(hash)&(hc_di_capacity-1),steps=0;
        while(hc_di_table[at].position){at=(at+1)&(hc_di_capacity-1);if(++steps==hc_di_capacity){hc_di_prepare_seconds+=hc_di_now()-started;return;}}
        hc_di_table[at]=(hc_di_entry){i+1,hash};
    }
    hc_di_active=1;hc_di_prepare_seconds+=hc_di_now()-started;
}
static len_t hc_di_scan(const bs_t *bs,const exp_t *e,sdm_t ns,exp_t *difference){
    for(len_t i=0;i<bs->lml;++i){++hc_di_scans;if(bs->lm[i]&ns)continue;
        const exp_t *f=bs->ht->ev[bs->hm[bs->lmps[i]][OFFSET]];len_t k;
        for(k=0;k<bs->ht->evl;++k){if(e[k]<f[k])break;difference[k]=(exp_t)(e[k]-f[k]);}
        if(k==bs->ht->evl)return i;
    }return bs->lml;
}
#ifdef HC_DIVISOR_INDEX_AUDIT
static len_t hc_di_reference(const bs_t *bs,const exp_t *e,sdm_t ns){
    len_t i=0,k;
start:
    while(i<bs->lml&&(bs->lm[i]&ns))++i;
    if(i<bs->lml){const exp_t *f=bs->ht->ev[bs->hm[bs->lmps[i]][OFFSET]];
        for(k=0;k<bs->ht->evl;++k)if(e[k]<f[k]){++i;goto start;}}
    return i;
}
#endif
static len_t hc_di_find(const bs_t *bs,const ht_t *sht,hm_t monomial,exp_t *difference){
    ++hc_di_queries;const exp_t *e=sht->ev[monomial];const ht_t *ht=bs->ht;len_t answer=bs->lml;
    uint64_t product=1;len_t support[ht->nv],count=0;int overflow=0;
    if(hc_di_active){
        for(len_t j=1;j<=ht->nv;++j)if(e[j]){support[count++]=j;uint64_t factor=(uint64_t)e[j]+1;
            if(product>UINT64_MAX/factor){product=UINT64_MAX;overflow=1;}else product*=factor;}
        if(product>hc_di_max_product)hc_di_max_product=product;hc_di_product_overflows+=overflow;
    }
    if(!hc_di_active||product>HC_DI_LIMIT){++hc_di_fallback;answer=hc_di_scan(bs,e,~sht->hd[monomial].sdm,difference);}
    else{
        ++hc_di_indexed;exp_t candidate[ht->evl];memset(candidate,0,ht->evl*sizeof(exp_t));val_t hash=0;
        for(uint64_t enumerated=0;enumerated<product;++enumerated){
            ++hc_di_candidates;uint64_t at=hc_di_mix(hash)&(hc_di_capacity-1),steps=0;
            while(hc_di_table[at].position){++hc_di_probes;hc_di_entry entry=hc_di_table[at];
                len_t position=entry.position-1;
                if(entry.hash==hash&&position<answer){++hc_di_equality;
                    bl_t idx=bs->lmps[position];
                    if(idx<bs->ld&&bs->hm[idx]&&!bs->red[idx]
                        &&!memcmp(candidate,ht->ev[bs->hm[idx][OFFSET]],ht->evl*sizeof(exp_t)))answer=position;
                }
                at=(at+1)&(hc_di_capacity-1);if(++steps==hc_di_capacity){
                    ++hc_di_fallback;answer=hc_di_scan(bs,e,~sht->hd[monomial].sdm,difference);goto finished;}
            }
            if(!answer)break;
            /* Sparse odometer.  Native DRL hash weights include the degree
             * slot: weight(j)=rn[j]+rn[0].  No dense key is rebuilt. */
            for(len_t k=0;k<count;++k){len_t j=support[k];val_t weight=ht->rn[j]+ht->rn[0];
                if(candidate[j]<e[j]){++candidate[j];++candidate[0];hash+=weight;break;}
                hash-=(val_t)candidate[j]*weight;candidate[0]-=candidate[j];candidate[j]=0;
            }
        }
        if(answer<bs->lml){++hc_di_rechecks;bl_t idx=bs->lmps[answer];
            if(idx>=bs->ld||!bs->hm[idx]||bs->red[idx]){++hc_di_fallback;answer=hc_di_scan(bs,e,~sht->hd[monomial].sdm,difference);goto finished;}
            const exp_t *f=ht->ev[bs->hm[idx][OFFSET]];
            for(len_t j=0;j<ht->evl;++j){if(e[j]<f[j]){++hc_di_fallback;answer=hc_di_scan(bs,e,~sht->hd[monomial].sdm,difference);goto finished;}
                difference[j]=(exp_t)(e[j]-f[j]);}
        }
        hc_di_avoided+=answer<bs->lml?answer+1:bs->lml;
    }
finished:
#ifdef HC_DIVISOR_INDEX_AUDIT
    ++hc_di_audited;if(answer!=hc_di_reference(bs,e,~sht->hd[monomial].sdm)){
        fprintf(stderr,"[divisor_index] first-divisor audit mismatch\n");abort();}
#endif
    return answer;
}
static void hc_di_report(const char *boundary){
    static uint64_t q=0,indexed=0,fallback=0,candidates=0,scans=0,avoided=0;
    static double lookup=0,materialize=0,prepare=0;if(hc_di_queries==q)return;
    fprintf(stderr,"[divisor_index] boundary=%s enabled=%d queries=%llu indexed_queries=%llu fallback_queries=%llu divisor_candidates=%llu scanned_entries=%llu avoided_entries=%llu lookup_seconds=%.6f materialize_seconds=%.6f prepare_seconds=%.6f table_bytes=%llu max_enumeration_product=%llu product_overflows=%llu total_queries=%llu total_indexed_queries=%llu total_fallback_queries=%llu total_divisor_candidates=%llu total_scanned_entries=%llu total_avoided_entries=%llu total_table_probes=%llu total_full_head_tests=%llu materialized_rows=%llu materialized_terms=%llu audited=%llu\n",
        boundary,hc_di_enabled,(unsigned long long)(hc_di_queries-q),(unsigned long long)(hc_di_indexed-indexed),
        (unsigned long long)(hc_di_fallback-fallback),(unsigned long long)(hc_di_candidates-candidates),
        (unsigned long long)(hc_di_scans-scans),(unsigned long long)(hc_di_avoided-avoided),
        hc_di_lookup_seconds-lookup,hc_di_materialize_seconds-materialize,hc_di_prepare_seconds-prepare,
        (unsigned long long)(hc_di_capacity*sizeof(hc_di_entry)),(unsigned long long)hc_di_max_product,(unsigned long long)hc_di_product_overflows,
        (unsigned long long)hc_di_queries,(unsigned long long)hc_di_indexed,(unsigned long long)hc_di_fallback,
        (unsigned long long)hc_di_candidates,(unsigned long long)hc_di_scans,(unsigned long long)hc_di_avoided,
        (unsigned long long)hc_di_probes,(unsigned long long)hc_di_equality,(unsigned long long)hc_di_rows,(unsigned long long)hc_di_terms,(unsigned long long)hc_di_audited);
    fflush(stderr);q=hc_di_queries;indexed=hc_di_indexed;fallback=hc_di_fallback;candidates=hc_di_candidates;
    scans=hc_di_scans;avoided=hc_di_avoided;lookup=hc_di_lookup_seconds;materialize=hc_di_materialize_seconds;prepare=hc_di_prepare_seconds;
}
#endif
