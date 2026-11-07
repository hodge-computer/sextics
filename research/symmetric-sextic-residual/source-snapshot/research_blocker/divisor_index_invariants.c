/* Exact enumeration/hash-collision/first-position tests, GPL-2.0-or-later. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <gmp.h>
#include "data.h"
#define HC_DIVISOR_INDEX_AUDIT 1
#include "divisor_index.h"
#define NV 38
#define N 3000
static exp_t head[N][NV+1],query[NV+1];static exp_t *ev[N+1],*qev[2];
static hd_t hd[N+1],qhd[2];static val_t weights[NV+1];
static hm_t row[N][OFFSET+1],*rows[N];static bl_t positions[N];static sdm_t masks[N];static int8_t redundant[N];
static ht_t ht,sht;static bs_t bs;static md_t md;static uint64_t checked=0;
static uint32_t state=834991;
static uint32_t next(void){state^=state<<13;state^=state>>17;state^=state<<5;return state;}
static void hash_heads(void){for(int i=0;i<N;++i){hd[i+1].val=0;for(int j=0;j<=NV;++j)hd[i+1].val+=weights[j]*head[i][j];}}
static len_t oracle(void){for(len_t i=0;i<bs.lml;++i){int divides=1;
 for(int j=1;j<=NV;++j)if(head[positions[i]][j]>query[j]){divides=0;break;}
 if(divides)return i;}return bs.lml;}
static void check(void){exp_t difference[NV+1];qhd[1].val=0;for(int j=0;j<=NV;++j)qhd[1].val+=weights[j]*query[j];
 len_t expected=oracle(),answer=hc_di_find(&bs,&sht,1,difference);
 if(answer!=expected)abort();if(answer<bs.lml)for(int j=0;j<=NV;++j)if(difference[j]!=query[j]-head[positions[answer]][j])abort();++checked;}
int main(void){ht.nv=sht.nv=NV;ht.evl=sht.evl=NV+1;ht.ev=ev;ht.hd=hd;ht.rn=weights;sht.ev=qev;sht.hd=qhd;qev[1]=query;
 bs.ht=&ht;bs.hm=rows;bs.lmps=positions;bs.lm=masks;bs.red=redundant;bs.ld=bs.lml=N;
 md.fc=37;md.trace_level=NO_TRACER;
 for(int j=0;j<=NV;++j)weights[j]=next()|1;
 for(int i=0;i<N;++i){positions[i]=i;rows[i]=row[i];row[i][OFFSET]=i+1;row[i][LENGTH]=1;ev[i+1]=head[i];
  head[i][0]=3;for(int j=0;j<3;++j)++head[i][1+next()%NV];}
 hash_heads();hc_di_prepare(&bs,&md);
 for(int q=0;q<600;++q){memset(query,0,sizeof(query));query[0]=6;for(int j=0;j<6;++j)++query[1+next()%NV];check();}
 if(hc_di_scans||hc_di_max_product>64||!hc_di_avoided)abort();
 uint64_t degree6_avoided=hc_di_avoided,degree6_candidates=hc_di_candidates,degree6_probes=hc_di_probes;
 /* Product512 exceeds the fixed256 limit and must use the exact scan. */
 memset(query,0,sizeof(query));query[0]=9;for(int j=1;j<=9;++j)query[j]=1;
 uint64_t fallback=hc_di_fallback;check();if(hc_di_fallback!=fallback+1)abort();
 /* All native hashes collide; key comparison must still choose the first
  * position, even when the active list is deliberately reordered. */
 memset(weights,0,sizeof(weights));memset(head,0,sizeof(head));bs.lml=bs.ld=12;
 for(int i=0;i<12;++i){head[i][0]=1;head[i][1+i%10]=1;positions[i]=11-i;}
 hash_heads();hc_di_prepare(&bs,&md);
 for(int bits=0;bits<256;++bits){memset(query,0,sizeof(query));
  for(int j=0;j<8;++j)if(bits>>j&1){query[j+1]=1;++query[0];}check();}
 /* A duplicate head at a later basis position cannot replace its earlier
  * occurrence.  Above fixture includes duplicates of x1 and x2. */
 memset(query,0,sizeof(query));query[0]=query[1]=1;check();
 md.in_final_reduction_step=1;hc_di_prepare(&bs,&md);if(hc_di_active)abort();check();
 md.in_final_reduction_step=0;ht.ebl=2;hc_di_prepare(&bs,&md);if(hc_di_active)abort();check();
 printf("{\"status\":\"PASS\",\"queries_checked\":%llu,\"degree6_basis_heads\":3000,\"degree6_queries\":600,\"degree6_avoided_scan_entries\":%llu,\"degree6_divisor_candidates\":%llu,\"degree6_hash_probes\":%llu,\"forced_all_hashes_equal\":true,\"duplicate_heads_and_reordered_positions\":true,\"enumeration_limit_fallback_checked\":true,\"unsupported_modes_fallback_checked\":true}\n",
  (unsigned long long)checked,(unsigned long long)degree6_avoided,(unsigned long long)degree6_candidates,(unsigned long long)degree6_probes);
 return 0;}
