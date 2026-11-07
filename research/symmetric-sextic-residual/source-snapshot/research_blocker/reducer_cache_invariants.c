/* Small semantic tests of the exact-cache lifetime rules, GPL-2.0-or-later. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <gmp.h>
#include "data.h"
static double realtime(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec+t.tv_nsec*1e-9;}
#define HC_REDUCER_CACHE_AUDIT 1
#include "reducer_cache.h"
static exp_t heads[10][5],query[5];static exp_t *ev[11],*qev[2];static hd_t qhd[2];
static hm_t row[10][OFFSET+1],*rows[10];static bl_t indices[10];static sdm_t masks[10];static int8_t redundant[10];
static ht_t ht,sht;static bs_t bs;static md_t md;static uint64_t checks=0;
static void exponent(exp_t *e,int x,int y,int z,int w){e[0]=x+y+z+w;e[1]=x;e[2]=y;e[3]=z;e[4]=w;}
static void active(const bl_t *list,len_t n,bl_t ld){memset(redundant,1,sizeof(redundant));bs.ld=ld;bs.lml=n;
 for(len_t i=0;i<n;++i){indices[i]=list[i];redundant[list[i]]=0;}hc_rc_prepare(&bs,&md);}
static len_t oracle(void){for(len_t i=0;i<bs.lml;++i){int yes=1;
 for(int j=1;j<=4;++j)if(heads[indices[i]][j]>query[j])yes=0;
 if(yes)return i;}return bs.lml;}
static void check(int x,int y,int z,int w,int expected){exponent(query,x,y,z,w);exp_t difference[5];
 len_t reference=oracle(),answer=hc_rc_find(&bs,&sht,1,difference);
 if(answer!=reference||(expected>=0&&answer!=(len_t)expected)){fprintf(stderr,"cache semantic mismatch\n");abort();}
 if(answer<bs.lml)for(int j=0;j<5;++j)if(difference[j]!=query[j]-heads[indices[answer]][j])abort();++checks;}
int main(void){ht.nv=sht.nv=4;ht.evl=sht.evl=5;ht.ev=ev;sht.ev=qev;sht.hd=qhd;qev[1]=query;
 qhd[1].val=1234567;qhd[1].sdm=0;bs.ht=&ht;bs.hm=rows;bs.lmps=indices;bs.lm=masks;bs.red=redundant;
 md.fc=37;md.trace_level=NO_TRACER;md.use_signatures=0;
 for(int i=0;i<10;++i){ev[i+1]=heads[i];rows[i]=row[i];row[i][OFFSET]=i+1;row[i][LENGTH]=1;}
 exponent(heads[0],2,0,0,0);exponent(heads[1],0,2,0,0);exponent(heads[2],0,0,2,0);
 active((bl_t[]){0,1,2},3,3);check(2,2,0,0,0);check(2,2,0,0,0);
 uint64_t hits=hc_rc_positive_hits;exponent(heads[3],1,0,0,0);active((bl_t[]){0,1,2,3},4,4);
 check(2,2,0,0,0);if(hc_rc_positive_hits!=hits+1)abort();
 check(0,0,0,2,4);check(0,0,0,2,4);uint64_t negative=hc_rc_negative_hits;
 exponent(heads[4],0,0,0,1);active((bl_t[]){0,1,2,3,4},5,5);check(0,0,0,2,4);
 if(hc_rc_negative_hits!=negative)abort();
 active((bl_t[]){1,2,3,4},4,5);check(2,2,0,0,0);check(2,2,0,0,0);
 hits=hc_rc_positive_hits;active((bl_t[]){1,3,4},3,5);check(2,2,0,0,0);if(hc_rc_positive_hits!=hits+1)abort();
 exponent(heads[1],0,0,0,3);active((bl_t[]){1,3,4},3,5);check(2,2,0,0,1);
 active((bl_t[]){3,1,4},3,5);if(hc_rc_active)abort();check(2,2,0,0,0);
 /* Shrink/reuse indices: old positive identities must not survive. */
 exponent(heads[0],0,1,0,0);exponent(heads[1],1,0,0,0);exponent(heads[2],0,0,0,1);
 active((bl_t[]){0,1,2},3,3);check(0,2,0,0,0);check(0,2,0,0,0);
 exponent(heads[3],0,0,1,0);active((bl_t[]){0,1,2,3},4,4);check(0,0,2,0,3);
 /* Every query has the SAME native hash; complete-vector checks prevent hits
  * between distinct exponent vectors. */
 uint64_t misses=hc_rc_misses;check(1,0,0,0,1);check(0,1,0,0,0);if(hc_rc_misses!=misses+2)abort();
 /* Exhaust all degree-at-most8 query exponent tuples across stable phases. */
 for(int phase=0;phase<3;++phase){active((bl_t[]){0,1,2,3},4,4);
  for(int x=0;x<=2;++x)for(int y=0;y<=2;++y)for(int z=0;z<=2;++z)for(int w=0;w<=2;++w){
   check(x,y,z,w,-1);check(x,y,z,w,-1);}}
 if(!hc_rc_positive_hits||!hc_rc_negative_hits||!hc_rc_saved_entries)abort();
 printf("{\"status\":\"PASS\",\"queries_checked\":%llu,\"positive_hits\":%llu,\"negative_hits\":%llu,\"avoided_entries\":%llu,\"full_hash_collisions_forced\":true,\"append_delete_head_change_reorder_shrink_reuse_checked\":true}\n",
  (unsigned long long)checks,(unsigned long long)hc_rc_positive_hits,(unsigned long long)hc_rc_negative_hits,(unsigned long long)hc_rc_saved_entries);
 return 0;}
