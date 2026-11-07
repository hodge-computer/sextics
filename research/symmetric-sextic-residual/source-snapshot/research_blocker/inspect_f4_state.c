/* Read-only timing/queue inspection for the pinned native checkpoint ABI.
 * GPL-2.0-or-later. These counters are performance evidence, not a proof.
 */
#include "data.h"
#include <stdio.h>
#include <string.h>

int main(int argc,char **argv) {
    if(argc!=2)return 2;
    FILE *f=fopen(argv[1],"rb");if(!f)return 2;
    char magic[8];uint32_t a[12];uint64_t b[3];md_t md;
    if(fread(magic,1,8,f)!=8||memcmp(magic,"HCF4ST01",8)
       ||fread(a,4,12,f)!=12||fread(b,8,3,f)!=3
       ||a[0]!=1||a[1]!=sizeof(md)||fread(&md,sizeof(md),1,f)!=1){fclose(f);return 2;}
    fclose(f);
    printf("{\"schema\":\"native-f4-state-timings-v1\",\"variables\":%u,\"prime\":%u,"
           "\"rounds\":%llu,\"basis_rows\":%u,\"pending_pairs\":%u,\"threads\":%d,"
           "\"wall_seconds\":{\"selection\":%.6f,\"symbolic\":%.6f,\"linear_algebra\":%.6f,"
           "\"basis_update\":%.6f,\"conversion\":%.6f,\"hash_reset\":%.6f},"
           "\"cpu_seconds\":{\"symbolic\":%.6f,\"linear_algebra\":%.6f,\"conversion\":%.6f},"
           "\"maximum_matrix_rows\":%lld,\"maximum_matrix_columns\":%lld,"
           "\"basis_independently_verified\":false,\"full_trace_evaluated\":false}\n",
           a[2],a[3],(unsigned long long)b[1],a[5],a[10],md.nthrds,
           md.select_rtime,md.symbol_rtime,md.la_rtime,md.update_rtime,md.convert_rtime,md.rht_rtime,
           md.symbol_ctime,md.la_ctime,md.convert_ctime,(long long)md.mat_max_nrows,(long long)md.mat_max_ncols);
    return 0;
}
