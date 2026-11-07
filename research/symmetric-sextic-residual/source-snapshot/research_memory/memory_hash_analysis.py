#!/usr/bin/env python3
"""Measured benchmark summary and source-based hash-capacity accounting.

Capacity formulas are allocation sizes for one table, NOT peak RSS estimates.
The RSS observations come from the fresh single-child benchmark receipts.
Vendor snapshots are optional. Their independently audited hashes are recorded
below; any locally present snapshot must match before the report is generated.
"""
from pathlib import Path
import hashlib
import json
import re

HERE=Path(__file__).resolve().parent
GIB=1024**3
AUDITED_VENDOR_SHA256={
    'data.h':'652834ff70b173ab66f93d4c5c5efefaee1a293db771a5c1c1ddc32a0a73da53',
    'hash.c':'1cae7cab02e7a2ed35a997f391c087e6e3ff4150ec221181ff4209da2b8df3fe',
    'f4.c':'a545ffd5e4117c4cc3cba421d64d7145fa295c0befc45d5fd5d0b735b5a031a5',
}

def vendor_provenance():
    vendor=[]
    for name,expected_hash in AUDITED_VENDOR_SHA256.items():
        p=HERE/('memory_vendor_'+name)
        status='absent_local_snapshot'
        if p.exists():
            actual_hash=hashlib.sha256(p.read_bytes()).hexdigest()
            if actual_hash!=expected_hash:
                raise ValueError('Vendor snapshot hash mismatch: '+p.name)
            status='present_hash_verified'
        vendor.append({
            'file':name,
            'sha256':expected_hash,
            'url':'https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/'+name,
            'hash_provenance':'Recorded SHA256 of the source snapshot used in the completed audit.',
            'local_snapshot_status':status,
        })
    return vendor

def matrices(path):
    rows=[]
    for m in re.finditer(r'^\s*(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+x\s+(\d+)\s+',path.read_text(),re.M):
        d,selected,pending,nrows,ncols=map(int,m.groups())
        rows.append({'selected_degree':d,'selected_pairs':selected,'pending_pairs':pending,
                     'rows':nrows,'columns':ncols,'matrix_area':nrows*ncols})
    return rows

def benchmark(tag):
    p=HERE/(tag+'_receipt.json')
    if not p.exists():return {'tag':tag,'status':'NO_FINISHED_RECEIPT'}
    data=json.loads(p.read_text());rows=matrices(HERE/(tag+'.log'))
    out={k:v for k,v in data.items() if k not in ['samples']}
    out['receipt_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
    out['measured_peak_rss_gib']=data['measured_peak_rss_kib']/1024**2
    out['sampled_cgroup_peak_gib']=data['max_sampled_cgroup_bytes']/GIB
    out['sampled_cgroup_headroom_bytes']=8*GIB-data['max_sampled_cgroup_bytes']
    out['proc_status_samples']=sum('VmRSS' in x for x in data.get('samples',[]))
    out['matrix_observations']=len(rows)
    diagnostic=re.findall(r'Enlarging exponent vector for hash table failed\s+for esz = (\d+)',(HERE/(tag+'.log')).read_text())
    if diagnostic:
        out['explicit_allocation_failure_capacity']=int(diagnostic[-1])
        out['failure_scope']='The solver reported a failed exponent-array allocation under RLIMIT_AS. This is not a claim that the shared cgroup memory limit was exhausted.'
    if rows:
        out['largest_observed_matrix']=max(rows,key=lambda x:x['matrix_area'])
        out['last_observed_matrix']=rows[-1]
        out['largest_observed_selected_pair_count']=max(x['selected_pairs'] for x in rows)
    return out

def main():
    vendor=vendor_provenance()
    slots=[]
    for n in [31,44,50,51]:
        slots.append({'variables':n,'exponent_fields_DRL':n+1,
                      'persistent_table_bytes_per_capacity_slot':2*(n+1)+32,
                      'additional_reset_arrays_bytes_per_capacity_slot':2*(n+1)+8,
                      'old_and_new_arrays_during_reset_bytes_per_capacity_slot':4*(n+1)+40})
    cases=[benchmark(tag) for tag in ['memory_old64','memory_scaled64','memory_B0_64','memory_B7_64']]
    comparison=None
    old_candidates=[HERE.parent/d/'finite_msolve_p37_reduced_hashreset.log'
                    for d in ['research_trace','proof_attempt5']]
    old=next((path for path in old_candidates if path.exists()),old_candidates[0])
    if old.exists():
        previous=matrices(old);current=cases[0].get('largest_observed_matrix')
        if previous and current:
            big=max(previous,key=lambda x:x['matrix_area'])
            comparison={'earlier_1000_pair_largest_matrix':big,'new_64_pair_largest_matrix':current,
                        'observed_max_matrix_area_ratio':current['matrix_area']/big['matrix_area'],
                        'interpretation':'Different schedules, thread counts and run lengths; this is not a comparison at equal algebraic progress. Earlier peak RSS was not measured.'}
    receipt={'status':'SOURCE_AND_MEASUREMENT_ANALYSIS',
      'platform_assumptions':{'pointer_bytes':8,'exp_t_bytes':2,'hd_t_bytes':16,'hi_t_bytes':4},
      'vendor_version':'msolve 0.11.0','vendor_sources':vendor,
      'normal_hash_map_load_policy':'hsz=2*esz at the capacities discussed here',
      'persistent_DRL_table_formula_bytes':'esz * (2*(nvars+1)+32)',
      'reset_additional_arrays_formula_bytes':'esz * (2*(nvars+1)+8)',
      'source_findings':[
        'Exponents use uint16_t even when the coefficient field fits in 8 bits.',
        'DRL stores nvars+1 exponent fields; a two-block elimination order stores nvars+2.',
        'enlarge_hash_table doubles allocated capacity.',
        'reset_hash_table keeps the old capacity, allocates replacement exponent and pointer arrays, reinserts live basis/pair monomials, then frees the old arrays.',
        'Thus hash reset removes stale entries but does not shrink capacity and can increase transient allocation.',
        'The allocation diagnostic does not identify which of the algorithm\'s hash tables was growing.'
      ],
      'per_slot_table':slots,
      'capacity_examples':[{'variables':31,'esz':2**24,'persistent_table_gib':1.5,'reset_main_arrays_gib':2.625},
                           {'variables':31,'esz':2**26,'persistent_table_gib':6.0,'reset_main_arrays_gib':10.5}],
      'measurement_caveats':[
        'Capacity arithmetic counts nominal arrays of one table, excluding polynomial coefficients, sparse matrices, allocator overhead and other tables.',
        'Allocation size, virtual address space and physical peak RSS are different quantities.',
        'The benchmark peak RSS is Linux getrusage(RUSAGE_CHILDREN) in a fresh runner with exactly one subprocess.',
        'The /proc samples may be unavailable because of PID namespaces; this does not invalidate getrusage.',
        'Cgroup readings cover the shared environment and are sampled, not an exact per-process peak.'
        ,'The configured pair budget is 64; logged batches can contain 65 or 66 pairs, so 64 is not asserted to be a strict observed upper bound.'
        ,'Smaller batches do not bound the total stored basis, pending pair set or hash capacity. A successful two-minute memory benchmark does not show that the complete computation fits this cap.'
        ,'Logged matrix dimensions describe sparse matrices; their row-times-column area is not a dense-memory allocation estimate.'
      ],
      'benchmarks':cases,'matrix_size_comparison':comparison,
      'next_step_policy':'Prefer small batches and the audited cubic presentation. A 64-pair/u0 run would be a controlled follow-up only if needed; u0 avoids reset-copy peaks but can retain more stale monomials.',
      'quotient_basis_verified':False,'quotient_degree_known':False,'trace_values_computed':False}
    (HERE/'memory_hash_analysis_receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
    lines=['# Lower-memory computation: measured results and mechanism','',
      'The identical historical input ran for its 120-second budget with the pair-budget option set to 64, hash regeneration enabled, and a 2 GiB virtual-address-space cap. Its measured peak resident memory was **%.3f GiB**. The new point-scaled cubic input used **%.3f GiB** during the same time budget. Both stopped at the time limit without a quotient basis or trace.'%(cases[0].get('measured_peak_rss_gib',0),cases[1].get('measured_peak_rss_gib',0)),'',
      '## Measurements','',
      '| Input | Status | Seconds | Measured peak RSS | Peak sampled shared cgroup | Basis output |',
      '|---|---|---:|---:|---:|---:|']
    for b in cases:
        if 'measured_peak_rss_gib' in b:
            lines.append('| %s | %s | %.2f | %.3f GiB | %.3f GiB | %s bytes |'%(b['tag'],b['status'],b['seconds'],b['measured_peak_rss_gib'],b['sampled_cgroup_peak_gib'],b['output_bytes']))
        else:lines.append('| %s | Pending | — | — | — | — |'%b['tag'])
    lines+=['',
      'RSS comes from Linux `getrusage` after a fresh runner reaps its sole child. The 2 GiB setting limits virtual address space; it is not the reported RSS measurement. Shared cgroup usage also includes the rest of the environment. The unavailable `/proc` samples arise from PID namespaces and do not affect the kernel RSS result.','',
      'The B0 chart failed an exponent-array allocation at capacity 16,777,216 and then exited with signal 11 under the address-space cap. Its 1.566 GiB measured RSS is compatible with an address-space allocation failure; it does not show that the shared 8 GiB physical-memory limit was exhausted. The B7 exceptional-chart screen timed out after 30 seconds and establishes no emptiness claim.','',
      '## Why the earlier hash growth was expensive','',
      'The pinned [type definitions](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/data.h) use 16-bit exponent entries. For ordinary degree reverse lexicographic order, each monomial stores one total-degree entry and one exponent per variable. On 64-bit Linux, one table reserves',
      '`esz * (2*(nvars+1) + 32)` bytes across its exponent block, pointers, metadata and hash map.','',
      'The [hash implementation](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/hash.c) doubles capacity when it grows. Its reset function retains that capacity and allocates replacement exponent/pointer arrays before freeing the old ones. Reset therefore needs another `esz * (2*(nvars+1)+8)` bytes temporarily. It can remove stale entries, but it neither shrinks the allocation nor guarantees a lower peak.','',
      '| Variables | Persistent bytes/slot | Additional reset bytes/slot |',
      '|---:|---:|---:|']
    lines += ['| %d | %d | %d |'%(r['variables'],r['persistent_table_bytes_per_capacity_slot'],r['additional_reset_arrays_bytes_per_capacity_slot']) for r in slots]
    lines += ['',
      'For 31 variables and 2^26 slots, one table alone calls for 6 GiB of persistent arrays. A reset can bring those arrays to 10.5 GiB while old and new storage coexist. These are allocation-capacity calculations, not measured RSS; sparse matrices, coefficients, allocator effects and other tables add separate costs.','',
      '## What the benchmark establishes','',
      'Smaller batches limit the union of monomials introduced into each F4 matrix. The 64-pair run\'s largest observed matrix was 45,545×583,419; the earlier 1000-pair run reached 204,612×990,506. These runs used different schedules and durations, so the dimensions do not establish equal algebraic progress or an equivalent-time memory saving. Earlier peak RSS was not measured.','',
      'The new point-scaled equations reduce total input degree to at most 3. That can reduce the number of distinct monomials needed even though the presentation retains more variables than the earlier degree 9 elimination. Its measured result appears above when available.','',
      'All runs are at prime 37 and base parameters (lambda, r, s) = (1, 2, 3). The 50-variable point-scaled presentation and the 51-variable B0 chart include inexpensive open conditions, but omit the full regularity localization. B0 and B7 are different strata of a sign quotient; neither chart alone is the entire trace algebra. Their differing matrix progress must not be interpreted as an equal-work performance comparison.','',
      'The pair-budget setting was 64; some logged batches contain 65 or 66 pairs. Smaller batches do not bound the total basis, pending pair set, or hash capacity. The two-minute observations therefore demonstrate reduced working memory over a bounded run, not that the complete calculation will finish within 2 GiB. Logged matrix dimensions refer to sparse matrices; multiplying their row and column counts does not estimate their actual storage.','',
      'Changing variable order does not change the bytes per exponent vector, but can change intermediate polynomial growth. A two-block elimination order adds another degree field; it is not automatically a memory optimization.','',
      'A later `-u0` comparison would test whether avoiding reset-copy peaks helps this input. It would also allow stale monomials to accumulate, so it should be a controlled experiment rather than an assumed improvement.','',
      '**Scope:** memory and preprocessing progress. No completed quotient, quotient degree, source trace, or final certificate is asserted.']
    (HERE/'memory_hash_analysis.md').write_text('\n'.join(lines)+'\n')
    print(json.dumps({'status':receipt['status'],'benchmarks':[{k:b.get(k) for k in ['tag','status','measured_peak_rss_gib']} for b in cases]}))

if __name__=='__main__':main()
