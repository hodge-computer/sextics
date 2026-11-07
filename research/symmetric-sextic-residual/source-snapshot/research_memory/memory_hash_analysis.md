# Lower-memory computation: measured results and mechanism

The identical historical input ran for its 120-second budget with the pair-budget option set to 64, hash regeneration enabled, and a 2 GiB virtual-address-space cap. Its measured peak resident memory was **1.152 GiB**. The new point-scaled cubic input used **0.725 GiB** during the same time budget. Both stopped at the time limit without a quotient basis or trace.

## Measurements

| Input | Status | Seconds | Measured peak RSS | Peak sampled shared cgroup | Basis output |
|---|---|---:|---:|---:|---:|
| memory_old64 | TIME_LIMIT | 120.14 | 1.152 GiB | 4.256 GiB | 0 bytes |
| memory_scaled64 | TIME_LIMIT | 120.14 | 0.725 GiB | 3.845 GiB | 0 bytes |
| memory_B0_64 | PROCESS_FAILED | 113.60 | 1.566 GiB | 4.432 GiB | 0 bytes |
| memory_B7_64 | TIME_LIMIT | 30.06 | 0.792 GiB | 3.910 GiB | 0 bytes |

RSS comes from Linux `getrusage` after a fresh runner reaps its sole child. The 2 GiB setting limits virtual address space; it is not the reported RSS measurement. Shared cgroup usage also includes the rest of the environment. The unavailable `/proc` samples arise from PID namespaces and do not affect the kernel RSS result.

The B0 chart failed an exponent-array allocation at capacity 16,777,216 and then exited with signal 11 under the address-space cap. Its 1.566 GiB measured RSS is compatible with an address-space allocation failure; it does not show that the shared 8 GiB physical-memory limit was exhausted. The B7 exceptional-chart screen timed out after 30 seconds and establishes no emptiness claim.

## Why the earlier hash growth was expensive

The pinned [type definitions](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/data.h) use 16-bit exponent entries. For ordinary degree reverse lexicographic order, each monomial stores one total-degree entry and one exponent per variable. On 64-bit Linux, one table reserves
`esz * (2*(nvars+1) + 32)` bytes across its exponent block, pointers, metadata and hash map.

The [hash implementation](https://github.com/algebraic-solving/msolve/blob/v0.11.0/src/neogb/hash.c) doubles capacity when it grows. Its reset function retains that capacity and allocates replacement exponent/pointer arrays before freeing the old ones. Reset therefore needs another `esz * (2*(nvars+1)+8)` bytes temporarily. It can remove stale entries, but it neither shrinks the allocation nor guarantees a lower peak.

| Variables | Persistent bytes/slot | Additional reset bytes/slot |
|---:|---:|---:|
| 31 | 96 | 72 |
| 44 | 122 | 98 |
| 50 | 134 | 110 |
| 51 | 136 | 112 |

For 31 variables and 2^26 slots, one table alone calls for 6 GiB of persistent arrays. A reset can bring those arrays to 10.5 GiB while old and new storage coexist. These are allocation-capacity calculations, not measured RSS; sparse matrices, coefficients, allocator effects and other tables add separate costs.

## What the benchmark establishes

Smaller batches limit the union of monomials introduced into each F4 matrix. The 64-pair run's largest observed matrix was 45,545×583,419; the earlier 1000-pair run reached 204,612×990,506. These runs used different schedules and durations, so the dimensions do not establish equal algebraic progress or an equivalent-time memory saving. Earlier peak RSS was not measured.

The new point-scaled equations reduce total input degree to at most 3. That can reduce the number of distinct monomials needed even though the presentation retains more variables than the earlier degree 9 elimination. Its measured result appears above when available.

All runs are at prime 37 and base parameters (lambda, r, s) = (1, 2, 3). The 50-variable point-scaled presentation and the 51-variable B0 chart include inexpensive open conditions, but omit the full regularity localization. B0 and B7 are different strata of a sign quotient; neither chart alone is the entire trace algebra. Their differing matrix progress must not be interpreted as an equal-work performance comparison.

The pair-budget setting was 64; some logged batches contain 65 or 66 pairs. Smaller batches do not bound the total basis, pending pair set, or hash capacity. The two-minute observations therefore demonstrate reduced working memory over a bounded run, not that the complete calculation will finish within 2 GiB. Logged matrix dimensions refer to sparse matrices; multiplying their row and column counts does not estimate their actual storage.

Changing variable order does not change the bytes per exponent vector, but can change intermediate polynomial growth. A two-block elimination order adds another degree field; it is not automatically a memory optimization.

A later `-u0` comparison would test whether avoiding reset-copy peaks helps this input. It would also allow stale monomials to accumulate, so it should be a controlled experiment rather than an assumed improvement.

**Scope:** memory and preprocessing progress. No completed quotient, quotient degree, source trace, or final certificate is asserted.
