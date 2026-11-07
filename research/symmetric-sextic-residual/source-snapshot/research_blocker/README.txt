COMPACT DELIVERY WITH COMPLETE ARCHIVE PARTS
===========================================
This compact ZIP omits only the two large .hcf polynomial checkpoint files.
All source code, reports, validation evidence and native-state sidecars remain here.
The complete 1.48 GB ZIP is preserved in six verified download parts.
Open CHECKPOINT_DOWNLOADS.txt for saved download links and restoration instructions.
Use join_checkpoint_archive.py with parts_manifest.json to verify and assemble it.
Statements below that checkpoints are included refer to that complete archive.
The target theorem remains unproved and no full source trace has been evaluated.

SYMMETRIC SEXTIC: JACOBIAN LOCALIZATION AND NATIVE SOLVER REPAIR
7 November 2026

PROOF STATUS
============
The protected HasCertificate theorem is still unproved. No individual full
source trace has been evaluated. No complete finite incidence algebra, its
dimension, or final denominator/numerator certificate is supplied here.
The 51 previously checked Lean modules are retained; this continuation does
not add a new Lean theorem or change the protected target.

The new source identities are exact computer-algebra results. The native
solver patches were checked against independent complete-basis calculations
on small systems. Those checks are not a Lean verification of this target.
An incomplete packed F4 checkpoint is explicitly marked incomplete and must
never be treated as a Groebner basis or a trace certificate.

The current chosen contact form is not known to push forward to the prescribed
source. Its nine candidate comparisons must be evaluated and proved. If they
fail, a non-scalar combination of contact forms, an inverse push-pull operator,
or an exact differential correction may be needed; no scalar action is assumed.
Merely obtaining nine trace values would not prove source matching. Proving
all nine actual characteristic-zero coefficient equalities with the prescribed
source WOULD discharge that source-matching step.

1. CORRECTION TO THE EARLIER HASH-RESET EXPLANATION
================================================
The ordinary finite-field core_f4 path in pinned msolve 0.11.0 does not call
reset_hash_table or consult reset_ht. The only upstream call occurs in a
saturation trace-application path. Thus the earlier ordinary runs recorded
-u1, but that flag did not enable hash regeneration in those computations.
All their recorded peak RSS values and outcomes remain as measured.

finite_reset_path_audit.json/.md contains the complete-source and static-
binary audit. It corrects the operational interpretation in research_memory.
The earlier analysis of the unused reset function's nominal allocations was
an analysis of the function, not evidence that the function executed.

The local repair adds actual in-place compaction between ordinary F4 batches.
It marks every referenced basis monomial and pending-pair LCM, remaps those
references, compacts exponent vectors, and rebuilds the table. It does not
allocate a second full-capacity exponent table. A separate selective-column
patch avoids inserting matrix columns unused by surviving output rows.

The patches are restricted to the ordinary, signature-free, finite-field
NO_TRACER path. No broad claim about every msolve mode is made.

Files: compact_hash.c, selective_columns.c, msolve_compact_hash.patch,
msolve_selective_columns.patch, build_neogb.py, build_resumable*.py,
neogb_repair_receipt.json, finite_compact_invariants_receipt.json,
finite_selective_audit_receipt.json, and resumable*validation_receipt.json.

The invariant checks cover all retained exponent references, hash lookups,
degree/divisor masks, table resizing, block order, null/redundant rows, and
sanitizer checks. Complete small bases were compared with the original
native implementation and independently with SymPy, over four primes.

2. A SPARSE POLYNOMIAL REDUCTION
===============================
Write the parity blocks as

  Q2 = ab + M,       g2 = E + ab O,       R = R_even + ab T.

The exponents of a,b in M,E,O,T are even. The contact equation is
R + Q2*g2 = 0. Its fourteen odd-parity coefficients give, with an identity
pivot matrix,

  E = -M O - T.

The remaining equation is exactly

  R_even - M T + (a^2 b^2 - M^2) O = 0.

For the actual source T is quadratic in the contact coefficients. Eliminating
these fourteen g2 variables introduces no denominator and leaves cubic
equations. The recommended variant retains mu0,A0 with their two linear
point equations, avoiding expansion of those expressions throughout the
other equations.

Recommended exact packet: sparse32_system.json.
Core: 32 variables, 32 equations, 539 terms, maximum degree 3.
At p=37, (lambda,r,s)=(1,2,3), with the same six small opens:

  sparse32_smallopens_p37.ms       38 variables/equations; 585 terms
  sparse32_witness_1rhs_p37.ms     70 variables/equations; 1,878 terms
  sparse32_witness_2rhs_p37.ms    102 variables/equations; 3,171 terms

The builders and independent audits leave lambda,r,s formal over QQ. They
check all original equations, reduced derivatives, reconstruction derivatives,
off-ideal chain rules, point equations, and all six open-factor bindings.
With the recorded permutations, J32=J46=J44_point on the equation ideal.
Here J46 is the Jacobian of the UNELIMINATED POINT-SCALED 46-equation system.
It is not the pre-scaling alpha-incidence Jacobian, whose conversion has
separate unit factors already recorded in the earlier source packets.

Alternative sparse30 files eliminate the two point variables too, but are
denser. The full Schur25 elimination is also exact; its one/two-RHS inputs
have 56/81 variables, but 276,850/502,090 terms and degree 9. Its determinant
identity is J25=delta1^17*delta2^20*delta3^24*J44. The smaller variable count
therefore does not provide an automatic computational advantage.

3. DETERMINANT-FREE JACOBIAN LOCALIZATION
=======================================
For n equations f(x)=0, write J=Df. Adjoin two unrestricted vectors v,w and
the equations Jv=b, Jw=c. Over the field with 2n independent RHS parameters,
the augmented algebra is exactly the localization where det(J) is invertible.

On a corank-d stratum, the x-locus has dimension at most d. The bad triples
(x,b,c), with b,c in the image of J, therefore have dimension at most
d+2(n-d)=2n-d<2n. Generic RHS values exclude every singular point. The
determinant is then a unit, and the adjugate formula gives the inverse
algebra isomorphism. The accompanying theorem treats scheme-level units,
including possibly nonreduced input rings.

For a FIXED RHS choice (one or two vectors), a completed zero-dimensional
augmented quotient would certify the same equivalence: any singular point
would leave a positive-dimensional unrestricted kernel fibre. No fixed
finite-field RHS choice is declared generic before that acceptance gate.
Adding an arbitrary linear normalization of the solve vectors invalidates
this criterion; an explicit counterexample is included.

Files: jacobian_witness_theorem.txt, jacobian_witness_system.py,
trace_jacobian_witness_review.txt, and corresponding exact packets/receipts.
The selected residue and regularity opens delta9,D10 remain to be imposed
inside any completed finite algebra.

4. PACKED CHECKPOINTS AND MEMORY
===============================
The packed .hcf format stores each monomial's exponent vector once, then
stores polynomial rows as monomial-ID/coefficient pairs. A flag distinguishes
input generators, incomplete checkpoints, and native completed output.

The first checkpoint preserves the original-generator prefix and every
non-null current derived row. This gives an ideal-preserving partial-basis
restart: retained derived rows belong to the original ideal, and the original
prefix prevents removal of any original equation. This is not, by itself, an
exact pending-pair-queue snapshot. Earlier pairs may need to be rechecked.

The final native-state driver additionally saves the exact pending pair queue,
basis redundancy flags, leading-monomial list, row degrees, numeric metadata,
and completed-round count in a matching .hcf.state sidecar. A state resume
skips initial pair generation. Four small systems passed sixteen process
checkpoints with every matrix batch matching the uninterrupted repaired
build; final packed bases were byte-identical and matched independent SymPy.
An independent read-only source review found no material defect on the
supported path. The sidecar is tied to the pinned native ABI and trusted
computation; its accidental-mismatch fingerprint is not a proof certificate.
Keep each packed checkpoint and its matching sidecar together.

The strict restart checks exposed a separate upstream pair-selection read
beyond the live queue. The documented bounds patch extends the selected
prefix through the LCM group of its last selected pair, with all reads inside
the live range. The final driver also flushes checkpoint output every 64 MiB,
synchronizes it, and advises completed input/output pages DONTNEED.

One earlier resumed run was interrupted by the shared-cgroup guard during a
large temporary checkpoint write, despite process peak RSS of 1,457,384 KiB.
The incomplete temporary file was rejected and removed; the earlier valid
checkpoint was preserved. The cache-aware writer addresses this distinct
shared-page-cache pressure. Its advisory does not promise a bound on unrelated
memory in the shared cgroup. See sparse32_resume_checkpoint_failure.json and
resumable_state_REPLAY.txt for the exact distinction and replay instructions.

The initial flat restart loader would expand one exponent vector per term.
For the 131,940,444-term, 38-variable checkpoint that would require about
20.05 billion bytes just for that int32 exponent array. The replacement
dictionary-native importer reads the packed dictionary directly into the
native hash and row storage. It keeps flat exponents only for the small
original-generator prefix. On the actual checkpoint, import took 5.298710
seconds and peaked at 814,460 KiB RSS; the derived flat array is absent.

The initial checkpoint contained 2,939 rows, 1,252,479 distinct monomials,
and 131,940,444 terms; its uncompressed size was 1,150,735,532 bytes. It was
produced after 314.56 seconds, with 1,412,900 KiB peak RSS. It is incomplete.
Only 7 of 38 variables had pure-power leading monomials at that point, which
does not decide the dimension of the final quotient.

The earlier repaired 138-variable two-RHS run reached a 600-second limit
at 701,676 KiB peak RSS, also incomplete. These runs use different equations
and do not compare matched algebraic progress or establish a full-run memory
bound. The exact current outcomes are in the guarded-run receipts/logs.

The serial native-state run saved 158,257,737 terms after 45 completed
batches, with 53,867 pending pairs and peak RSS 1,784,256 KiB. A four-thread
continuation saved 288,999,191 terms after batch 53, with 63,369 pending
pairs and peak RSS 3,041,692 KiB. The subsequent one-batch profile saved
300,588,916 terms after batch 54, with 64,135 pending pairs. None is a
completed basis; increasing row and term counts do not measure percentage
completion. The current main checkpoint is identified in the package-level
receipt, which also records any later continuation.

The first 102-variable Jacobian-witness attempt crashed under its 2 GiB
address-space cap without an explicit allocation diagnostic. Its cause was
not established. A retry with 64-pair batches and a 4 GiB address-space cap
successfully saved 68,876,431 terms after 65 batches, with 109,783 pending
pairs and 1,407,396 KiB peak RSS. This validates that retry's checkpoint
outcome, not a general cure for the earlier crash or finite dimensionality.

The guarded runner now separates raw cgroup memory from a conservative
estimate of nonreclaimable pressure. Clean unmapped non-shmem file cache can
occupy most of the cgroup when hashing checkpoints. Raw cgroup values are
retained in every receipt; they are not equated with process RSS or evidence
of physical-memory exhaustion. Per-process address-space limits remain active.

4A. PARALLELISM AND MEASURED LOOKUP COST
======================================
The separate OpenMP driver supports one to eight threads. An upstream loop
temporary was made thread-private. Twenty complete small-basis comparisons
and twenty-four cross-thread native-state resumes passed. The underlying
symbolic-preprocessing loop remains serial, and no fourfold speedup is claimed.
See resumable_openmp_REPLAY.txt and its validation receipt.

Native timing counters showed that symbolic preprocessing dominated both
target formulations. A profile-only driver then measured one real main-route
batch without changing reducer choices or checkpoint format. It performed
835,256 lookups, of which 65,514 found a reducer. The original scan inspected
2,935,500,503 leading positions and made 2,924,533,806 full divisibility tests.
Lookup took 43.0777 seconds; constructing the resulting 194,964,886 row terms
and inserting their monomials took 43.4851 seconds. The two regions exclude
initial S-pair row construction and other symbolic bookkeeping and include
profiling overhead. Their shares were about 49.8% and 50.2%, respectively.
This is a measured bottleneck, not an end-to-end speedup result.

An optional bounded reducer cache is separately frozen. It checks full keys,
active status, unchanged heads and preserved order before reusing a first
divisor; invalid cases fall back to the original scan. Ten complete systems,
twelve native-state resumes, per-lookup shadow comparisons, and a forced-
collision semantic fixture passed. Its fixed storage for the 38-variable
target is 22.5 MiB plus small reported index snapshots. Small-fixture savings
are not extrapolated to the target. See reducer_cache_REPLAY.txt and the
actual target continuation log for measured results.

That cache continuation processed two 256-pair batches and saved 328,207,197
terms after batch 56, with 65,498 pending pairs and 3,540,256 KiB peak RSS.
It avoided only 136,144 of roughly 9.25 billion ordered scan visits. Thus the
cache was not a useful target speed fix; it is retained as a tested historical
variant, not the recommended lookup implementation.

The recommended lookup implementation is the separate exact divisor index.
It rebuilds a small hash table of active leading monomials once per symbolic
phase, enumerates the divisors of a query monomial when their count is at
most 256, checks full exponent equality on hash matches, and chooses the
smallest active-list position. Unsupported modes and larger divisor counts
fall back to the original exact scan. The first-divisor choice is preserved.
Ten complete systems, twelve native-state restores, per-lookup shadow audits,
and an 860-query collision/fallback fixture passed.

The actual 835,256-query target batch was then replayed from exactly the same
input basis AND native queue. Every query used the index; the maximum divisor
count was 64. The table used 65,536 bytes. It enumerated 36,118,595 divisors
instead of scanning 2,935,500,503 active-head positions. Lookup time fell from
43.0777 to 0.5870 seconds, and matrix-batch time from 91.64 to 46.70 seconds.
The resulting 2,521,901,008-byte polynomial checkpoint is byte-for-byte
identical (also checked with cmp), including all 300,588,916 terms. The state
sidecars have different timing counters, as expected. Peak RSS was 2,615,160
KiB versus 2,598,136 KiB in the profiled scan run; this was a speed improvement,
not a measured reduction in overall peak RSS. These are one-batch results,
not a full-solve speedup or a completion-time prediction. Future queries can
exceed the enumeration bound and fall back to scanning.

See divisor_index_REPLAY.txt, divisor_index_validation_receipt.json,
divisor_index_target_comparison.json, and the latest continuation receipt.

FINAL SAVED MAIN CONTINUATION: the divisor-index run completed two further
batches and saved 373,625,484 terms in 4,268 packed rows (4,230 native basis
rows plus the original 38 generators). It has 1,682,471 distinct monomials,
58 completed batches and 68,546 pending pairs. Peak RSS in this continuation
was 4,093,324 KiB, about 3.90 GiB. Its 3,116,905,876-byte packed checkpoint
and matching native-state sidecar are included, together with the separate
Jacobian-witness checkpoint. Both are explicitly incomplete.

latest_computation_status.json is the concise final status record. There are
zero evaluated full source traces and zero new Lean theorems in this turn.
No total-runtime estimate, global dimension, or completion percentage follows
from these intermediate counts. The solver jobs have stopped at checkpoints;
this package does not imply a continuing background computation.

5. AN EXACT OBSTRUCTION TO A NEW GEOMETRIC SHORTCUT
================================================
The upstream quadratic-net theorem at commit
a2716a5d55e176ae5f999483b4b3115831385216 requires a representation of the
equation using three ternary quadrics in one parity block.

For this target, such a representation in either original block would require
q=xy+xz+yz to belong to the net and x^6+y^6+z^6 to be a cubic in that net.
The fixed mixed coefficient forces q into the net; setting the other block
to zero gives the Fermat sextic.

This is impossible over C. Parametrize q=0 by
(x,y,z)=(u(u+v),v(u+v),-uv). The restriction is

  F12=(u^6+v^6)(u+v)^6+u^6 v^6.

A proposed net would make F12 a cubic in two quartics. Its twelve roots must
then partition into three quartics with dependent coefficient vectors.
At the good completely split prime 1459, all 5,775 possible partitions have
rank three. Every partition has an explicit nonzero minor witness.

Any characteristic-zero partition has monic algebraic-integer coefficients.
Reducing at a prime above 1459 preserves the twelve distinct roots and would
give a forbidden dependent partition. Thus this is a characteristic-zero
obstruction, not merely an unsuccessful modular search.

Files: trace_quadratic_net_obstruction.py/.txt, the complete partition-minor
certificate, and its receipt. A second independent Gaussian-elimination
audit checked all partitions. The obstruction includes arbitrary changes
within each original block. It does not cover transformations mixing the
blocks, other geometric methods, or the requested certificate itself.

6. OTHER EXACT FINDINGS AND REMAINING GATES
=========================================
The nine universal current coefficients have rank eight: only the previously
known coefficient-field relation follows from the point/motion equations.
An explicit projective P29 (P35 with small-open inverse variables) lies in
the common zero set of the leading generator forms. This prevents invoking
the elementary no-zeros-at-infinity Euler-Jacobi shortcut. It is not a proof
of an affine positive-dimensional component.

The fixed-quadric norm image has degree 16,384. This is not asserted to be
the degree of the actual full incidence algebra. The obvious contact gauges
are already removed, and the current small-open fibre's global dimension
has not been established.

The remaining work is concrete but unfinished: complete and independently
verify a suitable finite quotient; impose all required opens; evaluate the
nine actual source traces; reconstruct/verify the characteristic-zero source
identity (adjusting the chosen form if its comparisons fail); clear legal denominators; and
close the protected HasCertificate statement in Lean.

The independent final review confirms the sparse32 source binding, including
the unchanged 2,964-node original scalar-circuit prefix. It also records the
precise Jacobian naming and the distinction between evaluating traces and
proving their required source identity. See final_mathematical_review.txt/.json.

A final read-only upstream check at 2026-11-07 02:09:32 UTC found main at
2d60d08d25fba3e02162b39d4c50f6b467e7f506, four commits after the protected
checkout. The q=1 instance is unchanged. Its current provenance still cites
the two-reflection support theorem, and the complete comparison added or
modified no Lean files or files under formal/. This check found no new
accepted formal solution for the target on public main; it makes no claim
about unpublished work. Pinned source URLs and blob hashes are recorded in
upstream_symmetric_q1_status.json. The protected local checkout is unchanged.

7. REPLAY AND DEPENDENCIES
=========================
The mathematical source builders/audits use Python and SymPy (python-flint
is used when available). The quadratic-net obstruction uses only Python's
standard library. The packed reader/guarded runner also use the standard
library. Source paths recognize the sibling research_memory and research_trace
directories in the complete archive. portability_receipt.json verifies that
the source-path repairs changed none of the exact packets or solver inputs.

The native driver is built from pinned official msolve 0.11.0 source, the
included patches, and a public GMP header for the checked installed 64-bit
GMP ABI. Build receipts contain source and binary hashes and compiler flags.
The local SIMD build requires the CPU features verified in those receipts.
See the included upstream licenses. No external repository was modified or
published by this continuation.

Representative commands from the research_blocker directory:

  python sparse32_system.py
  python trace_sparse32_audit.py
  python trace_quadratic_net_obstruction.py
  python packed_f4.py inspect <checkpoint.hcf>

Before a native replay, build the corresponding tested driver and use the
exact command recorded in the desired run receipt, replacing session-local
paths with the extracted archive paths. Do not use the old flat importer for
the large target checkpoint.
