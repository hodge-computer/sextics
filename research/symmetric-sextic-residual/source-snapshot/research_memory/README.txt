SYMMETRIC SEXTIC: LOWER-MEMORY COMPUTATION
7 November 2026

STATUS
======
The new cubic presentation used 760,044 KiB (0.725 GiB) peak resident memory
in a two-minute trial. The earlier degree-nine presentation used 1,207,864 KiB
(1.152 GiB) with the same solver settings and time budget: a measured 37.1%
reduction. Neither run completed a Groebner basis. This does not establish
that the complete computation fits in that amount of memory or that the two
runs made equal algebraic progress.

No individual full trace has been evaluated. No complete localized finite
coordinate algebra or its dimension has been computed. The protected theorem
HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q
HodgeSubmission.A remains UNPROVED.

This continuation contains exact coordinate reductions, transport of all nine
actual source operands, bounded native-solver runs, and an independent audit
of the trace route. The new algebraic checks use exact computer algebra, not
new Lean proofs. All 51 previously checked Lean source modules are retained.

The source identities are still candidate conditions for the chosen canonical
contact form. Its required push-pull normalization, and the exact comparison
with the target current (possibly including a differential correction), have
not been established. Even completing the nine traces would need to address
that source-matching question before yielding the requested certificate.

1. WHAT WAS CHANGED
===================
For a contact coefficient c_e whose monomial has Y-degree k, use

  hat(c_e) = alpha^k c_e,          t = alpha^2.

The moving point (1,r,alpha,s*alpha) becomes (1,r,1,s). Its two equations
eliminate hat(mu0) and hat(A0) with coefficient 1, introducing no new open
condition. Keeping the quartic auxiliary coefficients, instead of eliminating
them, leaves 44 equations in 44 variables, all of degree at most 3.

This realizes the exact quotient by the involution
(B,alpha) -> (-B,-alpha). It is not an arbitrary replacement of alpha by its
square. On the prescribed alpha!=0 open, adjoining alpha with alpha^2=t is
a quadratic etale cover. The original nine operands are invariant, so their
normalized traces descend unchanged when the complete algebra is retained.

point_scaled_system.py verifies all 44 coefficient identities exactly over
Q(lambda,r,s), both unit-coefficient eliminations, and the degree bounds.
The coefficient-weight sums are 78 and 132. With the recorded row and column
orders, on the incidence the determinant relations are

  J_old = 2*alpha^(-53)*J44,
  delta9_hat = alpha^399*delta9_old,
  D10_hat = alpha^534*D10_old.

The specialized mod-37 cubic solver input at (lambda,r,s)=(1,2,3) has
50 variables, 50 equations, 698 terms, and maximum degree 3 after adding six
small opens. The earlier eliminated input has 31 variables, 31 equations,
4,434 terms, and maximum degree 9. Fewer variables did not yield the lower
observed memory usage in these runs.

2. THE SECOND SYMMETRY: ALL EIGHT CASES ARE RETAINED
==================================================
The remaining involution reverses all hatted A and B coefficients together.
The full Jacobian open implies that the B-vector is not zero. Partition it
into the disjoint cases

  B0=...=B(j-1)=0, Bj!=0,         j=0,...,7.

Write b=hat(Bj), z=b^2, hat(Ai)=b*Ai, and hat(Bi)=b*Bi, with Bj=1 and
earlier Bi=0. The resulting equations remain cubic. The main B0 case has
44 core variables; case j has 44-j. This is a second degree-two quotient,
not a guarantee of a smaller Groebner-basis memory footprint.

point_scaled_Bpivot.py checks another 352 exact coefficient identities,
44 for each case. Together the two equation builders verify 396 identities.
No case has been discarded or declared empty. If the quotient case algebras
have dimensions n_j and unnormalized traces tau_ij, then

  dimension(original) = 4*sum_j n_j,
  Tr_original(M_i) = 4*sum_j tau_ij,
  normalized Tr_original(M_i) = (sum_j tau_ij)/(sum_j n_j).

A plain average of the eight normalized traces would be incorrect in general.
The main B0 case actually used MORE memory in the recorded trial; the first
cubic quotient is the best measured presentation so far.

3. THE ACTUAL SOURCE EXPRESSIONS WERE TRANSPORTED
================================================
point_scaled_current.py differentiates the original equations in the original
variables before substituting the new coordinates. It transports the actual
nine source operands, their Jacobian density, and the two selected regularity
matrices. It does not substitute a freshly defined canonical form that would
omit coordinate-change differential terms.

The determinant frames remain small matrices over an exact arithmetic circuit;
their enormous multivariate determinants are never expanded. The first source
packet has 35,827 scalar nodes. Exact parity checks cover every entry of the
46-by-46 incidence matrix, the 220-by-220 residue matrix, and the 286-by-286
regularity matrix. The required extra 1/t factors are retained.

Writing Tbar*sigma=96*e_last gives the source components L_j. Instead of
expanding 45 cofactors or selecting a kernel coordinate that might vanish on
another component, form the 45-by-45 matrix

  B = [ Hbar ; h_alpha*qbar - q_alpha*hbar ],

whose determinant equals the full transformed incidence determinant. Solve
B*v=e_last. All nine operands share this solve and the residue solve:

  M_i = (sum_(j=0)^15 v_(10+j)*L_j)*P_i/t.

This construction is valid on the whole full open. It does not divide by
q_alpha or select an unproved unit pivot. After the second quotient, the
corresponding density denominator is t*z.

Three independent finite-field controls compare the first transported source
with the original matrices and explicit cofactors. They check 35,383 scalar
node identities per control and equality of all nine operands. A further nine
controls check the second quotient across all eight cases. These controls
satisfy the two eliminated point equations and check every original open.
They are NOT solutions of the remaining contact equations and are NOT traces.

sign_quotient_current.py transports all eight cases. Its default export is
b0_quotient_current.json; other case packets can be generated with its builder.
The mathematical audit is in research_memory/trace_memory_audit.txt.

4. ACTUAL MEMORY MEASUREMENTS
=============================
Each run used msolve 0.11.0, one thread, -m64 -u1 -l2, and RLIMIT_AS=2048 MiB.
RLIMIT_AS is a virtual-address-space cap, not a resident-RAM measurement.
Peak RSS was measured independently with Linux getrusage(RUSAGE_CHILDREN)
in a fresh runner containing exactly one solver child.

Input                       Seconds    Peak RSS, KiB    Peak GiB    Result
Earlier degree-nine input    120.14       1,207,864        1.152     Time limit
Point-scaled cubic input     120.14         760,044        0.725     Time limit
Main B0 quotient             113.60       1,642,120        1.566     Allocation failure
Exceptional B7 quotient       30.06         830,260        0.792     Time limit

The B0 log records failure to allocate an exponent array at capacity
16,777,216 slots, then signal 11. This occurred under the 2 GiB address-space
cap; it is not evidence that the shared 8 GiB physical-memory limit was used
up. B7 produced no emptiness certificate. All runs have stopped.

The 37.1% comparison holds for the measured two-minute trials with identical
solver settings and budgets. The inputs are different preliminary algebra
presentations, with different intermediate branches and small opens; neither
yet includes the full regularity localization. This is not a controlled claim
of equal progress, identical incomplete ideals, or guaranteed final memory.

The vendor-source audit explains why -u1 is insufficient by itself: the hash
reset removes stale entries without shrinking capacity, and temporarily
allocates replacement arrays before freeing old ones. Smaller pair batches
limit individual matrix growth but do not bound the total basis or hash table.
The configured budget of 64 can yield logged batches of 65 or 66 pairs.

See memory_hash_analysis.md and its JSON receipt for source provenance,
allocation formulas, solver/input hashes, exact measurements, and matrix
dimensions. Individual memory_*_receipt.json files and logs are also included.
No solver executable or vendor source snapshot is bundled. The report generator
embeds the audited snapshot hashes and URLs, checks snapshots if present, and
explicitly records their absence if run without them.

5. WHAT THE LOWER-MEMORY METHOD STILL NEEDS
==========================================
The small-open solver input includes the three Delta factors, t, beta, and
G_w; the B-pivot cases additionally include z. The full incidence determinant,
selected degree-nine residue determinant, and selected degree-ten regularity
determinant remain mandatory. They are preserved in the exact source packet
but not yet imposed in the solver input. A completed preliminary basis would
therefore still need exact full-open filtering.

Once a COMPLETE finite algebra is known, nine dense multiplication matrices
are unnecessary. For a verified univariate representation K[zeta]/(F), with
F monic, squarefree, and degree n, and an operand N/D with D invertible,

  V = N*D^(-1) mod F,
  Tr(N/D) = coefficient of zeta^(n-1) in (F'*V mod F).

One can process irreducible factors sequentially, perform the shared 45-by-45
and 220-by-220 source solves in each factor, filter the full opens exactly,
and add the field traces. Alternatively, a certified monomial basis permits
streaming one normal-form column at a time and retaining only its diagonal
coefficient. Neither method supplies the missing complete algebra by itself.

The independent audit also derives an exact residue reformulation on the
first quotient:

  det(Jbar)=2*t^(-31)*J44,
  Tr(M_i)=Res_full_open((t^30/2)*Fbar*P_i; H1,...,H44).

The B0 formula has numerator -t^30*z^14*F2*P2_i/4. These formulas cancel the
incidence determinant against the global-residue denominator. They have NOT
been evaluated. The separate length-96 residue computation used to define
the contact form is not the residue functional of the much larger incidence
algebra and cannot replace it.

A completed finite-field calculation would still need justified specialization
and exact reconstruction before proving a statement over Q(lambda,r,s).
In characteristic p, compare Tr(M_i)-n*T_i without dividing by n, since p
could divide the rank. A partial basis, a single root, or a random projected
minimal polynomial cannot certify a complete trace.

6. REPRODUCTION AND PRESERVATION
================================
The previous trace README is PREVIOUS_TRACE_COMPUTATION.txt. All previous
payload files were checked against the previous 373-entry SHA256 manifest
before this update. The prior README and manifest are retained verbatim.
All 51 Lean source modules and their objects are unchanged. This continuation
adds no Lean theorem and does not claim a new kernel check.

Pinned upstream commit: ca173aad142bd5f6bf5dd156b6798223a45df54f.
Lean 4.33.1; Mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
Protected HodgeTarget.lean SHA256:
a51532e0442d72e8ce95d6728390fac0f719287d1cf20020701625bc1b5409d9

From the unpacked package, use Python 3 with SymPy and python-flint as needed:

  python research_memory/point_scaled_system.py
  python research_memory/point_scaled_Bpivot.py
  python research_memory/point_scaled_current.py
  python research_memory/sign_quotient_current.py
  python research_memory/memory_hash_analysis.py

These regenerate packets and receipts; elapsed-time fields can change. To
repeat a bounded solver benchmark, supply the separately obtained msolve
0.11.0 binary whose hash/provenance is recorded in the receipts:

  python research_memory/root_memory_run.py \
    --binary /absolute/path/to/msolve \
    --input research_memory/point_scaled_p37_smallopens.ms \
    --tag repeat_cubic --pairs 64 --seconds 120 --memory-mib 2048

The benchmark runner stops the child process at the requested time and records
the outcome. Its logs do not claim a verified basis just because a process
exits successfully. Package integrity is recorded in PACKAGE_SHA256.json;
memory_computation_receipt.json summarizes the status and source bindings.

The useful result here is an exact reformulation with lower observed working
memory, together with a way to evaluate the actual source without expanded
cofactors. The unresolved step is still the complete finite algebra and its
traces, followed by source matching and the final Lean certificate.
