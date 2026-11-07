SYMMETRIC SEXTIC: ACTUAL-TARGET CONTACT SPANNING STEP
Updated 2026-11-07 UTC

FULL TARGET STATUS: UNPROVED

This update closes a finite contact-spanning calculation for the unchanged
symmetric-sextic-residual instance at q=1. It does not supply Solution.lean,
a rational current, or a proof of HodgeComputer.HasCertificate for the target.
All earlier compiled Lean work and computational checkpoints are retained.

WHAT IS NEW

1. The actual weighted fiber has a full-rank 48-row contact jet.

   The reflection pencil is specialized to lambda=1, using the original
   rational coefficients 5/7 and 10/7. Its monic weighted equation G has
   coefficient normalization ell(1)=13/7. The contact-parameter curve is
   rho0=1/4+t/4096. Taylor orders 0 through 47 give 48 rows on the 60
   negative weighted-degree-six monomials.

   Discovery uses outward-rounded Arb arithmetic. An independent verifier
   reconstructs every required residual over exact Q(i), proves a Banach
   contraction, propagates rigorous errors for the implicit contact and
   normalized-functional coefficients, and checks a Neumann inequality for
   the selected 48-by-48 source minor. The verifier uses neither Arb nor
   floating-point linear algebra. Its total inverse defect is at most
   2^(-981), which is strictly less than one. A fresh independent replay
   used about 161 MiB of peak resident memory and took under five seconds
   in this environment; this measures finite-witness verification only.

   This is a finite exact-arithmetic proof with an ordinary mathematical
   justification of its bounds. It has not been translated into Lean.

2. The number 48 is bound to the exact protected equation.

   actual_target_jacobian.py reads the original instance.rec, checks its F
   and A after the reflection substitution, and checks equality with the
   contact circuit. It enumerates the complete negative degree-six part of
   the weighted Jacobian ideal. There are 60 source monomials and 12
   independent Jacobian columns. A selected rational minor has determinant

     -979256651289092498423808 / 1792160394037,

   and reduces to 1 modulo 5. Thus the actual quotient has dimension 48.
   This calculation is exact rational arithmetic, outside Lean.

3. The annihilator is justified by algebra, not interval zero containment.

   Write h=A+B, k=A-B and g1=G_u(-Q1). The norm identity is

     G(-Q1)=A^2-B^2+Q2*g2.

   Along the fixed-equation contact curve its derivative gives

     k*D(h)+h*D(k)+g1*D(Q1)+g2*D(Q2)+Q2*D(g2)=0.

   In the complete-intersection quotient (Q2,h,g1,g2), this says k*D(h)=0.
   Therefore the canonical residue functional R -> tau(R*D(h)) kills
   Q2,g1,g2,A,B. A previously certified regular sequence defines tau; the
   previous nonzero prescribed-source residue proves that the functional
   is nonzero. The new 39-column negative-ideal minor identifies the
   computed normalized row with this functional up to a formal unit.
   Multiplication by a formal unit preserves the rank of the first 48 jets.

   ContactResidueAnnihilator.lean proves the differentiated norm identity,
   the five-generator annihilation, and the spatial Jacobian reduction.
   These are actual ring/derivation proofs. The module does not assume or
   assert the missing target certificate.

4. The geometric nondegeneracy checks are explicit.

   A degree-six 84-by-84 Macaulay minor proves the projective (2,3) contact
   curve smooth throughout the original certified root ball. Its separate
   exact-rational checker reconstructs the matrix and verifies its inverse
   bound. The old (2,3,4,4) residue regularity and nonzero residue witnesses
   remain part of the dependency chain.

   The 44-by-44 contact derivative is contained in the 44-dimensional plus
   ideal component, so it proves that component is full. The minus
   component has rank 39 out of 40. Consequently the complete degree-six
   quotient has dimension one. The normal sequence of the smooth genus-four
   contact curve then gives h0(N)=h1(N)=1. This last interpretation uses
   ordinary algebraic geometry; it is not a Lean normal-bundle theorem.

   WeightedFiberSmoothness.lean proves that the exact weighted fiber at
   lambda=1 satisfies the projective Jacobian criterion. It replaces u by
   z^2, appends a sixth-variable Fermat term, applies the existing uniform
   mod-5 Macaulay theorem, and transfers back through an algebraic closure.

HOW THIS NARROWS THE REMAINING PROOF

The exact-target contact curve can replace the earlier unrelated weighted
rank witness. After the normal-obstruction/Abel-Jacobi comparison, the 48
independent jets make the curve correspondence detect all of the negative
(2,1) part. Hodge conjugation and duality would make its transposed image
surject onto the negative H3. Because the correspondence is supported on a
divisor, algebraic de Rham comparison would make these classes exact in the
function field.

The precise remaining theorem is:

  the actual contact obstruction span implies that
  H3_dR(T/k)^- -> H3(Omega^bullet_{k(T)/k}) is the zero map.

This means zero restriction on the negative subspace; it does not assert
that the entire function-field de Rham group vanishes. It requires an actual
algebraic correspondence, its comparison with the residue functional, and
the supported de Rham/Gysin argument. These are not presently supplied by
the pinned Lean development. The finite exact-arithmetic enclosures also
remain to be kernel-checked in Lean.

generic_fiber_current_route.txt spells out the passage from lambda=1 to an
open of this particular pencil. It does not assume that one successful
specialization proves all specializations. For the generic fiber the exact
weighted source is

  R_lambda = 2*b*d*(a^2-u)*(c^2-lambda^2*u)/ell(lambda)^2.

If the missing theorem supplies a relative rational primitive beta of its
residue, then -d(lambda) wedge beta is an absolute primitive after the
coordinate/form binding is checked. This avoids the old containing-Fano,
monodromy, and supported-projector routes. Finite trace and the already
proved regular/Euler clearing would then yield the original certificate.

The currently compiled endpoint remains

  SymmetricRegularCurrent.certificate_iff_regular_game_exists

and the proposition SymmetricRegularCurrent.RegularGameExists is unproved.

LEAN VALIDATION FOR THIS UPDATE

Both new modules compiled under Lean 4.33.1. All 20 public theorems in these
two modules passed an axiom audit admitting only propext, Classical.choice,
and Quot.sound. Both module objects then passed independent leanchecker
kernel replay against the existing pinned imported environment. This does
not claim that the numerical witnesses have been checked by Lean, or that
every imported dependency was replayed again from an empty environment.
Pinned mathlib revision: 0df444a360eaa60ab8c11dca51a86af692955474.

REPLAY AND FILE LAYOUT

The combined packet keeps Lean sources and objects at its top level.
New computations and interpretation notes are in research_span/; earlier
contact witnesses are in research_contact/. Within a development checkout
these directories are proof_attempt9/ and proof_attempt4/ respectively.

Python dependencies: Python 3, python-flint 0.9.0, NumPy, SciPy and SymPy.
The exact finite-jet checker requires python-flint; the independent target
Jacobian checker requires SymPy. Numerical discovery additionally uses
NumPy and SciPy. The exact finite-jet verifier does not invoke numerical
discovery. Earlier residue replays can be run from research_contact/.

From the extracted packet:

  python research_span/actual_target_jacobian.py
  python research_span/contact/check_contact_jet_witness.py
  python research_span/contact/check_contact_curve_smoothness.py

The finite witnesses are data, not added axioms. Axiom and kernel-replay
results for the two new Lean modules are in contact_steps_axiom_audit.json.
Use audit_contact_steps.py --repo /path/to/sextics to replay them with the
pinned Lean toolchain and existing imports. The existing verify_partial.py
uses the updated modules.json for the complete source rebuild.
compile_lean.py is the original
development-layout helper, not the portable packet entry point.

FAILED ROUTES RETAINED FOR SCOPE

The additional mod-5 Fermat contact seed is singular and supplies no etale
lift. Higher powers of the previously excluded block-Euler support cannot
help at q=1 by the paper's prescribed-support theorem. The bounded modular
screens of its square and cube are retained as redundant evidence only.
They are not characteristic-zero nonexistence proofs on their own.

No large F4 computation was restarted. Earlier checkpoint restoration links
remain in CHECKPOINT_DOWNLOADS.txt and the associated parts manifest.
