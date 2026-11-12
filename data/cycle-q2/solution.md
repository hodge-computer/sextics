# A nonconstructive geometric route for cycle-q2

## Development compilation checkpoint — 12 November 2026

**The complete Lean existence proof remains unfinished.** This checkpoint
preserves compiler-driven repairs to the exterior differential, projector,
and finite-trace constructions. `Submission.missing_geometric_existence`
still contains the existing explicit admission. The complete proposal has
not passed protected verification or a new independent kernel replay.

The source snapshot was taken at **18:57 UTC on 12 November 2026**, against
parent commit `2dc62680311df2045971a268f1410b00e045d875`. The existing
development run uses Lean 4.33.1, pinned Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`, one worker, and a 7,168 MiB
Lean memory limit. Its recorded results are:

| Scope | Result at this checkpoint |
| --- | --- |
| Full `Proposal.GeometricFormalInputs` | Compiled successfully, exit 0, 1,345.43 seconds; sampled peak process-tree RSS 6,184,751,104 bytes. |
| Extracted `DebugQ2.TargetSections` | Compiled successfully, exit 0, 149.05 seconds. This diagnostic covers finite descent, actual trace projectors, supported projectors, and finite top de Rham constructions. |
| Full `Proposal.GeometricTarget` | Still running in the recorded receipt; no exit status yet. The diagnostic result does not establish compilation of the complete module. |
| Full `Proposal.Solution` and protected certificate verification | Not completed in this development run. The final existence theorem remains admitted. |

The successful full-module receipt matches the submitted
`GeometricFormalInputs.lean` SHA-256
`ca30a92600d3196948fedc0dc9965452cf3f17ece8fc4eeeed2bb320cc35b3df`.
The diagnostic source SHA-256 is
`6ff9f1958b17e8b607b5f601414a1e52170e451b77a9629ec460c4f82e444d42`,
extracted from `GeometricTarget.lean` with SHA-256
`c8fdd4b50a68e3d28e5ce8ddf352200d87a4dedf5858b80346b854558a89a595`.
`Solution.lean` has SHA-256
`2dedc1e8c78fe0a3d50e44d7d6a63decc1ed7dbf2216df0d500cae4fef471688`;
its changes since the parent commit are compilation-status comments only.

These results are development compilation evidence, with the scopes above.
Earlier source-only statements below describe their historical checkpoints;
earlier kernel-replay records do not certify the newly modified sources.

## Current Lean source continuation — 12 November 2026

**The complete Lean existence proof is still unfinished.** This continuation
implements further parts of the written proof with explicit Lean proof bodies,
using the existing polynomial quotients, normal Cech modules, Fermat Jacobian
components, and actual exterior powers of Kaehler differentials. It does not
remove or discharge `Submission.missing_geometric_existence`. The one existing
explicit admission in that theorem remains.

**At the source-only checkpoint `2dc62680311df2045971a268f1410b00e045d875`,
no Lean elaboration, compilation, language server, Lake invocation, kernel
replay, mathematical recomputation, or proposal-verifier execution was run.**
The additions were reviewed as source against the existing declarations and
Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`. They were uncompiled
proof drafts at that checkpoint, including their dependency on the earlier uncompiled bridge
commit `619b7e36367aef388d7d3419995ccb5d1fc618ef`. Earlier verification records in
this document do not certify the modified sources. The development compilation
checkpoint above records the later compiler repairs and their verification scope.

The source base for this continuation is
`baf0dbc951fdcac9b9453bc67a8b85935ca3e371`, which records the full classical
proof below. The new work is integrated into the three existing Lean files;
it adds no proposal modules and does not change the protected data or target.

| Existing file | Namespace | New construction and conclusion |
| --- | --- | --- |
| `Solution.lean` | `CycleQ2NormalKoszulBridge` | The literal five-generator seed quotient maps to the actual normal Cech quotient by a simple-pole representative. Its normal connecting class has numerator `originalK * L - A`. On degree-nine numerators, the existing seed trace is the coefficient of a specific nonzero actual Cech class, giving an exact equivalence of vanishing. |
| `GeometricFormalInputs.lean` | `CycleQ2AffineDeRhamComplex` | A basis of the genuine second exterior power, the actual degree-one and degree-two exterior derivatives, their scalar-times-wedge formulas, and all successive-composition identities through the existing degree-three differential. |
| `GeometricTarget.lean` | `CycleQ2GeometricBridgeAlgebra`, `CycleQ2SupportedProjectorAlgebra` | Construction of the projection associated to complementary submodules, its self-adjointness for the actual Fermat trace pairings, the resulting zero-or-full-image criterion, and a zero-constant polynomial projector with the required composition-closure property. |
| `GeometricTarget.lean` | `CycleQ2AffineFiniteTopCohomology` | Actual Kaehler differentials and exterior pullback over a finite extension of the protected function field, normalized trace on three-forms and four-forms, compatibility with differentiation, and split-injective pullback on the existing top de Rham quotient. |

### The trace now reaches an actual Cech class

The new map sends a polynomial numerator `p` to the class of
`p / (g1 * g2)` in the existing overlap localization. The three curve equations
vanish there, while multiplication by either `g1` or `g2` yields a genuine
single-open boundary. These five identities descend the map through the
existing `SeedAlgebra`; its image under the existing normal/scalar Cech
equivalence is proved, not postulated.

An explicit polynomial inclusion and elimination comparison connect the
four-variable reduced quotient to that map. The existing one-dimensional
degree-nine quotient calculation then gives

\[
\left[\frac{p}{g_1g_2}\right]
=\operatorname{seedTrace}([p])\,\nu,
\qquad \nu\ne0,
\]

when the eliminated numerator is homogeneous of degree nine. Nonvanishing
of `nu` uses the existing residue calculation excluding boundaries of
arbitrary pole order. The declarations `seedTrace_simplePoleClass` and
`seedTrace_eq_zero_iff_simplePoleClass` state these conclusions on the actual
objects.

This construction concerns the sparse seed with `r^3 = 2`. Its associated
surface is singular. The classical proof separately intersects the nonempty
rank open with the nonempty smooth open in the full parameter family. Neither
that generic intersection with the required geometric family nor the
projective Serre/semiregularity identification is asserted by this Cech map.

### Exterior differentiation and finite-cover descent

The new lower differentials use the already constructed commuting tangent
derivations of the protected hypersurface function field. Their codomains are
the actual exterior powers of `Omega[K / C]`; coefficient vectors are only
coordinates in proved bases. The scalar-times-wedge formulas identify the
coordinate maps with exterior differentiation. The supplied proof bodies
establish `d1(d a) = 0`, `d2(d1 omega) = 0`, and `d3(d2 eta) = 0`.

For a finite extension `L/K`, separability and the transitivity sequence for
Kaehler differentials prove that the pulled-back four coordinate forms are
a basis of `Omega[L / C]`. Exterior pullback is constructed from the universal
alternating property. Normalized field trace on coefficients gives actual
maps `traceThree` and `traceFour`, with

\[
\operatorname{Tr}(d\eta)=d\operatorname{Tr}(\eta),
\qquad
\operatorname{Tr}(\operatorname{pullback}\omega)=\omega.
\]

Consequently `pullbackClass_injective` supplies the finite-cover injection on
the original top de Rham quotient. `exact_pullback_iff` descends an actual
primitive by its constructed trace. These statements do not assert that the
specific protected source becomes exact on such an extension.

### What still prevents closing the final theorem

The remaining work is geometric: construct and compare the projective sheaf
classes and Serre trace; build the smooth moving-curve family and its nonzero
Abel--Jacobi/cylinder map; identify the actual Fermat pairings with the
polarized variation; realize the polynomial projector by divisor-supported
algebraic correspondences and spread it to the protected pencil; and prove
the Leray and algebraic de Rham comparisons giving vanishing of the specific
residue class. None of these statements is replaced here by a new axiom, an
admitted lemma, or an altered final target.

Prepared for `fqlx` with OpenAI ChatGPT assistance, continuing the credited
geometric route and existing formal developments described below.


## Classical existence proof — 12 November 2026

**The written classical argument is complete; the Lean formalization remains
incomplete.** This update records a nonconstructive proof of the precise
mathematical statement named by
`Submission.missing_geometric_existence`,
including its conversion to the ordinary protected certificate. The full
argument and finite certificates are included below under
[Complete classical proof and finite certificates](#complete-classical-proof-and-finite-certificates).

The preceding classical-proof commit changed only this explanation. No Lean elaboration, compilation,
language server, Lake invocation, kernel replay, or proposal-verifier execution
was run. The existing explicit admission in `Solution.lean` remains;
neither this written proof nor its finite calculations are a checked Lean
replacement. No expanded coefficient tuple is claimed.

Prepared for `fqlx` with OpenAI ChatGPT assistance. Credit to
`benediamond` and collaborators for the geometric route, and to Claire
Voisin and the other authors cited in the reconstruction for its classical
inputs. The proof reconstructs and expands
[Chapter 3D at the pinned source revision](https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/docs/03d-hodge-loci.md);
it does not claim independent authorship of that strategy.

### Exact conclusion and geometric route

Use the protected chart \(X_0=1\), with equation \(f\), numerator \(a\),
function field \(K=\operatorname{Frac}(\mathbf C[x_0,\ldots,x_4]/(f))\),
and \(g=\partial_0f\), as defined in the existing explanation. The conclusion is

\[
\exists\,\eta\in\Omega^3_{K/\mathbf C},\qquad
d\eta=
\frac12\left(
\frac{a_{00}}{g^3}
-\frac{3a_0g_0+ag_{00}}{g^4}
+\frac{3ag_0^2}{g^5}
\right)dx_1\wedge dx_2\wedge dx_3\wedge dx_4.
\]

The complete proof below supplies the following chain.

1. The complete-intersection socle trace is identified with the actual curve
   Serre trace by the Koszul connecting isomorphism. The rank-seven
   Noether–Lefschetz map and rank-eight augmentation give a surface motion
   preserving the orbit divisor class and having nonzero Abel–Jacobi
   derivative.
2. The holomorphic implicit function theorem integrates the divisor class.
   Lefschetz \((1,1)\), a positive twist, and the flag Hilbert scheme produce
   genuine algebraic moving curves over a dense open of the full parameter
   space.
3. The scalar-only Higgs equations imply irreducibility of the invariant
   rational variation. The curve correspondence therefore surjects onto the
   invariant \(H^3\). Polarization and a polynomial in the correspondence
   produce a projector supported on a divisor square.
4. Proper Hilbert parameter spaces spread a supported representative to
   every smooth member, including the special weighted pencil obtained from
   the protected fourfold. Normalized trace descends the relative
   correspondence from a finite cover.
5. Over the affine pencil base, the next Leray filtration piece is zero.
   The relative projector therefore fixes the whole relevant
   \(H^1(U,R^3)\) class. Together with the hyperplane contribution, this
   proves divisor support of the full protected residue class.
6. Explicit normal pole reduction identifies the literal affine source
   form. Grothendieck's affine algebraic de Rham theorem gives its rational
   three-form primitive. An explicit product-rule identity clears and
   homogenizes that primitive to the required certificate.

### Exact finite checks

The finite inputs were checked with exact arithmetic; no Lean process was
involved.

| Input | Result |
| --- | --- |
| Complete-intersection length and socle degree | \(96\), degree \(9\) |
| Noether–Lefschetz rank | \(7\) |
| Rank after adjoining the Abel–Jacobi test row | \(8\) |
| Explicit maximal minors modulo \(109\) | \(80\) and \(76\) |
| Higgs equations on \(33\times33\) matrices | \(1088\) independent identifications; only scalar matrices remain |
| Recorded peak memory | \(27168\) KiB |
| Recorded elapsed time | Approximately \(0.22\) seconds |

The characteristic-zero seed uses \(r^3=2\), whereas \(r=57\) and \(i=33\)
are residues modulo \(109\). Flatness of the complete-intersection model
transfers the nonzero minors to characteristic zero. This reconstruction
does not identify that seed with the literal complex \(r=57\) used in parts
of the older formal continuation.

The appendices contain the complete integer Higgs forest certificate and
the exact-check receipt. For independent reproduction, retrieve the
[pinned finite-input script](https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/scripts/verify-hodge-locus-span.py).
With Python 3 and NumPy available, import that downloaded file and call only
the two functions below; running the script's `main()` also performs two
larger fourfold calculations that this proof does not use.

```python
import hashlib
import importlib.util
import json
from pathlib import Path

source = Path("verify-hodge-locus-span.py")
assert hashlib.sha256(source.read_bytes()).hexdigest() == (
    "9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9"
)
spec = importlib.util.spec_from_file_location("q2_finite_inputs", source)
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
seed_receipt, _ = module.seed_divisor()
print(json.dumps(seed_receipt, indent=2))
print(json.dumps(module.higgs_field(), indent=2))
```

The source SHA-256 is also recorded verbatim in Appendix B. The displayed
reproduction snippet is documentation; it was not executed for this push.

### Earlier formalization checkpoints

The following sections retain the existing implementation and historical
verification record. References there to missing geometric comparisons
describe the Lean formalization; the ordinary mathematical proofs are
supplied by the new reconstruction appended below.


## Uncompiled implementation continuation — 12 November 2026

**Source draft only. No Lean elaboration, compilation, language server,
Lake invocation, kernel replay, tests, or proposal-verifier execution was
performed for this continuation.** It starts from source commit
`8d88f06e782704e301a6e817195f907e816f46d8`. The historical verification
records later in this document describe earlier sources and do not certify
the four new components or the modified combined files.

The reconstructed mathematical argument has now supplied the following
concrete Lean source bodies, using the existing definitions rather than
new abstract placeholders for the geometric objects:

| Existing proposal file | New namespace | Implemented scope |
| --- | --- | --- |
| `GeometricFormalInputs.lean` | `CycleQ2ExplicitPoleReduction` | Explicit third-order to first-order pole reduction in the actual ambient rational-function field; regularity and specialization of its coefficient to the existing residue source form. |
| `GeometricFormalInputs.lean` | `CycleQ2AffineTopCohomology` | The quotient of actual fourth exterior forms by the image of the actual complex-linear exterior derivative, with zero class equivalent to an actual three-form primitive. |
| `GeometricTarget.lean` | `CycleQ2GeometricBridgeAlgebra` | The finite Higgs projector dichotomy transferred to endomorphisms of the actual degree-six, character-one Fermat Jacobian component and its actual socle pairings. |
| `Solution.lean` | `CycleQ2OrbitTraceBridge` | Character eigenvalues for the existing localization action, the literal ambient test, and the correctly twisted three-term orbit and nonzero-pairing identities. |

The pole reduction defines the genuine normal derivation
\(D_t=g^{-1}\partial_0\), with \(D_t f=1\) proved from the existing
protected equation. For \(b=a/g\), its correction coefficient is

\[
\psi=-\frac{b}{2f^2}-\frac{D_t b}{2f},\qquad
D_t\psi=\frac{b}{f^3}-\frac{D_t^2b/2}{f}.
\]

The regular simple-pole coefficient specializes to exactly
`CycleQ2AffineExactness.residueSourceForm`; this algebraic specialization
is not being called a cohomological residue map.

The top quotient uses **complex scalars**, as required by the actual
differential. It establishes the precise algebraic target for a future
comparison map:

```lean
CycleQ2AffineTopCohomology.residueClass CycleQ2AffineClearing.affineA = 0 ↔
  ∃ η : CycleQ2AffineExterior.Form 3,
    CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA
```

It does not establish the left-hand vanishing. The projector result likewise
does not construct a geometric polarized variation or a supported projector.
The orbit result identifies the actual localization action but does not
construct the semiregularity or Abel–Jacobi comparison.

**The final `Submission.missing_geometric_existence` theorem and its single
explicit admission are unchanged. There is still no closed Lean proof of
`CycleQ2Nonconstructive.AffineResidueFormExact`.** In particular, these
source bodies do not replace the admission by a new axiom, an assumed zero
residue class, a conditional assertion presented as unconditional, or a
choice of a nonexistent witness.

The remaining geometric work includes the actual normal-class-to-surface
and Abel–Jacobi comparison; the identification of the Jacobian pairings
with a geometric variation and the supported-cycle construction; the
relative Leray/vanishing argument; and the cohomological residue and
algebraic de Rham comparisons that prove the actual top class is zero.
Those results are not supplied by the finite algebra alone or by an
existing theorem in the inspected project and pinned Mathlib sources.

This continuation is integrated into existing proposal files, so it adds
no submitted helper files. The protected instance, goal, proof manifest,
shared library, and workflow definitions are unchanged. It is saved on a
separate branch with no pull request, whose push does not match the
repository's build/verification workflow triggers. At that source-only
checkpoint, compilation was deferred as requested; the development compilation
checkpoint above records the later run.

## Status and protected goal

**Draft; not a completed Lean proof.** The algebraic implication from a
rational primitive of the actual affine residue to the unchanged certificate
is proved. Its formulation in actual relative Kähler differentials and
exterior powers, the formal normal residue density, and universal exterior
pullback are proved. Specialization from the actual generic pencil and
descent through finite algebraic extensions are now proved as well.
The concrete incidence equations, their polynomial relations, and the
sparse and theta-one seed Čech residue calculations are also formalized.
The actual fixed-sextic Jacobian now has rank 1922, its image is the
actual relation kernel, and a trace-one complex tangent exists by a
nonconstructive augmented-matrix rank argument. Exact characteristic-zero
Jacobian identities now cover the literal seed curve by normal charts.
Global equation-class bases of the genuine seed conormal modules and
nonvanishing of the actual chosen-curve normal connecting class are now
proved. The full relative surface Čech calculation, its character dimensions
7, 8, 8, canonical tensor base change, and conditional character-one
persistence on the actual pointed component are proved. Exact seed-surface
Jacobian identities and a coefficient-open argument now cover every
relevant prime of the actual finite pointed trace surface. Actual local
lifts of coefficient motion and the relative Kodaira--Spencer/transition
identity remain available for the next geometric comparison.
The existence of a primitive remains unproved. The one
explicit admission, `Submission.missing_geometric_existence`, states exactness
of that genuine exterior form. Consequently `Submission.certificate` still
depends on `sorryAx` and must not be accepted.

A nonconstructive existence proof is sufficient. Neither an evaluated
coefficient tuple nor a bound on its denominator degree is required.
The new algebra does not replace existence by a choice operation.

The exact \(F,A,q=2\) remain those of the [instance record](instance.rec), in
coordinate order \((X_0,X_1,X_2,Y_0,Y_1,Y_2)\). The protected goal asks for a
nonzero homogeneous denominator \(D\), homogeneous \(N_i\) of degree
\(\deg D+7\), and an unrestricted polynomial \(Q\), with
\(\gcd_{\mathbb C}(F,D)=1\), satisfying
\[
AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]
No protected polynomial or condition has been changed.

## The exact remaining theorem

Use the actual projective chart \(X_0=1\), with
\[
(x_0,x_1,x_2,x_3,x_4)=(X_1,X_2,Y_0,Y_1,Y_2)/X_0.
\]
The dehomogenized equation and source are
\[
\begin{aligned}
f={}&1+x_0^6+x_1^6+x_2^6+x_3^6+x_4^6\\
&+\tfrac12(x_0x_2x_3+x_0^3x_1x_3x_4+x_1^3x_2x_4),\\
a={}&x_0^2x_1^3x_2^2x_3^2x_4.
\end{aligned}
\]
Let
\[
K=\operatorname{Frac}\bigl(\mathbb C[x_0,\ldots,x_4]/(f)\bigr),
\qquad g=f_0.
\]
The code proves irreducibility of \(f\), the domain property, and
\(\bar g\ne0\) in this actual field. It constructs the four implicit
coordinate derivatives
\[
E_j(\bar P)=\overline{\partial_jP}
-\frac{\overline{f_j}}{\bar g}\overline{\partial_0P},
\qquad 1\le j\le4,
\]
and proves their quotient well-definedness, extension to fractions,
annihilation of complex constants, and pairwise commutation.

Write polynomial expressions in \(K\) without bars and define
\[
c=\frac12\left(
\frac{a_{00}}{g^2}
-\frac{3a_0g_0+a g_{00}}{g^3}
+\frac{3a g_0^2}{g^4}
\right).
\]
The remaining assertion is exactly
\[
\boxed{\exists w\in K^4:\quad
c+\sum_{j=1}^4E_j(w_j)
-\frac1g\sum_{j=1}^4w_jE_j(g)=0.}
\]
In Lean, it is:

    ∃ w : Fin 4 → CycleQ2AffineHypersurface.AffineFunctionField,
      CycleQ2AffineResidueClosure.affineResidueExpression
        CycleQ2AffineClearing.affineA w = 0

[Solution.lean](Solution.lean) names this proposition
`CycleQ2Nonconstructive.AffineResiduePrimitiveExists`. The proved theorem
`exact_form_iff_primitive` identifies it with
`CycleQ2Nonconstructive.AffineResidueFormExact`, which asserts exactness of
the actual top exterior form described below. The single admission now
states that equivalent exterior-form assertion. The final theorem applies

    CycleQ2AffineExactness.protected_certificate_of_exact_residueSourceForm

from [GeometricFormalInputs.lean](GeometricFormalInputs.lean).
That implication has no assumed grading, regular lift, residue
homomorphism, derivative compatibility, or desired defect identity:
all of these have been proved for the actual target. It does not prove
the boxed existence assertion.

## Genuine exterior forms and the normal residue calculation

The module of differentials is mathlib's actual relative module
\(\Omega^1_{K/\mathbb C}\). The universal differential satisfies
\[
dz=\sum_{j=1}^4 E_j(z)\,dx_j
\quad(z\in K),
\]
and the four \(dx_j\) form a proved \(K\)-basis. This includes the
quotient relation \(df=0\), the eliminated coordinate, and arbitrary
fractions. All derivations are complex-linear; the base field has not been
changed to absolute differentials over the integers.

Let \(\mathrm{vol}=dx_1\wedge\cdots\wedge dx_4\), and let
\(\beta_j\) be the increasing wedge omitting \(dx_j\).
The actual third and fourth exterior powers have the resulting bases.
The degree-three exterior derivative is complex-linear and satisfies
\[
d_3(b\beta_j)=db\wedge\beta_j.
\]
The proof identifies the wedge with multiplication in mathlib's exterior
algebra, proves the scalar Leibniz rule, and proves uniqueness from this
generator formula. In particular,
\[
d_3\left(\sum_{j=1}^4(-1)^{j-1}\frac{w_j}{g}\beta_j\right)
=\frac1g\left(\sum_jE_j(w_j)-\frac1g\sum_jw_jE_j(g)\right)\mathrm{vol}.
\]
Consequently the boxed PDE is equivalent to existence of a three-form
\(\eta\) with
\[
d_3\eta=(c/g)\,\mathrm{vol}.
\]
The negative of the displayed three-form is the primitive of the positive
source when the PDE holds. This sign is part of the checked equivalence.

The normal density is also derived in a genuine formal coordinate, rather
than supplied as an assumed residue formula. Hensel's lemma constructs
\(z(T)\in K[[T]]\), with constant coefficient \(x_0\), such that
\[
f(z(T),x_1,x_2,x_3,x_4)=T.
\]
The resulting polynomial substitution is proved injective, and its
constant-coefficient map is exactly the existing quotient map to \(K\).
The actual chain rule gives \(g(z(T))z'(T)=1\). Writing
\(g_0=\partial_0g\) and \(g_{00}=\partial_0^2g\), its first three jets are
\[
z'(0)=1/g,\qquad z''(0)=-g_0/g^3,\qquad
z'''(0)=(3g_0^2-g g_{00})/g^5.
\]
The formal Laurent density uses the image of the actual equation \(f\):
\[
\frac{a(z(T))z'(T)}{T^3}.
\]
Its \(T^{-1}\)-coefficient is proved equal to \(c/g\).
`residueSourceForm_eq_formalResidue` binds this coefficient to the genuine
top exterior form used by the certificate implication.

The coordinate change is also proved in universal differential forms. Set
\(S=K[[T]]\), write \(\phi\) for the actual normal substitution, and put
\(v=z'(T)\). The coefficientwise extensions of the four complex tangent
derivations satisfy
\[
\widetilde E_j(\phi(P))
=\phi(\partial_jP)-v\phi(f_j)\phi(\partial_0P).
\]
They commute with one another and with \(\partial_T\). Their actual
five-coordinate Jacobian determinant is \(v\). The proof additionally
differentiates \(\phi(f)=T\) inside the full algebraic Kähler module
\(\Omega^1_{S/\mathbb C}\) and constructs the induced exterior pullback.
It proves
\[
\phi^*(dx_0\wedge\cdots\wedge dx_4)
=v\,dT\wedge d\phi(x_1)\wedge\cdots\wedge d\phi(x_4).
\]
This uses the universal properties of differentials and exterior powers;
it does not assume that the differential module of a power-series ring
has rank five. Thus the normal-density factor is tied to the actual
universal coordinate-volume pullback. The global comparison with the
cohomological residue and geometric support is still needed.

Coefficientwise derivations on actual Laurent series are also proved to
obey the Leibniz rule. Taking any Laurent coefficient commutes with them,
even when a primitive has negative powers of the formal parameter.
The proof does not infer a rational generic primitive from an unbounded
formal deformation.

## Actual generic specialization and finite descent

`CycleQ2GenericSpecialization` constructs an actual deformation of the
protected affine hypersurface. Choose any polynomial \(H\) whose image
in \(K\) is nonzero and put
\[
\tau=-f/H\in\mathbb C(x_0,\ldots,x_4).
\]
The generic coordinate ring is the actual quotient
\(\mathbb C[x_0,\ldots,x_4,t]/(f+tH)\). The proof identifies its
kernel, embeds it in the ambient rational function field, and proves
that this field is its fraction field. It also proves that \(\tau\)
is transcendental over \(\mathbb C\), so the parameter field is
genuinely \(\mathbb C(t)\).

The generic tangent derivations annihilate \(\tau\) and every element
of \(\mathbb C(t)\), and commute pairwise. A faithful Hensel chart
maps this actual generic field into \(K((T))\), sends \(\tau\) to
\(T\), and intertwines the generic tangents with the coefficientwise
affine tangents. The generic residue density is computed with the
parameter held fixed. Its constant Laurent coefficient is precisely
\(c/g\), the density of the protected affine residue form.

Consequently a generic rational primitive specializes to an actual
primitive on the protected hypersurface by taking constant Laurent
coefficients. The primitive may have negative powers of \(T\); no
regularity at the special fiber is assumed. This is the checked theorem
`affine_primitive_of_generic_primitive`, with the final implication
`protected_certificate_of_generic_relative_primitive`.
The concrete `protectedDirection` gives the pencil containing both the
protected and Fermat equations. The theorem does not assume that this
pencil has a generic primitive.

`CycleQ2FiniteDifferentialDescent` proves that a derivation extends
uniquely to a finite characteristic-zero field extension, that these
extensions preserve commutators, and that normalized field trace
commutes with the extended derivations. It does not require a Galois
extension. Applied to the actual affine field, primitive existence
over a finite extension is equivalent to primitive existence over the
base field.

`CycleQ2GenericFiniteSpecialization` composes these results. A primitive
over any finite extension of the actual generic field descends by trace
and then specializes to the protected certificate. The extension need
not itself embed in the selected Laurent chart: trace is taken first.
This removes the finite-extension and specialization obligations from
that route. It leaves the existence of the initial generic primitive
unproved.

`CycleQ2VeryGeneralPencil` also proves faithful polynomial specialization
along a pencil through an arbitrary prescribed complex point, over a
chosen countable coefficient subfield. This uses simultaneous avoidance
of its countably many nonzero polynomial conditions. Applying this to
a generic primitive requires first retaining its finitely many
coefficients in that subfield. The theorem does not embed a field of
several independent variables over all of \(\mathbb C\) into
\(\mathbb C(t)\) while fixing every complex number.

## Explicit reduction to the weighted pencil

The paired-sign reduction is now bound directly to the actual function
field and source. In the same affine coordinates, put
\[
u=x_1,\qquad v=x_4,\qquad \lambda=v/u,\qquad w=u^2.
\]
The proof obtains \(u\ne0\) by applying the actual tangent derivative
\(E_1\) to a hypothetical equality \(u=0\): it already satisfies
\(E_1(u)=1\). The weighted equation is
\[
T_\lambda=1+x_0^6+x_2^6+x_3^6+(1+\lambda^6)w^3
+\tfrac12(x_0x_2x_3+\lambda x_0^3x_3w+\lambda x_2w^2).
\]
Its vanishing after \(w=u^2\), \(\lambda=v/u\) is proved from the
actual quotient equation. Its source is
\[
b=x_0^2x_2^2x_3^2w^2,\qquad a=\lambda b.
\]
Here the normal coordinate \(x_0\) is unchanged. Differentiating the
literal polynomial identity \(u a=v b\) twice in that normal coordinate
proves \(c_a=\lambda c_b\), where \(c_b\) is the same proved
normal-source formula with \(a\) replaced by \(b\).

Define three actual complex derivations of \(K\) by
\[
R_1=E_2,\qquad R_2=E_3,\qquad
R_3=\frac{E_1+\lambda E_4}{2u}.
\]
Each annihilates \(\lambda\); the last is the direction of the weighted
coordinate \(w\) and has zero ordinary coordinate divergence. For any
\(t=(t_1,t_2,t_3)\in K^3\), define
\[
W(t)=\left(\frac{\lambda t_3}{2u},\ \lambda t_1,\
\lambda t_2,\ \frac{\lambda^2t_3}{2u}\right).
\]
The actual product and quotient rules give the checked identity
\[
\operatorname{affineResidueExpression}(a,W(t))
=\lambda\left(c_b+\sum_{j=1}^3R_j(t_j)
-\frac1g\sum_{j=1}^3t_jR_j(g)\right).
\]
Consequently
`CycleQ2AffineWeightedTransfer.protected_certificate_of_relative_primitive`
proves the unchanged protected certificate from existence of a solution
to this three-derivation equation. There is no assumed coordinate chain
rule or transfer identity in that theorem.

This gives a concrete algebraic endpoint for the weighted-threefold route.
The new module does not assert that a solution of the three-derivation
equation exists, construct a relative cohomology theory, or identify a
cylinder image containing the specified source. Those are the remaining
geometric and de Rham inputs. The final admission continues to state the
original equivalent four-dimensional exterior exactness.

## The proved algebraic conversion

### Regular lifts and the normal-source identity

In the ambient rational field
\(L=\mathbb C(x_0,\ldots,x_4)\), let \(R\) consist of fractions \(P/T\)
whose denominator is nonzero and relatively prime to \(f\).
The code proves that \(R\) is a subring preserved by every coordinate
derivative. It constructs the actual surjective residue homomorphism
\[
\rho:R\longrightarrow K,
\qquad \ker\rho=fR.
\]
Representative independence, the kernel equality, and surjectivity are
proved from polynomial and fraction-field properties. Thus any proposed
\(w\in K^4\) has lifts \(\widetilde w_j\in R\). These lifts are chosen only
after the existence hypothesis has supplied \(w\).

Put \(B=\partial_0(a/g)\) and define an actual rational vector field by
\[
\begin{aligned}
v_j&=f\widetilde w_j &&(1\le j\le4),\\
v_0&=\frac{a}{2g}
+f\left(\frac{B}{2g}
-\sum_{j=1}^4\frac{f_j\widetilde w_j}{g}\right).
\end{aligned}
\]
The coordinate calculations prove
\[
2v(f)=a+fB
\]
and
\[
a-2v(f)+f\operatorname{div}v
=f^2\left(c+\sum_j E_j(\widetilde w_j)
-\frac1g\sum_j\widetilde w_jE_j(g)\right).
\]
The expression in parentheses is evaluated in \(L\); its image under
\(\rho\) is the exact boxed equation in \(K\).
The identity uses equality of the actual mixed polynomial partials.
It is not a hypothesis of the constructor.

If the boxed equation vanishes, the expression in parentheses belongs
to \(fR\). Therefore
\[
a-2v(f)+f\operatorname{div}v=f^3t
\quad\text{for some }t\in R.
\]
Every component of \(v\) is also in \(R\).

### Actual projective chart and homogeneous clearing

The code constructs the injective chart map \(L\to\mathbb C(X_0,\ldots,Y_2)\)
by \(x_i\mapsto Z_{i+1}/Z_0\), where
\((Z_0,\ldots,Z_5)=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\).
It proves the chain rule for every rational function, not only for
polynomials or formal generators.

Define
\[
V_0=0,\qquad V_{i+1}=Z_0^7v_i(Z_1/Z_0,\ldots,Z_5/Z_0).
\]
The exact scaling identities are
\[
F=Z_0^6f(Z/Z_0),\quad A=Z_0^{12}a(Z/Z_0),
\]
and
\[
A-2V(F)+F\operatorname{div}V
=Z_0^{12}(a-2v(f)+f\operatorname{div}v).
\]
Thus the homogeneous defect divided by \(F^3\) is regular along \(F\).

The finite common-denominator and homogenization proofs produce a
nonzero homogeneous \(D\), relatively prime to \(F\), and polynomials
\(N_i=DV_i\) homogeneous of degree \(\deg D+7\).
The code proves that homogenizing an affine denominator prime to \(f\)
gives a denominator prime to \(F\); \(Z_0\) is also prime to \(F\).
Ordinary quotient differentiation gives the exact protected numerator.
Finally, primality of \(F\) cancels any remaining legal denominator and
produces the polynomial \(Q\).

This proves every algebraic clause of `HasCertificate` from the actual
affine primitive. The affine chart is essential here: a rational field
on the six-coordinate cone alone would not supply the required degree.

### Other checked algebraic routes

The consolidated helper also preserves and extends the following useful
results.

- **General pole reduction.** A rational primitive with any finite
  \(F\)-pole order and a differential with pole order at most three can
  be replaced by one with pole order at most two. The proof extracts the
  finite pole order by unique factorization, then lowers it by an explicit
  divergence identity. Coordinate derivatives commute and preserve legal
  denominators. The regular remainder is retained.
- **Euler and Cartan calculations.** A homogeneous horizontal skew array
  \(B_{ij}\) of degree \(k+1\) is lifted by
  \(N_j=(k+5)^{-1}\sum_l\partial_lB_{lj}\), with
  \(B_{ij}=X_iN_j-X_jN_i\) and \(N_j\) homogeneous of degree \(k\).
  The rational coordinate Cartan identity and its certificate consequence
  are proved. The exterior-form and cohomological interpretation is still
  a separate comparison.
- **Square denominators.** For the protected irreducible sextic,
  `protected_certificate_iff_square_primitive` proves that a square
  denominator loses no generality. This equivalence is not an existence
  proof.
- **Finite averaging.** Certificates can be combined over the product of
  their denominators with explicit numerator and quotient sums.
  Weights summing to one preserve the common source, grading and legality.
  This does not establish existence of the input certificates.

No mixed-Hodge-module strictness or Bott vanishing is needed in the new
affine algebraic conversion. The absence of a denominator-degree bound
allows the needed legal denominators to be enlarged.

## Why the geometric route would supply the primitive

The geometric references are
[Chapter 3D](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/03d-hodge-loci.md)
and [Chapter 1](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/01-certificates.md).
They are mathematical references, not Lean imports or added axioms.

For \(\omega^3=1,\ \omega\ne1\), use
\[
\beta:(X_2,Y_2)\mapsto(-X_2,-Y_2),\qquad
\gamma=\operatorname{diag}(\omega^2,\omega^2,1,\omega,1,1).
\]
[GeometricTarget.lean](GeometricTarget.lean) proves that \(F\) is fixed
and that the determinant-weighted source is fixed. The numerator's
\(\gamma\)-weight is \(10\equiv1\pmod3\), while the volume form's
determinant weight is \(5\equiv2\pmod3\); their product is invariant.
Under \(\beta\), the source has pair-degree four and the determinant
is positive. This uses the individual asymmetric source, not a cyclic sum.

The intended geometric conclusion is
\[
H^4(X,\mathbb Q)^{\langle\beta,\gamma\rangle}
\subset N^1H^4(X,\mathbb Q).
\]
After complexification, it supplies a proper algebraic support for
\(\alpha=\operatorname{Res}(A\Omega/F^3)\); the individual residue need
not be rational. The written argument proceeds through a moving curve
family on weighted sextic threefolds, a nonzero Abel--Jacobi derivative,
generation of the invariant variation, a supported projector,
specialization, and the relative paired-sign quotient pencil.
Those geometric implications have not been implemented here.

Once actual support is known, restrict to a smooth affine open of
\(X_0=1\) avoiding the support and \(g=0\). The residue is represented
there by
\[
(c/g)\,dx_1\wedge dx_2\wedge dx_3\wedge dx_4.
\]
[Grothendieck's affine algebraic de Rham theorem](https://www.numdam.org/item/PMIHES_1966__29__95_0.pdf),
Theorem 1, identifies its vanishing cohomology class with an algebraic
three-form primitive. If the latter is
\(\iota_u(dx_1\wedge\cdots\wedge dx_4)\), set \(w=-g\,u\).
The derivative formula is precisely the boxed equation above.

This is a smaller classical bridge than the earlier filtered projective
argument. The formalization still needs the geometric support theorem and
global algebraic de Rham comparison. The local normal-density calculation
and universal exterior pullback are proved above; their
comparison with the global cohomological residue remains to be formalized.
It does not need an explicit coefficient list or a separately prescribed
pole bound. The allowed regular ambient remainder becomes \(Q\), so
ambient exactness is not asserted.

## Concrete geometric inputs already formalized

### Exact target and support equations

`protected_F_gradient_nonzero` proves that every nonzero affine
representative has a nonzero partial derivative of the protected \(F\).
At a maximum-modulus coordinate \(M>0\), the pure derivative has modulus
\(6M^5\), while mixed terms have total modulus at most \(2M^5\) in an
\(X\)-coordinate and \(M^5\) in a \(Y\)-coordinate.
This is a polynomial gradient theorem; its use as scheme or analytic
smoothness requires the geometric Jacobian criterion.

Absolute irreducibility, primality, and the quotient-domain property are
also proved. The proof views \(F\) as monic in \(X_0\), specializes
\((X_1,X_2,Y_0,Y_1,Y_2)=(0,0,t+1,0,i)\), and applies Eisenstein at \(t\)
to \(X_0^6+(t+1)^6-1\).

The actual protected hypersurface in mathlib's projective spectrum is
proved irreducible. From any closed proper subset of it, the code
selects a positive-degree homogeneous polynomial \(S\), with \(F\nmid S\),
covering that subset. It also proves that finite unions of such supports
remain proper and admit a legal square \(S^2\).
This selects an equation after a support is given; it does not prove
that the specific residue is supported there.

The countability step used in very-general-point specialization is now
proved for actual polynomial conditions. Over an uncountable field,
countably many nonzero polynomials in finitely many variables admit a
common nonvanishing point. The complex version permits a prescribed
nonempty principal open. Consequently, if countably many actual affine
algebraic zero loci cover such an open, one zero locus is the whole affine
space. This proves the selection step; the families of supported
projectors and their proper images still have to be supplied.

### An exact auxiliary one-term family

There is now an unconditional checked certificate, with \(Q=0\), for the
distinct family
\[
F_s=\sum_{j=0}^2(X_j^6+Y_j^6)+sX_2^3X_0Y_2Y_0,
\qquad s\in\mathbb C,
\]
with the same source \(A\). Put \(U=X_2^6+Y_2^6\),
\(V=X_1^6+Y_1^6\), and \(M=X_2^3X_0Y_2Y_0\). The witness has
\[
D=36UV,\quad
N_i=\begin{cases}
3AVZ_i,&i\in\{2,5\},\\
-2sAMZ_i,&i\in\{1,4\},\\
0,&i\in\{0,3\},
\end{cases}
\]
where \((Z_0,\ldots,Z_5)=(X_0,X_1,X_2,Y_0,Y_1,Y_2)\).
The exact polynomial identity, degree-12 denominator, degree-19 numerators,
and coprimality for every complex \(s\) are proved by
`CycleQ2PureM2.hasCertificate`. The protected target has all three mixed
terms, so this family theorem does not solve the protected instance.

### Actual Fermat Jacobian algebra

For the auxiliary weighted Fermat polynomial
\[
x_0^6+x_1^6+x_2^6+x_3^6+w^3,
\]
the actual ideal of its partial derivatives is proved equal to
\[
(x_0^5,x_1^5,x_2^5,x_3^5,w^2).
\]
The code supplies the quotient normal form and a full monomial basis,
with total dimension \(1250\). Its weighted-degree-six character-one
and invariant pieces have the actual listed bases of dimensions
\(33\) and \(35\), respectively.

The socle trace is the coefficient of \((4,4,4,4,1)\), of weighted degree
\(18\). It descends to the quotient, is normalized, and gives exactly the
35 matrices of triple products used by the finite Higgs computation.
The scalar-commutant and scalar-idempotent conclusions therefore apply
to these actual algebraic matrices. Identifying them with the geometric
Higgs field and deducing irreducibility of a variation still require
geometric comparison theorems.

### Actual sparse seed trace

Use auxiliary weighted coordinates \((x_0,x_1,x_2,x_3;w)\) and
\[
b=x_3^3+x_2^3+x_1x_2x_3+x_0x_2x_3+x_0x_1^2.
\]
For \(r^3=2\), define
\[
\begin{aligned}
f_1&=x_0^2-rx_1x_3,&
g_1&=x_0^4+rx_0^2x_1x_3+r^2x_1^2x_3^2,\\
f_2&=w+x_2^2,&
g_2&=w^2-wx_2^2+x_2^4,\\
h&=b-i(x_1^3+x_3^3),&
k&=b+i(x_1^3+x_3^3).
\end{aligned}
\]
The trace on the actual quotient by \((f_1,g_1,f_2,g_2,h)\) is now
constructed and checked. After \(w=-x_2^2\), an explicit 24-term
degree-fifteen polynomial \(H\) gives
\[
\tau(p)=\frac1{12}[x_0^3x_1^9x_2^3x_3^9](Hp).
\]
Four polynomial identities prove that \(H\) times each reduced ideal
generator lies in
\((x_0^4,x_1^{10},x_2^4,x_3^{10})\).
The trace therefore annihilates the whole ideal, descends to the
original weighted quotient, satisfies \(\tau(x_0x_1^8)=1\), and
vanishes on homogeneous degrees other than nine.

The degree-nine component of the reduced four-variable algebra is proved
to be one-dimensional, spanned by the class of \(x_0x_1^8\).
The proof uses actual polynomial ideal-membership
witnesses for 32 normal monomials, then reduces every homogeneous
degree-nine polynomial to their span. It proves
\[
p-\tau(p)x_0x_1^8\in
\bigl(x_0^2-rx_1x_3,x_1^2x_3^2,x_2^4,h\bigr)
\]
in the reduced four-variable algebra, and uniqueness of the normalized
linear trace on that degree-nine component. This proves the trace's
normalization intrinsically; it is not an arbitrary functional fitted
to the matrix entries.

The invariant cubic column order is
\[
(x_3^3,x_2^3,x_1x_2x_3,x_1^3,x_0x_2x_3,
x_0x_1^2,x_0^2x_1,x_0^3,x_3w).
\]
The first seven rows are \(\tau(kL\sigma)\), with
\[
\sigma\in(x_2x_3^2,x_1x_2^2,x_1^2x_3,
x_0x_2^2,x_0x_1x_3,x_0^2x_3,x_2w),
\]
and the last is \(\tau(x_2x_3^3wL)\).
Scale the first five rows by \(6/r^2\), the next two by three,
and the last by six.

All 72 entries of this actual quotient-trace matrix are proved equal
to the matrix in [GeometricSeed.lean](GeometricSeed.lean).
Its explicit right inverse and tangent
\(\ell=ix_0^2x_1+(i-1)x_0^3\) consequently satisfy
\[
MR=I_8,\qquad M\ell=(0,0,0,0,0,0,0,2)^{\mathsf T}
\]
for the actual trace.

### Actual Čech comparison and the smooth seed

The sparse trace is now compared with a literal Čech calculation on the
curve, rather than merely a functional on an Artinian quotient.
After eliminating \(w=-x_2^2\), set
\(U=x_1x_3\) and \(V=x_2\). The actual reduced projective curve
is covered by \(D_+(U)\) and \(D_+(V)\). The cover is proved on
mathlib's `ProjectiveSpectrum`, including nonclosed primes, for every
member \(h_\theta=h+\theta x_0^3\).

The boundary predicate uses arbitrary denominator powers: a homogeneous
numerator represents a boundary precisely when suitable multiples can
be written as a sum from the two chart sections, modulo the actual
curve ideal. Two explicit Laurent charts and their residue functional
annihilate every such boundary. The argument is not a search limited
to a fixed pole order.

For the sparse member \(\theta=0\), the theorem
`CycleQ2SeedCech.cechResidue_eq_trace` proves, for every homogeneous
degree-nine numerator \(p\),
\[
\operatorname{Res}_{\check C}\frac{p}{U^2V^4}=3r\,\tau(p).
\]
Moreover `cechBoundary_iff_trace_zero` proves both directions: the
actual Čech class vanishes if and only if \(\tau(p)=0\).
The 72-entry matrix, its right inverse, and its selected tangent are
therefore bound to this actual Čech calculation. The first seven
selected tangent classes are boundaries and the last has residue
\(r\ne0\).

The smooth-member calculation is separate. In the cubic order
\[
(wx_3,x_3^3,x_2^3,x_1x_2x_3,x_1^3,x_0x_2x_3,
x_0x_1^2,x_0^2x_1,x_0^3),
\]
write \(L=\sum_jv_jL_j\). The actual Laurent calculation for
\(-x_2^3x_3^3L/(U^2V^4)\) gives
\[
\operatorname{Res}_{\check C}=3r\,\ell_\theta(v),\qquad
\ell_\theta(v)=\frac{\theta i\,v_1-(1+i)v_8}{6}.
\]
`CycleQ2SeedCechTheta.nonboundary_of_derivativeTrace_ne_zero` proves
that a nonzero value of this functional yields a nonboundary for every
\(r\ne0\). At \(\theta=1\), the additional \(iv_1/6\) term
is retained. No equality of the entire sparse and smooth trace matrices
is asserted.

The selected polynomial \(ix_0^2x_1+(i-1)x_0^3\) has residue \(r\)
for every \(\theta\). At the smooth member this is an algebraic test
class; it is not yet a proved tangent to a moving divisor family.
The sparse surface is singular, and its tangent-space calculation
cannot simply be transported to the smooth member. Identifying these
Čech classes with an obstruction or Abel--Jacobi derivative, constructing
the relevant moving correspondence, and proving divisor support remain
separate obligations.

### Cartier-curve resolution algebra

The new `CycleQ2CartierResolution` namespace supplies literal matrices for
the cubic
\[
G=a^3-b^3+c^3+d^3.
\]
Its \(4\times6\) and \(6\times2\) maps, together with two explicit
homotopies, give \(6\times6\) matrices \(B_0,B_1\) satisfying
\[
B_0B_1=B_1B_0=GI_6.
\]
All polynomial identities, including compatibility with the residual
ideal's four displayed generators, are proved over an arbitrary
commutative ring. Over a domain with \(G\ne0\), the proof lifts a kernel
vector and cancels \(G\) to establish genuine quotient-module exactness:
\[
\ker(\overline B_0)=\operatorname{im}(\overline B_1),\qquad
\ker(\overline B_1)=\operatorname{im}(\overline B_0)
\quad\text{over }R/(G).
\]
This supplies the complete periodic algebraic complex, including the
homotopy columns omitted by the two original second syzygies. Saturation,
base change through a surface section, and its geometric interpretation
are separate obligations.

### The literal Segre seed and its local differential data

`CycleQ2SegreSeed` contains the actual chosen section polynomials, the
nine entries of the degree-fourteen seed matrix, and explicit cofactor
quotients. Its 25 linkage identities hold over an arbitrary commutative
ring. With
\[
(a,b,c,d)=(x_0^2,r x_1x_3,w,x_2^2),\qquad
G=a^3-b^3+c^3+d^3,
\]
the code proves, for the literal raw seed matrix \(M_0\),
\[
\operatorname{Cof}(M_0)_{ij}=GQ_{ij}.
\]
This is a characteristic-zero polynomial identity before imposing any
surface equation \(h\); it even holds with \(r\) an arbitrary coefficient.
The selected left and right sections satisfy the explicit product
identities modulo \(G\), and the first right-section numerator is proved
equal to the chosen \(\Gamma_4\) numerator. A proved two-outer-product
factorization makes the cofactor calculation finite and inspectable.
These identities bind the abstract matrix construction to the chosen seed.
The characteristic-zero basepoint cover is now proved separately, as
described below. The large Jacobian rank conditions still require their
own proofs.

`CycleQ2SegreRelations` proves the sixteen universal polynomial relations
among the nine cofactors of a \(3\times3\) matrix. They are the six
off-diagonal entries of each of \(M\operatorname{Cof}(M)^{\mathsf T}\)
and \(\operatorname{Cof}(M)^{\mathsf T}M\), together with two diagonal
differences for each matrix. The residual-elimination theorem uses an
actual invertible complementary block of those relations, not a dimension
count alone.

When the cofactors vanish and one matrix entry is a unit,
`CycleQ2SegreLocal` proves an explicit normalized outer-product
factorization. `CycleQ2SegreImage.image_linearEquiv` identifies the actual
image of the matrix's linear map with a free rank-one module. A separate
ideal-membership theorem shows that coordinate-power witnesses imply a
nonzero matrix entry at every nonzero field point. The arithmetic
argument below supplies coordinate-power ideal membership for the
actual complex seed and strengthens the cover to relevant primes.

`CycleQ2SegreCech` gives the explicit transition units between these charts,
their multiplicative cocycle identity, the gluing of the first-column
local equations, and equality of their principal ideals on overlaps.
The formulas commute with coefficient maps, including localization.
Their logarithmic differentials use the genuine universal module
\(\Omega^1_{R/K}\):
\[
d\log(u)=u^{-1}du,\qquad
d\log(uv)=d\log(u)+d\log(v).
\]
The transition differentials satisfy the corresponding additive cocycle
identity and evaluate to \(u^{-1}\delta(u)\) under every derivation
\(\delta\). The homogeneous degree twist is retained explicitly. For
degree-fourteen entries, the intended divisor bundle is
\(\mathcal O_D(14H)\otimes L^{-1}\); with
\(L=\mathcal O_D(10H-E)\), this is \(\mathcal O_D(E+4H)\).
The untwisted image cocycle alone is not the divisor class.

These are actual module, transition, and differential identities.
The projective prime cover, regularity of the linkage element, and local
principality of the two actual linkage ideals are now proved below.
The geometric identification with the specified divisor bundle, the
construction of the projective family, its cycle class and cylinder map,
and the Abel--Jacobi comparison still remain.

### The actual moving incidence equations and their relations

`CycleQ2IncidenceNormalForm` proves the full moving normal form over
every commutative coefficient ring in which the two selected leading
coefficients are units. The cubic and sextic include every invariant
monomial, including their leading coefficients. Their leading monomials
are \(x_0^3\) and \(w^3\), which are relatively prime. The proof
establishes existence and uniqueness of normal representatives,
preservation of weighted degree and character, and compatibility with
coefficient specialization.

The quotient piece is defined as the image of actual homogeneous
polynomials in the actual quotient ring. Its proved basis consists of
the corresponding standard monomials. Ordinary kernel-checked finite
enumeration gives 9 cubic parameters, 45 sextic parameters, and
\[
\dim S_{14}^{\mu_3}=239,\qquad
\dim S_{28}^{\mu_3}=1058,\qquad
\dim S_{42}^{\mu_3}=2465.
\]
These are proved dimensions of the actual graded quotient pieces, not
definitions setting a desired dimension.

The matrix family is centered on the literal raw seed:
\(M=M_{\mathrm{raw}}+\delta M\), with nine sets of 239 matrix
coefficients. `CycleQ2IncidenceEquations` defines the 9,522 equations
as the degree-28 coefficients of the nine cofactor remainders. Their
simultaneous vanishing is equivalent to actual cofactor membership in
\((h,F)\). The literal smooth seed satisfies every equation by the
proved universal cofactor factorization.

`CycleQ2IncidenceJacobian.infinitesimal_incidenceEquations_eq` proves
the exact first-order equation, for all square-zero thickenings:
\[
E(h+t\eta,F+t\zeta,M+t\delta M)
=t\,\operatorname{NF}\!\left(
D\operatorname{Cof}_M(\delta M)+\eta kQ-\zeta Q\right).
\]
Here \(Q\) is the actual matrix of cofactor quotients at the seed.
Thus the claimed linearization is tied to the same moving remainder
equations.

The sixteen universal Segre identities give a 39,440-by-9,522 coefficient
relation matrix after reduction and expansion in the proved degree-28
and degree-42 bases. `coefficientRelations_incidenceEquations` proves
the identity for the entire moving family. It is not inferred from
evaluation at seed points on a single fiber.

The universal coefficient ring is the polynomial ring in the raw
cubic, sextic, and matrix parameters, localized at the product of the
two leading coefficients. Its specialization maps, leading units, and
actual seed are proved. `CycleQ2IncidencePolynomialPresentation`
supplies ordinary polynomial numerators for the equations and proves
equivalence of their zero sets on this open, together with the precise
derivative scaling.

`CycleQ2IncidencePolynomialRelations` goes further: one common power
of the leading product clears both the equations and all their
relations. Injectivity of the localization proves the resulting
polynomial relation identity in the original polynomial ring.
At the literal seed both leading coefficients are one, so the clearing
factor is one. Differentiating the actual polynomial identity proves
`seed_relations_jacobian`, the exact relation-matrix-times-Jacobian
identity at that seed. None of these theorems asserts a large rank or
an unverified determinant value.

### A nonconstructive characteristic-zero tangent with nonzero residue

`CycleQ2SegreNonconstructiveTangent.exists_actual_trace_one_tangent`
proves existence of an actual fixed-sextic incidence tangent at
\(r=57,\iota=i\). It satisfies all 9,522 linearized equations and has
normalized derivative trace one. The complex tangent is chosen from a
proved rank inequality; no complex correction vector or denominator is
required as input.

Here is the finite argument, with every matrix bound to the original
normal-form coefficient equations. Over \(\mathbb F_{109}\), let \(E\)
be the 9522-by-2151 entry block, \(C\) the nine actual cubic columns, and
\(J=(C\ E)\) the fixed-sextic Jacobian. Seven checked coefficient
functionals form a matrix \(L\) with
\[
LE=0,\qquad (LC)B=I_7
\]
for a checked 9-by-7 matrix \(B\). Their arithmetic is linked to the
actual polynomial normal forms and monomial exponents. The structural
factor argument gives \(\operatorname{rank}E\ge1915\), and the independent
complex relation bound, together with Gaussian rank transfer, gives
\(\operatorname{rank}J\le1922\). Thus the restriction of \(L\) to
\(\operatorname{im}J\) is onto a seven-dimensional space and
\[
\operatorname{im}J\cap\ker L=\operatorname{im}E.
\]
This is a proved equality of the actual subspaces.

The small vector
\[
v=(0,76,93,93,92,93,93,71,0)
\]
has \((LC)v=0\) and \(33v_1-34v_8=1\). Consequently \(Cv\) lies in
\(\operatorname{im}E\). Classical choice selects \(w\) with \(Ew=Cv\),
so \((v,-w)\) is an actual modular tangent with trace one. This does
not assume that any modular kernel vector lifts to characteristic zero.

The row
\[
\ell(\eta)=i\eta_1-(1+i)\eta_8
\]
is defined over the Gaussian integers. The indexing theorem identifies
column 1 with \(x_3^3\) and column 8 with \(x_0^3\). Appending this row
to the same integral Jacobian gives rank at least 1923 modulo 109, hence
rank at least 1923 over \(\mathbb C\). The complex Jacobian itself has
rank 1922. Rank-nullity therefore gives a complex kernel vector on which
\(\ell\ne0\), and scaling gives \(\ell=6\). The normalized trace is
\(\ell/6=1\). All existence statements follow from proved finite
linear algebra and ordinary kernel-checked arithmetic.

`CycleQ2IncidenceCubicCechTrace` proves the residue formula for every
invariant cubic coefficient vector. Substituting the chosen tangent via
`CycleQ2IncidenceTraceDirection` gives actual curve Čech residue 171,
normal trace \(-1/171\) with the fixed sign convention, and a class that
is not an all-poles Čech boundary. These formulas concern the chosen
\(\theta=1\) curve component. The orbit-sum character comparison and the
identification with a geometric Abel--Jacobi derivative remain separate
obligations.

The previously checked explicit Gaussian tangent is retained in the
research archive. The active proof uses the smaller nonconstructive
rank argument; the seed polynomials and multiplication tables used by
the detector proof retain their literal definitions.

### Characteristic-zero cover and actual local factor sequences

The arithmetic continuation uses the actual seed with \(r=57\) and
\(\iota=i\). The moving normal form and universal linkage identities
permit arbitrary \(r\); this choice is distinct from the earlier sparse
trace calculation requiring \(r^3=2\).

Over \(\mathbb F_{109}\), ordinary kernel-checked identities place
\(x_0^{24},x_1^{24},x_2^{24},x_3^{24},w^{12}\) in the ideal of the nine
matrix entries and the actual seed equations. Every invariant monomial
of weighted degree 120 is divisible by one of these monomials: otherwise
its weighted degree is at most 114. The actual coefficient matrix
presenting this entire homogeneous ideal piece is therefore surjective.

`CycleQ2ArithmeticSurjectivity` transfers this finite rank statement
through the Gaussian integers. It lifts a right inverse and uses its
nonzero determinant after reduction to prove surjectivity over
\(\mathbb C\). It does not lift a modular kernel vector. The result for
the literal complex seed is
\[
x_0^{120},x_1^{120},x_2^{120},x_3^{120},w^{60}\in(M_{ij})\subset S,
\quad S=\mathbb C[x_0,x_1,x_2,x_3,w]/(h,F).
\]
`CycleQ2SegreComplexBasepoint.prime_pivot_cover` proves the cover on every
relevant prime. The entries generate the unit ideal on every nonempty
coordinate localization. On those actual rings, the sixteen-relation
kernel equals the cofactor-derivative image. Common-denominator clearing
and projection onto the original degree and character supply homogeneous
local lifts. These specialized theorems have no remaining basepoint or
local-exactness premise.

The actual linkage element
\(p=x_0^2w+r x_1x_3x_2^2\) is proved regular whenever \(\iota\ne1\).
The seed quotient is free of rank nine over the three remaining
coordinates. In the fiber \((x_1,x_2,x_3)=(0,0,1)\), its equations make
\(x_0,w,p\) units. The determinant of multiplication by \(p\) is
therefore nonzero over the base domain. This proves regularity without
assuming that the full seed quotient is a domain.

For the actual five-generator linkage ideals \(I,J\) and selected
sections \(a_i,b_j\), the proved identities are
\[
IJ\subset(p),\qquad a_i b_j=pM_{ij}.
\]
Thus both ideals have regular principal generators on every unit-entry
chart. A Bezout argument using all nine entries also proves, on every
nonempty coordinate localization, the actual exact sequence
\[
0\longrightarrow S_{\rm loc}\xrightarrow{c\mapsto(ca,-cb)}
I_{\rm loc}^{3}\oplus J_{\rm loc}^{3}
\longrightarrow\ker(D\operatorname{Cof}_M)\longrightarrow0.
\]
The second map divides \(v_i b_j+a_i w_j\) by the regular element \(p\).
Its existence, linearity, kernel, and surjectivity are proved.
The graded lifting theorem retains the left degree-ten invariant and
right degree-eight character-one factors, with degree-fourteen invariant
matrix output.

The regular linkage pairing now also gives actual linear equivalences
\[
J_{\rm loc}\simeq
\operatorname{Hom}_{S_{\rm loc}}(I_{\rm loc},S_{\rm loc})
\simeq\operatorname{im}M_{\rm loc}.
\]
The first sends \(y\) to \(x\mapsto xy/p\); the second uses the
literal products \(a_i y/p\). The selected \(b_j\) map to the actual
matrix columns. The degree-eight character-one input gives the exact
degree-four invariant dual twist and degree-fourteen invariant matrix
coordinates. These maps commute with the actual restriction maps.

On every coordinate chart the three cyclic component ideals are
pairwise comaximal. `SeedLinkageOrbitProduct` proves that the actual
linkage ideal is their product, and that the cyclic action maps each
component ideal exactly to the next. This supplies the orbit ideal
identity. It does not yet prove that the geometric trace of the orbit
sum is three times the selected-component trace: the character,
orientation, and differential comparison still need to be checked.

### Actual seed and curve Čech complexes

The seed quotient has the proved free basis \(x_0^a w^b\),
\(0\le a,b<3\), over \(\mathbb C[x_1,x_2,x_3]\). The three
coordinate opens cover every relevant prime. Their actual localization
maps embed in Laurent coordinates, whose grading is proved equivalent
to fractions with a polynomial numerator of the original weighted degree
and character. A literal contraction gives Čech \(H^1=0\) in every
grade; compatible zero-cochains glue uniquely to an actual quotient
element with a homogeneous polynomial representative. The top Čech
quotient in degree zero and character zero has proved dimension seven.
All pole exponents are arbitrary.

Both chosen curve quotients are free of rank six over
\(\mathbb C[x_1,x_3]\). Their leading monomials are
\((x_0^2,x_2^3)\) on the left and \((x_2^2,x_0^3)\) on the right.
The six basis shifts have degrees at most three. The two base-coordinate
opens cover every relevant prime; sections glue uniquely, and the
actual Čech differential is surjective in every degree at least two.

The right coordinate transformation is explicitly included:
\[
(x_0,x_1,x_2,x_3,w)
=(u+v,2y_1,u-v,2y_3,4r y_1y_3).
\]
The global and localized restriction kernels are proved to equal the
original chosen component ideals
\[
(x_0^2-rx_1x_3,w+x_2^2),\qquad
(x_0^2+x_2^2,w-rx_1x_3).
\]
The actual restriction maps commute with overlaps and preserve degree,
including the scalar factors in the right-chart denominators. Regularity
of the last base coordinate makes the middle-chart comparison faithful.
Consequently, the two-open gluing calculation gives agreement on all
three original seed charts.

Checked modular minors and Gaussian-integer transfer prove surjectivity
of the actual complex restriction maps, with dimensions
\[
S_{10}^{(0)}\longrightarrow H_{10}(C_{\rm left}):113\to57,
\qquad
S_8^{(1)}\longrightarrow H_8(C_{\rm right}):68\to45.
\]
Separate minors of actual monomial multiples of the linkage generators
prove \(\dim I_{10}^{(0)}=56\) and \(\dim J_8^{(1)}=23\).
These two ideal pieces equal the corresponding global restriction kernels.
The ideals and maps are concrete polynomial constructions, not abstract
spaces defined to have the required ranks.

The cyclic orbit identification is now proved as well. On every nonempty
seed coordinate open, each linkage ideal is the intersection of its three
literal curve components. The diagonal cube-root action is defined on the
actual quotient and its localizations. A homogeneous fraction is an
eigenvector up to a unit; membership in one component therefore forces
membership in all three. Consequently, for a genuinely homogeneous local
section, membership in the orbit ideal is equivalent to vanishing under
restriction to the chosen component.

This closes the positive-degree vanishing statements
\[
\check H^1(I_{10}^{(0)})=0,\qquad
\check H^1(J_8^{(1)})=0.
\]
The theorems `CycleQ2SeedLinkageCechVanishing.left_idealCechExact` and
`right_idealCechExact` use the actual three coordinate localizations.
Starting from an ideal-valued cocycle, seed exactness supplies ambient
local sections. Their restrictions glue to a homogeneous curve section;
the checked restriction surjectivity lifts it globally. Subtracting that
lift gives ideal-valued homogeneous singleton sections with the original
Čech differences. The orbit identification supplies the ideal membership
in this last step. No orbit, gluing, or surjectivity premise remains.

Finally, the literal degree-28 relation kernel modulo the actual global
cofactor image is proved linearly equivalent to the graded Čech \(H^1\)
of the cofactor kernel. Its source is bound to the actual coefficient
system, and the complex local-exactness theorem discharges local
liftability. For the reverse direction, entrywise scalar Čech \(H^1\)
vanishing lifts a kernel cocycle to local matrices. Their cofactor images
agree on overlaps, so homogeneous gluing produces a global relation
vector with the prescribed connecting class. This proves surjectivity of
the same connecting map, rather than merely equality of dimensions.

### Actual global factor dimensions and coefficient-matrix binding

The actual global factor domain is
\[
(I_{10}^{(0)})^3\oplus(J_8^{(1)})^3,
\qquad \dim=3\cdot56+3\cdot23=237.
\]
Its map to degree-fourteen matrix variations is defined by dividing the
literal factor expression by the proved regular linkage element. Local
factor gauges, actual degree-zero gluing, and a nonzero global gauge
vector show that its kernel is exactly a one-dimensional scalar line.
Its image therefore has dimension 236 and lies in the actual cofactor
kernel. The reverse inclusion is now proved: any local graded factor
lifts of a cofactor-kernel element differ by a scalar Čech cocycle;
the actual \(\check H^1(\mathcal O)=0\) contraction corrects them, and actual
ideal-valued \(H^0\) gluing produces global factors. Thus
\[
\ker D_{\rm cof}=\operatorname{im}(\text{global factor map}),
\qquad \dim\ker D_{\rm cof}=236.
\]
Since the degree-fourteen matrix space has dimension
\(9\cdot239=2151\), the cofactor differential has rank exactly 1915.
These are `CycleQ2SeedGlobalFactorExact.entry_kernel_eq_factor_image`,
`entry_kernel_finrank`, and `entry_rank`; no global-liftability hypothesis
remains.

These dimensions refer to the original maps. The theorem
`CycleQ2SegreEntryCoefficientBinding.entryJacobianBlock_rank_eq`
identifies the rank of the literal 9522-by-2151 matrix-entry block of
`linearizedMatrix` with the rank of that cofactor differential. It uses
the actual normal form, a surjective coefficient-to-quotient decoding map,
and equality of kernels. Similarly,
`CycleQ2SegreCoefficientRankBinding.coefficient_rank_eq` identifies the
rank of the literal 39440-by-9522 coefficient relation matrix with its
actual quotient relation map. No independently defined model matrix is
substituted for either coefficient matrix.

The second actual connecting map is also proved. A kernel cocycle is
lifted on the three pair opens to the actual factor sequence, and its
triple defect is a degree-zero scalar gauge. Positive factor \(H^1\)
vanishing proves that its scalar top class is zero exactly when the
original kernel cocycle is a kernel boundary. Simultaneous lifts form a
linear submodule; descending that relation gives a genuine injective
linear map
\[
\frac{\ker R}{\operatorname{im}D_{\rm cof}}
\xrightarrow{\;\sim\;}\check H^1(\ker D_{\rm cof})
\hookrightarrow\check H^2(\mathcal O)^{(0)}.
\]
The right-hand space has the already proved seven-element basis.
Consequently the actual obstruction quotient has dimension at most seven,
\(\dim\ker R\le1915+7=1922\), and the actual relation map has rank at
least \(9522-1922=7600\). The coefficient binding gives the unconditional
theorem `CycleQ2SegreActualRelationRank.literal_coefficient_matrix_rank_lower_bound`
for the original 39440-by-9522 matrix.

The seven checked cubic detectors now give the opposite rank bound.
`CycleQ2SegreExactRanks` proves
\[
\operatorname{rank}J_{\mathrm{fixed}}
=\operatorname{rank}J_{\mathrm{full}}=1922,\qquad
\operatorname{rank}R=7600,\qquad
\operatorname{im}J_{\mathrm{fixed}}=\ker R.
\]
The obstruction quotient has dimension exactly seven, and its previously
constructed injection into scalar Čech \(H^2\) is now surjective.
`relationObstructionEquivH2` packages this same connecting map as a
linear equivalence; it does not substitute a separately defined
seven-dimensional model.

The full parameter space has dimension 2205. Its actual incidence
tangent space therefore has dimension 283, and projection onto the 45
independent sextic coefficient directions is surjective. Its kernel,
the fixed-sextic tangent space, has dimension 238. The resulting linear
right inverse supplies actual cubic and matrix corrections to every
sextic coefficient variation. These are finite statements about the
original equations. They do not yet identify an Abel--Jacobi map or a
supported cohomology class.

### Nonlinear polynomial lifting with redundant equations

The lifting lemmas now prove existence from actual polynomial data.
For a square system \(e_i(T,x)\) with coefficients in \(K[[T]]\), a
constant seed solving \(e(0,x_0)=0\) and a unit seed Jacobian give a
solution \(x(T)\) with \(x(0)=x_0\). Formal smoothness of the
Jacobian-localized presentation and the required adic completeness are
proved or supplied by checked library theorems. Existence of a formal
solution is not a premise.

Suppose the omitted equations \(r\) satisfy a literal polynomial identity
\[
Ar+Be=0
\]
and the determinant of \(A\) is a unit at the seed.
`CycleQ2SegreFormalLifting.lift_all_equations` proves that the constructed
formal solution satisfies every omitted equation as well. The complementary
block stays invertible because its constant determinant is a unit.

The separate `CycleQ2OpenSquareLifting` theorem gives an algebraic generic
solution inside a prescribed principal open. It adds the actual equation
\(u\,c(x)-1=0\) and proves that the augmented Jacobian determinant is
\(c(x)\det J(x)\). An actual nonsingular seed with \(c(x_0)\) a unit,
together with an injective coefficient map \(R\to K\), yields a solution
over a finite separable field extension of \(K\), with \(c\) still a unit.
The actual generic-specialization theorem above separately handles
specialization of a primitive to the protected target; it does not
assert that this incidence lift supplies such a primitive.

The actual quotient normal forms, seed equations, coefficient relations,
and denominator-cleared polynomial presentation are proved. The actual
range/kernel equality proved above now discharges the finite linear
hypothesis of the compatible lifting constructor. No displayed enormous
minor or assumed numerical rank is needed. The geometric identification
of the resulting family with the specified residue class is still open.

There is now a structural substitute for choosing and printing enormous
complementary minors. For finite matrices \(J,R\) with
\(\operatorname{im}J=\ker R\),
`CycleQ2LinearExactSequenceSplit.exists_matrix_split` proves the existence
of matrices \(P,Q,V,W,T,B\) satisfying
\[
QP+VW=I,\qquad PJB=I,\qquad TRV=I,\qquad RQ=0,\qquad PV=0.
\]
It chooses bases and linear splittings of the actual exact sequence.
The compatible affine lifting theorem uses these identities to impose a
square system on the slice \(x=a+Bz\). The first determinant and the
complementary relation determinant are both exactly one at the seed.
Every omitted equation then follows from the original polynomial
relations. This construction is nonconstructive. For the literal incidence
system, `CycleQ2SegreExactRanks.exists_compatible_square_blocks`
discharges its exactness hypothesis. These are arbitrary proved linear
coordinate splittings, rather than claimed values of selected minors.

The parameter substitution is tied to the literal incidence presentation.
It works over the fraction field of the polynomial ring in all 45
independent sextic coefficients and extends each cubic/matrix direction
by zero on those coordinates. The resulting finite generic incidence
statement retains each sextic coefficient exactly, proves both leading
coefficients are units, and gives all nine original cofactor ideal
memberships over a finite separable extension. The actual exactness
identity supplies the splitting used in this construction.

### Actual open conditions and the moving parameter

`CycleQ2IncidenceBasepointOpen` constructs an actual polynomial in the
full incidence parameters, with value one at the chosen seed. The proof
uses a surjective homogeneous multiplication map in degree 120 and a
nonconstructively chosen right inverse. Its determinant gives an open
condition on which powers of all five coordinates lie in the ideal
generated by the nine matrix entries, the cubic, and the sextic. On
quotienting by the cubic and sextic, every relevant prime therefore has
a matrix pivot. `IncidenceBasepointChart` retains this condition in the
actual localized universal coefficient ring, including its original seed.

For a point of the actual incidence system in this open,
`IncidenceImageLine` proves that localization of the global matrix-image
module is the local matrix image and is free of rank one on a pivot
chart. `SegreGenericSection` proves that the ideal of a generic linear
combination of matrix columns has one regular local equation there,
with the exact unit transition on overlaps. These are actual module
and equation statements; a global projective Cartier divisor and its
cycle/cylinder map are not asserted by them.

`CycleQ2GenericSexticGradient` separately proves that every faithful
specialization of the 45 independent sextic coefficients to a field
has no nonzero common zero of its five partial derivatives. A degree-30
homogeneous multiplication map is surjective at the Fermat specialization;
its nonzero determinant becomes a unit under any such faithful field map.
This is the actual algebraic gradient condition. A geometric smoothness
theorem is not silently used or added to it.

For the external parameter \(t\), the affine slice follows the chosen
fixed-sextic trace-one direction and corrects it by the square Jacobian
block. Its implicit derivative is computed by the adjugate formula. The
polynomial trace numerator has seed value one; retaining its open set
makes the actual fixed linear trace of the derivative a unit. The
canonical derivation on the fraction field, and its extension through a
finite separable field, fix all 45 sextic coefficients and send \(t\)
to one.

Scalar rescaling of the cubic must also be excluded. Write \(h_8\) for
its leading coefficient and \(\lambda(h)=\ell(h)/6\) for the fixed
normalized trace. At the seed, \(h_8=1\) and \(\lambda(h)=0\). If
\(N_\lambda\) and \(N_8\) are the corresponding implicit derivative
numerators, the additional projective numerator is
\[
 h_8N_\lambda-\lambda(h)N_8.
\]
Its seed value is one. The proved derivative identity identifies it with
\(\det(J)[h_8D\lambda(h)-\lambda(h)Dh_8]\). Retaining this numerator
and the leading coefficient detects a nonzero derivative of
\(\lambda(h)/h_8\), so coefficient motion cannot be explained by
rescaling the section.

The generic component is chosen through the actual seed. The pointed
étale theorem uses flat going-down and localization of prime ideals to
choose a finite separable generic field quotient whose prime contracts
inside the seed kernel. The square-system, open-system, and compatible
affine constructions preserve this same quotient and its specialization
property. `CycleQ2IncidenceCertifiedGenericPoint.finite_pointed_trace_point`
discharges the actual exactness and basepoint hypotheses. For original
parameter polynomials, with their specified coefficient maps, it retains
\[
p(y_{\rm generic})=0\quad\Longrightarrow\quad p(y_{\rm seed})=0.
\]
In particular a scalar algebra element nonzero at the seed remains
nonzero on this chosen generic component.

These are algebraic incidence, scalar-specialization, and coefficient-trace
statements. Specialization of arbitrary module or cohomology classes does
not follow from the scalar statement. The fixed coefficient functional
away from the seed has not been identified with the Abel--Jacobi
functional. That relative comparison remains necessary. Likewise, the
generic gradient condition does not assert global quasismoothness of
the literal \(r=57\) seed surface. The exact cubic and seed-curve
Jacobian conditions are proved below. The needed surface smoothness
and persistence of the actual geometric class and trace remain
separate requirements.

### Exact Jacobian conditions at the literal seed

The three components `SeedCubicGradient`, `SeedCurveGradientArithmetic`,
and `SeedCurveGradient` prove algebraic Jacobian conditions for the actual
chosen cubic and curve. Write
\[
b=x_3^3+x_2^3+x_1x_2x_3+x_0x_2x_3+x_0x_1^2+x_0^3,
\qquad h=b-i(x_1^3+x_3^3),
\qquad f=x_0^2-57x_1x_3.
\]
Here the coefficient is the integer \(57\) in \(\mathbb C\). No relation
\(57^3=2\), or characteristic-109 hypothesis, is used.

For the cubic, explicit Gaussian-integer polynomial identities give
\[
d_jx_j^5=\sum_{k=0}^3 u_{jk}\,\partial_k h,
\qquad 0\le j\le3,
\]
with nonzero integer multipliers
\[
(d_0,d_1,d_2,d_3)
=(4272557211,2848371474,9526326,9526326).
\]
The identities are proved over every commutative ring with a chosen
element satisfying \(i^2+1=0\), then bound to the actual polynomial
`smoothH Complex.I`. Inverting the displayed constants over \(\mathbb C\)
places all four fifth powers in its gradient ideal.
`nonzero_gradient_over_complex_extension` consequently excludes a common
zero of these four partial derivatives whenever at least one of
\(x_0,\ldots,x_3\) is nonzero, over every field extension of the complex
coefficients.

For the curve after eliminating \(w\), put
\[
M_{jk}=(\partial_j f)(\partial_k h)
       -(\partial_k f)(\partial_j h),
\qquad
J_C=(f,h,M_{01},M_{02},M_{03},M_{12},M_{13},M_{23}).
\]
Four further explicit Gaussian-integer identities, with proved nonzero
integer multipliers, establish
\[
x_j^6\in J_C\quad(0\le j\le3)
\]
over \(\mathbb C\). `generators_binding` identifies every displayed
arithmetic generator with the actual equation or Jacobian minor.
`prime_minor_cover` therefore proves that, for every prime ideal
containing \(f,h\) but not all four coordinates, at least one \(M_{jk}\)
lies outside that prime. This covers all relevant prime ideals, including nonclosed primes.

Restoring the weight-two coordinate gives the ordered equation tuple
\[
(f,\ h,\ w+x_2^2).
\]
Its normal Jacobian determinant in columns \((x_j,x_k,w)\) is exactly
\(M_{jk}\), as proved by `normalMinor_eq`. If a prime contains these
three equations and all four base coordinates, it also contains \(w\).
Thus `weighted_prime_normal_cover` supplies a nonvanishing normal minor
at every relevant prime of the actual weighted seed curve.
`weighted_field_normal_cover` gives the corresponding unit determinant
after every homomorphism to a field satisfying the equations and the
nonzero-coordinate condition.

These results supply concrete algebraic hypotheses for geometric
smoothness and local normal-module arguments. The geometric Jacobian
criterion and its scheme-theoretic application remain separate steps.
The three components do not establish smoothness of the entire seed
surface or threefold, identify an Abel--Jacobi derivative, construct a
global support class, or prove the residue primitive required by
`Submission.missing_geometric_existence`.

### Genuine conormal bases and the actual normal matrix

The normal coordinates are now realized in the actual ideal cotangent
module. Let \(R=\mathbb C[x_0,x_1,x_2,x_3,w]\) with the existing weighted
grading, and let
\[
I=(f_1,f_2,h),\qquad
f_1=x_0^2-rx_1x_3,\qquad f_2=w+x_2^2.
\]
For any coefficient algebra \(S\) in which \(I\) vanishes,
`CycleQ2ConormalJacobian` works with the genuine base-changed conormal
module
\[
S\otimes_R I/I^2.
\]
A polynomial derivation into \(S\) becomes \(R\)-linear on \(I\), kills
\(I^2\), and induces an \(S\)-linear functional on this tensor product.
Inverting the actual equation-derivative matrix supplies functionals dual
to the equation classes. Ideal generation proves spanning, and these duals
prove independence. `conormalBasisOfJacobian` therefore constructs a basis
from the unit determinant of the actual Jacobian matrix.

`SeedConormalBasis` applies this to the literal seed equations. Its explicit
triangular chart inverts
\[
m=-r x_3(3x_2^2+x_1x_3+x_0x_3).
\]
The chart contains the complex point
\((0,0,c,1,-c^2)\), where \(c^3=i-1\), for every nonzero \(r\).
The point and the nonzero value of \(m\) are proved, so this construction
has a nonempty actual seed chart. A second constructor works for any
invertible normal Jacobian minor.

`CycleQ2ConormalCover.exists_actual_conormal_basis` combines that
constructor with the exact \(r=57,\theta=1\) curve-gradient identities.
For every relevant prime of the actual curve quotient, the original
three equation classes form a basis after prime localization. The
permutation between the gradient certificate's order \((f_1,h,f_2)\)
and the normal calculation's order \((f_1,f_2,h)\) is explicit.

The proved conormal relation for the actual sextic is
\[
[F]=g_1[f_1]+g_2[f_2]+k[h].
\]
Consequently, evaluation of a genuine normal homomorphism on \([F],[h]\)
is exactly the previously checked matrix
\[
\beta(u_1,u_2,u_3)=(g_1u_1+g_2u_2+ku_3,\ u_3).
\]
This is `actualEquationNormalMap_eq`; its scalar-extension form
`baseChangedNormalMap_eq` also applies on arbitrary prime charts.
For the target ideal \(J=(F,h)\),
`surfaceConormalBasisOnFirstOpen` constructs a genuine two-element
conormal basis on a source Jacobian chart where \(g_1\) is a unit.
If \(d_1,d_2,d_3\) are the supplied source duals, the target duals are \(g_1^{-1}d_1\) and
\(d_3-k g_1^{-1}d_1\).

`CycleQ2NaturalNormalMap` constructs the actual cotangent map induced by
\(J\subseteq I\), extends scalars, and dualizes:
\[
\iota_S:S\otimes_R (J/J^2)\longrightarrow S\otimes_R (I/I^2),
\qquad
\iota_S^\vee:\operatorname{Hom}_S(S\otimes_R (I/I^2),S)
\longrightarrow\operatorname{Hom}_S(S\otimes_R (J/J^2),S).
\]
The definition uses `Ideal.mapCotangent`, `LinearMap.baseChange`, and
`LinearMap.dualMap`; it does not choose equation coordinates.
`naturalNormalMap_equation_coordinates` proves
\[
\operatorname{ev}_{F,h}\circ\iota_S^\vee
=\beta\circ\operatorname{ev}_{f_1,f_2,h}
\]
on arbitrary scalar extensions. On a source Jacobian chart where \(g_1\)
is a unit, `naturalNormalMap_in_equation_bases` expresses the same equality
through the genuine source and target conormal bases.
`actualEquationNormalMap_eq_naturalNormalMap` also binds the earlier
literal-chart evaluation map directly to this dual natural map.

The next comparison must assemble these maps on the second denominator
chart and retain the grading when constructing the normal sequence.
The source equation degrees are
\((2,2,3)\), the target degrees are \((6,3)\), and the expected normal
line has twist \(\mathcal O_C(-2)\). Pairing its connecting cocycle with a cubic
therefore lands in the degree-one canonical piece of the curve.

The actual global conormal bases and the genuine normal connecting
construction have now been completed. The subsequent section
[Global conormal bases and the genuine chosen-curve class](#global-conormal-bases-and-the-genuine-chosen-curve-class)
gives the exact comparison with arbitrary localization boundaries and the
resulting nonzero theorem. It also distinguishes the value \(-1/513\)
for the selected trace-\(1/3\) tangent from \(-1/171\) for the
trace-one tangent. The graded projective interpretation, semiregularity,
moving-class identification, and Abel--Jacobi/de Rham comparisons remain.

### Actual local lifts and the relative transition identity

The coefficient motion now acts on the literal polynomial and localized
surface rings. `CycleQ2LocalizationDerivation` first constructs the unique
extension of a derivation through an arbitrary localization. Its proof
uses the graph homomorphism into the square-zero extension
\(S\oplus S\varepsilon\), with \(\varepsilon^2=0\). The localization's
universal property extends this graph, and its second coordinate gives
the derivation. No domain hypothesis is required.

`CycleQ2PolynomialCoefficientDerivation` applies the same construction to
multivariate polynomials. The resulting derivation fixes every coordinate
and satisfies
\[
D_{\rm coeff}(a x^e)=D(a)x^e.
\]
This formula is proved for the actual polynomial algebra, along with
uniqueness from the coefficient and coordinate values.

Let \(D\) be the coefficient motion, let \(D_a,D_b\) be two coordinate
derivations, and let \(F,h\) be the two actual surface equations. Put
\[
\Delta=D_a(F)D_b(h)-D_b(F)D_a(h).
\]
On the localization where \(\Delta\) is a unit, define
\[
\begin{aligned}
\widetilde D={}&D+
 \frac{D_b(F)D(h)-D_b(h)D(F)}{\Delta}D_a\\
&+\frac{D_a(h)D(F)-D_a(F)D(h)}{\Delta}D_b.
\end{aligned}
\]
`CycleQ2SurfaceLocalDerivations` proves
\(\widetilde D(F)=\widetilde D(h)=0\), proves that the actual ideal
\((F,h)\) is preserved, and constructs the induced derivation on the
literal localized quotient. It also proves that every element annihilated
by \(D_a,D_b\) retains its original coefficient derivative.

`CycleQ2IncidenceLocalDerivations` binds this construction to the finite
trace family's actual specialized sextic and cubic. The sextic's
coefficient derivative is zero. `actualLocalTime_coefficients` proves
that each resulting local surface derivation restricts to the already
constructed derivative of the coefficient field, which is finite over
the trace parameter field. The new theorem
`CycleQ2IncidenceSurfaceGradientOpen.actual_trace_prime_minor_cover`
proves that these Jacobian-minor opens cover every relevant prime
of this actual pointed trace surface. The projective graded-cover
and sheaf comparisons remain separate.

The transition calculation now retains the variation of the surface
coordinates. On a common overlap ring, let \(D_p,D_q\) be two local
lifts and let \(g_{pq}g_{qr}=g_{pr}\) be the actual unit transition
identity. Write
\[
a_{pq}=D_p\log g_{pq}=g_{pq}^{-1}D_p(g_{pq}).
\]
`CycleQ2SegreKodairaSpencer.boundary_eq_contraction` proves the chain
identity
\[
a_{qr}-a_{pr}+a_{pq}
 =\left\langle D_q-D_p,\,d\log g_{qr}\right\rangle.
\]
It also proves the cocycle identity on quadruple overlaps, the formula
for the actual matrix-entry transitions, compatibility with coefficient
maps, and change-of-lift behavior. The degree-fourteen homogeneous twist
is retained in `twisted_boundary_eq_contraction`.

When \(D_p,D_q\) agree on the coefficient ring \(A\), their difference
is constructed as a genuine \(A\)-derivation of the overlap ring \(R\).
`CycleQ2RelativeKodairaSpencer` identifies the displayed contraction with
evaluation on the actual relative Kähler module \(\Omega_{R/A}\).
The identity does not require the local derivations to commute. It is
an explicit comparison of cochains on a common ring. The global graded
cover, comparison with the normal connecting class, and de Rham/Gysin
interpretation must still be constructed.

## Global conormal bases and the genuine chosen-curve class

The equation-coordinate bases are now proved without restricting to a
Jacobian chart. The auxiliary monomial order has weights
\((3,1,4,1,9)\) on \((x_0,x_1,x_2,x_3,w)\). The actual equations
\(f_1,f_2,h_\theta\) have monic leading monomials
\(x_0^2,w,x_2^3\), and the actual surface equations
\(F,h_\theta\) have monic leading monomials \(w^3,x_2^3\).
These leading monomials have pairwise disjoint supports in each sequence.
The checked monic-division argument proves the required regular-sequence
relations. An independent cotangent argument then proves that the actual
equation classes form bases of the scalar-extended conormal modules.

In `CycleQ2SeedGlobalConormal`, `seedConormalBasis` and
`surfaceConormalBasis` work over every algebra annihilating the actual
curve ideal. They require neither a chosen Jacobian minor nor invertibility
of \(g_1\) or \(g_2\). The natural map is the genuine map induced by
\(J\subseteq I\) on cotangent modules, with
\(I=(f_1,f_2,h_\theta)\) and \(J=(F,h_\theta)\). In these proved
equation bases its dual is
\[
 (u_0,u_1,u_2)\longmapsto
 (g_1u_0+g_2u_1+k_\theta u_2,\;u_2),
\]
using the literal identity
\(F=f_1g_1+f_2g_2+h_\theta k_\theta\).

The actual localizations at \(g_1\), \(g_2\), and \(g_1g_2\)
carry this dual-conormal map. Its kernel is trivialized by
\((g_2,-g_1,0)\), and those trivializations commute with the actual
restriction maps. On each single open the normal map is surjective.
`CycleQ2ActualNormalCech.NormalCech` is the overlap kernel modulo the
sum of the two genuine kernel-restriction images.
`normalCechEquivalence` identifies it with the scalar overlap quotient.
Under that equivalence the connecting class, defined from the difference
of two genuine local normal lifts of \((A,L)\), is represented by
\[
 \frac{k_\theta L-A}{g_1g_2}.
\]
The class is unchanged by arbitrary changes of either lift by a local
kernel section. Thus the scalar formula is a proved coordinate description
of the genuine connecting construction.

The boundary comparison now handles arbitrary sections of the two actual
localizations. `CycleQ2LocalizationBoundary.clear_two_open_boundary`
clears their denominators and retains the extra common-product factor
that can occur when an equality is known only after localization. It
does not assume that the original ring is a domain or that either
localization map is injective. Its specialization
`CycleQ2SeedLocalizationBoundary.paired_boundary_witness` gives unrestricted
polynomial witnesses with some \(N\geq2\), \(M\geq4\). The subsequent
homogeneous projection produces the degrees required by the existing
all-poles Čech model. No fixed denominator bound is imposed.

Consequently a zero genuine normal connecting class would give a boundary
annihilated by the previously checked residue functional. Its explicitly
nonzero value proves

```lean
CycleQ2SeedNormalNonzero.actual_seed_ambient_test_nonzero :
  CycleQ2ActualNormalCech.connectingClass 57 1
    CycleQ2NormalConnecting.derivativeA 0 ≠ 0
```

The general theorem holds for every complex \(r\ne0\) and every
\(\theta\). There is no assumed smoothness, Jacobian rank, conormal
basis, or residue nonvanishing in this result. Here the ambient test is
\(A=x_2x_3^3w\), with \(L=0\). The exact paired representative has
value
\[
 -(3r)^{-1}\operatorname{derivativeTrace}(\theta,v).
\]
For the earlier selected tangent the trace is \(1/3\), giving
\(-1/513\) at \(r=57\). The distinct trace-one direction gives
\(-1/171\); these are different inputs to the same formula.

`CycleQ2SeedTwoOpenCover.relevant_prime_cover` proves that these two
denominator opens cover every relevant prime of the actual curve for
\(r\ne0\). On the curve, simultaneous membership of
\(g_1=3r^2(x_1x_3)^2\) and \(g_2=3x_2^4\) forces all five
coordinates into the prime, contradicting relevance. The cover theorem
therefore concerns arbitrary prime ideals, rather than only complex
closed points.

This is still an ungraded Čech quotient on the affine cone. The expected
projective normal sequence has twists
\[
0\longrightarrow\mathcal O_C(-2)
\longrightarrow\mathcal O_C(2)^{\oplus2}\oplus\mathcal O_C(3)
\longrightarrow\mathcal O_C(6)\oplus\mathcal O_C(3)
\longrightarrow0.
\]
Its kernel generator has coordinate degree four; the scalar connecting
coefficient has degree minus two, and multiplication by a cubic gives
the canonical degree-one curve class. The graded sheaf comparison and
the semiregularity map into the surface's top cohomology are not proved
by the preceding ungraded construction.

The ambient-test class is also different from the normal obstruction of
the actual fixed-sextic incidence motion, which vanishes. The chosen curve
is not itself stable under the order-three action. Its nonzero class
therefore does not, without a further comparison, establish nonvanishing
of the orbit trace or of a class on the moving component.

## Relative surface Čech modules and the pointed component

The relative calculation now uses the full invariant cubic and sextic
coefficient families over an arbitrary nontrivial commutative ring \(R\).
After normalizing their leading coefficients, the actual quotient
\[
 R[x_0,x_1,x_2,x_3,w]/(H,F)
\]
is free of rank nine over \(R[x_1,x_2,x_3]\), with basis given by the
actual quotient classes \(x_0^aw^b\), \(0\leq a,b<3\).
The proof uses the coprime monic leading monomials \(x_0^3,w^3\),
so it also applies to coefficient rings with zero divisors.
The three coordinate opens \(x_1,x_2,x_3\) cover every relevant prime:
their simultaneous vanishing forces \(x_0\) by the cubic and then
\(w\) by the sextic.

The localized bases, restrictions, and coefficient maps are constructed
on the actual quotient and its actual coordinate localizations. The
Laurent-coordinate descriptions follow from those constructions. In
weighted degree zero the quotient of the triple-open module by the three
pair-open images is free, with character dimensions
\[
\begin{array}{c|ccc}
 \chi\in\mathbb Z/3 &0&1&2\\\hline
 \operatorname{rank}_R&7&8&8.
\end{array}
\]
In `CycleQ2UniversalSurfaceCharacterPersistence`, `actualCoordinates` and
`coordinates_actualTopMap` prove the actual quotient's coordinate basis
and the coefficientwise naturality of its localization-induced maps.

For every nontrivial commutative \(R\)-algebra \(S\), these maps give a canonical
tensor base-change equivalence in each character:
\[
 S\otimes_R\operatorname{ActualTopCech}_{R,\chi}
 \simeq_S\operatorname{ActualTopCech}_{S,\chi}.
\]
The theorem
`CycleQ2UniversalSurfaceCharacterPersistence.actualBaseChange_tmul`
identifies the image of \(s\otimes z\) with
\(s\cdot\operatorname{actualTopMap}_\chi(R\to S)(z)\).
This identifies the equivalence with the original coefficient map,
rather than only asserting that two free modules have equal rank.

The character relevant to the intended ambient test is one. The polynomial
\(A=x_2x_3^3w\) has character one and the residue volume has character
two, making \(A\Omega/F^2\) invariant. An invariant cubic gives a
canonical residue of character two, so its dual top surface cohomology
piece has character one. The corresponding explicit Čech piece has
rank eight. The previously computed character-zero rank-seven piece
remains a distinct piece. Identifying this character calculation with
the projective canonical pairing is still a geometric obligation.

The normalization is bound to the literal incidence family:
`universalIdeal_normalized` and `mapped_universalIdeal_normalized` prove
equality of the original and normalized defining ideals, before and
after arbitrary coefficient specialization. The quotient equivalences
preserve each original polynomial class. The literal seed specialization
uses \((r,\iota)=(57,\mathrm i)\), without assuming \(r^3=2\).
`pointSurfaceEquiv` gives the same identification for the actual finite
trace-family surface.

Retain the chosen additional coefficient open \(c\), and form
\[
 A_z=\operatorname{ParameterRing}(\mathbb C)[c^{-1}]
       /\ker(\operatorname{openGeneric}_z).
\]
This is `CycleQ2IncidenceTraceComponent.ComponentRing`. Its generic
coefficient map is injective. Pointedness extends through both coefficient
localizations, so the literal seed specialization factors through
\(A_z\) whenever \(c\) has seed value one. The additional open is a
unit throughout this component ring, and all the actual cleared incidence
equations vanish there.

`CycleQ2IncidenceTraceCharacterComponent.componentTop_nonzero` proves
persistence for a class of any specified character defined on this actual
component: a nonzero image under the actual seed coefficient map has a
nonzero image under the actual generic coefficient map. Its relevant
specializations are `characterOne_nonzero` and `characterOne_rank_eight`.
The class need not lift to the unconstrained ambient parameter ring.

What is missing is a construction of the geometric ambient-test class on
this component and a proof that its seed equals the image of the computed
normal connecting class. The nonzero chosen-curve class and the conditional
surface-persistence theorem do not supply that identification. Orbit trace,
the projective semiregularity comparison, and the Abel--Jacobi/de Rham
interpretation remain separate obligations.

## Exact seed-surface cover and its persistence

The complete seed surface now has an exact algebraic Jacobian-minor
cover. Write
\[
 q=x_0^6+x_2^6-185193x_1^3x_3^3,\qquad
 G=w^3+q,\qquad F=G+hk,
\]
with the literal cubic \(h=\operatorname{smoothH}(\mathrm i)\),
the literal \(k=\operatorname{smoothK}(\mathrm i)\), and
\(185193=57^3\). For each \(j=1,2,3\), a proved exact
Gaussian-integer identity expresses a nonzero constant multiple of
\(x_j^{17}\) in the ideal generated by \(q,h\) and their six
two-column Jacobian minors in \(x_0,x_1,x_2,x_3\).
The sparse representation retains all 889 multiplier coefficient pairs
and the original exact denominators. Its evaluation theorem is proved
in Lean under every ring homomorphism from the Gaussian integers to a
commutative target ring. The identities are
then checked by ordinary kernel reduction, with no finite-characteristic
replacement for the characteristic-zero conclusion.

Consider a relevant prime containing \(F,h\). The existing coordinate
cover guarantees that one of \(x_1,x_2,x_3\) lies outside it. If the
prime contains \(w\), the new identities force at least one branch
Jacobian minor outside it. If it does not contain \(w\), the already
checked cubic-gradient cover and
\(\partial_wG=3w^2\) supply a two-column minor outside it.
The minors of \((F,h)\) and \((G,h)\) agree modulo \(h\).
This proves `CycleQ2SeedSurfaceGradient.prime_minor_cover` for every
relevant prime of the literal seed surface.

`actual_prime_normal_cover` binds the result to the determinants of the
actual ordered tuple `(actualSeedEquation 57 1, thetaH 1)` used in the
conormal construction. `actual_field_normal_cover` gives a unit determinant
under every field-valued point satisfying these two equations and the
relevance condition. No relation \(r^3=2\) is used.

The propagation to the family is also proved. For a finite homogeneous
generator family, the absence of a relevant prime at the seed implies,
by radical membership, that the seed ideal contains powers of every
coordinate. It then contains a sufficiently high full invariant graded
piece. The existing finite homogeneous coefficient-matrix construction
produces a coefficient polynomial \(s\) with seed value one such that
the same prime-cover conclusion holds after any coefficient specialization
where \(s\) is a unit. These steps are the theorems
`coordinate_powers_of_prime_cover`, `high_degree_homogeneous_mem`, and
`exists_prime_cover_open` in `CycleQ2HomogeneousPrimeCoverOpen`.

For the actual invariant cubic/sextic family, the homogeneous generators
are \(F,h\), and the cubes of all its two-column Jacobian minors.
Cubing makes every minor generator character zero. Their weighted degrees,
compatibility with coefficient maps, and literal seed specialization are
proved. Primality recovers a nonvanishing original minor from a nonvanishing
cube. This yields a coefficient open containing the literal seed on which
the actual surface minor cover persists.

The pointed trace condition says that a polynomial coefficient vanishing
at the generic point must vanish at the seed. It therefore makes every
coefficient polynomial of seed value one nonzero, and hence a unit, in
the trace extension field. The resulting endpoint is
`CycleQ2IncidenceSurfaceGradientOpen.actual_trace_prime_minor_cover`:
every relevant prime containing the actual specialized `actualF B z`
and `actualH B z` omits at least one of their genuine two-column Jacobian
minors. These are the same minor opens used to construct `actualLocalTime`.

This completes the algebraic cover condition for those local derivations.
It does not assert an already constructed projective smooth family, identify
the ambient-test semiregularity class, or supply the missing Abel--Jacobi,
support, and de Rham comparisons.

## Remaining formal obligations

| Obligation | Status |
| --- | --- |
| Protected target, actions, degrees, nonvanishing | Proved for the exact instance. |
| Gradient condition, absolute irreducibility, affine quotient field | Proved; geometric Jacobian criterion remains. |
| Actual Fermat Jacobian bases, socle trace, finite commutant | Proved; geometric Higgs comparison remains. |
| Sparse seed quotient trace, degree-nine dimension and uniqueness, all 72 matrix entries | Proved; actual all-poles Čech comparison and vanishing equivalence now proved too. |
| Actual curve chart cover and the theta-one nine-column residue functional | Proved on the actual curve; obstruction/Abel--Jacobi interpretation remains. |
| Literal cubic, seed-curve, and seed-surface Jacobian conditions | Exact Gaussian-integer identities prove the cubic gradient condition and normal-minor covers at all relevant curve and surface primes. The seed-surface cover persists to the actual finite pointed trace surface through a proved coefficient open. A geometric smoothness interpretation remains separate. |
| Actual seed conormal modules and normal matrix | Global genuine equation-class bases are proved over every algebra annihilating the curve ideal. The actual natural map and its dual agree with the computed normal matrix in those bases. No Jacobian-unit hypothesis is needed for these bases. |
| Genuine chosen-curve ambient-test connecting class | Actual dual-conormal restrictions, local surjectivity, kernel trivializations, connecting-class comparison, independence of lifts, and nonvanishing against all localization boundaries are proved. The two denominator opens cover every relevant curve prime. Graded sheaf, semiregularity, and orbit-trace comparisons remain. |
| Cubic Cartier matrix factorization and periodic quotient complex | Polynomial identities and genuine exactness proved; geometric base change remains. |
| Literal Segre seed, cofactor quotients, and selected section products | Universal polynomial identities proved for the actual chosen entries. |
| Actual complex basepoint cover and local Segre exactness | Proved on every relevant prime and every nonempty coordinate localization, including homogeneous local lifts. |
| Regular linkage element and actual local factor sequence | Proved; the literal factor ideals are principal with regular generators on unit-entry charts. |
| Seed and full relative surface Čech complexes | Actual localized quotient models and coefficient maps are proved. Degree-zero character dimensions are 7, 8, 8, with canonical tensor base change over nontrivial coefficient algebras. The relevant ambient-test piece is character one, of rank eight. |
| Pointed-component persistence for the surface class | The actual component coefficient ring, its seed and injective generic maps, and persistence for a class in its character-one Čech module are proved. Construction of the geometric ambient-test class and its seed identification remain. |
| Chosen curves, restrictions, and orbit ideals | Actual six-term bases, two-open cover and gluing, restriction kernels, cyclic orbit identification, and the 56/23 section dimensions proved. |
| Positive graded H1 of both linkage ideals | Proved for the actual degree-ten invariant and degree-eight character-one pieces. |
| Actual relation-kernel obstruction | The actual connecting maps identify the obstruction with kernel Čech H1 and scalar Čech H2; its dimension is exactly seven. |
| Actual matrix-entry Jacobian and coefficient relations | Entry-block rank 1915, combined Jacobian rank 1922, relation-matrix rank 7600, and actual image/kernel equality proved. |
| Unit-entry image modules, transition units, and logarithmic differentials | Proved, including coefficient-map naturality, the homogeneous degree twist, and the relative Kodaira--Spencer contraction/boundary identity. |
| Local lifts of the actual trace-family motion | Constructed on actual surface Jacobian-minor localizations, now proved to cover all relevant primes. Coefficient restriction and preservation of both equations are proved. Binding external ambient-test lifts and projective sheaf comparisons remain. |
| Formal and algebraic generic lifting of polynomial systems | Existence proved from actual seed equations and unit Jacobian; exact sequences provide compatible square blocks, and complementary relations force all omitted equations. |
| Actual large incidence system, graded bases, literal seed, and full first-order equations | Proved, including a nonconstructively chosen characteristic-zero fixed-sextic tangent with trace one satisfying all 9,522 equations. |
| Universal coefficient relations and polynomial denominator clearing | Proved, including the exact relation-Jacobian identity at the seed. |
| All 45 sextic coefficient directions | Actual tangent projection is surjective, with total tangent dimension 283 and fixed-sextic kernel dimension 238. |
| Universal basepoint and generic gradient opens | Actual homogeneous multiplication maps and faithful field specializations prove the stated algebraic conditions. |
| Generic component through the seed | Proved for the actual compatible incidence algebra: the generic prime contracts inside the seed kernel, and polynomial identities specialize. |
| Moving projective curve family | Incidence, local image lines, and regular local section equations are constructed; the global curve/cylinder and relative geometric trace comparisons remain. |
| Generation of the invariant variation and supported projector | Not formalized. |
| Actual generic primitive specialization and finite-extension descent | Proved, including primitives with parameter poles; existence of the initial generic primitive remains. |
| Paired-sign weighted equation, source, and relative primitive transfer | Exact equation/source and three-derivation-to-certificate implication proved; cohomological support comparison remains. |
| Proper support to homogeneous legal equation | Proved for actual projective closed subsets. |
| Countable algebraic avoidance and covering of a complex principal open | Proved for actual polynomial zero loci. |
| Actual Kähler differentials, exterior derivative, and exactness/PDE equivalence | Proved over the actual complex function field. |
| Formal normal chart, universal exterior pullback, and pole-three Laurent residue density | Proved, including faithfulness, actual tangent chain rules, and equality with the exterior source coefficient. |
| Support/cohomological vanishing to the displayed affine primitive | Global residue and algebraic de Rham comparison not formalized. |
| Auxiliary one-mixed-term family | Unconditional certificate proved for that distinct family. |
| Displayed affine primitive to the unchanged protected certificate | Fully proved algebraically. |

The polynomial-curve constructors in the existing library require actual
polynomial coordinates, normal fields, or densities in a parameter.
An algebraic Hilbert parameter curve does not automatically satisfy those
hypotheses. The actual finite incidence system and its compatible square
blocks are now proved, so an assumed large Jacobian rank is no longer
the obstruction. The missing work is the geometric comparison from the
moving line or curve data to the specified cohomology class, generation
and support of the invariant variation, and the global algebraic de Rham
comparison with the protected rational form. These interfaces cannot be
used to bypass that existence proof.

The next central comparison must construct the actual divisor or
semiregularity connecting map from the chosen-curve normal class into the
character-one surface Čech module, and prove that its pairing equals the
computed curve residue. It must then construct that same class on the
pointed component and identify its seed specialization. Lifting an arbitrary
nonzero seed coordinate vector into a free relative module would not supply
this geometric identification.

The existing trace-family local derivations follow the fixed-sextic
incidence motion. They have not yet been bound to the external ambient test
\(F+\varepsilon A\). Similarly, an orbit response must include the
character twist: for a generator \(g\) with \(gA=\zeta A\), the
expected covariant formula is
\[
 \sum_{j=0}^2 o_{g^jC}(A)
 =\sum_{j=0}^2\zeta^{-j}g^j o_C(A)=3e_1o_C(A).
\]
This formula is a remaining comparison, not a theorem claimed by the current
formalization. The ordinary sum of translates of a character-one vector
would vanish. Neither the existing fixed-sextic obstruction nor an untwisted
orbit sum can replace the required ambient-test class.

## Preserved current route

All `Current*.lean` files remain unchanged and are not dependencies of the
active entry point. [CurrentData.lean](CurrentData.lean) retains its 13,874
expressions and literal `transportError`, whose vanishing is not assumed.
[CurrentCorrection.lean](CurrentCorrection.lean) retains reconstruction and
`originalGoal_iff_actual_current_correction`: a future completed geometric
proof would imply that correction existential as well.

The denominator, normal-gauge, tangent and ambient-lift developments remain
available in their original files. Their source bodies remain unchanged.

## Source layout

The active development contains 485 consolidated components. The original
61-component [GeometricFormalInputs.lean](GeometricFormalInputs.lean)
baseline remains byte-for-byte unchanged, together with its checked artifact.
The 424 continuation components occupy four existing permitted files:

| File | Components | Contents |
| --- | ---: | --- |
| [GeometricFormalInputs.lean](GeometricFormalInputs.lean) | 61 baseline | Existing affine residue/certificate bridge and foundational geometric inputs. |
| [GeometricTarget.lean](GeometricTarget.lean) | 100 continuation | `AffineFiniteDescent` through `CurveRestrictionModularLeft`, after the original target/action declarations. |
| [Assembly.lean](Assembly.lean) | 36 continuation | `CurveRestrictionModularRight` through `SegreModularActionFlat01`, after the original assembly declarations. |
| [Normalization.lean](Normalization.lean) | 11 continuation | `SegreModularActionFlat02` through `SegreModularCubicData2`, after the original normalization declarations. |
| [Solution.lean](Solution.lean) | 277 continuation | The previous 239 components, followed by 38 new components for global conormal bases, genuine normal classes, relative character Čech modules, and seed/moving surface covers, then the unchanged entry-point body. |

`Workspace` and the original `GeometricSeed` precede the baseline. The
continuation imports in the table's order. All prior component proof bodies
and the exact original entry-point body are preserved. Every new helper
occurs before `Submission.missing_geometric_existence`, so no new helper
can use that later admission. The assembly record checks each component
body hash and its final byte range. Only `Solution.lean` and `solution.md`
change relative to checkpoint `5c9d41d179dd`.

The complete proposal remains within the existing 64-file limit and the
16 MiB source limit. The new source is consolidated without adding another
submitted file.

## Historical verification of earlier source checkpoints

The continuation documented at the beginning of this file was initially
uncompiled. Its later development compilation scope is recorded in the current
checkpoint above. The historical records below retain their original source
scope and must not be applied to the newly modified source files.

Development uses Lean 4.33.1 and mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. There are two distinct
validation scopes: the previous complete four-stage checkpoint, and this
revision's individually checked components plus their new integration check.

### New components and integration

All 38 new components have matching source-hash receipts for compilation
and separate independent `leanchecker` replay:

| Group | Components | Compilation, seconds | Independent replay, seconds |
| --- | ---: | ---: | ---: |
| Global conormal bases and genuine chosen-curve class | 12 | 103.890 | 55.538 |
| Seed and pointed surface Jacobian covers | 10 | 57.165 | 45.576 |
| Relative surface and character-one persistence | 16 | 171.326 | 88.299 |
| Total | 38 | 332.381 | 189.413 |

The separate `Proposal.NextContinuationVerification` module imports the
previous checked `Proposal.Solution` and jointly elaborates
33 new component bodies. It imports the 5 new sparse-arithmetic
artifacts after their individual compilation and independent replay, rather
than elaborating those large exact calculations a second time. Their complete
source bodies are still included in the submitted `Solution.lean`.
The integration compilation took 209.628 seconds, and its independent
kernel replay took 26.164 seconds. All seven imported checkpoint
artifacts and each reused arithmetic artifact are pinned by SHA-256.

This is a check of new helper integration over a previously checked
checkpoint. It is **not a fresh compilation or replay of the complete newly
assembled proposal**. The source-preservation audit and component checks do
not expand that stated execution scope.

The new component logs contain 93 printed endpoint axiom reports.
All reported helper axiom sets are subsets of `propext`, `Classical.choice`,
and `Quot.sound`; the same holds for the printed integration endpoints.
This audits those printed endpoints, not every declaration independently.
No native decision procedure or added axiom supplies the arithmetic proofs.
All component compilations used one thread. Thirty used a 4,096 MiB Lean
memory limit, and eight used 5,120 MiB. Eight root components recorded a
5,120 MiB RSS ceiling; the eight leading-term/surface components and sixteen
relative-surface components recorded a 5,376 MiB ceiling. These guarded
runs retained a 2,048 MiB available-memory threshold. The six normal-class
receipts record no external RSS or available-memory guard. The integration
used a 4,096 MiB Lean limit, a 5,120 MiB RSS ceiling, and a 2,048 MiB
available-memory threshold.
The maximum sampled component RSS was 3740.74 MiB. Integration
resource settings and sampled peaks are recorded in its separate receipt.

The original expanded surface arithmetic attempt timed out without a
successful artifact. The replacement sparse representation retains all
889 Gaussian-integer multiplier pairs and the exact denominators, and
proves its evaluation soundness in Lean. Each of the three coordinate
identities is checked by ordinary kernel reduction. The earlier failed
attempt and its bounded diagnostic remain recorded as unsuccessful checks.

The newly assembled `Solution.lean` source SHA-256 is
`87eda90e5f60dc243e9285f0c578ee2dbab2fcef777f113bb3c1cd8f688dea18`.
The separate integration source SHA-256 is
`d2c75cf1f8e9932aef0c6c4642c1afb3f3b9971ea202da19f50c9daf16177260`.
These are different sources and their receipts are not interchangeable.

### Historical four-stage checkpoint

The preceding 447-component source checkpoint passed all four complete
stage compilations and separate independent replays:

| Stage | Compilation, seconds | Independent replay, seconds |
| --- | ---: | ---: |
| `GeometricTarget` | 839.781 | 336.938 |
| `Assembly` | 788.955 | 372.881 |
| `Normalization` | 228.262 | 22.153 |
| Previous `Solution` | 2126.165 | 891.574 |

These historical successful stages total 3,983.163 seconds of compilation
and 1,623.546 seconds of independent replay, or 5,606.709 seconds. Their
driver wall time was 6,341.150 seconds, including recorded pauses and
unsuccessful split attempts. Those timings do not describe a fresh run of
this revision. The exact four Lean sources are preserved in source commit
[`314847b0c2e4`](https://github.com/fqlx/sextics/commit/314847b0c2e435df0f22e3d0fe42a232e75fa48d),
with the final prior verification explanation in
[`5c9d41d179dd`](https://github.com/fqlx/sextics/commit/5c9d41d179ddeabf367b5c2b6a7f3ed39f874abb).

Their source SHA-256 values are:

```text
GeometricTarget.lean
  83e9434d3124124d2bb610de1accd88e39a96a25a73cb0449c7809f4f3a8a809
Assembly.lean
  f5a7b3eadace85bfa69b137a76b5d79c74301080ca187dbc899b0df26f1dcfa1
Normalization.lean
  54e5b909d2dd17b400059066b50e18b3eca384a36e203fd101b095cd1c11db20
Previous Solution.lean
  5bf1220b1bcb565a85e920f38b8ffe504ee562cbed2df99533c7f59d22444b62
```

The original 61-component baseline was reused from its recorded
1,696.056-second compilation and 62.465-second replay. Its source SHA-256
is `68f06d3630e974fc8a7a0bc57ef952744bc98b00979c0092aecf2471f2640590`;
its main artifact SHA-256 is
`139c853a60871649e05f18d1ff5a1a96f56f6b8a010acc85d10823a09b094560`.
The baseline receipt does not record its thread or memory settings.
The unchanged `Workspace` and `GeometricSeed` artifacts also match their
successful historical receipts.

Those four historical compile logs contain 758 printed axiom reports:
757 helper reports covering 714 distinct helper declarations, plus the
certificate. All helper reports use only the three standard axioms named
above; 15 helper reports use none. Among those reports, only
`Submission.certificate` includes `sorryAx`. Failed monolithic and earlier
split attempts remain separate from these successful checks.

### Protected boundary and remaining execution limits

The protected target is generated from base
`e3936ff366ae2302f21fb9e5730bbbd284c81d69`, with generated source SHA-256
`8052a2dfa06a0e7b8f3322a38f9f7a3a49ce3b3f5ebeb0f9d10ac354ab1fa6c2`.
The protected instance, shared library, verifier, workflows, and proof
manifest remain unchanged. Static source-policy checks pass every helper
and the complete helper prefix in `Solution.lean`.

The full proposal is rejected by source policy because it still contains
the one explicit admission, `Submission.missing_geometric_existence`.
Its protected certificate still depends on `sorryAx`. Neither compilation
nor kernel replay of an admitted entry point proves that missing theorem.
No completed certificate or evaluated witness is claimed.

The 55 legacy Lean files outside the active seven-module `Proposal` import
closure have not been rebuilt against the new import environment. Checking
`CurrentNormalGauge` and `CurrentTangents` first requires the 52-module
`CurrentCorrection` dependency chain beyond the reused `Workspace`; those
artifacts are absent from the reused cache. Static source checks do not
replace their compilation.

The protected Linux verifier compiles every submitted helper, including
unused ones, in a two-CPU, 14-GiB container under one shared 3,600-second
deadline covering compilation, independent replay, wrappers, and final
auditing. The historical development sum exceeds that deadline but differs
in resources and scope; it is not an official timeout result. The complete
protected run and its full-proposal budget compliance remain untested.

## Attribution

The geometric route is the Chapter 3D argument of `benediamond` and
collaborators in
[Discussion #61](https://github.com/hodge-computer/sextics/discussions/61),
using Claire Voisin's moving-cycle strategy, Griffiths residue and
Abel--Jacobi formulas, Dolgachev's weighted residues, Aoki--Shioda-type
cycles studied by Braun--Fortin--Lopez Garcia--Villaflor Loyola, and the
references of Chapters 3 and 1. Grothendieck's affine algebraic de Rham
theorem supplies the smaller classical support-to-primitive bridge.

The chart-map formalization adapts the accepted rational chart methods
in the project's two-ternary-dense-hessian development. The earlier work
of `hodgepodgeconjecture`, `DiamondJM`, `fqlx`, and the Hodge Computer
collaborators remains preserved and credited. This continuation was
prepared for `fqlx` with OpenAI ChatGPT assistance.


## Complete classical proof and finite certificates

The following sections preserve the complete written reconstruction in plain-text
notation. The exact finite certificates follow as JSON. The proof is mathematical;
the admission in the Lean source is still present.

### Statement, scope, and attribution

```text
CYCLE-Q2: A CLASSICAL EXISTENCE PROOF OF THE MISSING GEOMETRIC STATEMENT
Completed written reconstruction and finite-input audit: 12 November 2026

Target:
  Submission.missing_geometric_existence :
  CycleQ2Nonconstructive.AffineResidueFormExact

STATUS, ATTRIBUTION, AND SCOPE
=============================

This document gives a classical, nonconstructive proof of the exact
mathematical existence statement, and an explicit conversion of its
rational primitive into the ordinary homogeneous q=2 certificate.
The argument follows the moving-Hodge-class strategy in the project's
Chapter 3D, itself based on work of Claire Voisin. It expands the trace,
moving-class, algebraization, supported-projector, specialization, and
full-residue comparisons that are needed to reach the protected instance.
It is a reconstruction and verification of that route, not a claim of
independent authorship of the underlying strategy.

The finite algebra calculations used in the proof were rerun exactly.
They give Noether-Lefschetz rank 7, augmented rank 8, and a scalar-only
Higgs commutant. The bounded Python calculation took about 0.22 seconds
and reported peak RSS 27,168 KiB, approximately 26.5 MiB. It invoked no
Lean, Lake, compiler, language server, kernel replay, or project build.

This is an ordinary mathematical proof, using the classical theorems
identified below. The Lean theorem has not been filled in or checked by
Lean, and its existing explicit sorry remains in the source. The proof
establishes existence; an expanded coefficient tuple for D, N_i, Q has
not been computed. No replacement axiom or admission has been introduced.

All project sources used here are pinned at:
  hodge-computer/sextics
  520a2a29c40cc40e1df2b1c41980552f25d08e65

THE PRECISE CONCLUSION
======================

Use homogeneous coordinates Z=(X0,X1,X2,Y0,Y1,Y2) and set

  F = sum_{i=0}^2 (Xi^6+Yi^6)
      +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2,
  A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2.

In the affine chart X0=1 put

  (x0,x1,x2,x3,x4)=(X1,X2,Y0,Y1,Y2)/X0,
  f=1+sum_{i=0}^4 xi^6
       +(x0 x2 x3+x0^3 x1 x3 x4+x1^3 x2 x4)/2,
  a=x0^2 x1^3 x2^2 x3^2 x4,
  K=Frac(C[x0,...,x4]/(f)),
  g=partial_0 f, g0=partial_0 g, g00=partial_0^2 g,
  vol=dx1 wedge dx2 wedge dx3 wedge dx4,
  rho=(1/2)[a_00/g^3-(3a_0 g0+a g00)/g^4+3a g0^2/g^5] vol.

THEOREM. There exists eta in Omega^3_{K/C} with d eta=rho.

In the project's notation this is exactly

  exists eta : CycleQ2AffineExterior.Form 3,
    CycleQ2AffineExterior.exteriorD3 eta =
      CycleQ2AffineExactness.residueSourceForm
        CycleQ2AffineClearing.affineA.

Moreover there are a nonzero homogeneous D coprime to F, homogeneous
N_0,...,N_5 of degree deg(D)+7, and a homogeneous Q such that

  A D^2 - 2D sum_i N_i partial_i F
    +F[D sum_i partial_i N_i-sum_i N_i partial_i D] = F^3 Q.

PROOF ORGANIZATION

Part I supplies the exact finite rank inputs and their certificates.
Part II turns these into genuine moving algebraic curves with a nonzero
invariant Abel-Jacobi map. Part III proves that their images fill the
invariant H^3 and constructs supported projectors, including for special
members and the actual pencil. Part IV proves divisor support of the
full protected fourfold residue class, obtains the literal rational
primitive by affine algebraic de Rham comparison, and explicitly clears
and homogenizes it to the displayed polynomial identity.

The symbols used for the auxiliary weighted threefold coordinates in
Parts I-III are local to those parts. They are not the five affine
coordinates of the protected fourfold in Part IV.
```

### Part I: finite algebra inputs

```text
PART I. THE FINITE ALGEBRA INPUTS
================================

1. The weighted family and its Hodge spaces
------------------------------------------

Let S=C[s0,s1,s2,s3,w] have weights (1,1,1,1,2), and let
  g_T=diag(zeta^2,zeta^2,zeta,1;1), zeta^3=1, zeta!=1.
Let B denote the irreducible smooth parameter open of invariant sextics
avoiding the weighted vertex, with the coefficient of w^3 normalized to
one. Its fibers T are smooth projective Calabi-Yau threefolds. The
determinant character of the residue volume is delta=zeta^2, so the
invariant part of H^{3,0} is zero. The invariant rational variation
V=H^3(T,Q)^{g_T} has only Hodge types (2,1) and (1,2).

Weighted residues identify H^{2,1}(T)^{g_T} with the degree-six,
character-zeta part of the Jacobian ring. At Fermat,

  R=C[s0,s1,s2,s3,w]/(s0^5,s1^5,s2^5,s3^5,w^2).

There are 33 such degree-six monomials, and 35 invariant degree-six
Jacobian monomials representing deformation directions. Thus V has
Hodge numbers (0,33,33,0). These dimensions remain constant over B.
The other cohomology groups are H^{2k}(T,Q)=Q H^k, k=0,1,2,3,
H^1=H^5=0, and integral_T H^3=3. Weighted weak Lefschetz and weighted
residue theory justify these identifications [R3]. Alternatively the
nonmiddle Betti numbers can be checked at Fermat via its smooth double
cover by an ordinary sextic and then transported over the connected B.

2. The moving-divisor rank calculations
---------------------------------------

Choose r^3=2 and i^2=-1. The auxiliary seed of Part II has

  F0=sum_j sj^6+w^3, Fb=F0+b^2,
  f1=s0^2-r s1 s3,
  g1=s0^4+r s0^2 s1 s3+r^2 s1^2 s3^2,
  f2=w+s2^2,
  g2=w^2-w s2^2+s2^4,
  h=b-i(s1^3+s3^3), k=b+i(s1^3+s3^3).

Then Fb=f1 g1+f2 g2+hk. For the calculation take

  b=5s0^3+10s0^2 s1+25s0 s1^2+20s0 s2 s3+30s1^3
       +25s1 s2 s3-25s2^3-20s3^3+10s3 w.

Reduce at p=109, r=57, i=33. Directly, 57^3=2 and 33^2=-1
in F_109. In the quotient A_CI=S/(f1,f2,g1,g2,h) the Hilbert
function is

  degree:     0  1  2   3   4   5   6  7  8  9  10
  dimension:  1  4  9  15  19  19  15  9  4  1   0.

Eliminating w using f2 shows the quotient is generated in degree one.
Consequently the zero degree-ten piece implies that all higher pieces
vanish. The quotient is Artinian of length 96. Five generators in this
five-variable polynomial ring therefore form a regular sequence. Its
socle degree is 2+2+4+4+3-(1+1+1+1+2)=9. The Hilbert series is
  (1+t)(1+t+t^2+t^3)^2(1+t+t^2).

Choose a nonzero socle functional tau:A_CI,9 -> F_109. With the
normalization produced by the pinned exact script, order the invariant
cubic columns as

  (s3w, s3^3, s2^3, s1s2s3, s1^3,
    s0s2s3, s0s1^2, s0^2s1, s0^3),

and the character-zeta cubic rows as

  (s2w, s2s3^2, s1s2^2, s1^2s3, s0s2^2, s0s1s3, s0^2s3).

The matrix M_{sigma,L}=tau(k L sigma) is

   0  78   0   0   8   0  75  66  63
  78  68   0   6   0  62   0   0  47
   0   6   0  39  49  62  39   0   0
   0   0  39   0   4   0  70   0   0
   0  62   0  62  39   0   0   0   0
   0  47  62   0  70   0   0   0   0
  94  91   0   0   0  47   0   0   0.

For Btest=s2 s3^3 w, the additional row v_L=tau(Btest L) is
  v=(0,21,0,0,0,0,0,0,70).

The determinant of the first seven columns of M is 80 modulo 109.
The determinant of the first eight columns of the stacked matrix
(M;v) is 76 modulo 109. Thus rank M=7 and rank(M;v)=8.
An additional directly checkable witness is

  ell=(19,26,71,38,38,74,19,24,0)^t,
  M ell=0, v ell=1, all modulo 109.

Part II.1 proves transfer of these ranks to characteristic zero using
flatness of the complete-intersection model at this prime. It then
intersects this nonempty rank-open with the separately nonempty opens
where the varieties and curves are smooth. The modular vector ell is
not assumed to be a characteristic-zero kernel vector.

3. The scalar Higgs calculation over the integers
-------------------------------------------------

Let E be the set of exponent vectors a=(a0,a1,a2,a3,aw) with
  a0+a1+a2+a3+2aw=6,
  0<=aj<=4, 0<=aw<=1,
  2a0+2a1+a2=1 modulo 3.
Let Tdir be the analogous set with character 0. Their cardinalities
are 33 and 35. Let soc=(4,4,4,4,1).

For m in Tdir define the symmetric 33-by-33 matrix
  H_m(a,b)=1 if a+b+m=soc, and 0 otherwise.
These are precisely the Higgs forms, up to a common nonzero residue
normalization: the variation is Jacobian multiplication followed by
the socle pairing.

Consider all equations P^t H_m=H_m P. For fixed m every row of H_m
has at most one nonzero entry. Write partner_m(a)=soc-m-a when this
belongs to E, and leave it undefined otherwise. The equation (a,b) is

  P[partner_m(b),a]=P[partner_m(a),b],

where an undefined partner means zero. Each equation therefore merely
identifies two entries of P or identifies one entry with zero. Form a
graph with one node for each of the 1089 entries, and one extra zero
node, using these identifications as edges.

Exact enumeration gives two connected components:
  - all 1056 off-diagonal entries together with the zero node;
  - all 33 diagonal entries.
There is a spanning forest of 1088 equation edges. Hence the equations
force every off-diagonal entry to vanish and every diagonal entry to be
equal. Scalar matrices do satisfy them. The solution space is therefore
exactly C I, of dimension one. This conclusion holds integrally as an
entry-identification argument; it is not inferred from a single random
finite-field rank.

Appendix A contains the complete compact forest certificate, with the
33 basis exponents, 35 deformation exponents, and each retained edge
labelled by the precise equation from which it came. For node number
33*i+j the entry is P[i,j], and node 1089 is zero. Thus the certificate
can be checked by integer comparisons of five-component exponent vectors
and ordinary graph connectivity, without any algebraic-geometry software.

4. Reproduction record
-----------------------

The seed's quotient and trace were computed using the inspected project
script at [P2]. Its generated matrix was then checked with a separate
small integer modular elimination routine, including the two explicit
minors and the normalized kernel vector. The Higgs equations and forest
were independently reconstructed directly from their monomial definition.

  Source SHA256:
  9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9
  Forest JSON SHA256 (including its terminal newline):
  f2ee2a403c3d8baa41684b9db9abe3208a066cea8f06bb22d5e8d662aef6212e

The calculation was limited to 1 GiB address space and 120 seconds CPU;
it actually reported 27,168 KiB peak RSS and 0.2214 seconds elapsed.
The larger alternative fourfold computation was not needed. None of
this invoked Lean or the project's full proof compilation.
```

### Part II: moving algebraic curves

```text
PART II. FROM THE FINITE RANKS TO GENUINE MOVING ALGEBRAIC CURVES
===============================================================

This part uses the verified ranks in Part I. For consistency with the
source calculation, its auxiliary weighted coordinates are named
(x0,x1,x2,x3,w); they correspond to (s0,s1,s2,s3,w) in Part I.

1. SEED, CHARACTERS, AND SMOOTH COMPLEX POINT

Write S=C[x0,x1,x2,x3,w], with weights (1,1,1,1,2), and let
g=(zeta^2,zeta^2,zeta,1;1), zeta^3=1, zeta!=1. Its determinant
character on the ambient residue volume is delta=zeta^2.

Let b be an invariant cubic and choose r^3=2 and i^2=-1. Set

  F0 = x0^6+x1^6+x2^6+x3^6+w^3,
  Fb = F0+b^2,
  f1 = x0^2-r*x1*x3,
  g1 = x0^4+r*x0^2*x1*x3+r^2*x1^2*x3^2,
  f2 = w+x2^2,
  g2 = w^2-w*x2^2+x2^4,
  h = b-i*(x1^3+x3^3),
  k = b+i*(x1^3+x3^3).

Then Fb=f1*g1+f2*g2+h*k. Define T=V(Fb), D=V(Fb,h),
C=V(f1,f2,h), and E=C+gC+g^2C.

The following are independently nonempty open conditions in the
irreducible affine space S_3^g of b's:

  (a) T is smooth: b=0 gives Fermat. Every T avoids the weighted vertex,
      because its equation at (0,0,0,0,w) is w^3.
  (b) D is smooth: on h=0 its other equation is
      x0^6+x2^6+w^3=2*x1^3*x3^3. That hypersurface has precisely the
      x1-coordinate and x3-coordinate points as singular points.
      The invariant cubic system contains xj^3 for every j, so it has no
      base point on this hypersurface. Bertini and avoidance of those two
      points give a smooth D.
  (c) C is smooth: eliminate w=-x2^2. It is a cubic section of the
      quadric cone x0^2=r*x1*x3 in P^3. The restricted invariant cubics
      are basepoint free (again they contain the four pure cubes).
      A general section avoids the cone vertex and is smooth by Bertini.
      The complete-intersection coordinate ring has depth two, hence
      H^0(O_C)=C. Thus a smooth C is connected, and so irreducible.
  (d) C,gC,g^2C are disjoint: intersecting C with a distinct translate
      forces x0=x2=w=0 and x1*x3=0. The only possible intersections are
      exactly the two points excluded in (b).

Adjunction gives

  K_D=O_D(3), N_{D/T}=O_D(3), K_C=O_C(1), N_{C/D}=O_C(-2).

The degree of C is 2*2*3/2=6 and its genus is four. The surface coordinate
ring is a complete intersection of dimension three, so
H^1(D,O_D(n))=0 for every n; in particular H^1(O_D)=H^1(K_D)=0.

ARITHMETIC TRANSFER. At the prime with r=57 and i=33 in F_109,
57^3=2 and 33^2=-1. Localize Z[r,i]/(r^3-2,i^2+1) at
(109,r-57,i-33). Since 3r^2 and 2i are nonzero modulo 109, this is an
unramified number-field DVR R. The quotient

  A_R=R[x0,x1,x2,x3,w]/(f1,f2,g1,g2,h)

has the stated finite-length complete-intersection special fiber.
Equivalently, the five homogeneous generators form a regular sequence
modulo the uniformizer. The relative regular-sequence flatness criterion
makes A_R flat over R. Each graded piece is therefore finite free over R,
with the same rank in the special and generic fibers. Its degree-nine
piece is a free line. Choose a basis of that line and the dual trace so
that its reduction agrees with the modular trace, up to a nonzero scalar.
The nonzero modular minors are then units of R and remain nonzero in
characteristic zero.

This can also be seen locally by taking the six elements consisting of
the uniformizer and the five homogeneous generators in a regular ring
of dimension six: the finite special fiber makes them a system of
parameters, hence a regular sequence. Permuting that regular sequence
shows that the uniformizer is a non-zero-divisor on the quotient.

The rank conditions are open in b wherever the Artinian quotient has
its complete-intersection Hilbert function. Their nonempty open meets
(a)–(d). Therefore an actual smooth complex seed satisfying BOTH ranks
exists. It is unnecessary to assert that the displayed integral lift of
the modular b is itself smooth. Likewise the modular kernel vector is
evidence of a rank jump; it need not satisfy the same equations over C.

2. THE ARTINIAN TRACE REALLY IS THE CURVE SERRE TRACE

Put A=S/(f1,f2,g1,g2,h). The five weighted degrees are 2,2,4,4,3.
Their product divided by the product of variable weights is 96, and
their sum minus the sum of variable weights is 9. Thus A has length 96
and a one-dimensional socle A_9. Let tau:A_9->C be any nonzero functional.

Since D and C are smooth, g1 and g2 have no common zero on C. Their
Koszul sequence, twisted by O_C(9), is

  0 -> O_C(1) -> O_C(5) direct_sum O_C(5) -> O_C(9) -> 0.

Here H^1(O_C(5))=H^0(O_C(-4))^*=0 by K_C=O_C(1) and Serre duality.
The depth-two coordinate ring identifies its graded pieces with the
global sections in this sequence. Hence its boundary gives an actual
isomorphism

  A_9  ->  H^1(C,K_C),
  p    |-> [p/(g1*g2)].

The Serre trace of this class is c*tau(p) for ONE fixed c!=0, independent
of p. This proves nonvanishing of the comparison; dimensions alone
would not have sufficed without the surjective Koszul boundary.

3. THE NORMAL CONNECTING FRACTION AND HODGE OBSTRUCTION

For the first-order surface deformation (Fb+epsilon*B,h+epsilon*L),
the local normal fields for C in the ambient weighted projective space
satisfy

  u3=-L,
  g1*u1+g2*u2+k*u3=-B.

On g1!=0 choose u2=0, and on g2!=0 choose u1=0. Their difference is

  ((kL-B)/(g1*g2))*(g2,-g1,0),

so its coefficient is the actual class in H^1(N_{C/D})=H^1(O_C(-2)).

Let rho be the Kodaira-Spencer class of the surface deformation and
omega_sigma the canonical two-form represented by the cubic sigma.
Flatness of the intersection pairing and Griffiths transversality give

  <bar_nabla_[B,L][C],omega_sigma>
    = - integral_C (rho contraction omega_sigma)|C.

After restriction to C, contraction with omega_sigma kills the tangent
part T_C. Thus this expression depends only on the image of rho in
H^1(N_{C/D}), just computed. Adjunction identifies multiplication by
sigma with N_{C/D} tensor K_D|C -> K_C. The trace calculation of Section 2
therefore gives

  <bar_nabla_[B,L][C],omega_sigma>
       = c0*tau((B-kL)*sigma),  c0!=0,

up to a uniform sign convention. This is also the usual divisor
semiregularity/Atiyah obstruction formula, but the displayed calculation
derives precisely the required pairing rather than merely invoking a
map with the desired source and target.

4. THE ORBIT SUM AND THE TWO DISTINCT CHARACTER SPACES

For invariant L and sigma of character zeta, omega_sigma has character
zeta*delta=1. Thus naturality shows that each translate of C gives the
same fixed-threefold obstruction pairing. Consequently NL_E is a
nonzero constant times 3*tau(kL*sigma).

For the external degree-six test B=x2*x3^3*w, B has character zeta,
whereas eta_B=Res(B*Omega/Fb^2) has character zeta*delta=1. If L is
invariant, omega_L has character delta=zeta^2. The Kodaira-Spencer
class rho_B has character zeta, so the tensor

  rho_B contraction omega_L

is invariant. Its integral over C, gC, and g^2C is therefore the same.
The ambient-B obstruction paired with omega_L is 3*c0*tau(BL).

This argument uses intrinsic equivariance and does not assume that the
non-invariant Artinian presentation A itself carries a scalar g-action.
The invariant surface obstruction space has dimension seven. The
external-B obstruction is in a DIFFERENT character component of
dimension eight, paired against the eight-dimensional invariant cubic
space modulo h. These two spaces are never identified.

The recorded ranks now imply that there is an invariant cubic L with

  NL_E(L)=0,  tau(BL)!=0.

Indeed the row tau(BL) does not lie in the row space of the rank-seven
matrix; equivalently it is nonzero on its kernel. That kernel in the
nine-dimensional cubic space has dimension two. The rescaling vector h
lies in both kernels because h=0 in A. Hence L is nonzero modulo h,
leaving a genuine one-dimensional tangent direction of surface motion.

5. INTEGRATE THE CLASS, NOT THE ORIGINAL SMALL CURVE

Let Bpar be the smooth irreducible open of ALL invariant sextic
polynomials (modulo harmless equation rescaling), and let U parameterize
smooth invariant cubic sections D of their threefolds. Around the seed,
choose a small simply connected analytic neighborhood and transport
lambda=[E] flatly. It stays g-invariant because the automorphism is
defined on the whole family and commutes with Gauss-Manin transport.

The condition that lambda has type (1,1) is exactly vanishing of its
projection into the rank-seven bundle H^{0,2}(D)^g. Its derivative in
the cubic-section directions is NL_E, which is surjective. The
holomorphic implicit function theorem therefore gives a smooth local
Hodge locus Z, with Z -> Bpar a submersion whose fibers have dimension
9-1-7=1. In particular the selected vector L integrates to an actual
analytic curve in a fixed-threefold fiber of Z.

By Lefschetz (1,1), lambda is the Chern class of a line bundle on each
D in Z. Since H^1(O_D)=0, the line bundle is unique up to isomorphism.
After shrinking to a contractible analytic neighborhood these line
bundles form a holomorphic relative line bundle. For m sufficiently
large, Serre vanishing, cohomology/base change and Bertini give a
projective bundle of sections of L_lambda(m), with a nonempty open of
smooth effective curves. This is an actual analytic family of curves
Gamma, and its projection to Z is smooth and surjective. A tangent L
therefore lifts to a genuine infinitesimal motion of a smooth Gamma.

The original C need not deform along L, and no unobstructedness of its
Hilbert point is asserted. High twisting is what supplies effective
smooth curves representing the transported class.

Optional explicit bound at the seed: E is a disjoint union and
O_E(E+4H) is the direct sum of O_{g^j C}(2). The exact sequence

  0 -> O_D(4) -> O_D(E+4H) -> direct_sum_j O_{g^j C}(2) -> 0

and H^1(O_D(4))=H^1(O_C(2))=0 show H^1(O_D(E+4H))=0. Both the
left-hand line bundle and the restrictions on E are generated by
sections, so O_D(E+4H) is basepoint free. It has intersection 12 with
each component of E and positive intersection with every other
irreducible curve, since E is effective and H is ample. Its square is
-36+8*18+16*9=252. Nakai's criterion makes it ample, so a general
smooth member is connected. Thus m=4 can be used on a sufficiently
small neighborhood, although no fixed bound is needed in the proof.

6. WHY THE ACTUAL ABEL-JACOBI DERIVATIVE IS NONZERO

Keep T fixed and take a curve Gamma_s in the above relative linear
systems with section tangent L. The cycles Gamma_s-Gamma_0 are
homologous to zero. Let nu(s) be their Abel-Jacobi image. Sweeping Gamma
along a short path gives its bounding three-chain, so differentiation
of the defining period integral gives

  <d nu(L),eta> = integral_Gamma (v contraction eta)|Gamma,

where v is the normal field of Gamma in T. This derivation requires no
universal-moduli or sufficiently-ample-surface theorem.

Use the conormal sequence

  0 -> N_{D/T}^* tensor Omega_D^1
    -> Omega_T^2|D -> K_D -> 0.

Since H^1(K_D)=0, eta|D has a lift eta_tilde in the H^1 of the left
term. Locally the inclusion is dh wedge beta. Restricting its contraction
by v to Gamma keeps exactly dh(v)*beta; the other term has dh along
Gamma and vanishes. As dh(v)=-L, the derivative is, up to a fixed sign,

  integral_D [Gamma] cup (L*eta_tilde).

For eta=eta_B, contraction with the nowhere-vanishing holomorphic
three-form identifies eta_B with the Kodaira-Spencer class of Fb+eps B.
The surface deformation (Fb+eps B,h) supplies a lift rho_B in H^1(T_D),
and its contraction with the three-form is a valid eta_tilde. The local
tensor identity then identifies L*eta_tilde with plus or minus
rho_B contraction omega_L. Therefore

  <d nu(L),eta_B>
    = c1 * <ambient-B obstruction of [Gamma], omega_L>.

Since [Gamma]=lambda+mH and O_D(1) extends over the ambient deformation,
the mH contribution to this obstruction is zero. By Sections 3–4,

  <d nu(L),eta_B> = c2 * 3 * tau(BL),  c2!=0.

This is nonzero for the chosen L. It is the derivative of an actual
curve family, tested against an actual invariant H^{2,1} class.

The choice of conormal lift does not affect this answer: two lifts
differ by a boundary from H^0(K_D); its pairing with lambda is precisely
NL_lambda(L) evaluated on that section, and hence vanishes.

If one prefers the primitive-class formulation used in Voisin's
normal-function treatment, replace lambda by lambda0=E-2H.
Indeed H_T^3=3, deg C=6, deg E=18, i_*E=6H_T^2 and i_*H=3H_T^2,
so i_*lambda0=0. Also lambda0 is primitive on D and lambda0^2=-72.
The hyperplane subtraction changes neither NL nor the derivative.
Take a higher positive twist to represent lambda0 by effective curves.

7. ALGEBRAIZE AND SPREAD THE NONZERO FAMILY

The passage from an analytic Hodge-class germ to an algebraic family
requires the following argument.

All curves in the local family have the same Hilbert polynomial with
respect to a fixed projective embedding: their degree and arithmetic
genus are determined by the flat class lambda+mH. Hence the analytic
family maps into ONE finite-type relative flag Hilbert scheme H
parameterizing (T,D,Gamma). Its projection to Bpar contains an analytic
open because Z -> Bpar is a submersion.

Let W be the irreducible Zariski closure of the image of a connected
analytic germ of this family in H. Then W -> Bpar is dominant. Every
nonempty analytic open of the germ has the same Zariski closure W
(identity theorem). The nonzero vertical derivative condition is open
in that germ. It therefore meets the nonempty algebraic open where W
is smooth over Bpar. At such a point, the vertical tangent of W contains
a vector on which the averaged Abel-Jacobi derivative is nonzero.

Take a projective compactification/resolution of W over Bpar. Cut it by
sufficiently general relative ample hypersurfaces to relative dimension
one, choosing their tangent hyperplanes to retain a vertical direction
outside the kernel of that derivative. This is ordinary relative
Bertini in characteristic zero, with a prescribed open tangent
condition at one smooth point. After shrinking the base and normalizing,
the resulting parameter family Lambda -> Bpar' is smooth and projective.
It may be disconnected; alternatively use its Stein factorization and a
finite etale base change. The universal curve restricts over the dense
open originally in H, and its closure supplies a codimension-two cycle
Gamma on Lambda times_{Bpar'} T.

The resulting correspondence induces a morphism of rational variations

  R^1 p_{Lambda*} Q(-1) -> R^3 p_{T*} Q.

Its averaged component is nonzero, because its Abel-Jacobi differential
still pairs nontrivially with the invariant class eta_B. This supplies
the genuine nonzero subvariation used in the next Higgs step.

An alternative algebraicity input is Cattani–Deligne–Kaplan, Theorem 1.1
and Corollary 1.2: the relevant integral Hodge-class germ is algebraic.
Together with the relative Picard/Hilbert construction, this gives the
same algebraic family. The Hilbert-closure argument above already
supplies the needed repair, so the stronger CDK theorem is optional.
No Hodge conjecture is assumed: the only cycle-existence assertion at
this point is Lefschetz (1,1) for divisor classes on surfaces.
```

### Part III: supported projectors

```text
PART III. HIGGS IRREDUCIBILITY AND SUPPORTED PROJECTORS
======================================================

The hypotheses of this part are now established: Part I.3 supplies the
scalar Higgs equations, and Part II supplies the nonzero algebraic
cylinder correspondence over a dense open of the full parameter base.

1. THE PRECISE HIGGS IRREDUCIBILITY LEMMA

Let B be a smooth connected complex algebraic variety and V a polarized
rational variation of Hodge structure of weight three whose only Hodge
types are (2,1) and (1,2). Put E=F^2(V tensor O_B). Polarization identifies
V_C/F^2 with E^vee, and the Higgs field has the form

  theta: T_B -> Hom(E,E^vee),

with symmetric forms theta_v. Consider the bundle map

  L: End(E) -> Hom(T_B, Hom(E,E^vee)),
  L(P)(v) = P^t theta_v - theta_v P.

Scalar endomorphisms are in its kernel everywhere. If at one point its
kernel consists exactly of scalars, the maximal-rank locus B_good is a
nonempty open set. In the present geometric situation the bundles and
Higgs map are algebraic, so this may be taken Zariski open. Analytic
openness together with a proper analytic bad locus would also suffice
to meet every nonempty Zariski open of the connected base.

Let B' -> U be a finite etale cover of a dense open U in B, and work on
one connected component of B'. Suppose W is a rational subvariation of
the pullback of V. A sub-Hodge structure of a polarized Hodge structure
has nondegenerate restricted polarization: its positive Hodge metric is
the restriction of the ambient positive metric. Consequently W has a
rational orthogonal complement, and the projection e onto W is flat,
self-adjoint for the polarization, and of Hodge type (0,0).

Choose a point of B' above U intersect B_good. If P is e on E there, then
self-adjointness makes its action on E^vee equal to P^t. Flatness implies
commutation with the Higgs field, so

  P^t theta_v = theta_v P

for all tangent directions. Etaleness is relevant here: tangent vectors
on B' supply all tangent vectors on B. Therefore P=c I. As e is an
idempotent, c is 0 or 1. Since e is rational, its action on the conjugate
Hodge summand is correspondingly 0 or I. Thus e is 0 or I on the whole
fiber. Flatness keeps its rank constant, proving W=0 or W=V everywhere
on the connected component.

This proves irreducibility as a variation even after the finite covers
used to spread a family of parameter curves. No assertion that an
arbitrary rational local subsystem is automatically a subvariation is
needed; the image of an algebraic correspondence is a subvariation.

For the invariant weighted sextics, E is the character-one degree-six
Fermat Jacobian component, of dimension 33, and the invariant tangent
directions are the 35 character-zero degree-six classes. The actual
Higgs forms are, up to the conventional nonzero residue normalization,
the socle triple-product forms. Thus the finite equations in the project
are exactly the equations of this lemma, rather than a dimension count
used as a substitute for the Higgs comparison.

2. FROM A NONZERO CURVE CORRESPONDENCE TO THE WHOLE INVARIANT SECTOR

Suppose, after the allowed base change and shrinking, that there is a
smooth projective family of parameter curves Lambda and an algebraic
relative correspondence Gamma of codimension two from Lambda to the
family of threefolds T. Averaging Gamma by the order-three action gives
a morphism of rational variations

  R^1(Lambda/B')_* Q(-1) -> V.

Its image has constant rank and is a rational subvariation: the cycle
class gives a morphism of local systems and of Hodge filtrations. A
nonzero invariant Abel–Jacobi derivative at any point makes this image
nonzero. The preceding lemma makes it equal to all of V. In each fiber,
Gamma is a two-dimensional cycle on Lambda x T, so its target image is
contained in a proper closed subset of dimension at most two. Enlarge
that subset to a divisor and take the union of its three translates.

Part II supplies the genuinely algebraic family of curves and its
nonzero invariant Abel-Jacobi derivative. Therefore the image is all V.

3. A SUPPORTED PROJECTOR, INCLUDING THE NECESSARY POLARIZATION ARGUMENT

Fix a fiber T. On each connected component of Lambda choose a point p,
and set

  pi_1 = Delta_Lambda - [p] x Lambda - Lambda x [p].

This is the Chow–Kunneth projector on H^1. Replace Gamma by
pi_g composed Gamma composed pi_1, with pi_g=(1+g+g^2)/3. It then vanishes
on H^0 and H^2 of the curve and maps H^1 onto V=H^3(T,Q)^g. Its target
support remains in the chosen g-stable divisor Z.

The cup-product polarizations on H^1(Lambda)(-1) and H^3(T) make the
transpose correspondence equal to the adjoint up to a fixed sign.
Here all of H^3(T) is primitive, because H^1(T)=0. This point avoids any
need for an unproved algebraicity statement about an inverse Lefschetz
operator.

For a surjective morphism A of polarized Hodge structures, AA^dagger is
invertible on the target. Indeed the positive Hodge metrics make

  <AA^dagger y,y> = <A^dagger y,A^dagger y>,

and A^dagger is injective. Thus M=Gamma composed transpose(Gamma) is
invertible on V, whether its comparison with AA^dagger carries a plus
or minus sign. This positivity argument matters: the corresponding
claim for arbitrary nondegenerate bilinear forms would be false.

M vanishes on every other cohomology degree and on the noninvariant
part of H^3. Let q(t) in Q[t] be its characteristic polynomial on V.
Since M is invertible, q(0) is nonzero. Then

  p(t)=1-q(t)/q(0)

has zero constant term and p(M)|V=I. Since Gamma has target support Z,
transpose(Gamma) has source support Z, so M and all its positive powers
are represented by cycles supported on Z x Z. Hence p(M) is a rational
cycle supported on Z x Z whose action is the desired projector in every
cohomological degree. Composition uses intersection with supports, so
the support statement remains valid even when intersections have excess
dimension; it is not a claim about arbitrary moved representatives.

For the smooth weighted sextic, H^{2k}(T,Q)=Q H^k and integral_T H^3=3.
The other odd groups except H^3 vanish. Consequently the globally
defined relative cycle

  P = pi_g - sum_{k=0}^3 (1/3) pr_1^* H^{3-k} pr_2^* H^k

has exactly the same action as p(M). Poincare duality and Kunneth identify
degree-six classes on T x T with degree-preserving cohomological
endomorphisms, so equality of all these actions means equality of the
cycle classes, not merely equality on V.

4. SPECIALIZATION OF A SUPPORTED REPRESENTATIVE

Let X -> B be a smooth projective family of n-folds and P a relative
rational codimension-n correspondence. Assume its fiber class has a
representative supported on a divisor square at very general points.
In our application this holds on the open obtained in Section 2.

There is a countable collection of proper parameter spaces S_i -> B
parametrizing tuples consisting of:

  - a closed subscheme D of relative dimension n-1;
  - finitely many effective n-dimensional cycles in X_b x X_b supported
    on D x D, with positive or negative integral multiplicities;
  - a positive integer N, so that their signed sum is to represent N[P_b].

Use products of fixed-Hilbert-polynomial relative Hilbert schemes for
the components. Taking tuples with integral multiplicities avoids any
need to realize an arbitrary effective cycle as the fundamental cycle
of a single nonreduced subscheme. The flag condition that each component
lies in D x D is closed. Each such parameter space is proper over B,
and there are countably many polynomials, tuples, and multiplicities.

The universal flat cycles define a locally constant section of the
pulled-back cohomology local system. Its difference from N[P] therefore
vanishes on a union of connected components. This can also be seen by
restricting to normalized algebraic curves in a parameter component:
the ambient family over such a smooth curve is smooth, and the class
of a flat algebraic cycle has constant transported fiber class.

Discard components where that equality does not hold. The remaining
proper components have closed images in B. Exclude all images which
are proper closed subsets. There are countably many; a nonempty open
in the irreducible complex base is not their union. Choose b outside
them where a supported representative exists. The component carrying
that representative cannot have proper image and hence maps onto B.

This single proper component S_0 -> B has universal supported cycles
with the same fixed cohomological equality on every fiber. For each
b' choose a point above b'. The fixed Hilbert polynomial of D has
degree n-1, so its support cannot become all of X_{b'}; the incidence
condition preserves support on its square. Divide by N. This proves
the assertion for every smooth member.

No assertion that an arbitrary rational Hodge class extends as an
algebraic cycle is being used. P was an algebraic relative cycle from
the start, and the issue was the existence of a representative with
smaller support. Proper Hilbert parameter spaces preserve that specific
property once it holds at very general points.

5. RELATIVE SUPPORT OVER THE ACTUAL AFFINE PENCIL

Pull back the single S_0 above to any smooth affine curve U mapping to
B, in particular to the actual pencil of weighted quotients. The
proper map S_0 x_B U -> U is surjective, even if this pencil is entirely
inside the complement of the first good open. Choose a component
dominating U and a closed point of its generic fiber. Its residue field
is finite over C(U); normalize and shrink U. In characteristic zero this
gives a finite etale cover U' -> U with a map U' -> S_0.

Thus over U' there is a relative divisor D' and relative rational cycle
Z' supported on D' x_{U'} D', with every fiber class equal to the desired
projector. Push Z' through the finite map of relative products and divide
by its degree. The descended relative correspondence Z has the same
fiberwise action. Its support lies in D x_U D, where D is the finite
image of D'; D has relative dimension at most two and is proper in the
total threefold family T -> U.

Relative correspondences act on Rp_*Q and hence preserve the Leray
filtration on H^4(T,Q). On its graded pieces their actions are induced
by the corresponding maps of local systems R^j p_*Q. For an affine
complex curve, every local system has H^i=0 for i>1 (the curve has the
homotopy type of a finite one-dimensional CW complex). Hence

  0 -> H^1(U,R^3p_*Q) -> H^4(T,Q) -> H^0(U,R^4p_*Q) -> 0,
  L^2 H^4(T,Q)=0.

On H^1(U,V), the associated graded action of Z is the identity. Since
there is no next Leray step, its action on this subgroup of H^4(T,Q) is
exactly the identity. The action's image is supported on D by the target
support of Z. Therefore every class in H^1(U,V) vanishes on T minus D.

This is the reason fiberwise projector identities suffice here. In a
higher-dimensional base, an uncontrolled higher Leray piece could remain;
it is absent for the affine-curve base used in the proof.
```

### Part IV: the protected pencil and certificate

```text
PART IV. THE PROTECTED PENCIL AND THE EXACT ALGEBRAIC ENDPOINT
===========================================================

Parts I-III have proved the following geometric result, used as (G):

(G) For every smooth invariant sextic T in P(1,1,1,1,2), with action
    g_T=diag(zeta^2,zeta^2,zeta,1;1), the cohomological projector onto
    H^3(T,Q)^{g_T} is represented by a rational algebraic correspondence
    supported on Z x Z for a proper divisor Z in T. Over any smooth
    curve mapping to this family, after shrinking the curve, there is
    a relative correspondence with divisor support whose action on
    R^3 is the invariant projector.

The relative assertion is over the shrunken original curve: the finite
cover used to construct it has already been removed by normalized
trace in Part III.5. It applies even when that curve lies outside the
first open where the moving curves were constructed.

1. Exact protected data and smoothness
-------------------------------------

Use projective coordinates

  Z = (Z0,...,Z5) = (X0,X1,X2,Y0,Y1,Y2),

and set

  F = sum_{i=0}^2 (Xi^6 + Yi^6)
      + (X0^3 X1 Y0 Y1 + X1^3 X2 Y1 Y2 + X2^3 X0 Y2 Y0)/2,

  A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2.

Thus deg F = 6 and deg A = 12. Let X = V(F) in P^5, let

  Omega = contraction_{sum Zi partial_Zi}(dZ0 wedge ... wedge dZ5),
  alpha = Res_X(A Omega/F^3) in H^4(X,C).

The hypersurface X is smooth. Indeed, suppose a nonzero point of the affine
cone were critical and let M > 0 be the maximum modulus of its six
coordinates. If |Xi| = M, the equation partial_Xi F = 0 gives

  6 M^5 <= (3+1) M^5/2 = 2 M^5.

Each Xi occurs with exponents 3 and 1 in two mixed monomials. If instead
|Yi| = M, its two mixed exponents are both 1, and

  6 M^5 <= (1+1) M^5/2 = M^5.

Either inequality is impossible. This proves smoothness without a
computer algebra calculation.

F is irreducible over C. A factorization into two positive-degree
homogeneous factors would give intersecting hypersurfaces in P^5, and
their intersection would be singular for F by the product rule.
Repeated factors also contradict smoothness. Dehomogenization at Z0=1
therefore gives an irreducible polynomial f.

Write the affine coordinates as

  (x0,x1,x2,x3,x4) = (X1,X2,Y0,Y1,Y2)/X0.

Then

  f = 1 + sum_{i=0}^4 xi^6
      + (x0 x2 x3 + x0^3 x1 x3 x4 + x1^3 x2 x4)/2,
  a = x0^2 x1^3 x2^2 x3^2 x4.

Let R=C[x0,...,x4], K=Frac(R/(f)), and

  g = partial_0 f
    = 6 x0^5 + (x2 x3 + 3 x0^2 x1 x3 x4)/2.

Since g is a nonzero polynomial of degree 5 and f has degree 6, f does
not divide g. Thus g is a nonzero element of K. The differential relation

  g dx0 + sum_{j=1}^4 f_j dxj = 0,  where f_j=partial_j f,

shows that dx1,...,dx4 form a K-basis of Omega^1_{K/C}.

2. The symmetries, including the determinant character
------------------------------------------------------

Let zeta be a primitive cube root of unity. Define

  beta(X0,X1,X2,Y0,Y1,Y2) = (X0,X1,-X2,Y0,Y1,-Y2),
  gamma = diag(zeta^2,zeta^2,1,zeta,1,1).

Both transformations fix F. For beta the three mixed monomials have
total degrees 0,2,4 in X2,Y2. For gamma their weights are respectively
9,6,3, all divisible by 3. All pure sixth powers are fixed as well.

A is beta-invariant, since its X2,Y2 exponents add to 4. Its gamma-weight
is 2*2+2*2+2*1=10, hence gamma^*A=zeta A. Crucially,

  det(beta)=1,   det(gamma)=zeta^5=zeta^2,
  gamma^*Omega=zeta^2 Omega.

Consequently the rational differential A Omega/F^3 and its full residue
class alpha are invariant under beta and gamma. Invariance of A alone
under gamma would be false; the determinant character is essential.

3. Resolving the protected pencil and identifying the quotient
-------------------------------------------------------------

Put u=X2, v=Y2 and consider the pencil lambda=v/u. Its base locus is

  S = X intersect {u=v=0}.

This is a smooth surface. At u=v=0 both partial_u F and partial_v F
vanish; hence a singular point of S, computed in its P^3 of remaining
coordinates, would be singular on X. The two equations u,v cut out S
as a smooth codimension-two complete intersection on X.

The blowup of this smooth center resolves the pencil:

  pi : Xtilde=Bl_S X -> X,
  p  : Xtilde -> P^1.

The incidence description of the graph is valid because u,v form a
regular sequence. Xtilde is smooth. A smooth fibre is the sextic
threefold V_lambda=X intersect {v=lambda u} in P^4. The apparent blowup
on that fibre is along the Cartier divisor S and is an isomorphism.

Generic smoothness and properness allow us to remove finitely many
parameters so that p is smooth projective. Also remove infinity and the
six roots of 1+lambda^6. Denote the resulting nonempty connected affine
curve by U; it may be shrunk further later.

On each fibre beta sends u to -u and fixes the other four coordinates

  s=(s0,s1,s2,s3)=(X0,X1,Y0,Y1).

The quotient has weight-two coordinate w=u^2. Its equation in
P(1,1,1,1,2) is

  G_lambda = sum_{i=0}^3 si^6 + (1+lambda^6)w^3
      + (s0^3 s1 s2 s3 + lambda s1^3 s3 w
                              + lambda s0 s2 w^2)/2.

This follows by substituting v=lambda u into the protected F. In
particular the last two mixed terms give respectively u^2 and u^4,
not another choice of powers.

G_lambda avoids the unique singular vertex of the weighted projective
space, because 1+lambda^6 is nonzero. It is quasismooth: a nonzero
critical point (s,w) of its affine cone, lifted by any square root u of
w, would be a critical point of G_lambda(s,u^2), since

  partial_si G_lambda(s,u^2) = partial_si G_lambda(s,w),
  partial_u G_lambda(s,u^2) = 2u partial_w G_lambda(s,w).

That would contradict smoothness of V_lambda. Away from the weighted
vertex quasismoothness is ordinary smoothness. Thus the quotients form
a smooth projective family p_T:Tcal->U with a finite double quotient

  q:Xtilde_U -> Tcal.

The quotient is branched. No unramified-cover assertion is needed.
The action gamma fixes lambda and descends to

  g_T=diag(zeta^2,zeta^2,zeta,1;1).

If the invariant parameter space is written using a monic w^3 term,
divide G_lambda by 1+lambda^6. This is a regular coefficient map over U
and needs no extraction of roots or additional base change.

4. Quotient cohomology and the full Leray class
---------------------------------------------

For a finite group G acting on a complex algebraic variety M, with
quotient q:M->M/G, rational cohomology satisfies

  q^*:H^*(M/G,Q) -> H^*(M,Q)^G  is an isomorphism.

Freeness of the action is unnecessary. One proof uses proper base
change: the fibres of q are finite, so R^i q_*Q=0 for i>0. The invariant
subsheaf (q_*Q)^G is Q, because each fibre is a single orbit. The
averaging idempotent over Q makes invariants an exact direct summand.
Taking cohomology proves the assertion. Chenevert, Theorem 3.1.3,
gives the corresponding sheaf-theoretic isotypic decomposition [R6].

Apply this to the total space over U. Since pi^*alpha is beta-invariant,
there is a unique alpha' in H^4(Tcal,C) such that q^*alpha'=pi^*alpha.
The commuting gamma action and injectivity of q^* make alpha'
g_T-invariant.

For a smooth fibre T_lambda one has

  H^4(T_lambda,Q) = Q h_lambda^2,

where h=c1(O(1)). This can be deduced here without weighted weak
Lefschetz: the ordinary sextic V_lambda in P^4 has H^2=Q H by weak
Lefschetz, and H^4=Q H^2 by Poincare duality. Its hyperplane class is
beta-invariant. Quotient cohomology gives the statement for T_lambda.
The sheaf O(1) is an actual line bundle off the weighted vertex and
therefore on Tcal; its pullback is O_{V_lambda}(1). In particular h^2
is a global nonzero lift of the unique fibrewise H^4 class. One can
check nonvanishing by integral_{T_lambda} h^3=6/2=3.

The affine curve U has the homotopy type of a one-dimensional CW
complex. Hence H^r(U,L)=0 for r>=2 for every local system L. The Leray
spectral sequence therefore gives the exact sequence

  0 -> H^1(U,R^3 p_{T*}C) -> H^4(Tcal,C)
       -> H^0(U,R^4 p_{T*}C) -> 0.

The last term is C h^2, globally split by the indicated h^2. Thus

  alpha' = c0 h^2 + alpha'',
  alpha'' in H^1(U,(R^3 p_{T*}C)^{g_T}).

Here the invariant summand commutes with H^1 by the averaging
idempotent. This is a statement about the whole class alpha', not a
statement in one associated Hodge-graded quotient.

Apply (G), shrinking U as necessary. Its relative correspondence
preserves the Leray filtration, since it gives an endomorphism of the
derived direct image over U. In degree 4 the Leray piece L^1 is
H^1(U,R^3), and L^2=0. Consequently the correspondence acts as the
identity on alpha'' itself: there is no further filtration term in
which an error could lie. Its target support is contained in a relative
divisor D, so alpha'' restricts to zero on Tcal minus D.

The class h^2 is also supported on a divisor: a nonzero weight-one
coordinate section, for example s0, trivializes O(1) on its nonvanishing
set, where h and hence h^2 vanish. It follows that alpha' vanishes on
the complement of a proper divisor in Tcal.

Pull that support back through finite q. Take its closure in Xtilde
and add the omitted fibres and the exceptional divisor of pi. Each
component has dimension at most 3. Its proper image in the fourfold
X is therefore a proper closed subset. Outside this image pi is an
isomorphism and alpha vanishes. Enlarge the image to a proper divisor
Z_X on X, if necessary, by choosing a nonzero homogeneous polynomial
in its ideal modulo F. We have proved

  alpha|_{X minus Z_X}=0.                                      (4.1)

No assertion that a finite map is an etale cover and no unproved
splitting of the total Leray filtration are used here.

5. Exact local residue after reducing the pole order
---------------------------------------------------

On the ambient affine open g!=0 define

  D_t = g^{-1} partial_0,       b=a/g,
  nu = dx1 wedge dx2 wedge dx3 wedge dx4.

These definitions are made before imposing f=0. They satisfy D_t f=1
and, for every rational H,

  dH wedge nu = (D_t H) df wedge nu.

The dehomogenization of A Omega/F^3 is

  omega = a dx0 wedge nu/f^3 = b df wedge nu/f^3.

Let

  psi = [-b/(2f^2) - (D_t b)/(2f)] nu.

A direct differentiation gives

  dpsi = [b/f^3 - (D_t^2 b)/(2f)] df wedge nu,

and hence

  omega-dpsi = c' (df/f) wedge nu,   c'=(D_t^2 b)/2.             (5.1)

Write g_0=partial_0 g and g_00=partial_0^2 g. Expanding c' gives

  c' = (1/2)[ a_00/g^3
               -(3a_0 g_0+a g_00)/g^4 + 3a g_0^2/g^5 ].

This coefficient is regular along f=0 on g!=0. The Poincare residue
of (5.1) is

  rho = (c/g) nu,
  c = (1/2)[ a_00/g^2
              -(3a_0 g_0+a g_00)/g^3 + 3a g_0^2/g^4 ],        (5.2)

with all coefficients now interpreted in K. This is precisely the
affine source four-form of the protected exactness target.

The residue is compatible with restriction and unchanged by adding
the differential of a form with the displayed lower pole order. This
also follows directly from the logarithmic de Rham definition of the
residue; the explicit (5.1) is enough here. Thus the class of rho on
any such open subset of X is the restriction of the full alpha.

The normal derivation D_t DOES NOT descend to K, since D_t f=1.
Equation (5.1) alone must not be claimed to prove rho exact. It proves
the residue identification; actual exactness follows from (4.1) and
algebraic de Rham comparison in the next step.

6. From divisor support to the rational primitive
------------------------------------------------

Choose a nonzero h in R/(f) vanishing on the closed support Z_X in the
affine chart; if that intersection is empty take h=1. Because R/(f)
is a domain and h,g are nonzero, the principal open

  W = D(hg) in Spec(R/(f))

is nonempty. It is a smooth affine fourfold, lies outside Z_X, and the
form rho is regular on it. By (4.1)-(5.2) its complex cohomology class
is zero. All four-forms on W are closed, since W has dimension four.

Grothendieck's algebraic de Rham theorem for smooth affine complex
varieties identifies H^4(W,C) with the degree-four cohomology of the
complex of global regular algebraic differential forms [R5, Theorem 1
and equation (4)]. Consequently there is

  eta_W in Gamma(W,Omega_W^3),   d eta_W=rho.

Localization commutes with Kähler differentials, exterior powers, and
their exterior differential. Passing to the function field gives

  eta in Omega^3_{K/C},   d eta=rho.                           (6.1)

This proves the exact affine-residue-form existence conclusion. There
is no quantitative bound on the poles of eta in this argument and
none is needed for the existential protected target.

7. Explicit return to an ordinary polynomial certificate
-------------------------------------------------------

This section proves an elementary bridge from (6.1) to the final
polynomial identity, including the denominator legality and degrees.
It does not invoke the prescribed-support Hodge-theoretic theorem.

Because dx1,...,dx4 is a K-basis, write

  eta = sum_{j=1}^4 (-1)^{j-1} u_j
           dx1 wedge ... wedge omit(dxj) wedge ... wedge dx4,
  u_j in K.

The tangent derivations on the hypersurface are induced by

  E_j = partial_j - (f_j/g) partial_0,   1<=j<=4.

They satisfy E_j f=0, and (6.1) is equivalent to

  sum_j E_j u_j = c'|_{f=0}.                                  (7.1)

Let L=R_{(f)}, the ring of rational functions regular at the generic
point of the prime divisor f=0. Its residue field is K. Choose any
lifts utilde_j in L of the four u_j. All denominators of these lifts
are prime to f. The derivations partial_i, D_t, and E_j preserve L;
E_j preserves its ideal fL and induces the tangent derivation on K.
Thus (7.1) says exactly

  c' - sum_j E_j utilde_j in fL.                              (7.2)

Define the following five rational affine components in L:

  U_0 = b/2 + (f/2)D_t b + f sum_{j=1}^4 f_j utilde_j,
  U_j = -fg utilde_j,                    1<=j<=4.             (7.3)

They satisfy the exact rational-function identity

  a + f div(U) - 2 sum_{i=0}^4 U_i f_i
      = f^2 g [c' - sum_{j=1}^4 E_j utilde_j].                (7.4)

Here is the full product-rule check. Pairing (7.3) with df cancels
the two sums involving utilde_j and gives

  sum_i U_i f_i = a/2 + (f/2) partial_0 b.

On taking divergence, the terms f_j g utilde_j cancel. The terms with
undifferentiated utilde_j in the remaining multiple of f also cancel,
because partial_0 f_j=partial_j g. Hence

  div(U) = partial_0 b
       + f[(1/2)partial_0(D_t b)
            + sum_j f_j partial_0 utilde_j
            - g sum_j partial_j utilde_j]
     = partial_0 b + fg[c'-sum_j E_j utilde_j].

Substitution proves (7.4). By (7.2), the right side lies in f^3 L.

Choose a common nonzero polynomial denominator d, not divisible by
f, for the five U_i, and put n_i=dU_i in R. Clearing the denominator
in (7.4) gives the polynomial

  P = a d^2 - 2d sum_i n_i f_i
          + f[d sum_i partial_i n_i - sum_i n_i partial_i d]
      in f^3 L.

Since R is a unique factorization domain and f is irreducible,
f^3 L intersect R = f^3 R. Therefore there is q in R with

  a d^2 - 2d sum_i n_i f_i
       + f[d sum_i partial_i n_i - sum_i n_i partial_i d]
       = f^3 q.                                               (7.5)

This is an ordinary certificate; no demand that q=0 is imposed.

8. Homogenization and every certificate side condition
------------------------------------------------------

For a polynomial p in five affine variables and r>=deg p, denote by
h_r(p) its homogenization to degree r in Z0,...,Z5, using Z0 as the
homogenizing variable and xi=Z_{i+1}/Z0. Homogenize the zero
polynomial as zero at any required nonnegative degree.

Choose an integer

  m >= max(3, deg d, max_{i:n_i!=0}(deg n_i-7)).

Set

  D   = h_m(d),
  N_0 = 0,
  N_{i+1} = h_{m+7}(n_i),                0<=i<=4.

The affine index 0 corresponds to the projective index 1; setting
projective N_0=0 causes no conflict with the nonzero affine U_0.

Each term on the left of (7.5) has degree at most 2m+12: use
deg a<=12, deg f=6, deg f_i<=5, deg d<=m, and deg n_i<=m+7.
If q is nonzero, deg(f^3 q)=18+deg q, so

  deg q <= 2m-6.

The choice m>=3 makes this homogenization degree nonnegative. Put

  Q = h_{2m-6}(q).

The two sides of the following identity are homogeneous of degree
2m+12 and dehomogenize to (7.5):

  A D^2 - 2D sum_{i=0}^5 N_i F_i
       + F[D sum_{i=0}^5 partial_i N_i
                         - sum_{i=0}^5 N_i partial_i D]
       = F^3 Q.                                               (8.1)

Dehomogenization is injective on the homogeneous piece of a fixed
degree, so (8.1) holds identically. The numerator N_0 contributes
zero to both sums, and the other terms have exactly the required
homogeneous degrees.

Finally D is nonzero because d is nonzero. If F divided D, then f
would divide d after dehomogenization, contrary to its construction.
Since F is irreducible, this proves gcd(D,F)=1. Each N_i belongs to
the homogeneous piece of degree m+7, and D has degree m. Thus every
side condition of the ordinary q=2 certificate is satisfied.

The proof yields existence of a certificate; it does not expand a
numerical coefficient list for D or N_i. It equally proves the
rational-form exactness used as the missing geometric input. A
machine-checked Lean replacement remains a separate formalization
task; neither its existence nor successful compilation is claimed.
```

### Conclusion and formalization status

```text
CONCLUSION AND THE REMAINING FORMALIZATION TASK
==============================================

The chain is complete at the level of classical mathematics:

  exact finite ranks
  -> genuine moving algebraic curves with nonzero invariant Abel-Jacobi
  -> the whole invariant H^3, by the scalar Higgs equations
  -> divisor-supported projectors, on every smooth member
  -> support of the full protected fourfold residue class
  -> the literal rational primitive eta with d eta=rho
  -> the ordinary homogeneous q=2 certificate.

The proof uses no Hodge conjecture. The algebraicity needed in the
moving-class step is Lefschetz (1,1) on surfaces plus the relative
Hilbert construction. The finite ranks are now checked, rather than
left as unexecuted project inputs. All intermediary existence steps
have been given as ordinary mathematical arguments.

The characteristic-zero seed has r^3=2. The residue r=57 occurs only
in F_109. It must not be replaced by the literal complex number 57.
The older Lean continuation uses a different literal-complex seed in
some declarations; this written proof does not claim those declarations
already formalize the present seed or the classical geometric steps.

The source theorem Submission.missing_geometric_existence is therefore
still an unfilled Lean proof obligation. Replacing its sorry with an
actual checked proof requires formalizing or linking the relevant
geometric theorems. This document does not make that replacement and
no Lean compilation was attempted. It does settle the requested
mathematical existence argument and gives an explicit final algebraic
bridge, without computing the large certificate coefficient tuple.
```

### References

```text
PROJECT AND PRIMARY REFERENCES
===============================

[P1] hodge-computer/sextics, Chapter 3D, Moving cycles along Hodge loci.
     Exact seed, finite maps, and the strategy reconstructed here.
https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/docs/03d-hodge-loci.md

[P2] Same revision, scripts/verify-hodge-locus-span.py.
     Exact finite-input definitions and arithmetic.
https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/scripts/verify-hodge-locus-span.py

[P3] Same revision, Chapter 3, Geometric support, especially Section 3.6.
https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/docs/03-geometric-support.md

[P4] Same revision, Chapter 1, Certificates; protected instance.
https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/docs/01-certificates.md
https://github.com/hodge-computer/sextics/blob/520a2a29c40cc40e1df2b1c41980552f25d08e65/data/cycle-q2/instance.rec

[R1] Claire Voisin, The Griffiths group of a general Calabi-Yau threefold
     is not finitely generated, Duke Mathematical Journal 102 (2000),
     151-186. Section 2, Lemma 2 and Lemma 7: Hodge-locus tangent space
     and the vertical Abel-Jacobi derivative. The intrinsic proof in
     Part II establishes the formula for these particular cubic
     sections, so no unverified sufficiently-ample-surface hypothesis
     is imported from the paper's global universal-moduli setup.
https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf

[R2] Claire Voisin, Sur les zero-cycles de certaines hypersurfaces
     munies d'un automorphisme, Annali SNS Pisa IV 19 (1992), 473-492,
     Proposition 2.1 and Section 2. Historical moving-Hodge-class
     strategy in a related involution setting; the present weighted
     order-three adaptation is proved in Parts I-III.
https://www.numdam.org/item/ASNSP_1992_4_19_4_473_0.pdf

[R3] Igor Dolgachev, Weighted projective varieties (1982).
     Sections 3.2, 3.4, and 4.2-4.3: vanishing, graded section rings,
     weighted weak Lefschetz and residue/Jacobian-ring descriptions.
https://sites.lsa.umich.edu/idolga-new/wp-content/uploads/sites/1467/2024/08/weighted82.pdf

[R4] Pierre Deligne, Theorie de Hodge II, Publications mathematiques
     de l'IHES 40 (1971), 5-57, Sections 2.1 and 4.2: polarizations,
     positivity and orthogonal decompositions of polarizable Hodge
     structures and their variations.
https://www.numdam.org/item/PMIHES_1971__40__5_0.pdf

[R5] Alexander Grothendieck, On the de Rham cohomology of algebraic
     varieties, Publications mathematiques de l'IHES 29 (1966),
     95-103, Theorem 1, equation (4), and Theorem 1'. This is the
     precise smooth-affine global-forms comparison used in Part IV.6.
https://www.numdam.org/item/PMIHES_1966__29__95_0.pdf

[R6] Gabriel Chenevert, Exponential sums, hypersurfaces with many
     symmetries and Galois representations, PhD thesis, McGill (2008),
     Theorem 3.1.3, printed pages 53-54: finite-quotient cohomological
     decomposition, including group actions with fixed points.
     Part IV.4 also gives the short constant-sheaf proof needed here.
https://www.math.mcgill.ca/goren/Students/Chenevert.thesis.pdf

[R7] The Stacks Project, Section 108.7, Properties of the Hilbert functor,
     especially Lemmas 108.7.5 and 108.7.7: closed flag conditions and
     properness for a fixed Hilbert polynomial.
https://stacks.math.columbia.edu/tag/0DM5

[R8] Eduardo Cattani, Pierre Deligne, Aroldo Kaplan, On the locus of
     Hodge classes, Journal of the AMS 8 (1995), 483-506, Theorem 1.1
     and Corollary 1.2. Optional alternative for algebraizing the
     Hodge-class germ; the proof here uses the flag-Hilbert closure
     argument in Part II.7 and does not require this alternative.
https://arxiv.org/pdf/alg-geom/9402009
```

### Appendix A: complete integer Higgs forest certificate

Each edge records its deformation direction, matrix equation, and the two
entry nodes it identifies. Node 1089 denotes zero. The exponent bases and
all 1088 retained equations are included.

```json
{"basis":[[0,0,1,3,1],[0,0,4,0,1],[0,0,4,2,0],[0,1,2,1,1],[0,1,2,3,0],[0,2,0,2,1],[0,2,0,4,0],[0,2,3,1,0],[0,3,1,0,1],[0,3,1,2,0],[0,4,2,0,0],[1,0,2,1,1],[1,0,2,3,0],[1,1,0,2,1],[1,1,0,4,0],[1,1,3,1,0],[1,2,1,0,1],[1,2,1,2,0],[1,3,2,0,0],[1,4,0,1,0],[2,0,0,2,1],[2,0,0,4,0],[2,0,3,1,0],[2,1,1,0,1],[2,1,1,2,0],[2,2,2,0,0],[2,3,0,1,0],[3,0,1,0,1],[3,0,1,2,0],[3,1,2,0,0],[3,2,0,1,0],[4,0,2,0,0],[4,1,0,1,0]],"directions":[[0,0,0,4,1],[0,0,3,1,1],[0,0,3,3,0],[0,1,1,2,1],[0,1,1,4,0],[0,1,4,1,0],[0,2,2,0,1],[0,2,2,2,0],[0,3,0,1,1],[0,3,0,3,0],[0,3,3,0,0],[0,4,1,1,0],[1,0,1,2,1],[1,0,1,4,0],[1,0,4,1,0],[1,1,2,0,1],[1,1,2,2,0],[1,2,0,1,1],[1,2,0,3,0],[1,2,3,0,0],[1,3,1,1,0],[2,0,2,0,1],[2,0,2,2,0],[2,1,0,1,1],[2,1,0,3,0],[2,1,3,0,0],[2,2,1,1,0],[2,4,0,0,0],[3,0,0,1,1],[3,0,0,3,0],[3,0,3,0,0],[3,1,1,1,0],[3,3,0,0,0],[4,0,1,1,0],[4,2,0,0,0]],"zeroNode":1089,"entryNode":"P[row,column] has node 33*row+column","edgeColumns":["directionIndex","equationRow","equationColumn","leftNode","rightNode"],"independentEquations":[[0,0,10,1023,1089],[0,0,18,957,1089],[0,0,25,825,1089],[0,0,29,594,1089],[0,0,31,330,1089],[0,1,10,1024,1089],[0,1,18,958,1089],[0,1,25,826,1089],[0,1,29,595,1089],[0,1,31,331,1089],[0,2,10,1025,1089],[0,2,18,959,1089],[0,2,25,827,1089],[0,2,29,596,1089],[0,2,31,332,1089],[0,3,10,1026,1089],[0,3,18,960,1089],[0,3,25,828,1089],[0,3,29,597,1089],[0,3,31,333,1089],[0,4,10,1027,1089],[0,4,18,961,1089],[0,4,25,829,1089],[0,4,29,598,1089],[0,4,31,334,1089],[0,5,10,1028,1089],[0,5,18,962,1089],[0,5,25,830,1089],[0,5,29,599,1089],[0,5,31,335,1089],[0,6,10,1029,1089],[0,6,18,963,1089],[0,6,25,831,1089],[0,6,29,600,1089],[0,6,31,336,1089],[0,7,10,1030,1089],[0,7,18,964,1089],[0,7,25,832,1089],[0,7,29,601,1089],[0,7,31,337,1089],[0,8,10,1031,1089],[0,8,18,965,1089],[0,8,25,833,1089],[0,8,29,602,1089],[0,8,31,338,1089],[0,9,10,1032,1089],[0,9,18,966,1089],[0,9,25,834,1089],[0,9,29,603,1089],[0,9,31,339,1089],[0,10,11,1089,1034],[0,10,12,1089,1035],[0,10,13,1089,1036],[0,10,14,1089,1037],[0,10,15,1089,1038],[0,10,16,1089,1039],[0,10,17,1089,1040],[0,10,18,967,1041],[0,10,19,1089,1042],[0,10,20,1089,1043],[0,10,21,1089,1044],[0,10,22,1089,1045],[0,10,23,1089,1046],[0,10,24,1089,1047],[0,10,25,835,1048],[0,10,26,1089,1049],[0,10,27,1089,1050],[0,10,28,1089,1051],[0,10,29,604,1052],[0,10,30,1089,1053],[0,10,31,340,1054],[0,10,32,1089,1055],[0,11,18,968,1089],[0,11,25,836,1089],[0,11,29,605,1089],[0,11,31,341,1089],[0,12,18,969,1089],[0,12,25,837,1089],[0,12,29,606,1089],[0,12,31,342,1089],[0,13,18,970,1089],[0,13,25,838,1089],[0,13,29,607,1089],[0,13,31,343,1089],[0,14,18,971,1089],[0,14,25,839,1089],[0,14,29,608,1089],[0,14,31,344,1089],[0,15,18,972,1089],[0,15,25,840,1089],[0,15,29,609,1089],[0,15,31,345,1089],[0,16,18,973,1089],[0,16,25,841,1089],[0,16,29,610,1089],[0,16,31,346,1089],[0,17,18,974,1089],[0,17,25,842,1089],[0,17,29,611,1089],[0,17,31,347,1089],[0,18,19,1089,976],[0,18,20,1089,977],[0,18,21,1089,978],[0,18,22,1089,979],[0,18,23,1089,980],[0,18,24,1089,981],[0,18,25,843,982],[0,18,26,1089,983],[0,18,27,1089,984],[0,18,28,1089,985],[0,18,29,612,986],[0,18,30,1089,987],[0,18,31,348,988],[0,18,32,1089,989],[0,19,25,844,1089],[0,19,29,613,1089],[0,19,31,349,1089],[0,20,25,845,1089],[0,20,29,614,1089],[0,20,31,350,1089],[0,21,25,846,1089],[0,21,29,615,1089],[0,21,31,351,1089],[0,22,25,847,1089],[0,22,29,616,1089],[0,22,31,352,1089],[0,23,25,848,1089],[0,23,29,617,1089],[0,23,31,353,1089],[0,24,25,849,1089],[0,24,29,618,1089],[0,24,31,354,1089],[0,25,26,1089,851],[0,25,27,1089,852],[0,25,28,1089,853],[0,25,29,619,854],[0,25,30,1089,855],[0,25,31,355,856],[0,25,32,1089,857],[0,26,29,620,1089],[0,26,31,356,1089],[0,27,29,621,1089],[0,27,31,357,1089],[0,28,29,622,1089],[0,28,31,358,1089],[0,29,30,1089,624],[0,29,31,359,625],[0,29,32,1089,626],[0,30,31,360,1089],[0,31,32,1089,362],[1,0,9,1056,1089],[1,0,17,990,1089],[1,0,19,924,1089],[1,0,24,858,1089],[1,0,26,792,1089],[1,0,28,627,1089],[1,0,30,561,1089],[1,0,32,297,1089],[1,1,9,1057,1089],[1,1,17,991,1089],[1,1,19,925,1089],[1,1,24,859,1089],[1,1,26,793,1089],[1,1,28,628,1089],[1,1,30,562,1089],[1,1,32,298,1089],[1,2,9,1058,1089],[1,2,17,992,1089],[1,2,19,926,1089],[1,2,24,860,1089],[1,2,26,794,1089],[1,2,28,629,1089],[1,2,30,563,1089],[1,2,32,299,1089],[1,3,9,1059,1089],[1,3,17,993,1089],[1,3,19,927,1089],[1,3,24,861,1089],[1,3,26,795,1089],[1,3,28,630,1089],[1,3,30,564,1089],[1,3,32,300,1089],[1,4,9,1060,1089],[1,4,17,994,1089],[1,4,19,928,1089],[1,4,24,862,1089],[1,4,26,796,1089],[1,4,28,631,1089],[1,4,30,565,1089],[1,4,32,301,1089],[1,5,9,1061,1089],[1,5,17,995,1089],[1,5,19,929,1089],[1,5,24,863,1089],[1,5,26,797,1089],[1,5,28,632,1089],[1,5,30,566,1089],[1,5,32,302,1089],[1,6,9,1062,1089],[1,6,17,996,1089],[1,6,19,930,1089],[1,6,24,864,1089],[1,6,26,798,1089],[1,6,28,633,1089],[1,6,30,567,1089],[1,6,32,303,1089],[1,7,9,1063,1089],[1,7,17,997,1089],[1,7,19,931,1089],[1,7,24,865,1089],[1,7,26,799,1089],[1,7,28,634,1089],[1,7,30,568,1089],[1,7,32,304,1089],[1,8,9,1064,1089],[1,8,17,998,1089],[1,8,19,932,1089],[1,8,24,866,1089],[1,8,26,800,1089],[1,8,28,635,1089],[1,8,30,569,1089],[1,8,32,305,1089],[1,9,10,1089,1066],[1,9,11,1089,1067],[1,9,12,1089,1068],[1,9,13,1089,1069],[1,9,14,1089,1070],[1,9,15,1089,1071],[1,9,16,1089,1072],[1,9,17,999,1073],[1,9,18,1089,1074],[1,9,19,933,1075],[1,9,20,1089,1076],[1,9,21,1089,1077],[1,9,22,1089,1078],[1,9,23,1089,1079],[1,9,24,867,1080],[1,9,25,1089,1081],[1,9,26,801,1082],[1,9,27,1089,1083],[1,9,28,636,1084],[1,9,29,1089,1085],[1,9,30,570,1086],[1,9,31,1089,1087],[1,9,32,306,1088],[1,10,17,1000,1089],[1,10,19,934,1089],[1,10,24,868,1089],[1,10,26,802,1089],[1,10,28,637,1089],[1,10,30,571,1089],[1,10,32,307,1089],[1,11,17,1001,1089],[1,11,19,935,1089],[1,11,24,869,1089],[1,11,26,803,1089],[1,11,28,638,1089],[1,11,30,572,1089],[1,11,32,308,1089],[1,12,17,1002,1089],[1,12,19,936,1089],[1,12,24,870,1089],[1,12,26,804,1089],[1,12,28,639,1089],[1,12,30,573,1089],[1,12,32,309,1089],[1,13,17,1003,1089],[1,13,19,937,1089],[1,13,24,871,1089],[1,13,26,805,1089],[1,13,28,640,1089],[1,13,30,574,1089],[1,13,32,310,1089],[1,14,17,1004,1089],[1,14,19,938,1089],[1,14,24,872,1089],[1,14,26,806,1089],[1,14,28,641,1089],[1,14,30,575,1089],[1,14,32,311,1089],[1,15,17,1005,1089],[1,15,19,939,1089],[1,15,24,873,1089],[1,15,26,807,1089],[1,15,28,642,1089],[1,15,30,576,1089],[1,15,32,312,1089],[1,16,17,1006,1089],[1,16,19,940,1089],[1,16,24,874,1089],[1,16,26,808,1089],[1,16,28,643,1089],[1,16,30,577,1089],[1,16,32,313,1089],[1,17,18,1089,1008],[1,17,19,941,1009],[1,17,20,1089,1010],[1,17,21,1089,1011],[1,17,22,1089,1012],[1,17,23,1089,1013],[1,17,24,875,1014],[1,17,25,1089,1015],[1,17,26,809,1016],[1,17,27,1089,1017],[1,17,28,644,1018],[1,17,29,1089,1019],[1,17,30,578,1020],[1,17,31,1089,1021],[1,17,32,314,1022],[1,18,19,942,1089],[1,18,24,876,1089],[1,18,26,810,1089],[1,18,28,645,1089],[1,18,30,579,1089],[1,18,32,315,1089],[1,19,20,1089,944],[1,19,21,1089,945],[1,19,22,1089,946],[1,19,23,1089,947],[1,19,24,877,948],[1,19,25,1089,949],[1,19,26,811,950],[1,19,27,1089,951],[1,19,28,646,952],[1,19,29,1089,953],[1,19,30,580,954],[1,19,31,1089,955],[1,19,32,316,956],[1,20,24,878,1089],[1,20,26,812,1089],[1,20,28,647,1089],[1,20,30,581,1089],[1,20,32,317,1089],[1,21,24,879,1089],[1,21,26,813,1089],[1,21,28,648,1089],[1,21,30,582,1089],[1,21,32,318,1089],[1,22,24,880,1089],[1,22,26,814,1089],[1,22,28,649,1089],[1,22,30,583,1089],[1,22,32,319,1089],[1,23,24,881,1089],[1,23,26,815,1089],[1,23,28,650,1089],[1,23,30,584,1089],[1,23,32,320,1089],[1,24,25,1089,883],[1,24,26,816,884],[1,24,27,1089,885],[1,24,28,651,886],[1,24,29,1089,887],[1,24,30,585,888],[1,24,31,1089,889],[1,24,32,321,890],[1,25,26,817,1089],[1,25,28,652,1089],[1,25,30,586,1089],[1,25,32,322,1089],[1,26,27,1089,819],[1,26,28,653,820],[1,26,29,1089,821],[1,26,30,587,822],[1,26,31,1089,823],[1,26,32,323,824],[1,27,28,654,1089],[1,27,30,588,1089],[1,27,32,324,1089],[1,28,29,1089,656],[1,28,30,589,657],[1,28,31,1089,658],[1,28,32,325,659],[1,29,30,590,1089],[1,29,32,326,1089],[1,30,31,1089,592],[1,30,32,327,593],[1,31,32,328,1089],[2,0,19,891,1089],[2,0,26,759,1089],[2,0,30,528,1089],[2,0,32,264,1089],[2,1,19,892,1089],[2,1,26,760,1089],[2,1,30,529,1089],[2,1,32,265,1089],[2,2,19,893,1089],[2,2,26,761,1089],[2,2,30,530,1089],[2,2,32,266,1089],[2,3,19,894,1089],[2,3,26,762,1089],[2,3,30,531,1089],[2,3,32,267,1089],[2,4,19,895,1089],[2,4,26,763,1089],[2,4,30,532,1089],[2,4,32,268,1089],[2,5,19,896,1089],[2,5,26,764,1089],[2,5,30,533,1089],[2,5,32,269,1089],[2,6,19,897,1089],[2,6,26,765,1089],[2,6,30,534,1089],[2,6,32,270,1089],[2,7,19,898,1089],[2,7,26,766,1089],[2,7,30,535,1089],[2,7,32,271,1089],[2,8,9,1089,1065],[2,8,17,1089,1073],[2,8,19,899,1075],[2,8,24,1089,1080],[2,8,26,767,1082],[2,8,28,1089,1084],[2,8,30,536,1086],[2,8,32,272,1088],[2,9,19,900,1089],[2,9,26,768,1089],[2,9,30,537,1089],[2,9,32,273,1089],[2,10,19,901,1089],[2,10,26,769,1089],[2,10,30,538,1089],[2,10,32,274,1089],[2,11,19,902,1089],[2,11,26,770,1089],[2,11,30,539,1089],[2,11,32,275,1089],[2,12,19,903,1089],[2,12,26,771,1089],[2,12,30,540,1089],[2,12,32,276,1089],[2,13,19,904,1089],[2,13,26,772,1089],[2,13,30,541,1089],[2,13,32,277,1089],[2,14,19,905,1089],[2,14,26,773,1089],[2,14,30,542,1089],[2,14,32,278,1089],[2,15,19,906,1089],[2,15,26,774,1089],[2,15,30,543,1089],[2,15,32,279,1089],[2,16,17,1089,1007],[2,16,19,907,1009],[2,16,24,1089,1014],[2,16,26,775,1016],[2,16,28,1089,1018],[2,16,30,544,1020],[2,16,32,280,1022],[2,17,19,908,1089],[2,17,26,776,1089],[2,17,30,545,1089],[2,17,32,281,1089],[2,18,19,909,1089],[2,18,26,777,1089],[2,18,30,546,1089],[2,18,32,282,1089],[2,19,20,1089,911],[2,19,21,1089,912],[2,19,22,1089,913],[2,19,23,877,914],[2,19,24,1089,915],[2,19,25,1089,916],[2,19,26,778,917],[2,19,27,646,918],[2,19,28,1089,919],[2,19,29,1089,920],[2,19,30,547,921],[2,19,31,1089,922],[2,19,32,283,923],[2,20,26,779,1089],[2,20,30,548,1089],[2,20,32,284,1089],[2,21,26,780,1089],[2,21,30,549,1089],[2,21,32,285,1089],[2,22,26,781,1089],[2,22,30,550,1089],[2,22,32,286,1089],[2,23,24,1089,882],[2,23,26,782,884],[2,23,28,1089,886],[2,23,30,551,888],[2,23,32,287,890],[2,24,26,783,1089],[2,24,30,552,1089],[2,24,32,288,1089],[2,25,26,784,1089],[2,25,30,553,1089],[2,25,32,289,1089],[2,26,27,653,786],[2,26,28,1089,787],[2,26,29,1089,788],[2,26,30,554,789],[2,26,31,1089,790],[2,26,32,290,791],[2,27,28,1089,655],[2,27,30,555,657],[2,27,32,291,659],[2,28,30,556,1089],[2,28,32,292,1089],[2,29,30,557,1089],[2,29,32,293,1089],[2,30,31,1089,559],[2,30,32,294,560],[2,31,32,295,1089],[3,0,26,726,1089],[3,0,30,495,1089],[3,0,32,231,1089],[3,1,26,727,1089],[3,1,30,496,1089],[3,1,32,232,1089],[3,2,26,728,1089],[3,2,30,497,1089],[3,2,32,233,1089],[3,3,26,729,1089],[3,3,30,498,1089],[3,3,32,234,1089],[3,4,26,730,1089],[3,4,30,499,1089],[3,4,32,235,1089],[3,5,26,731,1089],[3,5,30,500,1089],[3,5,32,236,1089],[3,6,26,732,1089],[3,6,30,501,1089],[3,6,32,237,1089],[3,7,19,1089,1075],[3,7,26,733,1082],[3,7,30,502,1086],[3,7,32,238,1088],[3,8,26,734,1089],[3,8,30,503,1089],[3,8,32,239,1089],[3,9,10,1089,1033],[3,9,18,933,1041],[3,9,25,801,1048],[3,9,26,735,1049],[3,9,29,570,1052],[3,9,30,504,1053],[3,9,31,306,1054],[3,9,32,240,1055],[3,10,24,835,1089],[3,10,26,736,1089],[3,10,28,604,1089],[3,10,30,505,1089],[3,10,32,241,1089],[3,11,26,737,1089],[3,11,30,506,1089],[3,11,32,242,1089],[3,12,26,738,1089],[3,12,30,507,1089],[3,12,32,243,1089],[3,13,26,739,1089],[3,13,30,508,1089],[3,13,32,244,1089],[3,14,26,740,1089],[3,14,30,509,1089],[3,14,32,245,1089],[3,15,19,1089,1009],[3,15,26,741,1016],[3,15,30,510,1020],[3,15,32,246,1022],[3,16,26,742,1089],[3,16,30,511,1089],[3,16,32,247,1089],[3,17,18,941,975],[3,17,25,809,982],[3,17,26,743,983],[3,17,29,578,986],[3,17,30,512,987],[3,17,31,314,988],[3,17,32,248,989],[3,18,19,1089,943],[3,18,24,843,948],[3,18,26,744,950],[3,18,28,612,952],[3,18,30,513,954],[3,18,32,249,956],[3,19,22,877,1089],[3,19,25,811,1089],[3,19,26,745,1089],[3,19,29,580,1089],[3,19,30,514,1089],[3,19,31,316,1089],[3,19,32,250,1089],[3,20,26,746,1089],[3,20,30,515,1089],[3,20,32,251,1089],[3,21,26,747,1089],[3,21,30,516,1089],[3,21,32,252,1089],[3,22,26,748,884],[3,22,30,517,888],[3,22,32,253,890],[3,23,26,749,1089],[3,23,30,518,1089],[3,23,32,254,1089],[3,24,25,816,850],[3,24,26,750,851],[3,24,29,585,854],[3,24,30,519,855],[3,24,31,321,856],[3,24,32,255,857],[3,25,26,751,818],[3,25,28,619,820],[3,25,30,520,822],[3,25,32,256,824],[3,26,27,1089,753],[3,26,28,620,754],[3,26,29,587,755],[3,26,30,521,756],[3,26,31,323,757],[3,26,32,257,758],[3,27,30,522,1089],[3,27,32,258,1089],[3,28,29,589,623],[3,28,30,523,624],[3,28,31,325,625],[3,28,32,259,626],[3,29,30,524,591],[3,29,32,260,593],[3,30,31,327,526],[3,30,32,261,527],[3,31,32,262,329],[4,18,19,1089,910],[4,18,26,1089,917],[4,18,30,1089,921],[4,18,32,1089,923],[4,25,26,1089,785],[4,25,30,1089,789],[4,25,32,1089,791],[4,29,30,1089,558],[4,29,32,1089,560],[4,31,32,1089,296],[5,0,26,660,1089],[5,0,30,429,1089],[5,0,32,165,1089],[5,1,26,661,1089],[5,1,30,430,1089],[5,1,32,166,1089],[5,2,26,662,1089],[5,2,30,431,1089],[5,2,32,167,1089],[5,3,26,663,1089],[5,3,30,432,1089],[5,3,32,168,1089],[5,4,26,664,1089],[5,4,30,433,1089],[5,4,32,169,1089],[5,5,26,665,1082],[5,5,30,434,1086],[5,5,32,170,1088],[5,6,26,666,1089],[5,6,30,435,1089],[5,6,32,171,1089],[5,7,26,667,1089],[5,7,30,436,1089],[5,7,32,172,1089],[5,8,26,668,1089],[5,8,30,437,1089],[5,8,32,173,1089],[5,9,26,669,1089],[5,9,30,438,1089],[5,9,32,174,1089],[5,10,26,670,1089],[5,10,30,439,1089],[5,10,32,175,1089],[5,11,26,671,1089],[5,11,30,440,1089],[5,11,32,176,1089],[5,12,26,672,1089],[5,12,30,441,1089],[5,12,32,177,1089],[5,13,26,673,1016],[5,13,30,442,1020],[5,13,32,178,1022],[5,14,26,674,1089],[5,14,30,443,1089],[5,14,32,179,1089],[5,15,26,675,1089],[5,15,30,444,1089],[5,15,32,180,1089],[5,16,26,676,1089],[5,16,30,445,1089],[5,16,32,181,1089],[5,17,26,677,1089],[5,17,30,446,1089],[5,17,32,182,1089],[5,18,26,678,1089],[5,18,30,447,1089],[5,18,32,183,1089],[5,19,26,679,1089],[5,19,30,448,1089],[5,19,32,184,1089],[5,20,26,680,884],[5,20,30,449,888],[5,20,32,185,890],[5,21,26,681,1089],[5,21,30,450,1089],[5,21,32,186,1089],[5,22,26,682,1089],[5,22,30,451,1089],[5,22,32,187,1089],[5,23,26,683,1089],[5,23,30,452,1089],[5,23,32,188,1089],[5,24,26,684,1089],[5,24,30,453,1089],[5,24,32,189,1089],[5,25,26,685,1089],[5,25,30,454,1089],[5,25,32,190,1089],[5,26,27,1089,687],[5,26,28,1089,688],[5,26,29,1089,689],[5,26,30,455,690],[5,26,31,1089,691],[5,26,32,191,692],[5,27,30,456,1089],[5,27,32,192,1089],[5,28,30,457,1089],[5,28,32,193,1089],[5,29,30,458,1089],[5,29,32,194,1089],[5,30,31,1089,460],[5,30,32,195,461],[5,31,32,196,1089],[6,0,25,693,1089],[6,0,29,462,1089],[6,0,30,396,1089],[6,0,31,198,1089],[6,0,32,132,1089],[6,1,25,694,1089],[6,1,29,463,1089],[6,1,30,397,1089],[6,1,31,199,1089],[6,1,32,133,1089],[6,2,25,695,1089],[6,2,29,464,1089],[6,2,30,398,1089],[6,2,31,200,1089],[6,2,32,134,1089],[6,3,25,696,1089],[6,3,29,465,1089],[6,3,30,399,1089],[6,3,31,201,1089],[6,3,32,135,1089],[6,4,25,697,1081],[6,4,29,466,1085],[6,4,30,400,1086],[6,4,31,202,1087],[6,4,32,136,1088],[6,5,25,698,1089],[6,5,29,467,1089],[6,5,30,401,1089],[6,5,31,203,1089],[6,5,32,137,1089],[6,6,25,699,1048],[6,6,29,468,1052],[6,6,30,402,1053],[6,6,31,204,1054],[6,6,32,138,1055],[6,7,25,700,1089],[6,7,29,469,1089],[6,7,30,403,1089],[6,7,31,205,1089],[6,7,32,139,1089],[6,8,25,701,1089],[6,8,29,470,1089],[6,8,30,404,1089],[6,8,31,206,1089],[6,8,32,140,1089],[6,9,25,702,1089],[6,9,29,471,1089],[6,9,30,405,1089],[6,9,31,207,1089],[6,9,32,141,1089],[6,10,25,703,1089],[6,10,29,472,1089],[6,10,30,406,1089],[6,10,31,208,1089],[6,10,32,142,1089],[6,11,25,704,1089],[6,11,29,473,1089],[6,11,30,407,1089],[6,11,31,209,1089],[6,11,32,143,1089],[6,12,25,705,1015],[6,12,29,474,1019],[6,12,30,408,1020],[6,12,31,210,1021],[6,12,32,144,1022],[6,13,25,706,1089],[6,13,29,475,1089],[6,13,30,409,1089],[6,13,31,211,1089],[6,13,32,145,1089],[6,14,25,707,982],[6,14,29,476,986],[6,14,30,410,987],[6,14,31,212,988],[6,14,32,146,989],[6,15,25,708,1089],[6,15,29,477,1089],[6,15,30,411,1089],[6,15,31,213,1089],[6,15,32,147,1089],[6,16,25,709,1089],[6,16,29,478,1089],[6,16,30,412,1089],[6,16,31,214,1089],[6,16,32,148,1089],[6,17,25,710,949],[6,17,29,479,953],[6,17,30,413,954],[6,17,31,215,955],[6,17,32,149,956],[6,18,25,711,1089],[6,18,29,480,1089],[6,18,30,414,1089],[6,18,31,216,1089],[6,18,32,150,1089],[6,19,25,712,1089],[6,19,29,481,1089],[6,19,30,415,1089],[6,19,31,217,1089],[6,19,32,151,1089],[6,20,25,713,1089],[6,20,29,482,1089],[6,20,30,416,1089],[6,20,31,218,1089],[6,20,32,152,1089],[6,21,25,714,850],[6,21,29,483,854],[6,21,30,417,855],[6,21,31,219,856],[6,21,32,153,857],[6,22,25,715,1089],[6,22,29,484,1089],[6,22,30,418,1089],[6,22,31,220,1089],[6,22,32,154,1089],[6,23,25,716,1089],[6,23,29,485,1089],[6,23,30,419,1089],[6,23,31,221,1089],[6,23,32,155,1089],[6,24,25,717,817],[6,24,26,1089,818],[6,24,29,486,821],[6,24,30,420,822],[6,24,31,222,823],[6,24,32,156,824],[6,25,26,1089,719],[6,25,27,1089,720],[6,25,28,586,721],[6,25,29,487,722],[6,25,30,421,723],[6,25,31,223,724],[6,25,32,157,725],[6,26,28,587,1089],[6,26,29,488,1089],[6,26,30,422,1089],[6,26,31,224,1089],[6,26,32,158,1089],[6,27,29,489,1089],[6,27,30,423,1089],[6,27,31,225,1089],[6,27,32,159,1089],[6,28,29,490,590],[6,28,30,424,591],[6,28,31,226,592],[6,28,32,160,593],[6,29,30,425,492],[6,29,31,227,493],[6,29,32,161,494],[6,30,31,228,427],[6,30,32,162,428],[6,31,32,163,230],[7,0,30,363,1089],[7,0,32,99,1089],[7,1,30,364,1089],[7,1,32,100,1089],[7,2,30,365,1089],[7,2,32,101,1089],[7,3,30,366,1086],[7,3,32,102,1088],[7,4,30,367,1089],[7,4,32,103,1089],[7,5,30,368,1053],[7,5,32,104,1055],[7,6,30,369,1089],[7,6,32,105,1089],[7,7,30,370,1089],[7,7,32,106,1089],[7,8,30,371,1089],[7,8,32,107,1089],[7,9,30,372,1089],[7,9,32,108,1089],[7,10,30,373,1089],[7,10,32,109,1089],[7,11,30,374,1020],[7,11,32,110,1022],[7,12,30,375,1089],[7,12,32,111,1089],[7,13,30,376,987],[7,13,32,112,989],[7,14,30,377,1089],[7,14,32,113,1089],[7,15,30,378,1089],[7,15,32,114,1089],[7,16,30,379,954],[7,16,32,115,956],[7,17,30,380,921],[7,17,32,116,923],[7,18,30,381,1089],[7,18,32,117,1089],[7,19,30,382,1089],[7,19,32,118,1089],[7,20,30,383,855],[7,20,32,119,857],[7,21,30,384,1089],[7,21,32,120,1089],[7,22,30,385,1089],[7,22,32,121,1089],[7,23,30,386,822],[7,23,32,122,824],[7,24,30,387,789],[7,24,32,123,791],[7,25,26,1089,686],[7,25,30,388,690],[7,25,32,124,692],[7,26,29,455,1089],[7,26,30,389,1089],[7,26,31,191,1089],[7,26,32,125,1089],[7,27,30,390,591],[7,27,32,126,593],[7,28,30,391,558],[7,28,32,127,560],[7,29,30,392,459],[7,29,32,128,461],[7,30,31,195,394],[7,30,32,129,395],[7,31,32,130,197],[8,0,32,66,1089],[8,1,32,67,1089],[8,2,32,68,1088],[8,3,32,69,1089],[8,4,32,70,1055],[8,5,32,71,1089],[8,6,32,72,1089],[8,7,32,73,1089],[8,8,32,74,1089],[8,9,32,75,1089],[8,10,32,76,1089],[8,11,32,77,1089],[8,12,32,78,989],[8,13,32,79,1089],[8,14,32,80,1089],[8,15,32,81,956],[8,16,32,82,1089],[8,17,32,83,1089],[8,18,32,84,1089],[8,19,32,85,1089],[8,20,32,86,1089],[8,21,32,87,1089],[8,22,32,88,824],[8,23,32,89,1089],[8,24,26,1089,752],[8,24,30,1089,756],[8,24,32,90,758],[8,25,29,421,1089],[8,25,31,157,1089],[8,25,32,91,1089],[8,26,32,92,1089],[8,27,32,93,1089],[8,28,30,1089,525],[8,28,32,94,527],[8,29,30,1089,426],[8,29,31,161,427],[8,29,32,95,428],[8,30,31,162,1089],[8,30,32,96,1089],[8,31,32,97,164],[9,0,32,33,1089],[9,1,32,34,1088],[9,2,32,35,1089],[9,3,32,36,1055],[9,4,32,37,1089],[9,5,32,38,1089],[9,6,32,39,1089],[9,7,32,40,1089],[9,8,32,41,1089],[9,9,32,42,1089],[9,10,32,43,1089],[9,11,32,44,989],[9,12,32,45,1089],[9,13,32,46,1089],[9,14,32,47,1089],[9,15,32,48,923],[9,16,32,49,1089],[9,17,32,50,1089],[9,18,32,51,1089],[9,19,32,52,1089],[9,20,32,53,1089],[9,21,32,54,1089],[9,22,32,55,791],[9,23,32,56,758],[9,24,32,57,1089],[9,25,32,58,1089],[9,26,32,59,1089],[9,27,32,60,527],[9,28,32,61,1089],[9,29,30,1089,393],[9,29,32,62,395],[9,30,31,129,1089],[9,30,32,63,1089],[9,31,32,64,131],[10,0,32,0,1088],[10,1,32,1,1089],[10,2,32,2,1089],[10,3,32,3,1089],[10,4,32,4,1089],[10,5,32,5,1089],[10,6,32,6,1089],[10,7,32,7,1089],[10,8,32,8,1089],[10,9,32,9,1089],[10,10,32,10,1089],[10,11,32,11,1089],[10,12,32,12,1089],[10,13,32,13,956],[10,14,32,14,923],[10,15,32,15,1089],[10,16,32,16,1089],[10,17,32,17,1089],[10,18,32,18,1089],[10,19,32,19,1089],[10,20,32,20,824],[10,21,32,21,791],[10,22,32,22,1089],[10,23,25,1089,718],[10,23,29,1089,722],[10,23,31,1089,724],[10,23,32,23,725],[10,24,32,24,692],[10,25,32,25,1089],[10,26,32,26,1089],[10,27,29,1089,491],[10,27,30,1089,492],[10,27,31,1089,493],[10,27,32,27,494],[10,28,30,1089,459],[10,28,32,28,461],[10,29,32,29,1089],[10,30,32,30,1089],[10,31,32,31,1089],[11,20,32,1089,758],[11,31,32,1089,32],[12,7,30,238,1020],[12,7,32,1089,1022],[12,15,26,510,884],[12,15,30,246,888],[12,15,32,1089,890],[12,18,32,1089,824],[12,22,30,253,657],[12,22,32,1089,659],[12,25,30,256,591],[12,25,32,1089,593],[12,26,32,1089,527],[12,28,31,1089,361],[12,29,32,1089,329],[12,30,32,1089,263],[14,26,32,1089,461],[14,30,32,1089,197],[15,25,32,1089,494],[15,29,31,1089,229],[15,29,32,1089,230],[15,30,32,1089,164],[16,30,32,1089,131],[17,30,32,1089,98],[18,30,32,1089,65]]}
```

### Appendix B: exact-check receipt

```json
{
  "scope": "Exact finite arithmetic only. No Lean compilation or proof verification.",
  "projectCommit": "520a2a29c40cc40e1df2b1c41980552f25d08e65",
  "sourceSha256": "9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9",
  "seed": {
    "prime": 109,
    "r": 57,
    "i": 33,
    "length": 96,
    "socleDegree": 9,
    "noetherLefschetzRank": 7,
    "rankWithDerivativeRow": 8
  },
  "invariantCubicBasis": [
    [
      0,
      0,
      0,
      1,
      1
    ],
    [
      0,
      0,
      0,
      3,
      0
    ],
    [
      0,
      0,
      3,
      0,
      0
    ],
    [
      0,
      1,
      1,
      1,
      0
    ],
    [
      0,
      3,
      0,
      0,
      0
    ],
    [
      1,
      0,
      1,
      1,
      0
    ],
    [
      1,
      2,
      0,
      0,
      0
    ],
    [
      2,
      1,
      0,
      0,
      0
    ],
    [
      3,
      0,
      0,
      0,
      0
    ]
  ],
  "characterOneCubicBasis": [
    [
      0,
      0,
      1,
      0,
      1
    ],
    [
      0,
      0,
      1,
      2,
      0
    ],
    [
      0,
      1,
      2,
      0,
      0
    ],
    [
      0,
      2,
      0,
      1,
      0
    ],
    [
      1,
      0,
      2,
      0,
      0
    ],
    [
      1,
      1,
      0,
      1,
      0
    ],
    [
      2,
      0,
      0,
      1,
      0
    ]
  ],
  "noetherLefschetzMatrixMod109": [
    [
      0,
      78,
      0,
      0,
      8,
      0,
      75,
      66,
      63
    ],
    [
      78,
      68,
      0,
      6,
      0,
      62,
      0,
      0,
      47
    ],
    [
      0,
      6,
      0,
      39,
      49,
      62,
      39,
      0,
      0
    ],
    [
      0,
      0,
      39,
      0,
      4,
      0,
      70,
      0,
      0
    ],
    [
      0,
      62,
      0,
      62,
      39,
      0,
      0,
      0,
      0
    ],
    [
      0,
      47,
      62,
      0,
      70,
      0,
      0,
      0,
      0
    ],
    [
      94,
      91,
      0,
      0,
      0,
      47,
      0,
      0,
      0
    ]
  ],
  "derivativeRowMod109": [
    0,
    21,
    0,
    0,
    0,
    0,
    0,
    0,
    70
  ],
  "noetherLefschetzMinorColumnsZeroBased": [
    0,
    1,
    2,
    3,
    4,
    5,
    6
  ],
  "noetherLefschetzMinorDeterminantMod109": 80,
  "augmentedMinorColumnsZeroBased": [
    0,
    1,
    2,
    3,
    4,
    5,
    6,
    7
  ],
  "augmentedMinorDeterminantMod109": 76,
  "normalizedKernelVectorMod109": [
    19,
    26,
    71,
    38,
    38,
    74,
    19,
    24,
    0
  ],
  "noetherLefschetzValueMod109": [
    0,
    0,
    0,
    0,
    0,
    0,
    0
  ],
  "derivativeValueMod109": 1,
  "higgs": {
    "dimension": 33,
    "directions": 35,
    "independentEquations": 1088,
    "solutionDimension": 1,
    "freeComponent": "all 33 diagonal entries",
    "zeroComponent": "all 1056 off-diagonal entries",
    "forestSha256": "f2ee2a403c3d8baa41684b9db9abe3208a066cea8f06bb22d5e8d662aef6212e"
  },
  "elapsedSeconds": 0.2214030270006333,
  "peakRssKiB": 27168,
  "addressSpaceLimitMiB": 1024,
  "cpuLimitSeconds": 120
}
```
