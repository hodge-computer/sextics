# A nonconstructive geometric route for cycle-q2


## Actual inverse-ideal restrictions and principal-cover descent — 14 November 2026

The final theorem `Submission.missing_geometric_existence` remains open.
This checkpoint supplies actual inverse-ideal restriction maps, their
reduction to the original normal Čech complex, and the degree-one
change-of-cover theorem needed for the Cartier boundary argument. The
original scalar Cartier two-cocycle is placed in its actual cohomology
quotient. Nonvanishing of that quotient class is the next application;
it is not asserted by this checkpoint.

### The actual inverse ideal and its restrictions

[GeometricCartierNormalLift.lean](GeometricCartierNormalLift.lean) now proves
that the actual module
\[
M=\operatorname{Hom}_{A}(I,A),\qquad
A=\operatorname{SurfaceRing}(r,1),\quad
I=\operatorname{curveIdealOnSurface}(r,1),
\]
has nine free coordinates over \(R=\mathbb C[x_1,x_2,x_3]\).
The construction uses the original quotient ring and original curve ideal.
It provides the bases of the actual surface and ideal, a perfect
coefficient pairing, and the induced Hom equivalence. The coefficient
functional is the coefficient of \(x_0^2w^2\); its dual basis is constructed
explicitly. Freeness is over \(R\). No projectivity or freeness over the
surface ring is assumed.

This is an independent presentation of the inverse-ideal freeness also
proved in the preceding shared-branch contribution
[GeometricInverseIdealBasis.lean](GeometricInverseIdealBasis.lean). The
present continuation uses its own actual quotient-ring basis to establish
the restrictions and reduction maps needed by the four-open Cartier
construction. Both developments are preserved.

For every principal denominator \(g\), the actual ideal is finitely
presented, and the canonical tensor-localization comparison is proved:
\[
A[g^{-1}]\otimes_A\operatorname{Hom}_A(I,A)
\simeq_A
\operatorname{Hom}_{A[g^{-1}]}
 (I A[g^{-1}],A[g^{-1}]).
\]
`IdealHomLocalization.tensorEquiv` is fixed by evaluation on the original
ideal. `tensorEquiv_restriction` proves its compatibility with the actual
restriction homomorphisms. The restriction/evaluation identity holds on
all localized ideal elements, not only on a selected basis. Identity,
composition, and restriction of scalar multiplication are proved.

`CoordinateInverseIdeal.firstCech_exact` supplies actual local-Hom
primitives on the three coordinate opens. Its proof combines the proved
nine-element basis, coordinate Čech exactness, the actual localization
comparisons, and their naturality. Thus its input cocycle and output
primitives live in the genuine localized ideal Hom modules.

The `NormalReduction` construction then reduces local inverse-ideal
homomorphisms to the existing `FirstKernel`, `SecondKernel`, and
`OverlapKernel`. These maps commute with the original normal restriction
maps; scalar ideal inclusions reduce to zero. The fixed inverse-ideal
connecting lift reduces to the original connecting representative. In
particular, `connectingClass_zero_of_coboundary` proves that an equality
\[
\widetilde\nu=\varphi_1|_{01}-\varphi_0|_{01}+a\,\mathrm{id}_I
\]
in the actual overlap Hom module forces the original normal connecting
class to vanish. This is an explicit comparison of the original classes.
It requires no unproved sheaf identification.

### Actual Čech cochains and the principal-cover comparison

[GeometricCartierCech.lean](GeometricCartierCech.lean) defines the four-open
Čech complex for a restriction system with its original linear maps.
The differentials have the usual alternating signs, and both consecutive
composites are proved zero. Its second cohomology is the quotient of the
actual two-cocycles by the actual one-cochain boundaries.

For the original Cartier cover
\[
D(g_1),\ D(g_2),\ D(f_1),\ D(f_2),
\]
`cartierCycle` is precisely the previously constructed scalar cocycle:
its only nonzero faces are `boundary012` and `boundary013`.
`cartierClass_eq_zero_iff` states that its quotient class vanishes exactly
when this fixed cocycle has an actual scalar one-cochain primitive.

The affine lemmas are proved from principal localization. When one cover
member is a unit, an explicit contraction supplies degree-one primitives
and unique degree-zero gluing. Localization of the finite cochain
products and the local criterion for exactness then establish these
results for every four-element principal cover generating the unit ideal.
The proof also treats arbitrary scalar extension through its actual
tensor maps.

For two principal covers whose generated ideals have the same radical,
the common refinement is the actual module
\[
R[b_J^{-1}]\otimes_R
  \bigl(R[a_I^{-1}]\otimes_R M\bigr).
\]
The two restriction directions commute by their tensor formulas. On a
nonempty overlap of either cover, the other cover generates the unit
ideal; this is proved directly from the radical relation and the inverted
coordinate. The double-complex chase uses the resulting affine
exactness and gluing to construct primitives on the first cover from
primitives on the second. The theorem
`first_exact_of_radical_eq` therefore transfers degree-one exactness
between the actual localization complexes. A cover comparison is proved,
not supplied as a hypothesis.

The helper also proves the precise reduction from a three-member cover
to a four-member cover with an empty fourth open. This keeps the original
three-coordinate calculation compatible with the four-open Cartier
complex and its fixed signs.

### Verification and the remaining application

The exact 2,493-line `GeometricCartierNormalLift` source and the exact
1,850-line `GeometricCartierCech` source have each passed compilation and
independent kernel replay under the unchanged local resource limits.
Separate pure-import audits cover 38 and 27 named endpoints, respectively;
all use only `propext`, `Classical.choice`, and `Quot.sound`. These objects
have no dependency on the geometry files changed by the concurrent
canonical-cohomology contributions, so their source-bound checks remain
current after those contributions are integrated.

The declaration-free facades `Assembly05` and `Assembly06` are replaced in
their importers by their respective sole imports. Their proof bodies are
empty; surviving declarations and dependency reachability are preserved.
This checkpoint contains 255 proposal files. All protected files and the
protected target remain unchanged. The local checks reported here concern
the specified helper objects and their dependencies; they do not assert a
full build or acceptance of the older aggregate proposal.

The next step binds the proved coordinate Hom primitives to the Cartier
cover through `first_exact_of_radical_eq`, then combines the resulting
inverse-ideal primitive with `NormalReduction` and the literal nonzero
normal class. The current checkpoint does not yet contain that assembled
nonvanishing theorem. Projective and derived degree-two comparisons,
normal adjunction, the geometric trace and moving-cycle argument, and the
global support and algebraic de Rham passage remain further obligations.
The only admission is still `Solution.lean:138`.

The continuation follows Ben Diamond's nonconstructive geometric route
and preserves the prior shared-branch contributions. The new proof
construction and Lean work were developed with OpenAI assistant support.

## The actual inverse ideal has nine free coordinates — 14 November 2026

The final theorem `Submission.missing_geometric_existence` remains open.
This continuation supplies the previously missing freeness input for the
actual inverse ideal on the containing surface at `θ = 1`. It proves a
nine-element basis over the literal polynomial base, applies the existing
coordinate Čech exactness theorem to that module, and proves that its
localization is the actual Hom module of the localized curve ideal. No
freeness, finite-presentation, or separability assertion is added as a
geometric hypothesis.

### An actual two-stage cubic presentation

[GeometricInverseIdealBasis.lean](GeometricInverseIdealBasis.lean) works
over
\[
B=\mathbb C[x_1,x_2,x_3],\qquad
\alpha=x_1^2+x_2x_3,\qquad
\beta=x_3^3+x_2^3+x_1x_2x_3-i(x_1^3+x_3^3).
\]
Put
\[
C_0=B[u]/(u^3+\alpha u+\beta),\qquad
q=x_2^2,\qquad d=r x_1x_3,\qquad
f=u^2-d,\qquad g=u^4+du^2+d^2.
\]
The actual surface ring `SurfaceRing r 1` is proved isomorphic to
\[
A=C_0[v]/(v^3-3qv^2+3q^2v+fg).
\]
The forward and inverse quotient maps are constructed and proved inverse.
The coordinates are fixed by the original polynomials: `u` is the image
of `x₀`, and `v` is the image of `originalF2 = w+x₂²`. The base map is the
literal polynomial map in `x₁,x₂,x₃`. Both cubic equations are monic, so
`(1,u,u²)` and `(1,v,v²)` give genuine bases over the respective coefficient
rings. These results hold for every complex `r`; they do not require the
cover hypothesis `r ≠ 0`.

The element `f` is regular in `C₀`. Writing `c=α+d`, the proof verifies
\[
(cu^2-\beta u+c^2)f=\beta^2-dc^2.
\]
The right side is a nonzero element of `B`: evaluation at
`(x₁,x₂,x₃)=(0,0,1)` gives `−2i`. Multiplication by this scalar is injective
on the free `B`-module `C₀`, which proves the required regularity of `f`.
The proof does not assume that either cubic extension is unramified.

### Bases of the curve ideal and its actual inverse ideal

The helper proves the exact ideal identity
\[
I=\operatorname{curveIdealOnSurface}(r,1)=(f,v)\subset A.
\]
A general cubic lemma then gives the `C₀`-basis `(f,v,v²)` of this actual
ideal. For a ring with basis `(1,x,x²)` and relation
\[
x^3+ex^2+ax+fg=0,
\]
the lemma explicitly rewrites every element of `(f,x)` in the three
coordinates `(f,x,x²)` and uses regularity of `f` to prove uniqueness.
Thus `actualCurveIdealBasis` proves freeness; it does not take it as an
input. Combining with the inner cubic basis gives
`actualCurveIdealBaseBasis`, a nine-element `B`-basis of `I`.

To pass to the inverse ideal, let `λ` be the coefficient of `x²` in the
ambient cubic basis. The multiplication pairing `λ(yz)` has matrix
\[
\begin{pmatrix}
0&0&1\\
0&1&-e\\
1&-e&e^2-a
\end{pmatrix},
\qquad \det=-1.
\]
The source proves the pairing perfect over the coefficient ring, with an
explicit inverse coordinate formula. This is the coefficient functional;
ordinary algebra trace and separability are not used.

For every actual `A`-module `M`, composition with `λ` is proved to give a
linear equivalence
\[
\operatorname{Hom}_A(M,A)
 \simeq_{C_0}\operatorname{Hom}_{C_0}(M,C_0).
\]
The inverse is constructed from the perfect coefficient pairing, and its
`A`-linearity is proved. Applying this to the already free ideal `I` and
its dual basis gives `actualInverseIdealBasis`. Finally,
`actualInverseIdealBaseBasis` is a genuine nine-element `B`-basis of
\[
I^{-1}:=\operatorname{Hom}_A(I,A).
\]
The notation denotes the actual linear-Hom module. No freeness over the
surface ring `A` is asserted. The natural quotient action of `B` and the
composed action through `C₀` are compared through the literal base map,
so the nine-coordinate result uses the same scalars as the coordinate
Čech construction.

### Coordinate Čech exactness and localization of Hom

Let `M=Hom_A(I,A)` with this proved `B`-basis. Write `(z₀,z₁,z₂)=(x₁,x₂,x₃)`. For a subset
`J` of `{0,1,2}`, set
\[
M_J=B\bigl[(\prod_{j\in J}z_j)^{-1}\bigr]\otimes_B M.
\]
The helper applies `GeometricFreeCoordinateCech.firstCech_exact` to its
nine-element basis. Every triple `(p₀₁,p₀₂,p₁₂)` of actual localized
module elements satisfying the cocycle equation on the triple
intersection has actual primitives `(q₀,q₁,q₂)`, with
\[
p_{ij}=q_j|_{ij}-q_i|_{ij}.
\]
This closes the supplied-basis premise of the earlier coordinate
exactness theorem for the genuine inverse ideal. The result is stated
in the tensor-localization coordinate complex; the further comparison
with sheaf sections and the four Cartier opens is separate.

The same helper also proves a closed localization comparison. The actual
surface ring is noetherian, and its actual curve ideal is finitely
presented, for every `r, θ`. The pinned finite-presentation theorem and
the canonical ideal-localization map give
\[
S^{-1}\operatorname{Hom}_A(I,A)
 \simeq_A\operatorname{Hom}_{S^{-1}A}(S^{-1}I,S^{-1}A).
\]
The localization map is fixed by evaluation: the image of a global
homomorphism `ν`, evaluated on the image of `x∈I`, equals the image of
`ν(x)`. The helper proves that local Hom maps are determined by these
original ideal elements. Its canonical restrictions for nested
multiplicative submonoids compose correctly. These statements concern
the actual ideal and its actual Hom module, before reduction to the
relative conormal dual.

### Verification and remaining comparison

The local checked scope contains thirty-two proposal objects in a
seventy-nine-module dependency closure. The prior thirty objects and
their seventy-seven-module context retain their exact archived sources
and compiled objects. The unchanged published
`GeometricSurfaceCoordinates` and the new assembled
`GeometricInverseIdealBasis` receive fresh source-bound compilation,
independent kernel replay, and separate pure-import endpoint audits.
The new helper preserves the four checked namespace bodies and removes
only their scratch imports when assembling the permitted flat module.
All audited endpoints use only `propext`, `Classical.choice`, and
`Quot.sound`.

The new proof bodies retain the default heartbeat and recursion limits.
The incoming `GeometricSurfaceCoordinates` is checked byte for byte as
published, including its inherited heartbeat settings up to 4,000,000
and recursion limit 20,000. Runtime and memory caps remain unchanged;
this continuation introduces no larger proof budget.

The declaration-free facade `GeometricTarget10` is flattened into its
sole importer by replacing the import with `GeometricTarget10Part03`.
No proof-body bytes change, surviving dependency reachability is
preserved, and the proposal remains at exactly 256 files. The final
audit binds the staged source tree, the reconstructed four-body assembly,
the fresh receipts, the preserved contexts, protected files, and the
rendered explanation. This is local development evidence, not a full
build or acceptance of the older aggregate proposal.

The only admission remains `Solution.lean:138`. In particular, this
checkpoint does not assert nonvanishing of the Cartier second-cohomology
class. The remaining local comparison must carry coordinate exactness
to the four-cover inverse-ideal complex and identify the reduction of
its primitives with the actual normal Čech coboundary. Projective and
derived second-cohomology comparisons, the geometric trace and
moving-cycle argument, and the global support and algebraic de Rham
passage to the protected residue remain additional obligations.

## Literal canonical cohomology and projective normal classes — 14 November 2026

The final theorem `Submission.missing_geometric_existence` remains open.
This continuation computes the complete actual canonical cohomology group
at the literal incidence seed and constructs actual derived projective
classes from the homogeneous relative-normal frames. It proves a nonzero
ambient normal class and seven zero cubic images of one fixed incidence
normal class. The precise sheaf comparisons and remaining geometric
obligations are stated below.

### The complete canonical cohomology line at the literal incidence seed

`GeometricLiteralHOne.lean` closes the full complex-linear cohomology calculation at **`(r, θ) = (57, 1)`**. It uses the intrinsic complex scalar action induced by the actual structure morphism and differential module sheaf. Its `literalCanonicalNormalizationEquiv` is an equivalence

\[
\Phi:\mathbb C\simeq_{\mathbb C}H^1(C_{57,1},\Omega^1_{C_{57,1}/\mathbb C}),
\qquad \Phi(a)=aN.
\]

Here `N = literalCanonicalNormalization` is precisely the image of the original homogeneous Čech class

\[
\left[\frac{x_3^9}{g_1g_2}\right]
\]

through `degreeOneToProjectiveH1 57 1` and the already constructed `literalCanonicalH1Equiv`. This fixes the normalization through our existing literal canonical module isomorphism. The inverse coordinate `literalCanonicalCoordinate` is defined on **every** actual canonical cohomology class, sends `N` to `1`, and vanishes exactly on the zero class. The actual complex vector space is finite-dimensional, with finrank one.

The proof first compares the incoming complex action on homogeneous localization sections with the existing degree-zero projective coefficient action. Consequently `degreeOneCechHOneLinearEquiv` upgrades the previously proved full Čech-to-derived equivalence to a complex-linear equivalence for every `r ≠ 0` and every `θ`. The literal incidence Čech coordinate and the actual canonical comparison then prove bijectivity of scalar multiplication of `N`. No geometric trace is supplied as a premise.

For the original nine cubic columns, put

\[
\rho(v)=\frac{i v_1-(1+i)v_8}{6}.
\]

`literalPairedCanonicalLinear v` is explicitly the image of `pairedDegreeOneClass 57 1 v` through the same actual canonical map. Its numerator is `-derivativeNumerator (cubicDeformation v)`, namely \(x_2^3x_3^3\operatorname{cubicDeformation}(v)\). The checked identities are

\[
P(v)=\frac{12+24i}{5}\,\rho(v)N,
\qquad
\operatorname{literalCanonicalCoordinate}(P(v))
 =\frac{12+24i}{5}\,\rho(v),
\qquad
P(v)=0\iff\rho(v)=0.
\]

Every nonzero complex-linear functional \(\tau\) on this **full actual derived cohomology group** is injective and satisfies \(\tau(N)\ne0\). Thus

\[
\tau(P(v))=\frac{12+24i}{5}\,\tau(N)\rho(v)
\]

has one common nonzero coefficient. More generally, for any complex-linear map \(f\) into this group and any two nonzero complex-linear functionals \(\tau,\sigma\), `canonical_trace_kernel_independent` proves
\(\ker(\tau\circ f)=\ker(\sigma\circ f)\).

These results concern the original homogeneous classes and actual differential-sheaf cohomology. Identifying a geometric Serre trace, the moving-cycle or cylinder derivative, and the remaining support/comparison statements still requires the corresponding geometric proofs. This checkpoint does not remove the final admission in `Solution.lean`.

### Genuine projective cohomology of the inverse-square normal frames

`GeometricProjectiveNormalClass.lean` constructs an actual module sheaf on the
literal projective curve $C=C_{57,1}$. On the existing cover $U_1=D_+(g_1)$,
$U_2=D_+(g_2)$, let $t=x_2/x_1$. The sheaf $M$ is the existing
`TwistedModule.moduleSheaf` with transition $t^{-2}$. Its interpretation is
fixed by the actual surface-relative conormal duals: the two frames are
$x_i^{-2}\gamma$, where $\gamma=(g_2,-g_1,0)$ is the proved intrinsic
normal-kernel generator. The helper proves their literal equation values,
the inverse-square overlap transition, and compatibility with both canonical
tensor–Hom restriction maps. The maps from the degree-zero projective chart
rings into these relative-normal modules are injective and respect scalar
multiplication.

For every homogeneous cubic $\sigma$, actual sheaf gluing constructs a
module-sheaf morphism $\mu_\sigma:M\to\mathcal O_C(1)$. The image of the
source frame on $U_i$ is the degree-one fraction $\sigma/x_i^2$; its
coefficient in the ordinary degree-one frame $x_i$ is
$\sigma/x_i^3$. No global comparison map is supplied as a hypothesis.

For a homogeneous polynomial $p$ of degree six, the degree-zero fraction
$p x_1^2/(g_1g_2)$ defines an actual overlap section of $M$, and its
Mayer–Vietoris boundary gives a genuine derived class
$\alpha_p\in H^1(C,M)$. The theorem `cubicH1Map_normalClass` proves that
$H^1(\mu_\sigma)(\alpha_p)$ is exactly the previously constructed
degree-one class with numerator $p\sigma$, including its specified
denominator and sign. Composing with the proved literal canonical sheaf
isomorphism gives the following closed statements:

* For $p_A=x_2^3x_3^3$ and
  $L=i x_0^2x_1+(i-1)x_0^3$,
  `selectedCubicPairing_literalNormalClass` identifies the image of
  $\alpha_{p_A}$ with `selectedAmbientClass`. This target is nonzero, so
  `literalNormalClass_ne_zero` proves $\alpha_{p_A}\ne0$. Its overlap
  normal homomorphism is exactly
  `relativeConnectingRepresentative 57 1 derivativeA 0`.
* For $p_L=kL$, the theorem
  `selectedIncidenceNormalClass_in_seven_kernels` proves that the same seven
  specified cubic maps kill $\alpha_{p_L}$. Its overlap homomorphism is
  exactly `relativeConnectingRepresentative 57 1 0 weightedSelectedCubic`.

These are actual sheaf morphisms and derived cohomology classes, with closed
literal parameter values. The remaining geometric comparison is to identify
$M$ with the intrinsic normal sheaf of the actual projective immersion and
to identify this explicit cubic morphism with the surface-normal adjunction
pairing. This helper does not establish the surface Cartier $H^2$ boundary,
its nonvanishing, or a geometric Serre trace, and does not close the final
`missing_geometric_existence` obligation.

### Verification of the literal cohomology and normal-class continuation

The local checked scope now contains thirty proposal objects in a
seventy-seven-module proposal dependency closure. The twenty-four
previously checked objects retain exactly their archived sources,
compiled objects, and seventy-one-module dependency context. Six objects
receive fresh source-bound compilation and independent kernel replay:
`GeometricIncidenceTraceData`, `GeometricIncidenceCechTrace`,
`GeometricTwistedDifferential`, `GeometricCanonicalCechBoundary`,
`GeometricLiteralHOne`, and `GeometricProjectiveNormalClass`. Separate
pure-import endpoint audits check the allowed axioms `propext`,
`Classical.choice`, and `Quot.sound`.

The existing canonical-boundary helper needs one explicit-argument
elaboration repair: its use of `firstDenominatorFrame_generator` now
supplies `r hr`. The statement and mathematical construction are
unchanged. The literal linear equivalence is assembled through its
proved scalar normalization, with pointwise agreement with the original
cohomology maps; this keeps compilation within the unchanged resource
limits. No proof budget is increased.

The declaration-free import facade `GeometricTarget09` is replaced in
its sole importer by its own sole import, `GeometricTarget09Part04`.
All surviving declarations and transitive surviving dependencies are
preserved, and the import graph remains acyclic. The proposal therefore
contains exactly 256 files, within the existing limit. The staged-tree
audit also checks protected-file preservation, exact source and object
hashes, replay freshness, and the rendered mathematical explanation.
These local checks do not establish a full build or acceptance of the
older aggregate proposal.

The only admission remains `Solution.lean:138`. The new explicit normal
frame sheaf still has to be identified with the normal sheaf of the
projective immersion, and the cubic pairing with the intrinsic
surface-normal adjunction pairing. The surface Cartier second-cohomology
boundary and its nonvanishing, the geometric trace and moving-cycle
comparisons, and the global support and algebraic de Rham passage to the
protected residue remain separate proof obligations. Scratch work on a
cubic presentation and inverse-ideal bases is not part of this checked
checkpoint.

## Earlier integration with the Cartier-boundary continuation — 14 November 2026

The final existence theorem remains open. The combined proposal preserves
the new actual inverse-ideal lift, four-open Cartier boundary, coordinate
Čech exactness, and sparse canonical-boundary comparison, together with
the derived-cohomology and literal normal-nonvanishing work below. The
Cartier checkpoint is retained in full as a separate historical section.

This last merge changes none of the sources or compiled objects in the
71-module dependency closure of the twenty-four checked cohomology
objects. Their exact source, object, and independent-replay evidence is
therefore retained without another Lean rebuild. A separate source audit
checks the new merge, the complete incoming-source preservation, the one
existing import-facade substitution in the overlapping aggregate file,
the protected files, and the rendered explanation. The three new incoming
helpers are preserved exactly; this merge audit does not claim a fresh
local compilation of them or a full build of the older aggregate chain.

The incoming continuation removes four further declaration-free wrappers
and adds three proof helpers, leaving 255 proposal files after integration.
Earlier file counts below describe their respective checkpoints. The only
admission is still the existing `sorry` in `Solution.lean`; the actual
projective normal/Cartier comparison, geometric trace and support argument,
and algebraic de Rham passage to the protected residue remain to be closed.

## Integrated cohomology and incidence checkpoints — 14 November 2026

The final theorem `Submission.missing_geometric_existence` remains open.
This integration preserves both the full derived-cohomology continuation
and the incoming literal-incidence canonical-sheaf and Čech-trace
continuation. The two detailed sections immediately below record those
earlier checkpoints and their respective verification scopes.

The combined source retains the actual affine H¹-vanishing theorem, the
full Čech-to-derived-H¹ comparison, the intrinsic complex scalar action,
and the sparse canonical H¹ coordinate. It also retains the literal
canonical isomorphisms, the complete literal degree-one Čech line, and the
selected cubic's seven zero classes and nonzero ambient detector. The
actual relative-normal connecting class is proved nonzero in its cone
Čech quotient. These comparisons use the actual sheaves, localization
maps, and relative conormal duals described below.

The shared regular-pair module preserves both generalized constructions:
its entire prior source is followed by the incoming `Theta` namespace
verbatim. The shared affine differential-sheaf module is the incoming
source without alteration. The cohomology integration checks twenty-four
proposal objects: the two changed shared sources are compiled and
independently replayed, ten affected dependent objects receive fresh
independent replay, and twelve retain their unchanged checked source and
dependency contexts. The endpoint audit permits only `propext`,
`Classical.choice`, and `Quot.sound`. This local integration scope does
not certify the four new incoming proof modules or the older aggregate
modules afresh; their earlier validation claims are recorded in the
preserved incidence checkpoint below.

Four declaration-free import facades, `GeometricTarget05` through
`GeometricTarget08`, are flattened into their sole importers. Each edit
replaces one import line by the facade's sole import, and all other
surviving source bytes are preserved. The surviving modules have exactly
the same transitive surviving dependencies, and the import graph remains
acyclic. This keeps the proposal within its 256-file limit without
changing proof bodies or increasing proof budgets.

The integration checks the exact staged source tree, source and artifact
hashes, replay freshness, protected-file preservation, and rendered
mathematical explanation. It introduces no axiom or admission. The only
admission remains the existing `sorry` in `Solution.lean`; whole-proposal
verification and acceptance have not been established.

The next mathematical obligations are the projective graded
normal-sheaf boundary and its canonical pairing, the geometric
Serre/semiregularity and moving-cycle comparisons, and the global support
and algebraic de Rham passage to the protected residue. None of the
computed one-dimensional trace coordinates supplies those constructions
by itself.

## Affine vanishing and the full projective canonical cohomology — 14 November 2026

The final admission, `Submission.missing_geometric_existence`, remains
open. This continuation closes the cohomological gap identified in the
preceding checkpoint: the two actual affine denominator opens have zero
first cohomology, and the actual Mayer–Vietoris comparison is surjective.
At the sparse seed it gives a complex-linear isomorphism
\[
H^1(C_{r,0},\Omega^1_{C_{r,0}/\mathbb C})\simeq_{\mathbb C}\mathbb C,
\qquad r^3=2,
\]
whose coordinate agrees with the previously checked finite degree-nine
trace. The complex action is induced by the actual coefficient maps of
the sheaf. The global canonical-sheaf comparison is also now proved at
the separate literal incidence seed \((r,\theta)=(57,1)\).

### Affine vanishing in the actual category of additive sheaves

[GeometricAffineCohomology.lean](GeometricAffineCohomology.lean) proves
`affine_H_one_eq_zero` and `affine_H_one_subsingleton` for the actual
additive structure sheaf on \(\operatorname{Spec}A\), for every commutative
ring \(A\). Affine acyclicity is a conclusion, not an input. The proof
works with the same derived `Ext` definition of sheaf cohomology used by
the projective construction.

The algebraic step contracts a cocycle on a finite cover by basic opens.
Uniform powers clear its finitely many denominators and the possible
localization torsion in the cocycle equations. Since the basic opens
cover the spectrum, suitable powers of their defining functions generate
the unit ideal. A finite weighted sum then supplies the coboundary. This
argument does not assume that the ring is a domain.

For an actual short exact sequence of additive sheaves beginning with
\(\mathcal O\), local surjectivity supplies local lifts of a global
section. The preceding contraction corrects their differences, and the
sheaf gluing axiom gives a global lift. An injective presentation and the
actual `Ext` exact sequence then imply \(H^1(\operatorname{Spec}A,\mathcal O)=0\).
The enough-injectives and local-surjectivity instances are supplied by
the pinned Mathlib sources.

[GeometricAffineCohomology.lean](GeometricAffineCohomology.lean)
constructs the required restriction map
\[
F.H'\,1\,U\longrightarrow(F\!\mid_U).H\,1
\]
and proves it injective on a small thin site. The proof uses exact
restriction, additive Yoneda, and an injective presentation; it does not
assume that restriction preserves injective objects. It also constructs
the sheaf equivalence for the actual chart-site equivalence, including
the comparison of the constant integer sources defining cohomology.
These degree-one injections suffice to transport affine vanishing to
the ambient-site groups on the two projective opens. No all-degree
restriction isomorphism is asserted.

### The full Čech comparison and its intrinsic scalar action

[GeometricAffineCohomology.lean](GeometricAffineCohomology.lean) identifies
the restricted twisted sheaf with the actual affine structure sheaf,
using the previously proved chart section isomorphisms and linear
frames. Consequently both groups
\[
(\mathcal L_{r,\theta}).H'\,1\,U_1,
\qquad (\mathcal L_{r,\theta}).H'\,1\,U_2
\]
are zero for all parameters. When \(r\ne0\), the actual two-open cover
and Mayer–Vietoris exactness make the original Čech comparison bijective:

```lean
degreeOneCechHOneEquiv (r θ : ℂ) (hr : r ≠ 0) :
  DegreeOneCech r θ ≃+ ProjectiveSheafH1 r θ
```

[GeometricSheafCohomologyScalar.lean](GeometricSheafCohomologyScalar.lean)
constructs multiplication by a complex constant as an endomorphism of
the actual additive sheaf underlying a module sheaf. Applying the actual
cohomology functor gives its complex module structure in every degree.
The resulting maps commute with module-sheaf morphisms, the section/zero-cohomology
comparison, and the Mayer–Vietoris boundary.
[GeometricProjectiveCohomologyLinear.lean](GeometricProjectiveCohomologyLinear.lean)
proves the scalar compatibility of the homogeneous overlap fractions and
applies this construction to the canonical-sheaf isomorphism. Thus the
normalized canonical class depends complex-linearly on its coefficient.

Combining this linearity, the established sparse-seed Čech normalization,
and the new surjectivity gives

```lean
canonicalNormalizationEquiv (r : ℂ) (hr : r ^ 3 = 2) :
  ℂ ≃ₗ[ℂ] DifferentialSheafH1 r 0
```

Its inverse, `canonicalResidueCoordinate`, is defined on all of the
actual derived group. It sends the class of the normalization numerator
\(x_0x_1^8\), with denominator \(g_1g_2\), to one. For every homogeneous
degree-nine polynomial \(p\), the proved identity is
\[
\operatorname{canonicalResidueCoordinate}_r
 \bigl(\operatorname{degreeNineCanonicalClass}_r(p)\bigr)
 =\operatorname{traceLinear}_r(p).
\]
In particular this coordinate detects zero on the whole derived group,
not only on the previously identified image of the Čech map.

### The literal canonical sheaf and parameter discipline

The cofactor, overlap, and gluing arguments in
[GeometricChartKaehler.lean](GeometricChartKaehler.lean),
[GeometricCanonicalOverlap.lean](GeometricCanonicalOverlap.lean),
[GeometricProjectiveDifferentialForms.lean](GeometricProjectiveDifferentialForms.lean),
and [GeometricProjectiveCanonical.lean](GeometricProjectiveCanonical.lean)
now work with the two actual chart Jacobian ideals as their common input.
The already proved literal Jacobian cover supplies that input at
\((57,1)\), yielding the closed theorem

```lean
literalProjectiveCanonicalIso :
  projectiveDifferentialSheaf 57 1 ≅ degreeOneModuleSheaf 57 1
```

The sparse-seed public endpoints are retained. Likewise,
[GeometricCurveRegularPair.lean](GeometricCurveRegularPair.lean) now proves
the denominator regular-pair and degree-nine kernel results for every
\(r\ne0\) and every \(\theta\), retaining the earlier sparse wrappers.
This permits the literal calculation to use the same actual all-poles
Čech kernel theorem. It does not identify the literal curve with the
sparse curve.

### A nonzero canonical class at the literal seed

[GeometricLiteralCanonicalClass.lean](GeometricLiteralCanonicalClass.lean)
constructs an exact complex-linear coefficient functional on the original
four-variable polynomial ring at \((57,1)\). Its 24 coefficient terms
annihilate every polynomial in the ideal
\[
J_{57,1}=(f_{57},h_1,g_1,g_2),
\]
including arbitrary polynomial multiples of the four generators. These
identities are checked in Lean; no numerical rank or external symbolic
calculation is used as a proof. On the degree-nine witness it gives
\[
\lambda(x_0^3x_2^3x_3^3)=228\ne0.
\]
The actual all-poles Čech kernel theorem then proves that the corresponding
homogeneous fraction is nonzero in the Čech quotient. The original
Mayer–Vietoris injection and the new literal canonical-sheaf isomorphism
carry it into a nonzero class of
\(H^1(C_{57,1},\Omega^1_{C_{57,1}/\mathbb C})\). The resulting
`literalCanonicalClass_ne_zero` and
`literalDifferentialSheafH1_nontrivial` have no extra ideal-membership,
comparison, or smoothness premises.

The same helper also proves a statement about the particular selected cubic
\[
L=i x_0^2x_1+(i-1)x_0^3.
\]
For the seven displayed weighted cubic tests \(\sigma_j\), after the actual
substitution eliminating the weighted coordinate, every degree-nine
class represented by \(k_1L\sigma_j/(g_1g_2)\) is zero in this same
canonical-sheaf cohomology group. The seven exact Bézout identities used
here are copied, with their provenance recorded, from the earlier
explicit-direction calculation into a separate namespace. They are
checked independently without importing the unvalidated historical
aggregate; the earlier source is preserved byte-for-byte.

For the same \(L\), the ambient normal-lift numerator is
\[
-\operatorname{substitute}(x_2x_3^3w)\,L
 =x_2^3x_3^3L,
\qquad
\lambda(x_2^3x_3^3L)=228(i-1)\ne0.
\]
The theorem `selectedCubic_kernel_and_detector` therefore proves the
seven actual zero-class equations together with this actual nonzero
ambient class. Its `degreeNineCanonicalClass_zero_iff` identifies the
kernel for every homogeneous degree-nine numerator with membership in
\(J_{57,1}\). This is a statement about these explicit classes; it does
not claim a seven-dimensional kernel or identify a deformation or
cylinder differential by definition.

### Binding the detector to the actual relative normal cochain

The final section of
[GeometricLiteralCanonicalClass.lean](GeometricLiteralCanonicalClass.lean)
uses the preserved incoming relative-normal construction directly. It
extracts the coefficient of `relativeConnectingRepresentative` through
the actual relative-normal/kernel equivalence and the proved kernel frame.
Multiplying this coefficient by the selected cubic is exactly the
homogeneous degree-nine overlap representative used above. The seven test
products satisfy the corresponding identities, including their values
on the literal equation classes.

It also proves the closed theorem

```lean
CycleQ2GeometricLiteralNormalBinding.literal_normalConnectingClass_ne_zero :
  CycleQ2ActualNormalCech.connectingClass 57 1 derivativeA 0 ≠ 0
```

Indeed, a zero normal connecting class would make its scalar coefficient
a boundary. Multiplication by the chosen weighted cubic preserves that
boundary submodule. Its carrier agrees with the previously checked Koszul
boundary submodule: both are the sum of the same two localization-map
ranges. The regular-pair kernel theorem would then put the paired
numerator into \(J_{57,1}\), contradicting the exact nonzero detector.

This conclusion concerns the actual ungraded cone normal Čech quotient.
Its projective normal-sheaf descent, the geometric connecting-map
comparison, and the surface boundary or semiregularity interpretation
remain separate constructions. No projective normal-cohomology or
Serre-duality premise is introduced in the nonvanishing proof.

### Verification of this checkpoint

The concurrent relative-normal-module checkpoint is preserved below, and
its non-document sources are unchanged. To keep the combined proposal
within its 256-file limit, the new affine-vanishing, restriction, and full-H¹
helpers are combined in `GeometricAffineCohomology.lean`. This combination
retains all three original declaration bodies and namespaces. The projective
linearity construction retains its original separate module,
`GeometricProjectiveCohomologyLinear.lean`. Its linear equivalence is
packaged from the existing additive equivalence and a separately proved
scalar-compatibility lemma, retaining the same pointwise map. Both modules
are compiled and independently replayed again from their final source.

The cohomology verification scope is the nine changed or new Lean helpers, the
three previously checked dependents affected by the refactors, and three
additional literal-cover dependencies first checked in this continuation.
The changed and new sources are compiled from their final bytes. Each of
these fifteen proposal modules is independently replayed with
`leanchecker`, and the public endpoint audits allow only `propext`,
`Classical.choice`, and `Quot.sound`. The additional pinned Mathlib
dependency closure is compiled from unchanged pinned sources. The incoming
relative-conormal, seed-normal-ideal, and importing formal-input modules,
plus the conormal-basis and normal-connecting helpers, are also rebuilt and
replayed because they enter this checked dependency chain. This gives
twenty explicitly checked proposal modules in the integrated checkpoint.
The affected cohomology dependents are replayed against those new artifacts.
All concurrent non-document sources are preserved byte-for-byte.

The source audit preserves the protected target, manifest, instance,
toolchain, and verifier. It checks the import graph, permitted flat-file
scope and size limits, exact source/artifact hashes, and replay freshness.
No new admission, axiom, unsafe evaluation, executable extension, or
proof-budget increase is introduced. The only admission remains the
existing `sorry` in `Solution.lean`. This checkpoint verification is not
a successful build or acceptance of the whole proposal.

### Scope of this continuation

These results compute actual first cohomology of the canonical
differential sheaf and supply the literal canonical comparison. They do
not yet construct the normal-sequence/cylinder comparison identifying the
selected polynomial class with the geometric moving-cycle derivative.
The relevant geometric variation, supported correspondence, and regular
algebraic de Rham comparison bound to the protected residue are also still
required for `Submission.missing_geometric_existence`. The target,
manifest, and final admission are unchanged. The full historical aggregate
dependency chain has not passed a complete build.

The earlier checkpoint descriptions below record their status before
this continuation; their former affine-vanishing and scalar-linearity gaps
are resolved by the results above.

## Actual Cartier boundary and coordinate Čech exactness — 14 November 2026

The final admission, `Submission.missing_geometric_existence`, remains
open. This continuation constructs the surface inverse-ideal lift of the
existing normal cochain, its signed four-open boundary, and the actual
coordinate-localization comparison at the literal incidence parameter.
It also identifies the paired normal cochain with a nonzero boundary in
the actual canonical differential-sheaf cohomology at the compatible
sparse seed. These two parameter specializations remain distinct. The compatible
concurrent continuation below supplies the actual canonical sheaf and
nonzero trace at the literal parameter as well; identifying the normal
boundary with that literal canonical class is a subsequent step.

### The inverse-ideal lift and its actual boundary

[GeometricCartierNormalLift.lean](GeometricCartierNormalLift.lean)
works in the actual surface ring \(A=P/(F,h)\), with curve ideal
\(K=(f_1,f_2,h)A\). On \(D(g_1)\), the ideal is generated by
\(f_2\); on \(D(g_2)\), it is generated by \(f_1\). The generators
are nonzerodivisors on their respective localizations, proved using the
existing ambient regular sequences. Their inverse-ideal homomorphisms
are actual maps from the localized ideal into the surface ring.

For an ambient variation \(A_{\mathrm{test}}\) and a cubic variation
\(L\), `inverseIdealConnectingLift` is a homomorphism on the actual
overlap ideal. The theorem `reducedInverseIdealConnectingLift_eq`
proves that its reduction is precisely the previously fixed relative
normal representative. Thus the construction retains every defining
equation value and its sign.

Order the four surface opens by \(g_1,g_2,f_1,f_2\), and put
\(B=kL-A_{\mathrm{test}}\) in the surface quotient. The scalar
two-cochain has faces
\[
c_{012}=\frac{B}{g_1f_1},\qquad
c_{013}=-\frac{B}{g_2f_2},\qquad
c_{023}=c_{123}=0.
\]
Each nonzero face is obtained by evaluating the same actual inverse-ideal
lift on an invertible curve equation and dividing by that equation. The
alternating cocycle identity follows from agreement of these evaluations
on the quadruple overlap. The specialization \(r=57,\theta=1,L=0\)
retains the negative sign on the first face.

The file also proves that these four opens cover every relevant surface
prime when \(r\ne0\). When additionally \(\theta\ne0\), their
defining ideal has the same radical as the ideal of the three coordinate
functions \(x_1,x_2,x_3\). Both directions are proved from the literal
equations, with actual power-membership consequences. The literal
\((57,1)\) corollary has no assumed cover hypothesis. This radical
comparison alone does not assert an isomorphism of Čech cohomology groups.

### The literal surface coordinate diagram and finite free exactness

[GeometricSurfaceCoordinates.lean](GeometricSurfaceCoordinates.lean)
extracts the original incidence equations, quotient definitions, and
finite-basis and Laurent calculations without changing their definitions
or moved proof bodies. At \(\theta=1\), `seedRingEquiv` identifies
the actual surface ring with the original `SeedRing` by the identity on
all five polynomial coordinates. Its localization equivalences preserve
every polynomial fraction and commute with the actual restriction maps,
including at \(r=57\).

Over \(R=\mathbb C[x_1,x_2,x_3]\), the actual surface ring has the
nine-element basis
\[
\{x_0^a w^b:0\le a<3,\ 0\le b<3\}.
\]
The construction proves this basis from the original two monic equations
and polynomial division. `surfaceBasis_apply` identifies each vector with
its literal quotient-ring monomial; `literal_surface_rank_nine` gives
the rank at \((57,1)\).

The new `firstCech_exact` theorem applies to any specified finite basis of
an actual \(R\)-module. It proves that every one-cocycle on the three
coordinate localizations is the difference of actual local sections.
The proof uses the canonical tensor-localization restriction maps and
the existing Laurent-coefficient contraction. This is the free-module
exactness needed for the proposed inverse-ideal argument. It does not
assume or establish that the actual inverse ideal has such a basis;
that identification and its localization comparison are the next steps.

### A genuine nonzero canonical-cohomology boundary

[GeometricCanonicalCechBoundary.lean](GeometricCanonicalCechBoundary.lean)
proves naturality of the actual Mayer–Vietoris connecting map under an
additive sheaf morphism. It applies that naturality to the already proved
canonical differential-sheaf isomorphism, retaining the actual restricted
inverse frame and its orientation. The paired relative-normal coefficient
is exactly the degree-nine homogeneous overlap fraction, so its actual
derived boundary is the previously constructed degree-nine canonical
class.

At \(r^3=2,\theta=0\), take
\(A_{\mathrm{test}}=x_2x_3^3w\), \(L=0\), and
\(\sigma=x_0^3\). The paired numerator after \(w=-x_2^2\) is
\(x_0^3x_2^3x_3^3\). Its fixed finite trace is
\[
\tau(x_0^3x_2^3x_3^3)=\frac{1+i}{6}\ne0.
\]
The theorem `ambientNormalCanonicalBoundary_ne_zero` therefore proves a
nonzero class in actual \(H^1(C_{r,0},\Omega^1_{C_{r,0}/\mathbb C})\),
obtained from that specific normal cochain and the actual connecting map.
It has no supplied nonvanishing or desired-comparison hypothesis.

### Verification and remaining comparison

The three helpers above were compiled from their exact source. The
independent kernel replays and selected axiom audits use only
`propext`, `Classical.choice`, and `Quot.sound`. A stale compiled
dependency containing the original locations of the extracted seed
definitions was detected by the combined import check; the exact eleven
affected modules were rebuilt and independently replayed. Validation now
checks transitive source and build inputs, as well as each helper itself.
The older aggregate chain and the protected endpoint are not claimed to
have passed a complete build. Four declaration-free assembly wrappers are
inlined into their importers to accommodate both concurrent continuations
within the proposal file limit; their sole imports and all declarations
are preserved.

The next algebraic obligations are the actual free basis and Frobenius
duality for the inverse ideal, its localization comparison, and the
comparison of the four-open boundary with the character-one coordinate
Čech quotient. The actual surface adjunction and canonical-section
comparisons remain separate geometric obligations. None of the results
in this section supplies the moving-cycle, geometric variation, supported
correspondence, or algebraic de Rham comparisons needed to close the final
existence theorem.

## Canonical sheaf and trace on the actual incidence curve — 14 November 2026

The final admission, `Submission.missing_geometric_existence`, remains
open. This continuation works on the same literal incidence member
\((r,\theta)=(57,1)\) of the incidence calculation. It constructs
the actual canonical-sheaf comparison and gives a single complex trace
coordinate for the complete existing degree-one Čech quotient. These
results do not yet provide the moving-cycle and global support argument
needed for exactness of the protected residue form.

### Actual affine derivations and the projective canonical sheaf

[GeometricLocalizedDifferentials.lean](GeometricLocalizedDifferentials.lean) and
[GeometricAffineDifferentialSheaf.lean](GeometricAffineDifferentialSheaf.lean)
construct the derivative of genuine regular functions on every affine
open. Given a ring-linear frame of the actual Kähler module, they prove
that the associated differential sheaf is isomorphic to the structure
module sheaf. The proof constructs both maps and proves the inverse
identities using the sheaf differential universal property. No premise
asserting extension of local derivations or a sheaf comparison is needed.

[GeometricTwistedDifferential.lean](GeometricTwistedDifferential.lean) carries
these constructions through an actual affine open immersion. The
coefficient map is defined independently as a morphism into the genuine
direct image of the affine structure module. On each subopen of the
chart image it becomes a linear map to the original structure-sheaf
sections. Its derivative formula, restriction compatibility, and value
one on the normalized frame are proved. Every sheaf-valued derivation
reconstructs from its coefficient and the actual frame on every such
subopen.

[GeometricProjectiveAffine.lean](GeometricProjectiveAffine.lean),
[GeometricProjectiveAffineCoefficients.lean](GeometricProjectiveAffineCoefficients.lean),
and [GeometricProjectiveOverlap.lean](GeometricProjectiveOverlap.lean)
give the complex-algebra coordinate presentations, actual scheme maps
over \(\operatorname{Spec}\mathbb C\), and actual homogeneous-overlap
restrictions. [GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean)
identifies the section maps induced by those open immersions with the
previously specified projective coordinate maps. The induced maps on
universal differentials agree on every differential, by the universal
property and generation by coordinate differentials.

The full-overlap canonical calculation is now parameterized by the
two actual unit Jacobian ideals in
[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean).
[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean)
discharges these hypotheses at \((57,1)\), using the existing exact
integral identities and the same three signed cofactors as the whole-chart
Kähler construction. Thus the Jacobian certificates and Čech calculation concern the same curve.

The differential and section-comparison parts of
[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean) place the normalized forms in the genuine projective differential sheaf.
Their transition is
\[
\eta_2=(x_2/x_1)\eta_1.
\]
[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean)
proves that restriction to the original quartic-denominator Čech cover
gives exactly the previously constructed transition unit. The equality
holds for actual structure-sheaf sections and actual differential-sheaf
restrictions.

[GeometricTwistedDifferential.lean](GeometricTwistedDifferential.lean) glues
the two frames and two coefficient derivations into module-sheaf morphisms
and proves the two inverse identities.
The coefficient transition follows by applying the independently defined
first-chart coefficient map to the frame transition. Its normalization
is established before gluing, so the argument is not circular.

[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean) supplies the
actual specialization. The generic construction also requires \(r\ne0\);
this and both Jacobian hypotheses are discharged at \((57,1)\). Its
`incidenceCanonicalSheafIso` is an isomorphism
\[
\mathcal L_{57,1}\;\simeq\;\Omega^1_{C_{57,1}/\mathbb C}
\]
between the existing degree-one module sheaf and the existing genuine
differential sheaf. The forward map is the explicitly constructed
`incidenceCanonicalSheafMap`. Every chart, coefficient map, frame,
transition, reconstruction identity, and inverse normalization in this
application is constructed from the specified incidence curve.

The same file transports this isomorphism through the genuine derived
cohomology functor. Its `incidenceDegreeOneToCanonicalH1` composes the
existing Mayer–Vietoris injection with the induced additive equivalence
on derived first cohomology. This map is injective, and a Čech class maps
to zero exactly when it was zero in the original quotient. The
normalization described below therefore gives a nonzero element of the
actual differential-sheaf \(H^1\) on this same literal curve.

### The complete Čech quotient is a complex line

[GeometricIncidenceCechTrace.lean](GeometricIncidenceCechTrace.lean)
equips the original degree-one Čech quotient with its natural complex
scalar structure, coming from the actual localization modules. It then
proves that the complete quotient on the original two-open cover at
\((57,1)\) is a complex line. The proof includes arbitrary pole orders.

There are three substantive steps. First,
[GeometricIncidenceTraceData.lean](GeometricIncidenceTraceData.lean)
contains exact characteristic-zero identities reducing the 32 normal
degree-nine monomials to multiples of \(x_3^9\). The trace module applies
these identities to the actual polynomial quotient. It proves that every
coordinate kills the spanning degree-nine class, so every homogeneous
polynomial of larger degree belongs to the actual four-generator ideal.
The localization argument then lowers arbitrary poles and shows that every
original Čech class is a scalar multiple of
\[
\xi=\left[\frac{x_3^9}{g_1g_2}\right].
\]

Second, [GeometricCurveRegularPair.lean](GeometricCurveRegularPair.lean)
now proves denominator regularity for every \(\theta\) and every
\(r\ne0\). Its comparison with two successive monic root algebras retains
the additional \(\theta x_0^3\) term of the actual incidence equation.
This supplies the converse all-poles kernel theorem: a degree-nine class
vanishes exactly when its numerator belongs to the four-generator ideal.

Third, the independent dual certificates in
[GeometricIncidenceTraceData.lean](GeometricIncidenceTraceData.lean)
prove that \(x_3^9\) does not belong to that ideal. The explicit degree-15
polynomial \(T\) defines the normalized functional
\[
\lambda(p)=\frac{1}{285}
 [x_0^3x_1^9x_2^3x_3^9]\bigl(Tp\bigr).
\]
Four polynomial identities, together with the fixed quartic rescalings,
show that multiplication by \(T\) sends each
actual generator into
\((x_0^4,x_1^{10},x_2^4,x_3^{10})\). Ideal induction therefore proves
\(\lambda\) vanishes on arbitrary ideal elements, while direct coefficient
extraction gives \(\lambda(x_3^9)=1\). The finite matrix calculation was
used to discover these certificates; their validity is established by
ordinary Lean proofs of the polynomial identities.

Combining these steps constructs a complex-linear equivalence
\[
\mathbb C\;\simeq\;\mathrm{DegreeOneCech}(57,1)
\]
and proves `Module.finrank ℂ (DegreeOneCech 57 1) = 1` in
`incidenceCech_finrank`. This nonvanishing argument is independent of the
older source-only cone and incidence-tangent continuation.

The same trace module binds the original derivative numerator and the
original nine-parameter cubic family to these actual quotient classes.
For every \(v\in\mathbb C^9\) it proves
\[
\operatorname{pairedDegreeOneClass}(57,1,v)
 =\frac{12+24i}{5}\,
   \operatorname{derivativeTrace}(1,v)\,\xi,
\qquad
\operatorname{derivativeTrace}(1,v)
 =\frac{i v_1-(1+i)v_8}{6}.
\]
Since the constant and \(\xi\) are nonzero, the paired class is zero
exactly when the computed derivative trace is zero. The injection into
genuine differential-sheaf cohomology preserves this zero criterion.
The definitions of the cubic columns, deformation, derivative numerator,
and trace row are relocated unchanged from the older aggregate files.
No separately chosen trace-one cubic is presented as the fixed-sextic
incidence tangent.

These results still do not assert that the Čech injection is surjective
onto all derived \(H^1\), or identify the coefficient functional with a
geometric Serre trace. The actual Serre pairing and the family-level
moving-cycle comparison remain separate mathematical obligations.

### A compatible seed with full gradient rank

[GeometricCanonicalSheaf.lean](GeometricCanonicalSheaf.lean)
provides an explicit member with the required Jacobian ranks for the
threefold, surface section, and curve together. With \(r^3=2\) and \(b=x_0^3+x_2^3\), it proves the
factorization into the specified incidence equations and proves nonzero
gradient or full normal-gradient rank at every nonzero point satisfying
the respective equations, over every relevant field extension. The statements are bound to the actual
evaluated polynomials and their partial derivatives. This gradient-rank
witness is a separate member of the parameter family; the rank-seven
Noether–Lefschetz obstruction and rank-eight augmented derivative
conditions are not asserted at this
particular member. Their simultaneous occurrence still requires the
appropriate geometric open-locus and family arguments.

### Verification and remaining theorem

All 25 exact-source modules checked in this continuation compiled with
Lean 4.33.1 and mathlib commit
`0df444a360eaa60ab8c11dca51a86af692955474`, and passed independent
`leanchecker` replay. Source hashes were matched to successful compilation
receipts, and the resulting module hashes were matched to successful
replay receipts. The audited endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The six consolidated or extended
proof modules have the following scope.

| Verification scope | Modules |
| --- | --- |
| Genuine affine and projective differential comparison | `GeometricAffineDifferentialSheaf`, `GeometricTwistedDifferential`, `GeometricCanonicalSheaf` |
| Literal incidence Jacobian and the separate compatible gradient witness | The Jacobian and compatible-seed sections of `GeometricCanonicalSheaf` |
| Complete incidence Čech quotient and independent nonzero normalization | `GeometricCurveRegularPair`, `GeometricIncidenceTraceData`, `GeometricIncidenceCechTrace` |

The 14 modules from the concurrent sparse-seed canonical-sheaf continuation
are also recompiled and independently replayed against the merged affine
API. The four incoming normal/conormal modules and their changed shared
polynomial-input module are checked as well; their constructions and
explanation are preserved in the following checkpoint. Existing declaration namespaces are preserved. Consolidating the new
helper sources keeps the proposal at its 256-file limit; all 253 helper
modules pass the source-command and acyclic-import checks. An independent comparison of all 11 relocated public declarations
preserves their statements and fully qualified namespaces: ten declaration
bodies are byte-identical, and the remaining proof invokes an existing
homogeneity theorem with the same conclusion. The older aggregate modules
were not rebuilt; source preservation is distinct from compilation of
those source-only continuations.

This is verification of the stated continuation, not a successful full
solve. The final source still contains one admission, and the entire older
geometric dependency chain has not been validated as a closed proof of
`Submission.certificate`.

The protected polynomial target, manifest, and final admission are
unchanged. The concurrent normal-module construction below supplies the
intrinsic relative-normal comparison and its literal connecting coefficient.
The remaining proof must identify its projective graded normal-sheaf
boundary and cup product with the canonical differential class, establish
the geometric Serre pairing on the incidence family, and construct
the moving curves and their nonzero Abel–Jacobi image, establish the
geometric variation and supported correspondence, and carry that support
statement through the actual Leray and algebraic de Rham comparisons.
Only then does the existing residue-to-certificate bridge remove the
admission. Classical choice in the checked local and linear constructions
does not supply any of those missing geometric statements.

This continuation follows the Diamond argument credited below and was
prepared for `fqlx` with OpenAI ChatGPT assistance. It preserves the
concurrent canonical-sheaf and homogeneous-chart continuations below.

## Actual relative conormal modules and the normal connecting cochain — 14 November 2026

The final admission, `Submission.missing_geometric_existence`, remains
open. This continuation identifies the existing normal obstruction with
the normal module of the curve inside its actual containing surface.
It preserves the original local lifts and their difference, including
the sign of the ambient-test coefficient. The concurrent canonical
differential-sheaf comparison in the next section is retained.

### The actual quotient ideal and its conormal dual

Let \(P\) be the original polynomial ring in the five weighted variables,
\(I=(f_1,f_2,h)\) the curve ideal, and \(J=(F,h)\) the surface ideal, where
\[
F=f_1g_1+f_2g_2+hk.
\]
The identity proves \(J\subseteq I\). Write \(A=P/J\) and let
\(K=I A\) be the actual ideal of the curve in this surface ring.

[GeometricRelativeConormal.lean](GeometricRelativeConormal.lean)
constructs the canonical surjection \(I/I^2\to K/K^2\), proves that its
kernel is the image of \(J/J^2\), and retains this exactness after scalar
extension. Dualizing gives an actual linear equivalence
\[
\operatorname{Hom}_S\!\left(S\otimes_A K/K^2,S\right)
\;\simeq_S\;
\ker\!\left(
\operatorname{Hom}_S(S\otimes_P I/I^2,S)
\longrightarrow
\operatorname{Hom}_S(S\otimes_P J/J^2,S)
\right).
\]
This uses the quotient ideal and the natural conormal map. No regularity
or smoothness premise is required for this comparison. An evaluation
theorem identifies its inverse on every literal ideal class.

[GeometricSeedNormalIdeals.lean](GeometricSeedNormalIdeals.lean)
specializes the construction to the original equations, with both
parameters \(r,\theta\) retained. The actual curve coefficient maps on
the \(g_1\)-open, \(g_2\)-open, and their intersection factor through
\(P/(F,h)\). The file constructs these algebra actions and their scalar
towers. Its `normalModuleEquiv` identifies the relative normal module
with the kernel of the existing `naturalNormalMap`, preserving the values
on \(f_1,f_2,h\). The literal \((r,\theta)=(57,1)\) specialization is
stated explicitly.

### The existing connecting representative retains its geometric values

[GeometricSeedConormalBases.lean](GeometricSeedConormalBases.lean)
extracts the original monic-regularity arguments and conormal bases into
an independently checked helper. The original polynomial definitions,
monomial orders, regular sequences, basis vectors, and theorem names are
preserved.
[GeometricNormalConnecting.lean](GeometricNormalConnecting.lean)
similarly contains the original genuine normal lifts, their natural
restriction maps, the normal-kernel trivializations, and the actual
two-open Čech quotient. These declarations keep their original namespaces
and are imported by the old aggregate modules.

The new `relativeConnectingRepresentative` applies the proved quotient
comparison to the existing difference of local lifts. Its image under
that comparison is exactly `connectingRepresentative`, and its values
on the three equation classes are
\[
\frac{kL-A}{g_1g_2}\,(g_2,-g_1,0).
\]
For the original ambient test with fixed cubic, \(L=0\), the coefficient
is \(-A/(g_1g_2)\), with the actual localization units. The theorem
`literal_ambient_test_comparison` binds this same representative at
\((57,1)\); it does not replace this parameter by a cube root of two.

### Verification and next comparison

The four helpers above were compiled from their exact final source and
independently replayed with `leanchecker`. Their audited endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`. The old aggregate
modules import the extracted declarations. The moved proof of
`ambientCurveMap_f1` now proves the same substitution identity directly,
removing its dependency on an unrelated relation-list lemma; its statement
and maps are unchanged. This continuation does not claim a complete build
of the older aggregate dependency chain.

The next step constructs the inverse-ideal extension on the surface and
its actual boundary cochain, then compares that cochain with the existing
character-one surface Čech quotient. The normal-module equivalence alone
does not supply this boundary map, its nonvanishing, or a geometric trace.
The moving-cycle, variation, supported-correspondence, and algebraic de
Rham comparisons remain further obligations of the nonconstructive route.

## Earlier checkpoint: canonical differential sheaf and its nonzero class — 14 November 2026

The final admission, `Submission.missing_geometric_existence`, remains
open. The present continuation closes the canonical differential-sheaf
comparison at the compatible sparse seed. For every complex number
\(r\) with \(r^3=2\), it constructs an actual isomorphism of sheaves of
structure-ring modules
\[
\Omega^1_{C_{r,0}/\mathbb C}\;\simeq\;\mathcal L_{r,0},
\]
where the left side is the previously constructed universal differential
sheaf on the actual projective curve and the right side is the existing
degree-one twisted sheaf. The proof has no extra chart, comparison,
transition, or global-bijectivity hypotheses. It also transports the
previously checked nonzero derived class into actual
\(H^1(C_{r,0},\Omega^1_{C_{r,0}/\mathbb C})\).

This checkpoint preserves the separately published literal-incidence-seed
continuation at \((r,\theta)=(57,1)\), recorded in the parallel section
below. Its Jacobian-cover and minor-localized transition results have a
different parameter specialization from the isomorphism proved here.

### Actual affine charts and their complex structure

[GeometricProjectiveAffine.lean](GeometricProjectiveAffine.lean)
identifies each coordinate homogeneous localization with the literal
dehomogenized quotient ring. Its inverse identities hold on every
homogeneous fraction, not only on coordinate generators. This supplies
actual scheme isomorphisms for the first and second affine curve charts,
their two-open cover when \(r\ne0\), and the inclusions from the original quartic
denominator opens. Both parameters \(r,\theta\) are retained in these
chart identifications.

[GeometricProjectiveAffineCoefficients.lean](GeometricProjectiveAffineCoefficients.lean)
proves that these scheme maps are over \(\mathbb C\), with exactly the
coefficient map used by the differential sheaf.
[GeometricProjectiveOverlap.lean](GeometricProjectiveOverlap.lean)
identifies both affine localizations with the same actual projective
overlap. Its change of coordinates is the previously constructed
substitution \((a,b,c)\mapsto(a/b,1/b,c/b)\), and both restriction
squares commute as scheme maps and as maps of actual section rings.
[GeometricProjectiveTransition.lean](GeometricProjectiveTransition.lean)
then proves that the unit \(x_2/x_1\) on this coordinate overlap
restricts to exactly `projectiveTransitionUnit` on the original
quartic overlap. This is an equality of units in the actual section ring.

### Affine frames as genuine sheaf isomorphisms

[GeometricLocalizedDifferentials.lean](GeometricLocalizedDifferentials.lean)
extends an ordinary Kähler frame through an actual localization and
proves its fraction formula, naturality, and compatibility with iterated
localization. In particular the coefficient derivation satisfies
\[
\delta(a/b)=\frac{b\,\delta(a)-a\,\delta(b)}{b^2}.
\]
[GeometricAffineDifferentialSheaf.lean](GeometricAffineDifferentialSheaf.lean)
uses this formula in prime localizations to differentiate genuine regular
sections. The derivative is again locally a fraction. This gives a
natural derivation on all affine opens, rather than a separately assumed
sheaf derivation.

The same file proves that a sheaf-valued derivation on an affine scheme
is determined by its values on the global affine ring. Therefore an
ordinary frame \(e:\Omega^1_{A/\mathbb C}\simeq_A A\) gives a genuine
module-sheaf isomorphism on \(\operatorname{Spec}A\). Its inverse is
multiplication by the image of \(e^{-1}(1)\) under the actual universal
differential. Both inverse identities are proved.

[GeometricDifferentialRestriction.lean](GeometricDifferentialRestriction.lean)
proves that the projective differential sheaf restricted to the over-site
of an open still has the universal property for complex derivations. The
lift and its uniqueness come from the actual restriction/direct-image
adjunction and the global universal differential.
[GeometricAffineChartSections.lean](GeometricAffineChartSections.lean)
constructs the equivalence between that over-site and the affine chart's
open site, together with the natural isomorphism of actual section rings.
[GeometricDerivationTransport.lean](GeometricDerivationTransport.lean)
transports module-valued derivations through this data.

[GeometricDifferentialChartTransport.lean](GeometricDifferentialChartTransport.lean)
combines these constructions into `chartFrameIso`: a genuine isomorphism
from the restricted projective differential sheaf to the structure module.
It proves the inverse-one formula on the whole chart and on every
subopen. [GeometricProjectiveChartSections.lean](GeometricProjectiveChartSections.lean)
identifies the terminal section maps with the literal first and second
chart-ring equivalences, so these frames use the same affine forms as
the earlier cofactor calculation.

### The global canonical comparison

[GeometricSheafKaehlerMap.lean](GeometricSheafKaehlerMap.lean) constructs
the ordinary Kähler lift into actual sheaf sections along a compatible
ring map. Its restriction, scalar, coordinate-change, and module-morphism
identities are proved on all Kähler forms.
[GeometricProjectiveDifferentialForms.lean](GeometricProjectiveDifferentialForms.lean)
uses these maps to carry the checked whole-overlap cofactor identity into
the actual projective differential sheaf. With the negative orientation
on the first affine frame and the positive orientation on the second,
the resulting sections satisfy
\[
\eta_2\big|_{U_1\cap U_2}
=\left(\frac{x_2}{x_1}\right)
 \eta_1\big|_{U_1\cap U_2}.
\]
Their further restrictions to the original denominator cover have
precisely the previously constructed transition unit.

[GeometricSheafLocalIso.lean](GeometricSheafLocalIso.lean) proves actual
two-open gluing of additive local isomorphisms from sheaf unique gluing.
[GeometricModuleLocalIso.lean](GeometricModuleLocalIso.lean) proves
scalar compatibility and obtains an isomorphism of module sheaves.
[GeometricModuleOverFrame.lean](GeometricModuleOverFrame.lean) evaluates
an over-site frame on every subopen, and
[GeometricCanonicalGluing.lean](GeometricCanonicalGluing.lean) shows that
the single overlap identity between frame generators glues to the
existing twisted module sheaf. No global bijectivity is supplied as input.

The final concrete assembly is
[GeometricProjectiveCanonical.lean](GeometricProjectiveCanonical.lean):

```lean
projectiveCanonicalIso (r : ℂ) (hr : r ^ 3 = 2) :
  projectiveDifferentialSheaf r 0 ≅ degreeOneModuleSheaf r 0
```

It identifies both local generators with the actual cofactor sections,
uses their proved overlap identity, and applies the existing actual
two-open cover. The isomorphism is in the category of sheaves of modules
over the original projective structure sheaf.

### The normalized class in differential-sheaf cohomology

[GeometricProjectiveCanonicalH1.lean](GeometricProjectiveCanonicalH1.lean)
applies Mathlib's actual cohomology functor to this sheaf isomorphism.
Consequently the original Mayer–Vietoris injection now gives
\[
\mathrm{DegreeOneCech}(r,0)
\hookrightarrow H^1(C_{r,0},\Omega^1_{C_{r,0}/\mathbb C}).
\]
The class of the normalization numerator \(x_0x_1^8\), with the original
denominator \(g_1g_2\), is nonzero in this actual derived cohomology
group. The map from its complex coefficient to the derived class is
injective. For every homogeneous degree-nine numerator, the transported
class is zero exactly when the already checked finite trace is zero.

That checkpoint did not assert surjectivity of the Čech comparison, an isomorphism
from all derived cohomology to \(\mathbb C\), or identification with a
geometric Serre trace. At that stage the construction had only the proved additivity
and injectivity.

### Verification and the remaining obligation

All nineteen new Lean modules in this continuation have been compiled
from their final source and independently replayed by `leanchecker`.
The audited public endpoints depend only on `propext`, `Classical.choice`,
and `Quot.sound`. The new files contain no admissions, added axioms,
unsafe evaluation, or executable extensions. The protected target,
submission manifest, and existing final admission are unchanged.

The whole proposal is still a draft: the final theorem retains its
`sorry`, and the older aggregate incidence dependency chain has not
passed a complete compilation. The local successful checks reported here
do not claim full-proposal acceptance.

At that stage the next cohomological gap was the actual first-cohomology vanishing on
the two affine denominator opens, together with the required comparison
between ambient-site `H'` and cohomology of a restricted sheaf. The
existing Mayer–Vietoris sequence would then make the Čech injection
surjective. The pinned Mathlib has the actual affine quasi-coherent
equivalence, but that equivalence alone does not compute `Ext` in the
category of all additive sheaves used by the current `H'` definition.

After that seed-curve calculation, the nonconstructive existence route
still requires the geometric trace and moving-cycle interpretation,
the relevant variation and supported correspondence, and the regular
algebraic de Rham comparison bound to the protected residue. These are
substantive remaining constructions; the canonical-sheaf isomorphism
does not itself prove exactness of the final rational residue form.
The earlier checkpoint descriptions below record their status before
this continuation.

## Parallel checkpoint: homogeneous chart comparisons and the literal seed cover — 14 November 2026

The single admission in `Submission.missing_geometric_existence` remains
open. This continuation connects the affine equations and differential
calculations to the actual homogeneous localization rings of the projective
curve. It also proves the Jacobian cover at the literal incidence seed
\((r,\theta)=(57,1)\). The projective cohomology, sparse-seed smoothness, and canonical-frame
results are preserved, with a shared set of projective and sheaf
definitions. The preceding checkpoint proves the global canonical
comparison at the separate sparse seed.

### The projective coordinate opens have the stated affine equations

[GeometricDehomogenizedCharts.lean](GeometricDehomogenizedCharts.lean)
constructs mutually inverse ring homomorphisms between the degree-zero
homogeneous localization at a coordinate and the quotient by the two
dehomogenized curve equations. One map substitutes the inverted coordinate
as one. Its inverse evaluates the remaining coordinates at their actual
homogeneous ratios. Homogeneity proves the inverse identity on every
homogeneous fraction, without a domain or smoothness hypothesis.

The first and second specializations are exactly the previously defined
`ChartRing ![firstQuadric r, firstCubic theta]` and its second-chart
counterpart. Constants and coordinate generators are bound explicitly.
[GeometricAffineProjectiveCharts.lean](GeometricAffineProjectiveCharts.lean)
composes these equivalences with Mathlib's `Proj.basicOpenIsoSpec` and
`Proj.basicOpenIsoAway`. It obtains isomorphisms of the actual coordinate
open schemes with the spectra of these equation rings, and equivalences
of their actual rings of structure-sheaf sections.

[GeometricCurveCover.lean](GeometricCurveCover.lean) extracts the original
`CycleQ2SeedTwoOpenCover` calculation from `SolutionSupport07Part03`.
The original support module imports the same public declarations. This
retains the homogeneous relevant-prime cover used by the older cone
construction; the projective scheme also has the independently proved
cover in [GeometricProjectiveCharts.lean](GeometricProjectiveCharts.lean).

### Actual differentials on actual projective minor intersections

[GeometricKaehlerResidue.lean](GeometricKaehlerResidue.lean) identifies the
actual gradient-row quotient with the universal Kähler module on the same
Jacobian localization. The equivalence is proved to be the quotient map
sending coordinate-vector classes to their universal differentials. Its
normalized residue generator is the free-coordinate differential divided
by the actual inverted Jacobian minor. The independent comparison in
[GeometricCofactorKaehler.lean](GeometricCofactorKaehler.lean) is retained.

[GeometricProjectiveResidueTransition.lean](GeometricProjectiveResidueTransition.lean)
works in the actual degree-zero homogeneous localization at \(x_1x_2\),
for arbitrary complex \(r,\theta\). Its two affine maps are the proved
chart inverses followed by genuine homogeneous-localization restrictions.
With
\[
(a,b,c)=(x_0/x_1,x_2/x_1,x_3/x_1),\qquad
(A,B,C)=(a/b,1/b,c/b),
\]
it constructs the unit \(b=x_2/x_1\), the actual quotient map induced by
the coordinate Jacobian, and its compatibility with universal differentials.
The raw residue coefficient transforms by \(-b\); the projective deletion
signs give the oriented factor \(+b\). These coefficient and differential
identities use the actual equation gradients and their vanishing
relations. The normalized formula in this module requires the selected
minors to be units in the comparison ring.

[GeometricMinorResidueTransition.lean](GeometricMinorResidueTransition.lean)
places the normalized identity on its actual domain. It localizes that
homogeneous overlap at the product of an arbitrary first-chart minor and
an arbitrary second-chart minor, constructs both unit witnesses there,
and transports universal differentials using `KaehlerDifferential.map`.
The oriented normalized differentials then differ by the actual ratio
\(x_2/x_1\), with no extra unit or smoothness premise. This is an equality
in the Kähler module of the specified localized ring. For this
arbitrary-parameter, minor-localized construction, gluing to a global
canonical-sheaf identification remains a further step.

This construction is complementary to the full-overlap sparse-seed
identity in [GeometricCanonicalOverlap.lean](GeometricCanonicalOverlap.lean):
it uses the homogeneous projective overlap directly and retains both
parameters, including the literal incidence seed.

### Jacobian presentations cover both literal-seed affine charts

[GeometricSeedCurveGradientArithmetic.lean](GeometricSeedCurveGradientArithmetic.lean)
contains the original exact integral certificate, extracted unchanged
from `SolutionSupport07Part01`. Its coefficients, namespace, identities,
and existing proof budgets are retained.
[GeometricAffineJacobianCover.lean](GeometricAffineJacobianCover.lean)
uses its first- and second-coordinate certificates at the explicit
parameters \((57,1)\). Euler identities eliminate the minors involving
the deleted homogeneous coordinate. In each actual affine quotient, the
two defining equations vanish, and the certificate puts a nonzero complex
integer in the ideal of the remaining Jacobian minors. The ideal is
therefore the unit ideal in each of the two chart rings.

The theorems `first_prime_presentation_cover` and
`second_prime_presentation_cover` make the connection to the existing
presentations precise: every prime avoids
`(chartPresentation v e).jacobian` for some ordering \(e\) of the three
coordinates. Thus the actual Jacobian basic opens cover both affine
charts; nonsingularity is not supplied as a premise. This literal seed
is distinct from the \(r^3=2,\theta=0\) seed used for the trace and
whole-chart canonical-frame calculations in the sparse-seed checkpoints.

### Verification of this continuation

Each of the eight new helpers linked in this section was compiled from its
final source bytes under Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`, and its compiled module was
independently replayed with `leanchecker`. The named endpoints were
separately audited and use only `propext`, `Classical.choice`, and
`Quot.sound`. Checks used one bounded compiler process at a time, with
unchanged memory, time, and proof budgets.

The two original support modules now import the extracted components.
Their namespace bodies were checked byte for byte against the originals;
the arithmetic constants and proof statements are unchanged. The common
projective and sheaf constructions share the reconciled definitions
used by the sparse-seed projective cohomology checkpoint.
The older incidence and cone dependencies have not been validated as a
complete build in this continuation. The full proposal still fails source
acceptance at the single admission in `Solution.lean`.

This continuation follows the Diamond argument credited below and was
prepared for `fqlx` with OpenAI ChatGPT assistance.

### Remaining geometric comparison

These additions leave the final existential statement unchanged. The
next comparison for the moving-cycle argument must construct the
actual effective-Cartier boundary
\[
H^1(C,N_{C/D})\longrightarrow H^2(D,\mathcal O_D),
\]
bind the ambient-test normal obstruction to the computed surface Čech
pairing, and prove naturality on the pointed incidence component.
The character-one projection and twisted orbit trace must be retained.
The existing persistence theorem cannot supply this class by choosing an
arbitrary nonzero vector.

The global differential-sheaf comparison at the literal incidence seed
and on the pointed family remains separate from the sparse-seed
canonical isomorphism proved above. The geometric Serre trace, moving-cycle
construction, geometric variation and supported projector, and actual
Leray and algebraic de Rham comparisons still require proofs.
The normal operator \(g^{-1}\partial_0\) is not a primitive construction:
it sends the defining equation to one and does not descend to the
function field. The final certificate continues to depend on the single
admitted existence theorem.

## Earlier checkpoint: projective cohomology and whole-chart differentials — 14 November 2026

The last admission, `Submission.missing_geometric_existence`, is still
open. This continuation connects the previously checked Čech calculation
to actual derived projective sheaf cohomology, proves nonsingularity at
the same sparse parameter, and constructs a normalized Kähler differential
on each entire affine curve chart. It also constructs the actual
projective differential sheaf and its universal property. The remaining
global canonical-sheaf, Serre, moving-cycle, and support comparisons are
not asserted as hypotheses-free theorems.

### A nonzero class in actual projective sheaf cohomology

The projective construction has been separated into a small checked
dependency chain. [GeometricProjectiveCharts.lean](GeometricProjectiveCharts.lean)
constructs the same quotient grading, projective scheme, and two quartic
denominator opens, and proves their cover directly from the curve
equations. [GeometricProjectiveFrames.lean](GeometricProjectiveFrames.lean)
constructs the actual degree-one frames and their transition unit.

The generic sheaf and module constructions are now independently checked
in [GeometricSheafHZero.lean](GeometricSheafHZero.lean),
[GeometricTwistedSheaf.lean](GeometricTwistedSheaf.lean), and
[GeometricTwistedModuleCore.lean](GeometricTwistedModuleCore.lean).
Their specialization in [GeometricTwistedModule.lean](GeometricTwistedModule.lean)
is a genuine sheaf of modules over the actual projective structure sheaf.
Its linear frames cover every point when \(r\ne0\). Forgetting the module
structure gives exactly the additive sheaf used for cohomology.

[GeometricProjectiveCech.lean](GeometricProjectiveCech.lean) proves that the
actual Mayer–Vietoris connecting map has precisely the image of the
first-minus-second restriction map as its kernel. It therefore gives an
injection
\[
\mathrm{DegreeOneCech}(r,\theta)
\hookrightarrow
H^1\bigl(\operatorname{Proj}R_{r,\theta},\mathcal L_{r,\theta}\bigr),
\]
where \(\mathcal L_{r,\theta}\) is the constructed degree-one additive
sheaf and the group on the right is Mathlib's derived sheaf cohomology.
The proof uses the genuine Mayer–Vietoris square and the natural
identification of its degree-zero cohomology with sections. It does not
assume affine acyclicity or assert surjectivity onto derived cohomology.

[GeometricProjectiveNonzero.lean](GeometricProjectiveNonzero.lean) combines
this injection with the checked all-poles trace calculation. For
\(r^3=2\) and \(\theta=0\), the map
\[
c\longmapsto
\delta\!\left[\frac{c\,x_0x_1^8}{g_1g_2}\right]
\]
into the actual projective \(H^1\) is injective, and its value at one is
nonzero. For every homogeneous degree-nine numerator, the resulting
derived class vanishes exactly when the existing finite trace vanishes.
This uses the same cube-root parameter throughout; it does not substitute
the literal complex number 57 for a cube root of two.

### Nonsingularity at the compatible sparse parameter

On the first chart \(x_1=1\), write \((a,b,c)=(x_0,x_2,x_3)\).
The equations at \(\theta=0\) are
\[
a^2-rc=0,\qquad
b^3+(a+1)bc+a+(1-i)c^3-i=0.
\]
When \(r^3=2\), eliminating \(c\) gives the trigonal equation
\[
2b^3+P_r(a)b+Q(a)=0,
\quad
P_r(a)=r^2a^2(a+1),\qquad
Q(a)=(1-i)a^6+2a-2i.
\]
[GeometricSparseCurveSmooth.lean](GeometricSparseCurveSmooth.lean) uses
its discriminant polynomial
\[
\begin{aligned}
\Delta(a)={}&54ia^{12}-8a^9-24a^8
+(-132+108i)a^7+(100+108i)a^6\\
&-108a^2+216ia+108.
\end{aligned}
\]
The file supplies explicit integer Gaussian polynomials \(U,V\) and
checks the exact identity
\[
U(a)\Delta(a)+V(a)\Delta'(a)
=24896592594665052428858199326354844000.
\]
Ordinary kernel-checked polynomial normalization proves this identity.
A common zero of the curve equation and its two partial derivatives
would force both \(\Delta\) and \(\Delta'\) to vanish, contradicting the
displayed nonzero constant. The second chart is handled by the actual
cofactor transformation on the overlap and a direct nonzero-minor
calculation where the overlap coordinate vanishes. Both conclusions
hold over every characteristic-zero field with \(i^2=-1\) and \(r^3=2\).

[GeometricSparseJacobianCover.lean](GeometricSparseJacobianCover.lean)
then proves that the three signed minors generate the unit ideal in each
literal affine quotient ring. If that ideal were proper, a maximal
quotient field would contradict the field-valued theorem. This also
gives the actual three Jacobian basic-open covers and shows that each
chart prime lifts to a prime of one of the existing Jacobian localizations.
No algebraic-closedness premise is required for the residue-field argument.

### A differential frame on each entire affine chart

For an arbitrary pair of affine equations \(v_0,v_1\),
[GeometricChartKaehler.lean](GeometricChartKaehler.lean) constructs
\[
R^3/(R\,dv_0+R\,dv_1)\;\simeq\;\Omega^1_{R/\mathbb C},
\qquad
R=\mathbb C[a,b,c]/(v_0,v_1),
\]
using the actual presentation cotangent sequence. The image of each
coordinate vector is its actual universal differential. This comparison
holds before any Jacobian minor is inverted and does not require
smoothness of the equation pair.

Let \(c_0,c_1,c_2\) be the signed minors. When their ideal is the unit
ideal, choose coefficients \(u_j\) with \(\sum_j u_jc_j=1\).
[GeometricGlobalResidue.lean](GeometricGlobalResidue.lean) proves that
\[
\eta=\sum_j u_j\,dx_j,\qquad dx_j=c_j\eta
\]
is a global frame of the gradient cokernel. The proof sums the three
polynomial Cramer identities. Its residue functional is an isomorphism
to \(R\), and \(\eta\) is the unique element with residue coefficient
one, so it is independent of the chosen Bezout coefficients. Combining
this with the actual cotangent comparison and the proved unit Jacobian
ideals gives genuine equivalences
\(\Omega^1_{R/\mathbb C}\simeq R\) and normalized differentials on both
entire sparse charts.

[GeometricAffineOverlap.lean](GeometricAffineOverlap.lean) constructs the
actual algebra equivalence on the coordinate overlap,
\[
(A,B,C)\longmapsto(a/b,1/b,c/b),
\]
and the induced map on universal Kähler differentials. It checks all
three cofactor transformations and the normalized differential transition
on the common middle-minor patch.
[GeometricGlobalAdjunction.lean](GeometricGlobalAdjunction.lean) extends
the cofactor-cokernel transition to the entire coordinate overlap: the
actual coordinate Jacobian induces a map whose residue functional scales
by \(-b\). The resulting whole-chart frames consequently transform by
\(-b\), or by \(+b=x_2/x_1\) after the projective orientation signs.

[GeometricCanonicalOverlap.lean](GeometricCanonicalOverlap.lean) proves
the same transition for the genuine differentials constructed above,
using the two actual homomorphisms from the original chart rings to the
common overlap. The chain rule and the three transformed cofactors show
that each second-chart minor annihilates the difference of the proposed
forms. Transporting their Bezout combination proves that the difference
is zero. Thus the actual whole-chart Kähler forms have the required
transition on the full overlap, with no additional minor inverted.

### The actual projective differential sheaf

[GeometricDifferentialSheaf.lean](GeometricDifferentialSheaf.lean)
constructs the sectionwise universal Kähler modules with their actual
restriction maps, then sheafifies this presheaf as a sheaf of modules
over the structure ring. It proves its universal property for
sheaf-valued complex derivations, including existence and uniqueness of
the induced sheaf morphism. The complex coefficient map on the actual
projective curve is obtained from its genuine structure morphism to
\(\operatorname{Spec}\mathbb C\).

[GeometricProjectiveCoefficients.lean](GeometricProjectiveCoefficients.lean)
proves that these global complex coefficients restrict, under the actual
projective chart-section isomorphism, to the canonical coefficient map
in the homogeneous localization. This holds on every positive-degree
homogeneous basic open, including all coordinate charts. Thus the complex
structure used for the differential sheaf agrees with the one in the
literal chart constructions.

This constructs the required differential-sheaf object. The global
identification with the checked degree-one module sheaf, compatibility
with the geometric Serre trace, and the subsequent moving-cycle and
support argument remain further obligations.

### Verification boundary

Every helper named in this continuation has been compiled from its exact
source bytes under the pinned Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`, and independently replayed with
`leanchecker`. The audited endpoints depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Checks used one bounded compiler
process at a time. The original cone and projective aggregate files now
import the extracted checked constructions; their remaining older
incidence dependencies have not been validated as a complete chain.

The protected target, manifest, and final admission are unchanged. These
results do not constitute a verified solve: the full proposal still
fails source acceptance because of that admission. Earlier sections
record the preceding stages and their verification boundaries. This
continuation follows the Diamond argument credited below and was prepared
for `fqlx` with OpenAI ChatGPT assistance.

## Checked local differentials and the actual Čech trace — 13 November 2026

The final theorem `Submission.missing_geometric_existence` remains admitted.
This continuation proves two further parts of the selected nonconstructive
argument: the local comparison with genuine Kähler differentials and a
unique trace coordinate on every homogeneous Čech class, with arbitrary
pole order. These results use the existing curve and localization objects.
They do not yet construct the global support and de Rham comparison needed
by the final theorem.

### The cofactor quotient maps isomorphically to actual differentials

[GeometricCofactorKaehler.lean](GeometricCofactorKaehler.lean) works with the
literal affine chart ring localized at a Jacobian minor. For an arbitrary
ordering \(e\) of the three coordinates, it constructs the linear map
\[
R^3/(R\,df+R\,dh)\longrightarrow\Omega^1_{R/\mathbb C},
\qquad [\mathbf e_j]\longmapsto d x_{e(j)},
\]
and proves that it is an isomorphism. The module on the right is Mathlib's
universal Kähler differential module of this same localized ring. The proof
obtains a basis from the actual submersive presentation and identifies its
pivot determinant with the cofactor inverted by the localization. Thus no
comparison map or freeness assertion is supplied as an extra hypothesis.

The resulting `kaehlerResidueEquiv` identifies the actual differential
module with \(R\). It sends \(dx_{e(j)}\) to the signed cofactor \(c_j\).
Whenever two cofactors are units in the same chart ring, it proves
\[
c_k^{-1}dx_{e(k)}=c_l^{-1}dx_{e(l)}.
\]
The first and second affine equation pairs used by the projective curve
are explicit specializations of this construction. The orientation is the
chosen coordinate ordering; the theorem does not silently identify
different chart rings or different orderings.

The supporting
[cofactor quotient calculation](GeometricCofactorResidue.lean) now compiles
after repairs to scalar and quotient-membership elaboration. The existing
[affine Jacobian charts](GeometricAffineCurveCharts.lean),
[coordinate-change determinants](GeometricAdjunctionOverlap.lean), and
[residue-frame identities](GeometricResidueFrames.lean) also compile and
pass independent kernel replay. In particular, the oriented adjunction
transition is the actual degree-one transition \(x_2/x_1\). Transport
between chart differential modules and global canonical-sheaf gluing
remain separate obligations.

### Every homogeneous Čech class has a degree-nine representative

This calculation uses the sparse curve at \(\theta=0\), with \(r^3=2\).
It retains the actual quartic denominators
\[
g_1=3r^2(x_1x_3)^2,\qquad g_2=3x_2^4
\]
in its coordinate ring. In
[GeometricCechPoleReduction.lean](GeometricCechPoleReduction.lean), the
existing finite trace relations first show that every coordinate
annihilates the normalization class \([x_0x_1^8]\). Factoring each monomial
of degree greater than nine into a degree-nine part and a positive-degree
part then proves that every homogeneous polynomial of degree greater than
nine belongs to the actual four-generator `reducedIdeal r`.

[GeometricCechSurjectivity.lean](GeometricCechSurjectivity.lean) applies this
ideal-membership theorem to arbitrary homogeneous overlap fractions. A
degree-one fraction with denominator \(g_1^ng_2^m\) has numerator degree
\(1+4(n+m)\). When both poles occur and \(n+m>2\), homogeneous coefficient
extraction produces a relation that lowers one pole order. Terms with only
one pole are genuine sections on one chart and hence Čech boundaries.
Induction reduces every class to a simple-pole fraction with a degree-nine
numerator. The existing trace reduction then gives
\[
\forall z\in\mathrm{DegreeOneCech}(r,0),\quad
\exists c\in\mathbb C,\qquad
z=\left[\frac{c\,x_0x_1^8}{g_1g_2}\right].
\]
This is `normalizedCechClass_surjective`. It concerns the original
first-minus-second quotient of the actual homogeneous localized modules,
with no bound on pole order and no substituted Čech model. Surjectivity
does not require a regular-pair hypothesis. On its own it does not assert
that the displayed normalization class is nonzero or identify the
coefficient with the geometric Serre trace.

### Concrete cancellation for the two actual denominators

[GeometricCurveRegularPair.lean](GeometricCurveRegularPair.lean) proves the
previously required regularity hypotheses on the literal curve ring
\(R_r=\mathrm{CurveRing}(r,0)\), for every \(r\ne0\): multiplication by
\(g_1\) is injective on \(R_r\), and multiplication by \(g_2\) is injective
on \(R_r/(g_1)\).

The proof constructs faithful comparison maps to two successive monic root
algebras over \(\mathbb C[x_1,x_3]\). Their quadratic and cubic equations
are precisely the two curve equations, so their power bases preserve
cancellation from the base. The same construction is carried out after
imposing \((x_1x_3)^2=0\); it retains the squared denominator rather than
replacing it with its radical. For the second denominator the controlling
binary polynomial is
\[
N_r(x,y)=\big((1-i)y^3-i x^3\big)^2-rx^5y.
\]
Neither \(x\) nor \(y\) divides \(N_r\). Prime-power cancellation shows
that \(N_rp\in(x^2y^2)\) implies \(p\in(x^2y^2)\). An explicit identity
\(x_2q=N_r\) in the monic tower then proves that \(x_2\), and consequently
\(3x_2^4\), is a nonzerodivisor in the required quotient.

The resulting `degreeNineCechClass_zero_iff_reducedIdeal` applies the
existing all-poles Koszul kernel theorem without additional regularity
assumptions. For every homogeneous degree-nine \(p\), it gives
\[
\left[\frac{p}{g_1g_2}\right]=0
\quad\Longleftrightarrow\quad
p\in\mathrm{reducedIdeal}(r).
\]
These results concern \(\theta=0\). They do not equate this curve with the
separate incidence calculation at literal \(r=57,\theta=1\).

### The finite trace now detects exactly the actual Čech class

[GeometricCechTrace.lean](GeometricCechTrace.lean) combines these concrete
regularity theorems with the finite normalized trace. For \(r^3=2\), it
proves
\[
\operatorname{degreeNineCechClass}_{r,0}(p)=0
\quad\Longleftrightarrow\quad
\operatorname{traceLinear}_r(p)=0.
\]
It also proves that two homogeneous degree-nine numerators give equal
actual Čech classes exactly when their traces agree. Since
\(\operatorname{traceLinear}_r(x_0x_1^8)=1\), the normalization class is
nonzero, and the earlier surjectivity becomes a bijection:
\[
\forall z\in\mathrm{DegreeOneCech}(r,0),\quad
\exists!c\in\mathbb C,\qquad
z=\left[\frac{c\,x_0x_1^8}{g_1g_2}\right].
\]
The theorem `existsUnique_normalizedCechClass` makes this uniqueness
explicit. All regularity premises are discharged for the actual ring;
the result allows arbitrary-pole boundaries. It supplies a unique scalar
coordinate on the original algebraic Čech quotient. Identifying that
quotient and coordinate with canonical-sheaf cohomology and its geometric
Serre trace is still a further comparison.

### Verification and remaining global obligations

The following nine modules were compiled from their final source bytes
under the pinned Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. Each compiled module also passed
independent `leanchecker` replay.

| Module | Compilation | Kernel replay |
| --- | ---: | ---: |
| `GeometricAffineCurveCharts` | 4.02 s | 3.04 s |
| `GeometricAdjunctionOverlap` | 5.23 s | 3.23 s |
| `GeometricCofactorResidue` | 4.23 s | 3.03 s |
| `GeometricResidueFrames` | 4.23 s | 3.85 s |
| `GeometricCofactorKaehler` | 16.88 s | 3.63 s |
| `GeometricCechPoleReduction` | 5.23 s | 3.83 s |
| `GeometricCechSurjectivity` | 48.19 s | 35.54 s |
| `GeometricCurveRegularPair` | 13.88 s | 3.62 s |
| `GeometricCechTrace` | 3.63 s | 5.63 s |

The audited endpoint declarations use only `propext`, `Classical.choice`,
and `Quot.sound`. Each check used one bounded compiler process; the largest
peak compiler memory among these modules was 3,849 MiB. No heartbeat limit
was increased. The explanation's local links and displayed mathematics
also pass the repository renderer and bundled KaTeX check.

These are targeted checks of the stated continuation. The full proposal
and the final certificate have not passed verification: source validation
still rejects the single unchanged admission in `Solution.lean`. The global
canonical-sheaf and Serre comparisons, the moving-cycle and Abel–Jacobi
interpretation, the geometric variation and supported correspondence, and
the smooth affine de Rham comparison remain necessary. In particular,
`AffineComparison` in [GeometricExistence.lean](GeometricExistence.lean)
still requires a geometric comparison and its injectivity as inputs.

This formal continuation follows the Diamond argument credited below and
was prepared for `fqlx` with OpenAI ChatGPT assistance.

## Kernel-checked algebraic continuation — 13 November 2026

The final theorem `Submission.missing_geometric_existence` remains admitted.
This continuation supplies checked algebraic steps for the selected Diamond
argument. It does not replace geometric hypotheses with axioms or assert a
completed certificate. The verification statements in this section apply to
the named modules; the full older geometric dependency chain has not
thereby been validated.

### A characteristic-zero seed from the modular calculation

[GeometricDiamondSeed.lean](GeometricDiamondSeed.lean) uses the actual maps
\(\mathbb Z[i]\to\mathbb F_{109}\), with \(i\mapsto33\), and
\(\mathbb Z[i]\hookrightarrow\mathbb C\). It proves
\[
p(57)\ne0\text{ in }\mathbb F_{109}
\quad\Longrightarrow\quad
\exists r\in\mathbb C,\quad r^3=2\quad\text{and}\quad p(r)\ne0
\]
for every polynomial \(p\in\mathbb Z[i][T]\). In particular, the modular
parameter is not substituted as the literal complex number 57 into a
statement requiring \(r^3=2\).

The proof obtains three distinct complex roots of \(T^3-2\) from two real
intermediate-value arguments and an explicit factorization. If \(p\)
vanished at all three roots, the factor theorem would make \(T^3-2\) divide
\(p\) over \(\mathbb C\). Monic divisibility descent gives the same
divisibility over \(\mathbb Z[i]\), contradicting reduction at 57.
Applying this argument to a product preserves any finite collection of
nonvanishing conditions at **one common** characteristic-zero root. The
matrix-family theorem includes determinants of different sizes and one
additional polynomial containing all cleared denominators.

[GeometricDiamondRank.lean](GeometricDiamondRank.lean) makes the transfer
usable directly from rectangular rank certificates. For a finite family
\(A_j(T)\) of Gaussian-polynomial matrices and a polynomial \(d\) nonzero
at the modular seed, it proves
\[
\exists r\in\mathbb C,\quad r^3=2,\quad d(r)\ne0,\qquad
\operatorname{rank}_{\mathbb F_{109}}A_j(57)
\leq\operatorname{rank}_{\mathbb C}A_j(r)\quad\text{for every }j.
\]
The proof uses the shared
[rank retraction](GeometricRankRetraction.lean): a rank-\(k\) matrix over a
field admits matrices \(C,B\) with \(CAB=I_k\). Lifting the entries of
these two matrices to constant Gaussian polynomials supplies a nonzero
square determinant. Thus the theorem needs no explicit pivot list or
preselected minor. The old faithful-specialization argument imports this
same extracted retraction theorem.

This result does not, by itself, transfer the complete incidence tangent
argument. In particular, the existing lower bound 7600 for the relation
matrix is proved at literal complex parameter 57. The corresponding
Jacobian upper bound needs a structural proof at the selected root or an
appropriate modular certificate before it can be combined with the lifted
lower bounds. The literal-57 seed is also a point of the full invariant
parameter family; using that separate route requires keeping its existing
geometric objects and the full-family argument consistently matched.

There is also a separate parameter issue: the current incidence matrix is
bound to `thetaH 1`, whereas the sparse reduced-ideal trace calculation is
at \(\theta=0\). Selecting a genuine cube root does not identify these two
curves. A spreading or comparison argument must reconcile their parameter
values before the corresponding rank and trace results can be combined.

### The actual localization boundary and its homogeneous witnesses

[GeometricKoszulKernel.lean](GeometricKoszulKernel.lean) works with the
genuine rings \(R_f\), \(R_g\), and \(R_{fg}\), and defines
\[
\delta:R\longrightarrow R_{fg}/(\operatorname{im}R_f+
  \operatorname{im}R_g),\qquad p\longmapsto[p/(fg)].
\]
If \(f\) is a nonzerodivisor on \(R\) and \(g\) is a nonzerodivisor on
\(R/(f)\), it proves \(\ker\delta=(f,g)\). Boundaries may have arbitrary
pole order. The proof clears both the section denominators and the extra
annihilator allowed by equality in a localization, then cancels powers
using the regular-pair hypotheses. It does not assume that the localization
maps are injective.

[GeometricGradedWitness.lean](GeometricGradedWitness.lean) proves homogeneous
coefficient extraction in a finite homogeneous ideal. For generators of
degrees \(2,3,4,4\), a degree-nine element has a relation
\[
p=a f_1+b h+c g_1+d g_2,
\qquad \deg(a,b,c,d)=(7,6,5,5),
\]
where degree means the appropriate homogeneous component, including the
zero polynomial. The construction projects an arbitrary ideal witness to
the required graded component; generators above the target degree receive
zero coefficients.

[GeometricHomogeneousBoundary.lean](GeometricHomogeneousBoundary.lean)
then proves the literal identity in the overlap of the two actual
localizations of \(R=K[x]/(f_1,h)\):
\[
\frac{\bar p}{\bar g_1\bar g_2}
=\operatorname{res}_1\!\left(\frac{\bar d}{\bar g_1}\right)
 +\operatorname{res}_2\!\left(\frac{\bar c}{\bar g_2}\right).
\]
The retained quintic numerators make both chart sections homogeneous of
degree one. For the first-minus-second convention, the chart pair is
\((\bar d/\bar g_1,-\bar c/\bar g_2)\). Thus an ungraded ideal relation
has the precise homogeneous witnesses needed by the projective Čech
construction. This forward identity needs no regular-sequence hypothesis.
The canonical-bundle and Serre-trace identifications are separate
geometric obligations.

[GeometricKoszulTrace.lean](GeometricKoszulTrace.lean) applies these witnesses
to the existing `degreeNineCechClass`, in the original first-minus-second
Čech quotient. Its forward theorem kills the class of every homogeneous
degree-nine element of the four-generator ideal. Under regularity of the
two quartic images on the curve ring and its first quotient, it also proves
the converse. At \(\theta=0\), the nonzero constants \(3r^2\) and \(3\)
identify that ideal with the existing `reducedIdeal r`, for \(r\ne0\).
Thus the criterion concerns the actual reduced seed quotient and retains
the homogeneous degree of its existing Čech class. The same module proves
that two homogeneous degree-nine polynomials representing the same reduced
quotient element have equal Čech classes, without a regularity hypothesis.

[GeometricTraceBoundary.lean](GeometricTraceBoundary.lean) now binds the
existing finite socle-trace calculation to this same homogeneous Čech
class. For \(r^3=2\) and a homogeneous degree-nine \(p\), it proves
\[
\operatorname{traceLinear}_r(p)=0
\quad\Longrightarrow\quad
\operatorname{degreeNineCechClass}_{r,0}(p)=0.
\]
The earlier finite calculation gives
\(p-\operatorname{traceLinear}_r(p)x_0x_1^8\in\mathrm{reducedIdeal}(r)\).
The new homogeneous boundary theorem applies directly when the trace is
zero, with \(r\ne0\) derived from \(r^3=2\). This bridge needs no
regular-pair hypothesis. It proves the displayed implication; it does not
identify the computed functional with a geometric Serre trace.

To check this application independently, the existing coordinate and
localization definitions were moved to
[GeometricCurveCoordinates.lean](GeometricCurveCoordinates.lean), and the
existing quotient grading, degree-one chart modules, and Čech class were
moved to [GeometricDegreeOneCech.lean](GeometricDegreeOneCech.lean). The
projective construction imports these same public definitions. The
quotient-grading implementation required an elaboration repair: the
componentwise decomposition now descends directly through the additive
quotient, with its scalar law proved on representatives. Its representative
formula and both decomposition inverse identities are retained and checked.
This extraction does not establish the later projective-sheaf or Serre
comparisons.

### Integral primitivity without assuming torsion-freeness

[GeometricIntegralPrimitive.lean](GeometricIntegralPrimitive.lean) uses the
actual tensor product \(\mathbb Q\otimes_{\mathbb Z}M\) and proves
\[
1\otimes x=0\quad\Longleftrightarrow\quad
\exists n\in\mathbb N,\quad n>0\quad\text{and}\quad nx=0.
\]
Consequently, the rational Gysin identities
\(j_*E=6q\) and \(j_*H=3q\) give a positive integer \(N\) such that
\(j_*(N(E-2H))=0\) integrally. The same \(N\) preserves every nonzero
additive observable valued in a rational vector space, as well as every
additive fixed-point condition. This justifies the torsion-clearing step
without assuming that integral cohomology has no torsion. Construction of
the geometric Gysin map and identification of the observable with the
Abel–Jacobi derivative remain to be supplied.

The existing [GeometricLeray.lean](GeometricLeray.lean) has also been checked.
It proves the linear argument that a correspondence acting identically on
the first filtration quotient acts identically on the class when the next
piece is zero. After subtracting the normalized hyperplane lift, this gives
vanishing under the restriction map. The actual geometric filtration,
correspondence, and comparison with the protected residue are still needed
to instantiate that argument.

### Verification performed for this continuation

The following fourteen modules compile under the repository's pinned Lean
4.33.1 and Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`.
Each also passed independent `leanchecker` replay. The 52 audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

| Checked step | Modules |
| --- | --- |
| Complex seed and simultaneous rank bounds | `GeometricDiamondSeed`, `GeometricRankRetraction`, `GeometricDiamondRank` |
| Unrestricted and homogeneous localization boundaries | `GeometricKoszulKernel`, `GeometricGradedWitness`, `GeometricHomogeneousBoundary` |
| Existing curve objects and the actual homogeneous class | `GeometricCurveCoordinates`, `GeometricDegreeOneCech`, `GeometricKoszulTrace`, `GeometricTraceBoundary` |
| Positive integral primitive multiples | `GeometricIntegralPrimitive` |
| Earlier finite seed and filtration algebra | `GeometricSeed`, `GeometricLeray` |
| Protected nonsingularity and finite monomial completeness | `GeometricFormalInputs01Part01` |

Each check used one compiler process with bounded memory. The final
degree-one core and its concrete Koszul comparison compiled in 15.85 and
12.86 seconds respectively. The long intermediate conversion failures were
repaired by direct homogeneous witnesses and explicit map arguments; the
final source keeps its original heartbeat limit. No increased proof budget
or unchecked evaluator is used to bypass the kernel.

The minimal dependency chain for the earlier finite trace calculation also
compiled: all 31 local modules passed without admission warnings. Its
first source component needed a proof-performance repair in
`basis_complete` and `tangent_complete`: five outer cases with quantified
kernel decision replace 1,250 simultaneous elaborator goals. The theorem
statements and finite data are unchanged. The repaired complete module
compiled in 30.73 seconds under the original memory limit and separately
passed kernel replay and the four selected axiom audits. The final
`GeometricTraceBoundary` module compiled in 5.63 seconds and passed its
independent replay and axiom audit. These checks cover the displayed
trace-zero implication, while the larger projective and final-certificate
dependency chain remains unvalidated.

The existing [GeometricSeed.lean](GeometricSeed.lean) was also compiled and
independently replayed after replacing its aggregate tactic import with
the three tactics it actually uses. Its exact complex right-inverse and
tangent identities pass the same axiom audit. This verifies the finite
matrix statements, while their identification with geometric trace
pairings remains a separate step.

The final admission is unchanged. In particular, these checks do not
establish the moving-cycle comparison, the geometric variation and
supported correspondence, or the comparison of the protected residue
with its restriction in regular algebraic de Rham cohomology.

The next geometric interface is concrete: the
[projective source](GeometricProjectiveCurve.lean) declares
`degreeOneSheaf` as an additive sheaf and injects its Čech classes into
derived cohomology. The source in
[GeometricTwistedModule.lean](GeometricTwistedModule.lean) supplies an
\(\mathcal O_C\)-module structure on that same sheaf, but its complete
dependency chain has not been checked here. The local differential
comparison above is now checked; its global identification with the
canonical sheaf and a geometric Serre trace remain to be constructed.
Likewise, [AffineComparison](GeometricExistence.lean) currently requires a comparison
map and its injectivity as inputs. The actual smooth affine comparison and
the support argument must supply those inputs for the protected residue.

## Proof selected for formalization — 13 November 2026

The route to formalize is the surface-section argument of
[Diamond's Chapter 3D](https://github.com/hodge-computer/sextics/blob/01b48136366f28affae56762c42d707642baa0d5/docs/03d-hodge-loci.md).
The precise classical conclusion is
\[
\exists \eta\in\Omega^3_{K/\mathbb C},\qquad d\eta=\rho,
\]
where \(K\) is the function field of the unchanged affine chart and
\(\rho\) is the literal source in
[the final Lean goal](Solution.lean). The ordinary mathematical proof below
uses the stated classical geometry and comparison theorems. Its geometric
lemmas still need Lean implementations. The checked algebraic continuation
above implements supporting steps and does not replace the existing admission.

The detailed arguments in Parts I–IV below remain the mathematical reference.
This section fixes one consistent sequence of statements to implement and
makes explicit several coefficient and specialization issues that a formal
proof must retain.

### The theorem and its shortest closing argument

Put
\[
\begin{aligned}
F&=\sum_{i=0}^2(X_i^6+Y_i^6)
 +\frac12\sum_{i=0}^2X_i^3X_{i+1}Y_iY_{i+1},\\
A&=X_0^2X_1^2X_2^3Y_0^2Y_1^2Y_2,
\end{aligned}
\]
with cyclic indices, and let \(X=V(F)\subset\mathbb P^5_{\mathbb C}\).
Let \(\zeta\) be a primitive cube root of unity. In the original variable
order the automorphisms are
\[
\beta=\operatorname{diag}(1,1,-1,1,1,-1),\qquad
\gamma=\operatorname{diag}(\zeta^2,\zeta^2,1,\zeta,1,1).
\]
Diamond's fourfold theorem says that, for a smooth sextic invariant under
these two actions,
\[
H^4(X,\mathbb Q)^{\langle\beta,\gamma\rangle}
\subseteq N^1H^4(X,\mathbb Q).
\qquad\text{(D)}
\]
Here a class is in \(N^1\) if it restricts to zero off a proper algebraic
divisor. The construction proving (D), including the passage to a special
pencil, is specified in the next subsections.

All target-specific hypotheses of (D) can be checked directly. If the
gradient of \(F\) vanished at a nonzero cone point, let \(M>0\) be the
maximum coordinate modulus. A maximizing \(X_i\) gives
\(6M^5\leq 2M^5\); a maximizing \(Y_i\) gives
\(6M^5\leq M^5\). Both are impossible. Thus \(X\) is smooth.
The three mixed monomials have \(\beta\)-exponents \(0,2,4\) and
\(\gamma\)-weights \(9,6,3\), so \(F\) is invariant.

Write
\(\Omega=\iota_{\sum Z_i\partial_{Z_i}}
(dZ_0\wedge\cdots\wedge dZ_5)\).
The numerator \(A\) has \(\beta\)-exponent four and \(\gamma\)-weight
ten. Since \(\det\beta=1\) and \(\det\gamma=\zeta^2\), the whole form
\(A\Omega/F^3\) is invariant. Its scaling degree is \(12+6-18=0\).
Define \(\alpha_{\mathrm{dR}}\) as its algebraic cohomological residue
and \(\alpha\) as the complex comparison image of that class. This
fixes the residue normalization consistently.

It is unnecessary to assert that \(\alpha\) is rational. Averaging over
the finite group is defined over \(\mathbb Q\), so the complex invariant
space is the scalar extension of the rational invariant space. Apply
(D) to a finite rational basis and take the union of the supporting
divisors. This gives one proper divisor \(Z\subset X\) with
\[
\alpha|_{X\setminus Z}=0.
\qquad\text{(S)}
\]

On \(X_0=1\), use
\((x_0,x_1,x_2,x_3,x_4)=(X_1,X_2,Y_0,Y_1,Y_2)\), and put
\[
\begin{aligned}
f&=1+\sum_{j=0}^4x_j^6+
 \frac12(x_0x_2x_3+x_0^3x_1x_3x_4+x_1^3x_2x_4),\\
a&=x_0^2x_1^3x_2^2x_3^2x_4,\quad g=\partial_0f,\quad
\nu=dx_1\wedge dx_2\wedge dx_3\wedge dx_4.
\end{aligned}
\]
Smoothness implies irreducibility of \(F\) and \(f\). The polynomial
\(g\) is nonzero of degree five, so its image modulo \(f\) is nonzero.
In the ambient rational-function ring set
\(D_t=g^{-1}\partial_0\) and \(b=a/g\). Direct differentiation of
\[
\psi=\left(-\frac{b}{2f^2}-\frac{D_tb}{2f}\right)\nu
\]
gives
\[
\frac{a\,dx_0\wedge\nu}{f^3}-d\psi
=\frac{D_t^2b}{2}\frac{df}{f}\wedge\nu.
\]
Consequently the restriction of the full residue class is represented by
\[
\rho=\frac12\left[
\frac{a_{00}}{g^3}
-\frac{3a_0g_0+a g_{00}}{g^4}
+\frac{3a g_0^2}{g^5}\right]\nu.
\qquad\text{(R)}
\]
This is exactly the source already bound in
[the pole-reduction module](GeometricFormalInputs04.lean). The normal
derivation satisfies \(D_tf=1\); the displayed calculation is a residue
identification in the ambient ring.

Let \(R=\mathbb C[x_0,\ldots,x_4]/(f)\) and \(B=R[g^{-1}]\).
Choose a nonzero \(h\in R\) vanishing on the proper closed subset
\(Z\cap\operatorname{Spec}R\), taking \(h=1\) if it is empty. Its image
\(s\in B\) is nonzero. The open
\[
W=\operatorname{Spec}B[s^{-1}]=D(gh)
\]
is nonempty, smooth, affine, and disjoint from \(Z\). Formula (R) is
regular and closed there, since \(W\) has dimension four, and (S)
says that its comparison class is zero.
[Grothendieck's affine algebraic de Rham theorem, Theorem 1 and equation (4)](https://www.numdam.org/item/PMIHES_1966__29__95_0.pdf)
identifies complex cohomology with the cohomology of the complex of
global regular forms on this actual \(W\). It supplies
\(\eta_W\in\Gamma(W,\Omega_W^3)\) with \(d\eta_W=\rho\).
Localization to \(K=\operatorname{Frac}R\) gives the asserted rational
primitive.

Thus the exact intermediate Lean statement to establish is

    ∃ s : CycleQ2GeometricRegularDeRham.OpenRing,
      s ≠ 0 ∧ CycleQ2GeometricRegularDeRham.residueClass s = 0

The existing equivalence in [Solution.lean](Solution.lean) and the
algebraic certificate constructor then give the protected theorem.
This proof allows complex coefficients, as does the protected contract.

### The geometric input: a genuine moving class

Use the full smooth parameter open \(B_{\mathrm{par}}\) of invariant
weighted sextics in \(\mathbb P(1,1,1,1,2)\), with the coefficient of
\(w^3\) normalized to one. It has dimension 44. The action is
\(g_T=(\zeta^2,\zeta^2,\zeta,1;1)\), and the invariant rational
variation \(\mathbb V=(R^3p_*\mathbb Q)^{g_T}\) has Hodge types
\((2,1),(1,2)\), with dimensions 33 and 33.

For the seed, use \(r^3=2\) and \(i^2=-1\) in characteristic zero.
The values 57 and 33 occur only after reduction at the chosen prime
above 109. With the factorization of Part II,
\[
F_b=F_0+b^2=f_1g_1+f_2g_2+hk,\qquad
C=V(f_1,f_2,h)\subset D=V(F_b,h),
\]
put \(E=C+g_TC+g_T^2C\). For a suitable invariant cubic \(b\), all
varieties in this expression are smooth and the three curves are
disjoint. The rank conditions and smoothness conditions are nonempty
Zariski opens in the irreducible space of invariant cubics.

The rank-open comes from the complete-intersection calculation over
the number-field DVR. Smoothness of the threefold has the Fermat
witness \(b=0\). For the surface and curve, the invariant cubic system
is basepoint free away from the finitely many excluded singular
vertices. Its universal section zero locus is smooth there; properness
and characteristic-zero generic smoothness give a nonempty open of
smooth fibers. This justifies intersecting the required opens.

To match primitive-class hypotheses without assuming integral
torsion-freeness, start with
\[
\lambda=N([E]-2H_D)
\]
for a positive integer \(N\) annihilating the possibly torsion Gysin
image of \([E]-2H_D\). Such an \(N\) exists:
\(\deg E=18\), \(\int_T H^3=3\), and \(i_*H_D=3H_T^2\) give
\(i_*([E]-2H_D)=0\) rationally. Also
\(([E]-2H_D)\cdot H_D=0\). The class \(\lambda\) is integral,
invariant, and in the kernel of integral Gysin. Multiplication by
\(N\ne0\) preserves every rank and nonvanishing conclusion over
\(\mathbb C\).

Let
\(\mathcal A=\mathbb C[x_0,x_1,x_2,x_3,w]/(f_1,f_2,g_1,g_2,h)\).
Its degree-nine piece is a line. Define the geometric functional by
the Koszul boundary followed by Serre trace:
\[
\mathcal A_9\xrightarrow{\ \partial\ }H^1(C,K_C)
\xrightarrow{\ \operatorname{Tr}_C\ }\mathbb C.
\]
The exact sequence
\[
0\longrightarrow\mathcal O_C(1)
\longrightarrow\mathcal O_C(5)^{\oplus2}
\longrightarrow\mathcal O_C(9)\longrightarrow0
\]
and \(H^1(\mathcal O_C(5))=0\) identify the first arrow as an
isomorphism. Hence this functional is a nonzero scalar multiple of
the finite socle functional \(\tau\). A formal proof needs this
comparison; no particular normalization of the scalar is necessary.

The local normal-lift calculation gives, up to common nonzero scalars,
\[
\operatorname{NL}_{\lambda}(L)(\sigma)
=c\,3N\,\tau(kL\sigma),\qquad
\langle d\nu(L),\eta_{B_{\mathrm{test}}}\rangle
=c'\,3N\,\tau(B_{\mathrm{test}}L),
\]
where \(L\) is invariant,
\(\sigma\) has character \(\zeta\), and
\(B_{\mathrm{test}}=x_2x_3^3w\) also has character \(\zeta\).
The residue class \(\eta_{B_{\mathrm{test}}}\) is invariant because
the residue volume has character \(\zeta^2\).
The two formulas concern their respective geometric maps.

Ranks seven and eight imply that the first map is surjective and
that some \(L\) in its kernel has nonzero second pairing. The
holomorphic implicit function theorem gives a smooth local Hodge
locus submersive over the full sextic base. Its vertical dimension
is \(9-1-7=1\).

Here the moving object is the line bundle of class \(\lambda\).
On a contractible Stein neighborhood, the exponential sequence,
Grauert cohomology and base change, and coherent Stein acyclicity produce this
relative holomorphic line bundle. Its uniqueness on each surface
uses \(H^1(\mathcal O_D)=0\). For sufficiently large \(m\), its twist
by \(\mathcal O_D(m)\) has a smooth relative linear system, giving
actual curves \(\Gamma\) whose motion lifts \(L\).

The Abel–Jacobi derivative formula must be proved for these cubic
surface sections. The sufficiently-ample-surface setup in
[Voisin's 2000 paper](https://www.cmls.polytechnique.fr/perso/voisin/Articlesweb/griffithsgroup.pdf)
cannot simply be substituted for this case. The required specialized
proof uses the swept-chain derivative and
\[
0\longrightarrow N_{D/T}^*\otimes\Omega_D^1
\longrightarrow\Omega_T^2|_D\longrightarrow K_D\longrightarrow0.
\]
The hypothesis \(H^1(K_D)=0\) gives the needed lift. Contracting by
the curve's normal field gives the obstruction pairing above.
Its lift ambiguity pairs to zero because \(L\) lies in the
Noether–Lefschetz kernel. The ambient hyperplane twist contributes
zero. Only the curve line bundle is made sufficiently positive;
the surface remains a cubic section.

### Algebraization, generation, and support

The analytic curve family maps to the algebraic flag Hilbert scheme
of triples \((T,D,\Gamma)\), with the fixed Hilbert polynomials of
\(D\) and \(\Gamma\). Work on the open where both are smooth and
\(\Gamma\subset D\) is Cartier. This family map can be constructed from
the Grassmannian of sufficiently twisted curve ideals. If the Hodge
locus has dimension \(d\) and \(n=h^0(D,\mathcal O_D(\Gamma))\), the
analytic family has dimension \(d+n-1\) and injective differential.
Conversely, any first-order flag deformation lies over the kernel
of the same Noether–Lefschetz obstruction. The kernel of the tangent
map from flags \((T,D,\Gamma)\) to pairs \((T,D)\) has dimension
\(h^0(N_{\Gamma/D})=n-1\). Thus the flag Hilbert scheme is smooth at
this point and submersive over the full sextic base.

Its algebraic component therefore dominates that base. Relative
hyperplane cuts with the prescribed first-order tangent, projective
completion, resolution, and shrinking give smooth projective
parameter curves carrying a relative algebraic correspondence.
The nonzero derivative persists on an analytic neighborhood of the
smooth submersive point, which meets the inverse image of every
dense base open. A finite étale base change is allowed if needed
for connected fibers; retain a connected component carrying the
nonzero derivative. Averaging the resulting correspondence gives
a nonzero cylinder map of rational variations, since its derivative
pairs nontrivially with an invariant class:
\[
\pi_g\circ\Gamma_*:
R^1p_{\Lambda*}\mathbb Q(-1)\longrightarrow\mathbb V.
\]
The Tate twist makes both sides weight three.

At Fermat the 35 Higgs forms on the 33-dimensional upper Hodge
space satisfy
\[
\{P:P^{\mathsf T}H_m=H_mP\ \text{for all }m\}=\mathbb C I.
\]
These forms are identified with the geometric Higgs field through
the residue/Jacobian comparison. Polarization gives an orthogonal
flat Hodge projector onto any rational sub-variation. Its upper
block satisfies these equations, so its idempotence forces it to
be zero or identity. The maximal-rank condition persists on an open
of the full base and after finite étale base change. The nonzero
cylinder image is consequently all of \(\mathbb V\).

For a fiber, replace the correspondence by
\(\Gamma'=\pi_g\circ\Gamma\circ\pi_1^\Lambda\) to remove the parameter
curve's degree-zero and degree-two cohomology. Choose a \(g_T\)-stable
divisor \(Z\) containing its target image, which has dimension at
most two. Since \(H^1(T,\mathbb Q)=0\), all of \(H^3(T,\mathbb Q)\)
is primitive. The transpose correspondence agrees, up to a fixed
sign, with the adjoint for the cup-product polarizations. Let
\(M=\Gamma'\circ{}^t\Gamma'\). Hodge positivity makes \(M\)
invertible on \(V=H^3(T,\mathbb Q)^g\), and it vanishes on all other
degrees and eigenspaces. If \(m(t)\) is its minimal polynomial on
\(V\), then \(m(0)\ne0\) and
\[
p(t)=1-\frac{m(t)}{m(0)}
\]
has zero constant term. The cycle \(M\) and all its positive powers
have representatives supported on \(Z\times Z\); so does \(p(M)\).
It acts as the desired projector in every degree. Weighted weak
Lefschetz gives \(H^{2k}(T,\mathbb Q)=\mathbb QH^k\),
\(H^1(T)=H^5(T)=0\), and \(\int_T H^3=3\).
Künneth and Poincaré duality identify its full cohomology class with
the fiber restriction of the relative algebraic correspondence
\[
P=\pi_g-\frac13\sum_{k=0}^3
\operatorname{pr}_1^*H^{3-k}\operatorname{pr}_2^*H^k.
\]

Fixed-Hilbert-polynomial proper flag spaces parameterize supported
representatives of this fixed class. Equality of the flat cycle
classes persists on connected components. There are countably many
numerical choices, so a component dominates the irreducible complex
base. Properness then supplies a supported representative on every
smooth member. The requisite closed flag condition and properness
are [Stacks, Lemmas 108.7.5 and 108.7.7](https://stacks.math.columbia.edu/tag/0DM5).
This is specialization of the support of an already algebraic
relative projector.

Pull this proper component back to the protected pencil and choose
a component dominating it. A closed point of its generic fiber has
residue field finite over \(\mathbb C(U)\). Normalization and
shrinking give a finite étale cover with a relative supported cycle.
Normalized pushforward descends it to the original affine base curve.
Its fiberwise action is the invariant projector.

The pencil is \(Y_2=tX_2\), resolved by blowing up its smooth base
surface. Its paired-sign quotient has equation
\[
\begin{aligned}
G_t={}&s_0^6+s_1^6+s_2^6+s_3^6+(1+t^6)w^3\\
&+\frac12(s_0^3s_1s_2s_3+t s_1^3s_3w+t s_0s_2w^2).
\end{aligned}
\]
Remove the singular fibers, infinity, and the zeros of \(1+t^6\).
The normalized equation \(\widetilde G_t=G_t/(1+t^6)\) defines the
required map into \(B_{\mathrm{par}}\) and the same hypersurface.
The finite quotient may be branched; rational quotient cohomology
still identifies it with the invariant part. Over this affine curve,
Leray has only columns zero and one. Subtracting the global
hyperplane-square class leaves the complex invariant class in
\(H^1(U,\mathbb V_{\mathbb C})\), the invariant part of
\(L^1H^4(\mathcal T,\mathbb C)\). The relative supported cycle acts
identically on this actual subspace because \(L^2H^4=0\).
There is no claim of equality of the relative actions on all
degree-four classes merely from fiberwise equality.

The hyperplane-square class is separately divisor-supported.
Pull the supports back to the resolved fourfold, add the omitted
fibers and exceptional divisor, and push down. This proves (D).
Irreducibility of the variation along the protected pencil is not
a hypothesis.

### Implementation order and verification scope

The useful formalization units are the following genuine comparisons.
The names in this table describe intended lemmas, not declarations
already available in Lean.

| Unit | Required conclusion |
| --- | --- |
| Geometric seed trace | The actual Koszul boundary is an isomorphism to canonical-sheaf \(H^1\), and its Serre trace is a nonzero multiple of the computed socle trace. |
| Moving class and derivative | The integral primitive orbit class has a smooth Hodge locus, an actual algebraic family of curves, and the stated nonzero Abel–Jacobi derivative. |
| Geometric Higgs comparison | The actual invariant variation has the computed Jacobian Higgs forms over the full parameter base. |
| Supported projector | The cylinder map, polarization, and zero-constant polynomial construct the full cohomological projector with divisor-square support. |
| Proper specialization and Leray | The supported representative reaches the special pencil and annihilates the restriction of its whole invariant degree-four class. |
| Affine comparison | The literal regular residue on \(W\) maps to that restricted class and has a regular primitive. |

The first unit should use the chosen characteristic-zero seed.
Existing additive-sheaf classes at literal complex parameter 57
cannot be identified with this seed without a separate proved
comparison. Exact rational primitive, localization, and
certificate-clearing interfaces are already present downstream.

For this continuation, the original seed and Higgs routines were
rerun from the pinned verifier, with SHA-256
9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9.
They returned length 96, socle degree 9, ranks 7 and 8, upper Hodge
dimension 33, 35 effective directions, and scalar solution dimension 1.
Independent integer modular elimination reproduced the minors 80 and
76 and the normalized vector with image \((0,0,0,0,0,0,0,1)\).
These computations verify the finite inputs. The geometric lemmas,
the final existence theorem, and the protected certificate have not
thereby been checked by Lean.

The underlying strategy remains credited to Ben Diamond, Claire Voisin,
and the collaborators credited in Chapter 3D and the references below.
This reconstruction and implementation plan were prepared for
fqlx with OpenAI ChatGPT assistance.

## Upstream compatibility — 13 November 2026

Following `benediamond`'s [review comment](https://github.com/hodge-computer/sextics/pull/245#issuecomment-6857093789),
the branch incorporates upstream `main` at
[`01b4813`](https://github.com/hodge-computer/sextics/commit/01b48136366f28affae56762c42d707642baa0d5).
The merge is conflict-free. It preserves every cycle-q2 Lean source and the
proof manifest from the preceding branch head `139a5b0`; the protected target,
pinned Lean version, and Mathlib revision are unchanged.

The compatibility audit resolves all 13 distinct direct shared imports and
their 20-module shared-library dependency closure against this upstream
revision. None imports the removed or relocated Fermat, cyclic/polar cubic,
algebraic-specialization, or averaging-projector modules. The seven changed
modules in that closure require no source migration in this proposal:

| Shared module | Compatibility finding |
| --- | --- |
| `CertificateOperations` | Proof cleanup preserves the public interface. |
| `FiniteAlgebra.FractionDerivation` | Unused inferred arguments were removed. The existing `rationalPartial_map` proof in [GeometricFormalInputs01Part03.lean](GeometricFormalInputs01Part03.lean) uses `rw [QuadricContactFraction.extend_map]` without explicit instance arguments. |
| `HigherResidues.HigherResidue` | The proposal does not call `normal_cofactor_contraction`, whose unused normal-row hypothesis was removed. |
| `HoldoutCover.FiniteDifferentials` | The proposal does not call `derivations_ext_finite_quotient_fraction`, whose unused domain instance was removed. |
| `HoldoutCover.GenericIncidence` | The removed elaborator option does not change its public declarations. |
| `HoldoutCover.Piola` | The new subtraction and scalar-product divergence lemmas extend the existing interface. |
| `PolynomialCurves.ArithmeticLifting` | The proposal does not call `anchored_constantCoeff`, whose unused domain instance was removed. |

The newly shared `WeierstrassConic` and `WeierstrassChart` constructions use a
specific thirteen-coefficient curve and five-coordinate chart. They do not
directly replace this proposal's Segre incidence and exterior-form geometry;
such a replacement would need additional mathematical identifications. The
proposal's own scoped elaborator options are retained: upstream's cleanup
does not establish that those options can be removed from these proofs.

Validation for this update checks all 181 helper modules with the repository's
source/import policy, the unchanged Lean sources, the 184-file proposal
boundary, explanation links and displayed mathematics, and the catalogue
records. With pinned Lean 4.33.1, the updated `FractionDerivation` module and
an isolated check containing the unchanged `rationalPartial` and
`rationalPartial_map` bodies both compile. The latter check supplies the
required Mathlib imports explicitly; it does not import the full proposal.
Both modules are independently replayed with `leanchecker`, and their checked
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

This maintenance update does not discharge
`Submission.missing_geometric_existence`. Import and source compatibility
checks do not constitute a fresh compilation or independent kernel replay
of the complete proposal.

## Classical geometric audit — 13 November 2026

This continuation records an independent reconstruction and review of the
surface-section argument in Chapter 3D for the unchanged protected target.
The written classical proof gives existence of a legal ordinary certificate;
**the Lean submission remains incomplete**. The existing admission in
`Submission.missing_geometric_existence` is unchanged. No Lean elaboration,
compilation, kernel replay, or full proposal verification was run for this
documentation update, and no expanded coefficient witness is claimed.

The audit starts from the actual
[Chapter 3D source](https://github.com/hodge-computer/sextics/blob/97c875622f1c2573d0fcbff9e30b239f2fb6b176/docs/03d-hodge-loci.md),
not from an earlier assertion of completeness in this explanation. The
[surface-section revision](https://github.com/hodge-computer/sextics/commit/88d582a3a6144dfe6a7bfb42ecb97eff26512cda)
credits Fable 5.2 and replaces the Fano-fourfold density route with moving
divisor classes on surfaces. Credit remains with `benediamond`, the project
collaborators, Claire Voisin, and the authors of the classical results cited
below. Prepared for `fqlx` with OpenAI ChatGPT assistance.

### Geometric comparisons supplied by the review

The complete argument below now spells out the following points.

1. The integral orbit class has an actual relative line bundle on a small
   contractible Stein neighborhood of its Hodge locus. The exponential
   sequence, together with proper base change and Stein acyclicity, proves
   this family statement; pointwise Lefschetz \((1,1)\) alone would not.
2. A sufficiently positive twist gives an embedded analytic curve family
   and a holomorphic map to the algebraic flag Hilbert scheme through its
   Grassmannian presentation. A matching tangent-dimension bound proves
   that the Hilbert point is smooth and its projection to the full sextic
   parameter base is submersive. Relative cuts with prescribed first jets
   preserve the nonzero Abel--Jacobi direction through completion,
   resolution, and shrinking. Part II.7 supplies these details.
3. The checked Higgs matrices are bound to the actual infinitesimal period
   map using the ordinary sextic cover \(w=t^2\), with
   \(\phi^*\Omega_{\mathrm{weighted}}=2t\Omega_{\mathbf P^4}\).
   The pairing agrees up to one common nonzero residue normalization,
   which cancels from \(P^{\mathsf T}H_m=H_mP\). The normalized full
   parameter chart has dimension 44; the 35 checked monomials are its
   effective Jacobian deformation directions.
4. Polarization proves irreducibility for rational **sub-variations** on
   finite étale covers of dense opens of that full base. No irreducibility
   of arbitrary differential submodules, or of the restriction to the
   protected pencil, is asserted. Supported-projector specialization is
   the step that reaches the particular pencil.
5. The supported relative correspondence fixes the whole class in
   \(L^1H^4\), since \(L^2H^4=0\) over the affine curve. The normal pole
   subtraction identifies the literal protected four-form. Grothendieck's
   comparison is applied on an actual nonempty smooth affine open, then
   localization gives its rational primitive. Parts III--IV retain the
   full argument and the exact denominator-clearing identity.

The three mathematical reviews covered the moving-class/Abel--Jacobi
construction, the polarized variation and arithmetic lift, and the
supported-projector-to-protected-residue passage. They found no remaining
classical gap in the assembled argument. These are written mathematical
reviews, not kernel checks or external acceptance of the proposal.

The original characteristic-zero seed is over \(\mathbb Q(r,i)\), with
\(r^3=2\) and \(i^2=-1\); \(57\) and \(33\) are its residues at the
chosen prime above \(109\). This argument does not identify that seed with
the literal complex \(r=57\) used by some later Lean helper modules. The
individual orbit curves need not deform separately: their sum's line
bundle is the moving object. The conormal-lift ambiguity pairs to zero
because its pairing is the Noether--Lefschetz obstruction on the chosen
kernel direction. The Koszul sequence in Part II.2 identifies the actual
socle functional with Serre trace.

### Exact finite and algebraic checks

The original seed and Higgs routines were replayed without running the
supplementary fourfold computations. The source was the
[pinned verifier](https://github.com/hodge-computer/sextics/blob/97c875622f1c2573d0fcbff9e30b239f2fb6b176/scripts/verify-hodge-locus-span.py),
whose SHA-256 is
`9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9`.

| Check | Result |
| --- | --- |
| Complete-intersection Hilbert function through degree ten | \((1,4,9,15,19,19,15,9,4,1,0)\) |
| Noether--Lefschetz rank and augmented rank | \(7\) and \(8\) |
| First seven-column and eight-column minors modulo \(109\) | \(80\) and \(76\) |
| Normalized modular direction | \((19,26,71,38,38,74,19,24,0)^{\mathsf T}\) |
| Augmented matrix times that direction | \((0,0,0,0,0,0,0,1)^{\mathsf T}\) |
| Higgs dimension and effective directions | \(33\) and \(35\) |
| Integral entry-identification forest | \(1088\) edges; only scalars remain |
| Weighted-to-ordinary triple pairings | All \(38115\) comparisons agree |
| Euler-volume pullback coefficients | All five agree |
| Protected-source and universal differential identities | Fourteen exact checks pass |

The matrix, monomial orders and minors are displayed in Part I and
Appendix B; the complete integer Higgs forest is in Appendix A. The
fourteen endpoint checks cover the protected degrees, paired-sign and
order-three characters, literal weighted quotient, vertex coefficient,
affine equation and numerator, normal partial, residue coefficient,
pole reduction, normal pairing, divergence lift, and order-three
remainder. They verify algebraic identities, not the existence of a
primitive by a bounded search. The product-rule proof of the identities
is given in Part IV.5 and Part IV.7.

The following bounded reproduction, run from the repository root with
Python and NumPy, replays the original two inputs and all 38115 ordinary
cover comparisons. It does not invoke Lean or the large fourfold routines.

```python
from pathlib import Path
from itertools import product
import hashlib
import importlib.util

source = Path("scripts/verify-hodge-locus-span.py")
assert hashlib.sha256(source.read_bytes()).hexdigest() == (
    "9d673eff17a53fee04eb2677615db689833cf33b5fa23fe16ad42467d22a40a9"
)
spec = importlib.util.spec_from_file_location("chapter3d", source)
chapter = importlib.util.module_from_spec(spec)
spec.loader.exec_module(chapter)
seed, _ = chapter.seed_divisor()
higgs = chapter.higgs_field()

standard = list(product(range(5), range(5), range(5), range(5), range(2)))
degree = lambda a: sum(a[:4]) + 2*a[4]
character = lambda a: (2*a[0] + 2*a[1] + a[2]) % 3
E = [a for a in standard if degree(a) == 6 and character(a) == 1]
T = [a for a in standard if degree(a) == 6 and character(a) == 0]
assert (len(E), len(T)) == (33, 35)
cover_E = lambda a: (*a[:4], 2*a[4] + 1)
cover_T = lambda a: (*a[:4], 2*a[4])
weighted_socle = (4, 4, 4, 4, 1)
ordinary_socle = (4, 4, 4, 4, 4)
comparisons = 0
for m, a, b in product(T, E, E):
    weighted = tuple(x+y+z for x, y, z in zip(m, a, b)) == weighted_socle
    ordinary = tuple(x+y+z for x, y, z in
                     zip(cover_T(m), cover_E(a), cover_E(b))) == ordinary_socle
    assert weighted == ordinary
    comparisons += 1
assert comparisons == 38115
print(seed, higgs, {"ordinary_cover_comparisons": comparisons})
```

### Formal endpoint

The algebraic conversion from actual residue exactness to the protected
certificate remains proved in the existing helpers. Its geometric input
still needs Lean proof terms for the actual moving-cycle comparison,
polarized variation, supported correspondences, and algebraic de Rham
comparison. The exact remaining assertion is
\[
\exists\eta\in\Omega^3_{K/\mathbf C},\qquad d\eta=\rho,
\]
with the actual hypersurface field and literal source of Part IV.5--6.
This documentation update leaves every Lean source, the manifest, and
the protected \((F,q,A)\) unchanged.

## Checked finite seed and incidence charts — 12 November 2026

This continuation proves three additional concrete algebraic results. It does
**not** close `Submission.missing_geometric_existence`, construct the full
rational primitive, or establish a protected acceptance result.

### Explicit quotient tests at the literal complex seed

[GeometricExplicitTangent.lean](GeometricExplicitTangent.lean) proves seven
literal ideal memberships for the existing cubic
\[
L=i x_0^2x_1+(i-1)x_0^3.
\]
This is the already defined `CycleQ2SeedCechTheta.selectedTangent`; the new
result is its binding to all seven obstruction tests at \(r=57,\theta=1\).
For the actual polynomials \(f_1,f_2,g_1,g_2,h,k\) at that seed,
`CycleQ2ExplicitSeedDirection.selected_test_mem` proves
\[
kL\sigma\in(f_1,f_2,g_1,g_2,h)
\]
for each of
\[
\sigma=x_2w,\ x_2x_3^2,\ x_1x_2^2,\ x_1^2x_3,
\ x_0x_2^2,\ x_0x_1x_3,\ x_0^2x_3.
\]
The proof consists of explicit polynomial Bezout identities over Gaussian
coefficients, followed by exact binding to the existing five-variable seed
ideal. It assumes no equation \(57^3=2\).

The same module proves that \(3L\) has derivative trace one, is not a
coboundary in the existing unrestricted localization complex, and has paired
normal trace exactly \(-1/171\). Its important declarations are
`traceOne_test_mem`, `traceOne_trace`, `traceOne_not_boundary`, and
`traceOne_paired_normal_trace`.

These statements do not identify the quotient tests with the geometric
Noether--Lefschetz map or identify the paired trace with the derivative of an
Abel--Jacobi map. Nor do they identify \(3L\) with the cubic component of the
separately constructed, nonconstructively chosen incidence tangent: equality
of their scalar traces does not imply equality of the directions.

### Actual polynomial charts for the section zero locus

[GeometricIncidenceSection.lean](GeometricIncidenceSection.lean) strengthens
the existing principal-ideal calculation for the literal equations \(MT=0\).
For any commutative ring \(R\), a three-by-three matrix \(M\) with zero
cofactors, and a unit entry \(M_{ab}\),
`CycleQ2IncidenceSection.sectionQuotientEquiv` constructs an algebra isomorphism
\[
R[T_0,T_1,T_2]/((MT)_0,(MT)_1,(MT)_2)\simeq R[U,V].
\]
It constructs both inverse substitutions, solving the row equation for
\(T_b\). No field, domain, or reducedness hypothesis is imposed on \(R\).
The actual quotient algebra is therefore smooth and flat over \(R\), as
proved by `sectionQuotient_smooth` and `sectionQuotient_flat`.

Here \(R\) is the surface chart ring. This is not a theorem that every
individual curve fiber is smooth or that the family is flat over its
section-parameter space. The global projective gluing, divisor-class
identification, suitable smooth-family open, and Abel--Jacobi comparison
remain further geometric steps.

### The invariant-coordinate dictionary retains the exact source

[GeometricInvariantQuotient.lean](GeometricInvariantQuotient.lean) binds a
rational coordinate substitution to the generated protected \(F\) and \(A\).
On \(X_0=1\), write \((x,a,y,z,b)=(X_1,X_2,Y_0,Y_1,Y_2)\), and put
\[
t=yz,\qquad u=za^2,\qquad r=z^3,\qquad\lambda=b/a.
\]
On the nonempty coordinate open used for the substitution, the quotient
equation is
\[
H=r^4+(1+x^6+xt/2+\lambda x^3u/2)r^2
  +((1+\lambda^6)u^3+\lambda tu^2/2)r+t^6=z^6f.
\]
The forward Jacobian, in the displayed coordinate order, is \(-6z^4\).
The entire protected ambient form transforms to
\[
-\frac{\lambda x^2t^2u^2r^4}{6H^3}
  \,dx\wedge dt\wedge du\wedge dr\wedge d\lambda.
\]
The module proves the polynomial substitution, differential coefficients,
Jacobian determinant, numerator binding, and rational-density pullback.
It also proves the scalar normal-residue formula under the required jet
scalings. These identities preserve the character and all density factors;
they do not assert vanishing of a cohomology class or supply a primitive.
This quotient can be transformed back to the previously studied elliptic
cubic, so it is a verified dictionary, not a removal of that route's
unresolved compact class.

### Verification and the remaining endpoint

Each new module was compiled with pinned Lean 4.33.1 and individually replayed
with `leanchecker`. The printed transitive axioms of the principal new
declarations are exactly `propext`, `Classical.choice`, and `Quot.sound`.

| New module | Compile time | Peak compile RSS | Kernel replay |
| --- | ---: | ---: | --- |
| `GeometricExplicitTangent` | 42.15 s | 3.73 GiB | Passed |
| `GeometricIncidenceSection` | 7.04 s | 3.47 GiB | Passed |
| `GeometricInvariantQuotient` | 12.05 s | 3.22 GiB | Passed |

The selected checks used one compiler worker, a 5,120 MiB managed-memory
limit, a 6,144 MiB monitored RSS ceiling, and existing pinned compiled
dependencies, including compatibility modules from the source-preserved
pre-refactor layout. This is compilation and independent replay of the
three new modules, not a fresh build or replay of the complete refactored
dependency closure. The original explicit admission remains.

The proposal now has 184 permitted files (approximately 7.02 MiB), within
the unchanged 256-file and 16-MiB limits. All 181 helper modules pass the
source/import policy. The full proposal correctly fails that policy at the
existing placeholder in `Solution.lean`; the generated protected target and
the certificate entry point are unchanged.

The next substantive geometric comparison must connect an actual moving
divisor family to the nonzero paired class and its invariant Abel--Jacobi
derivative. Supported correspondences and restriction of the **specific**
protected residue to zero on a nonempty principal open must then supply the
existing algebraic exactness criterion. None of those conclusions is
introduced as a new axiom or hidden in the new definitions.

## Smaller proof modules — 12 November 2026

This refactor continues the newer `fqlx/cycle-q2-modular` development at
[`6a78158`](https://github.com/fqlx/sextics/commit/6a781583858cde35157487c221ccc35f1878ec05).
It preserves the mathematical source of that checkpoint. In particular,
`Solution.lean`, its protected certificate statement, and its existing
`Submission.missing_geometric_existence` admission are unchanged.

The first modularization still left many source files near 4,700 lines.
Forty of those modules now act as small import wrappers over 117 smaller
parts. Existing `Proposal` import paths continue to work. Parts retain
the original order, namespaces, options, component documentation, and
complete declaration bodies; data definitions remain with their associated
equality proofs.

| Module family | Existing modules split | New parts | Largest part, lines |
| --- | ---: | ---: | ---: |
| Assembly | 10 | 25 | 2,546 |
| Normalization | 8 | 20 | 1,984 |
| GeometricFormalInputs | 3 | 11 | 2,270 |
| GeometricTarget | 11 | 31 | 1,894 |
| SolutionSupport | 8 | 30 | 3,240 |

Three complete proof blocks intentionally exceed 2,000 lines:
[Assembly01Part02.lean](Assembly01Part02.lean),
[GeometricFormalInputs01Part02.lean](GeometricFormalInputs01Part02.lean), and
[SolutionSupport04Part01.lean](SolutionSupport04Part01.lean).
The first and third retain tightly coupled private helper proofs; the second
contains the existing long `scalar_of_entryConstraints` theorem. Further
division would require a proof refactor. Sparse arithmetic components also
remain intact. The largest new part is 141,460 bytes, compared with 594,392
bytes for the largest module before this refactor.

The proposal now has 181 permitted files, approximately 7.0 MiB of source,
within the current upstream limits of 256 files and 16 MiB. The verifier and
its policy are unchanged. The 64-file counts in the historical sections below
describe those earlier checkpoints.

### Refactor validation scope

Source-range reconstruction verifies that all 40 original module bodies are
preserved exactly. The complete helper import graph is acyclic, all 178
helpers pass the repository's source/import policy, and the sole explicit
admission remains in the unchanged entry point. An independent static review
checks scope closure, file-level options, local attributes, and private-helper
references at the new boundaries.

Bounded development compilation checked the following new part chains and
their original-name import wrappers. Each group used its own artifact tree
and source-hash-verified dependencies from the same `6a78158` checkpoint.

| Original module | Successful checks / selected modules | Result |
| --- | ---: | --- |
| Assembly01 | 4/4 | Passed |
| Normalization02 | 3/3 | Passed |
| GeometricFormalInputs01 | 5/5 | Passed |
| GeometricTarget04 | 3/3 | Passed |
| SolutionSupport01 | 8/8 | Passed |

The checks used Lean 4.33.1 and the pinned Mathlib revision, one worker,
a 5,120 MiB managed-memory limit, a 6,144 MiB RSS ceiling, a 1,536 MiB
available-memory reserve, and a 360-second deadline per module.
The 23 passing module checks cover these selected chains against cached
baseline dependencies. They are not a fresh build of the entire refactored
import closure or an independent kernel replay. No protected acceptance is
claimed. Explanation rendering, local links, record/content validation, and
whitespace checks also pass.

An initial coarser split of `SolutionSupport01` exceeded the 5,120 MiB managed-memory limit in existing cubic arithmetic checks. Those three complete arithmetic components were then isolated into separate modules without editing their proofs. The refined chain passed under the same limit. This is evidence for this selected layout and sample, not a general memory guarantee.

This source refactor does not establish the remaining geometric existence
argument. The projective, cycle-class, Abel–Jacobi, and residue-exactness
obligations described below retain their previous status. The admission still
prevents acceptance of the complete proposal.

## Restriction, projective cohomology, and incidence schemes — 12 November 2026

**This continuation supplies further geometric and cohomological
constructions. It does not prove `Submission.missing_geometric_existence`.**
The new declarations have explicit proof bodies and introduce no new
admissions or declared axioms. Lean elaboration, compilation, and kernel
checking remain deferred, so they are not claimed as verified Lean results.

Three further modules connect the previously constructed objects:

| Helper | Construction | Remaining boundary |
| --- | --- | --- |
| [GeometricPrincipalRestriction.lean](GeometricPrincipalRestriction.lean) | Canonical localization, Kähler and exterior restriction maps for actual inclusions of principal opens; compatibility with every differential; diagrams of regular complexes and cohomology. Its `CycleQ2GeometricRationalSpread` namespace clears finite denominators and constructs the actual filtered-colimit isomorphism with generic top cohomology. | The residue is still not shown to vanish on any open. The restriction diagram does not yet provide sheaf gluing, sheaf hypercohomology, or the Betti comparison. |
| [GeometricConeCech.lean](GeometricConeCech.lean) | The actual punctured affine cone, its two-open cover, and canonical localization-to-section maps. The Čech quotient injects into genuine derived sheaf cohomology through the actual Mayer--Vietoris boundary, preserving the nonzero classes, including the literal incidence tangent at \(r=57,\theta=1\). | The canonical-bundle comparison and geometric Serre trace remain separate constructions. |
| [GeometricProjectiveCurve.lean](GeometricProjectiveCurve.lean) | The homogeneous quotient grading and actual projective curve; degree-one modules with explicit frames; an actual additive sheaf and an injection into its derived cohomology. The same module constructs the weighted incidence surface and generic-section projective zero locus, with actual scheme morphisms and exact equation bindings. | The canonical module-sheaf and Serre identifications remain open. The incidence candidate still needs the divisor-class, flatness, smooth-fiber, and Abel--Jacobi comparisons. |

### Restriction and the generic-point limit

Write \(B=R[g^{-1}]\) for the already constructed smooth Jacobian-open
coordinate ring. For an actual inclusion \(D(t)\subseteq D(s)\) in
\(\operatorname{Spec}(B)\), the localization universal property constructs
\(B[s^{-1}]\to B[t^{-1}]\). The maps on Kähler differentials and exterior
powers are canonical, and commute with every differential of the regular
complex. The intersection of two nonempty principal opens is the
nonempty open \(D(st)\), since \(B\) is a domain. Thus restriction gives a
filtered diagram as the opens shrink.

Every rational exterior form has finitely many coefficients in the actual
function field. Clearing those coefficients in the original affine ring
constructs a common denominator. Multiplying that denominator by a
prescribed \(t\ne0\) keeps the resulting form inside \(D(t)\).
Injectivity of the already constructed maps on exterior forms then gives:

* every generic top-cohomology class is represented on some such open;
* a regular class that maps to zero generically becomes zero after a
  further principal restriction;
* two regular classes with the same generic image become equal after a
  further principal restriction.

These statements establish the universal property, rather than merely
defining the generic quotient to be a limit. The source constructs an
actual isomorphism of complex vector spaces

\[
  \mathop{\mathrm{colim}}_{D(s)\ne\varnothing}
    H^4\bigl(\Gamma(D(s),\Omega^\bullet)\bigr)
  \;\simeq\;
    \Omega^4_{K/\mathbb C}/d\Omega^3_{K/\mathbb C}.
\]

Here the left-hand groups are the constructed cohomology quotients of
global regular-form complexes. No sheaf-hypercohomology identification is
implicit in this notation. The colimit comparison agrees with each
existing `toGeneric` map, including the protected residue class.

Consequently the new `CycleQ2Nonconstructive.exact_form_iff_regular_zero`
states the exact equivalent target

\[
  \texttt{AffineResidueFormExact}
  \quad\Longleftrightarrow\quad
  \exists s\in B,\ s\ne0\ \text{and}\ [\rho]_{D(s)}=0.
\]

This preserves unrestricted nonconstructive existence. It neither bounds
the primitive's denominator nor asserts injectivity of cohomology from one
fixed affine open to the generic point. The missing support argument must
still produce the vanishing on some open.

### From localization fractions to actual sheaf sections

After eliminating \(w=-x_2^2\), the curve ring is the homogeneous coordinate
ring of an ordinary degree-\((2,3)\) curve in \(\mathbb P^3\). The two
denominators from the normal calculation give an actual cover of its
punctured affine cone. On each patch and the overlap, the canonical
localization-to-section equivalence respects the restriction maps.
The existing quotient by all localization coboundaries therefore agrees
with the quotient by actual structure-sheaf-section coboundaries. The
normalization and selected normal-pairing classes remain nonzero under
this comparison.

The source then goes beyond cochain homology. An explicit additive
free-Yoneda equivalence identifies Mathlib's degree-zero sheaf cohomology
with sections and proves compatibility with restriction. For the actual
structure sheaf on the cone, the Mayer--Vietoris sequence supplies

\[
  H^0(U,\mathcal O)\oplus H^0(V,\mathcal O)
  \longrightarrow H^0(U\cap V,\mathcal O)
  \xrightarrow{\delta} H^1(U\cup V,\mathcal O).
\]

Its exactness identifies the entire kernel of \(\delta\) with the existing
section coboundaries. Hence `sectionToSheafH1` is an injective additive map
from the actual section Čech quotient to genuine Ext-defined cohomology
(`H'` in Mathlib's notation). Both the normalization and selected
normal-pairing class remain nonzero there. This injection needs no affine
acyclicity assertion; a surjectivity assertion would require more work.

These comparisons retain the existing sparse `originalB` and theta
family. They do not identify that family with the full nine-coefficient
cubic used by the written modular rank-seven/rank-eight calculation.
There is now also a direct binding to the actual incidence seed:
`incidenceCubicCoefficients` is the cubic part of the previously constructed
`parameterDirection`. Its checked trace is one, its cubic is the restriction
of the actual full invariant tangent polynomial, and
`incidenceSheafClass_ne_zero` carries its paired normal connecting class
into genuine derived cohomology at \(r=57,\theta=1\). This statement
does not impose the incompatible complex equation \(57^3=2\).

### The actual projective degree-one class

The projective construction retains the grading instead of assigning a
projective interpretation to the ungraded cone quotient. The new general
`HomogeneousQuotient.gradedRing` constructs the grading of a quotient by
any homogeneous ideal from the original direct-sum decomposition. Its
application to the actual quadratic and cubic equations defines
`projectiveCurve` as a genuine scheme. The two original degree-four
denominators cover this scheme, and Mathlib's canonical projective affine
charts identify their rings with homogeneous degree-zero localizations.

On a chart with a homogeneous denominator \(f\) of degree \(d\),
`degreeOneModule` consists of the actual fractions
\[
  a/f^n,\qquad a\in A_{1+nd}.
\]
Closure and restriction to product-denominator charts are proved by
clearing denominators. The original normal-pairing numerator has degree
nine, so division by \(g_1g_2\), of degree eight, gives an actual member of
the overlap's degree-one module. Its quotient by the two genuine
single-chart restrictions maps to the previously constructed scalar
Čech quotient and onwards to cone sheaf cohomology. The source proves
`incidenceDegreeOneClass_ne_zero` and identifies both images with the
literal incidence classes.

The next comparison is now constructed as well. On the first chart the
degree-one module has frame \(x_1\); on the second it has frame \(x_2\).
The ratio \(t=x_2/x_1\) is an invertible section of the actual projective
structure sheaf on the overlap. The source constructs the additive sheaf
\[
  \mathcal F=\ker\!\left(
    j_{1*}\mathcal O_{U_1}\oplus j_{2*}\mathcal O_{U_2}
    \xrightarrow{\ (a,b)\mapsto a-tb\ }
    j_{12*}\mathcal O_{U_1\cap U_2}\right).
\]
Its evaluated sections are proved to be the compatible pairs, using
free-sheaf representability of sections and the actual kernel universal
property. This yields local section equivalences with the degree-one
modules, and both equivalences commute with the actual restrictions.
Consequently the projective Mayer--Vietoris boundary gives
\[
  \mathrm{DegreeOneCech}(r,\theta)
    \hookrightarrow H'^1(C,\mathcal F),\qquad r\ne0.
\]
`degreeOneToProjectiveH1_injective` proves this injection, and
`incidenceProjectiveSheafClass_ne_zero` gives the nonzero class at
\(r=57,\theta=1\). `incidence_class_images` binds the projective and
cone derived classes to the same concrete degree-one numerator. It does
not supply a general map between those two derived cohomology groups.

This is an actual additive sheaf and actual derived cohomology. Packaging
the sheaf as an \(\mathcal O_C\)-module, identifying it with the canonical
bundle, and constructing the geometric Serre trace and pairing are still
required. The argument proves an injection and makes no affine-acyclicity
or derived-cohomology surjectivity claim.

The homogeneous core of a prime also constructs the continuous map from
the punctured cone to this projective scheme. Its preimages of homogeneous
basic opens agree with the original cone basic opens. A compatible map
of structure sheaves is still needed to promote it to a scheme morphism.

The ordinary projective presentation also gives a more direct prospective
route to the remaining twist calculation: the Koszul resolution of
\(\mathcal O_C(1)\) starts with
\(\mathcal O_{\mathbb P^3}(-4)\), followed by
\(\mathcal O_{\mathbb P^3}(-1)\oplus\mathcal O_{\mathbb P^3}(-2)\).
The corresponding resolution of \(\mathcal O_C(5)\) starts with
\(\mathcal O_{\mathbb P^3}(0)\). Constructing those module-sheaf
resolutions, their cohomological comparison, and the resulting trace
remains a prospective route beyond the additive sheaf constructed here.

### A concrete incidence route for the moving family

The existing incidence algebra provides a possible shorter geometric
route than the written Hodge-locus reconstruction. Its fixed and full
Jacobian ranks, trace-one fixed-sextic tangent, lifts of all 45 sextic
coefficient directions, and `finite_pointed_trace_point` are tied to
literal polynomial equations. The actual seed-surface minor cover also
persists along the pointed trace construction.

The `CycleQ2GeometricIncidenceProj` namespace now constructs projective
schemes from these actual equations. The geometric variables have weights
\((1,1,1,1,2)\), while coefficient and section parameters have degree zero.
The actual cubic \(h\), sextic \(F\), and matrix entries are proved
homogeneous in degrees three, six, and fourteen. The existing
`PointSurface y` quotient therefore has an actual weighted projective
spectrum, together with scheme morphisms to its affine coefficient base
and weighted ambient space.

Over \(S[T_0,T_1,T_2]\), the three literal entries of \(M T\) give the
projective candidate
\[
  \Gamma=\operatorname{Proj}
    \frac{S[T_0,T_1,T_2][x_0,x_1,x_2,x_3,w]}
         {(h,F,(MT)_0,(MT)_1,(MT)_2)}.
\]
The source constructs actual morphisms from this scheme to the incidence
surface, the weighted ambient scheme, and the affine parameter base.
Swapping the geometric and section polynomial variables and quotienting
the geometric coefficients sends its defining ideal to the exact
previous `sectionIdeal`; this is
`toSectionPolynomial_genericCurveIdeal`. It is an image-ideal identity,
not yet a quotient-ring or scheme base-change isomorphism.

The previously proved local regularity retains all three independent
section variables. It does not assert that every specialized section is
a nonzero regular divisor. The projective candidate still needs its
Cartier and divisor-class identifications and a suitable parameter open
with nonempty flat smooth curve fibers. Identifying the seed divisor class
with \(E+4H\), and the relative ambient-test/orbit pairing with the
Abel--Jacobi derivative, remains essential. These scheme definitions do
not supply the Abel--Jacobi comparison or establish closed immersions.

The existing graded linkage duality specifies which line bundle must be
constructed. In [SolutionSupport05.lean](SolutionSupport05.lean),
`actualImage_selected` identifies the selected right-ideal sections with
the actual matrix columns, `actualDuality_grade` retains the degree-four
twist, `actualImage_grade` gives the degree-fourteen columns, and
`actualDuality_restriction` supplies their compatibility. Together with
`localized_linkageIdeal_eq_components` in
[SolutionSupport03.lean](SolutionSupport03.lean), these give concrete
algebraic data for the missing sheafification and identification with
\(\mathcal O_D(E+4H)\). This identification has not yet been proved at
the scheme/sheaf level. Likewise, the existing nonzero character vector
alone does not prove that its pairing with the chosen vertical cubic
direction remains nonzero; the relative pairing must retain the seed's
explicit normal-pairing value \(-1/171\).

The proposal now contains **62 Lean modules and 64 total proposal files**.
The target and original final admission are unchanged. The moving-curve
and Abel--Jacobi construction, geometric polarized variation, supported
correspondences, and analytic de Rham comparison remain unfinished.

## Concrete geometric objects and regular forms — 12 November 2026

**This continuation implements further prerequisites of the written proof.
It does not close `Submission.missing_geometric_existence`.** The new Lean
source has complete proof bodies without additional admissions, but its
elaboration, compilation, and kernel replay remain deferred. The preceding
local modular compilation fixes from `0da28f2391f2353a75bb3bd14bd4f24fb6dd024b`
are retained.

Four helpers now construct specific objects appearing in the remaining
comparisons:

| Helper | Construction in this continuation | Boundary of the result |
| --- | --- | --- |
| [GeometricSerre.lean](GeometricSerre.lean) | An injective degree-nine Koszul boundary, its equivalence onto its actual Čech image, a unique normalized trace there, and a cubic pairing on genuine normal Čech classes. The pairing is bound to the literal connecting fraction and its nonzero ambient test. | The image is not defined to be projective cohomology. Twisted projective sheaves, the projective Čech comparison and Koszul surjectivity, geometric Serre trace, and semiregularity remain to be constructed. |
| [GeometricVariation.lean](GeometricVariation.lean) | The actual degree-six and degree-twelve character-one Fermat Jacobian components, their socle-trace duality, the resulting 66-dimensional paired graded model, and Higgs operators given by actual quotient multiplication. Compatible graded self-adjoint projectors are trivial. | This is the algebraic graded fiber. Its identification with a polarized geometric variation, connection, Hodge filtration and residue pairing is still required. |
| [GeometricAffineScheme.lean](GeometricAffineScheme.lean) | A genuine smooth affine scheme obtained by inverting the actual normal partial, its open immersion into the protected affine hypersurface, a basis of its actual Kähler module, and the same constructions on further principal opens. | It supplies the geometric open and its differential basis, but not a Betti comparison or divisor-support vanishing. |
| [GeometricRegularDeRham.lean](GeometricRegularDeRham.lean) | Genuine regular Kähler and exterior forms on these concrete opens, their bounded de Rham complex, its cochain map to the rational complex, its fourth-homology quotient, and the protected residue expressed over the regular coordinate ring. | The analytic comparison and the geometric proof that the residue class vanishes on a suitable open remain necessary. |

### Actual smooth opens

Let \(R=\mathbb C[x_0,\ldots,x_4]/(f)\), with the existing protected
dehomogenized polynomial \(f\), and let \(g=[\partial f/\partial x_0]\).
The new open is the actual scheme \(\operatorname{Spec}(R[g^{-1}])\).
Its presentation combines the hypersurface equation with the localization
equation. The chosen Jacobian determinant is \(g^2\), which is a unit in
that coordinate ring. The Mathlib submersive-presentation construction
therefore supplies standard smoothness of relative dimension four and the
genuine regular differential basis
\(dx_1,dx_2,dx_3,dx_4\).

The same presentation method gives these bases on
\(\operatorname{Spec}(R[g^{-1}][s^{-1}])\). For \(s\ne0\), that open is
nonempty. This extra localization matters: the written support argument
must remove its support divisor, and does not assert that the residue
already vanishes on the entire initial Jacobian open.

The regular-to-generic restriction is constructed on the actual Kähler
and exterior modules and proved to commute with each differential. The
associated sheaves of these form modules are also constructed, with the
canonical identification of their global sections on the affine scheme.
Exterior differentiation is complex-linear, so constructing its sheaf map
requires more than the tilde functor on coordinate-ring-linear maps.
The fixed regular residue maps to the existing protected rational residue,
including its normal-density factor and sign. The new specialization in
`GeometricExistence` therefore uses a concrete regular class and a proved
source-binding identity. It no longer asks a caller to supply an arbitrary
regular class, a map to the generic quotient, or that binding equation.
An injective geometric comparison on the same chosen open and its
support-derived zero class are still required.

### Actual normal pairing and actual Jacobian components

The new normal pairing is defined after passing to genuine normal Čech
classes. Multiplication by a homogeneous cubic lands in the image of the
degree-nine boundary, whose normalized trace is constructed from the
existing quotient trace and a proved linear equivalence. Consequently,
changing a representative by any actual localization coboundary leaves
the pairing unchanged. For the existing normal connecting class its value
is exactly the quotient trace of \((kL-A)\sigma\), with the sign fixed by
the local lift calculation. The sparse seed condition \(r^3=2\) remains
explicit; no identification with literal complex \(r=57\) is made.

For the Higgs calculation, complementary monomials in the actual socle
pair the degree-twelve, character-one piece with the dual of the
degree-six, character-one piece. The trace pairing is proved to be the
Kronecker pairing on those bases. Multiplication by an actual invariant
degree-six tangent class is then intertwined with the paired Higgs
operators. Their projector result is a theorem about those concrete
graded modules; it does not declare them to be a geometric Hodge
structure by definition.

### Remaining global construction

The written moving-curve argument still requires a formal implementation
of the surface Hodge locus, its relative line bundle and effective curves,
and the Abel--Jacobi differential and algebraization. The subsequent
variation and supported-correspondence construction also remains open.
Finally, the regular algebraic class must be compared with cohomology on
the same complex affine open, and its zero restriction must be proved from
that support construction. These geometric conclusions are not assumptions
silently added to the final theorem.

All four new helpers were imported by the submission. At this checkpoint,
the proposal contained **59 Lean modules and 61 total proposal files**. The protected target and
the original final admission are unchanged. Source inspection and static
dependency checks are distinct from Lean validation; no completed
certificate is claimed for this checkpoint.

## Source-only geometric formalization — 12 November 2026

**This continuation adds Lean proof source, with compilation deliberately
deferred. The final existence theorem is not yet formalized.** No Lean
elaboration, Lake build, language server, kernel replay, or protected
verification was launched for these additions. The written classical argument
below remains the mathematical reference; the new source must still be
checked by Lean before its declarations are counted as verified.

Five flat helpers implement distinct steps of that argument:

| Helper | New source-level construction | Geometric input still required |
| --- | --- | --- |
| [GeometricSeedSmooth.lean](GeometricSeedSmooth.lean) | A full cubic-parameter family exactly containing the existing incidence seed; an explicit nonzero-gradient witness whenever \(r^3\ne0,4\), including literal \(r=57\). | The weighted-projective Jacobian interpretation, geometric smooth opens, and intersection with the relevant rank open. |
| [GeometricProjector.lean](GeometricProjector.lean) | Surjectivity of a positive-metric map gives injectivity of its adjoint composite; rational comparison yields a rational minimal polynomial and the supported projection operator. | Actual geometric cohomology, the Hodge metrics and correspondence comparison, and a submodule realized by divisor-supported cycles. |
| [GeometricLeray.lean](GeometricLeray.lean) | The explicit edge-kernel decomposition and the passage from graded identity to identity on the full first-piece class when the next filtration piece vanishes. | The actual Leray filtration, edge map, invariant hyperplane lift, correspondence action, and restriction maps. |
| [GeometricDeRham.lean](GeometricDeRham.lean) | The existing actual rational exterior derivatives form a Mathlib cochain complex; its degree-four homology is canonically identified with the protected rational-form quotient. | Comparison with algebraic forms on an affine open and with its Betti cohomology. |
| [GeometricExistence.lean](GeometricExistence.lean) | The Leray and affine-comparison implications are assembled into the exact rational primitive and protected certificate statements, with their hypotheses explicit. | A concrete construction satisfying those geometric hypotheses for the protected source. |

The affine comparison has the correct two-map shape. It compares regular
algebraic de Rham cohomology with Betti cohomology on the **same affine open**;
a separate map then restricts regular forms to the function field. The new
assembly does not assume an injection from arbitrary rational-form cohomology
into the cohomology of a single fixed open.

The seed calculation preserves an important distinction. The written proof
uses \(r^3=2\), whereas the existing incidence implementation contains literal
\(r=57\) over the complex numbers. In their common full cubic family the
equation is

\[
F_{r,b}=x_0^6+x_1^6+x_2^6+x_3^6+w^3
       +(2-r^3)x_1^3x_3^3+b^2.
\]

The middle two gradient equations at \(b=0\) have determinant
\(4-(2-r^3)^2=r^3(4-r^3)\). This yields the new witness for the actual
literal-57 family without identifying 57 with a cube root of two. The zero
cubic is a point of the full parameter space; it is not claimed to belong to
the normalized incidence chart with leading cubic coefficient one.

At this checkpoint the proposal had **55 Lean modules and 57 total proposal files**.
All five helpers are reachable from `Solution.lean`. The existing theorem
bodies are preserved, including the one explicit admission in
`Submission.missing_geometric_existence`; the new helpers add none.

### What prevents the unconditional endpoint

Source inspection of the pinned Mathlib and existing proposal did not locate
the geometric Serre/semiregularity comparison, the moving-curve Abel--Jacobi
construction, a polarized variation with its actual Jacobian-ring comparison,
the supported algebraic correspondences, or the required algebraic de Rham
comparison. The existing algebraic modules are not implementations of these
geometric theorems. Their constructions and hypotheses must be formalized
before `GeometricExistence` can be applied to the actual protected variety.

Independent source review checked the new algebra, comparison directions,
and named APIs against the pinned library. It found no definite mathematical
contradiction in the targeted portions of the written argument; that review
does not certify the whole classical proof or establish that the new Lean
files elaborate. No certificate without the existing admission is claimed.

## Local modular compilation — 12 November 2026

The 50-module modular checkpoint compiled locally after fixing elaboration
errors in `SolutionSupport08.lean` and `SolutionSupport09.lean`. All 50
proposal modules and the generated `HodgeTarget` compiled from source, in
dependency order, using Lean 4.33.1 and Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. The run used one Lean worker and
an 8,192 MiB Lean memory limit. The successful compilation steps took a
combined 2,755.53 seconds, excluding failed attempts; the largest
reported per-process peak RSS was 5,128,650,752 bytes.

The compiled fixes have SHA-256
`feab4aede408385dd0c4759c5a9f34ce7cc86614416a8f8d1945e8c9170f9997`
for `SolutionSupport08.lean` and
`df1eea70354d117e377d294cc483355a7a35d977a11a1c81e41aed584a705134`
for `SolutionSupport09.lean`. The compilation used the other proposal sources
from modular checkpoint `2493df96772fbace8f9689cf7ab3f346e280d926`.
This build did not include the five later source-only helpers or the later
changes to `Solution.lean` described above.

This is a development build, not protected verification or independent kernel
replay. The existing `sorry` in `Submission.missing_geometric_existence`
remains, and the final certificate depends on `sorryAx`. The geometric
existence theorem and complete certificate are therefore still unproved.

## Modular source layout — 12 November 2026

**This is a source-organization refactor of the incomplete proof.** The
previous large modules are split into flat, separately importable helpers,
with small compatibility modules retaining their original names. The final
`Solution.lean` contains the original existence obligation, certificate
implication, and endpoint axiom reports. The existing
`Submission.missing_geometric_existence` admission remains.

The preserved source checkpoint is
[`2cb80949c1d0`](https://github.com/fqlx/sextics/commit/2cb80949c1d060bd884bef43cae335ee188d245e).
The split retains declaration order, complete theorem and definition bodies,
namespace contexts, and scoped elaboration settings. Most boundaries follow
the existing complete components. Three large literal-data components are
divided only between complete public definitions, with their original
namespace and option contexts reopened in each part.

The repository accepts flat `Proposal.Helper` modules and limits a proposal
to 64 files. Its verifier compiles and independently replays every submitted
Lean module, including unused ones. The 55 `Current*.lean` files, which are
outside the active geometric proof's import closure, are therefore retained
at the pinned checkpoint rather than submitted with this geometric route.
The [preserved current route](#preserved-current-route) remains available for
further work. The [source layout](#source-layout) below lists the new helpers.

At this modular checkpoint, the proposal contained **50 Lean modules and 52
total proposal files**, leaving 12 file slots below the limit. There are 43 numbered body modules,
four import facades, the final `Solution.lean`, and the unchanged `Workspace`
and `GeometricSeed`. The largest module has **4,795 lines**. Structural checks
verify complete source-body coverage, matching copied bytes, balanced scopes
at the new boundaries, the original scoped settings, an acyclic import graph,
and reachability of every submitted Lean helper from `Solution`. No proof
body, declaration visibility, protected target, verifier, or workflow was
changed, and no admission or axiom was added.

An independent audit matched **9,061 declaration bodies and their source-level
qualified names**, checked **543 exact copied byte segments**, and verified
complete, disjoint coverage of the original bodies. The only changed source
text inside those bodies is the explanatory archive comment before the final
entry point; every endpoint declaration remains byte-for-byte unchanged.
All retired current-route files were also checked to be proposal additions,
absent from the immutable upstream base, so their retirement preserves the
submission's one-instance, additions-only boundary relative to that base.

Smaller modules permit separate compilation and reuse of unchanged compiled
dependencies. They do not remove the memory needed to load those dependencies
or make an expensive individual theorem cheaper. No reduction in peak memory
or total protected-verifier time is claimed without a matching measurement.
At this modular source checkpoint, the full newly split dependency graph had
not yet completed a fresh Lean build or independent kernel replay. The later
local compilation and its limits are recorded above. Historical successful
compilations below apply to their exact original filenames and source hashes,
not to the new module layout.

### Bounded compilation sample

The new actual `Proposal.GeometricFormalInputs01` module compiled successfully
with exit 0 in **395.50 seconds**, using one worker and a **5,120 MiB** Lean
memory cap. Its sampled peak process-tree RSS was **5,353,160,704 bytes**.
The compiled source SHA-256 is
`70276723f9bf3370ad7d7444989d29e110c548d51c1429e8ffa1315bc665c454`.
The test used verified unchanged dependencies and compiled the new module
from source; no monolithic artifact was renamed or substituted.

The adjacent `Proposal.GeometricFormalInputs02` module then compiled
successfully with exit 0 in **245.22 seconds**, importing the newly compiled
first module. Its source SHA-256 is
`67b85d98deda614126cfe43e1f7a44619f64091ef98d73e473f618d7c34dbed3`;
sampled peak process-tree RSS was **4,898,963,456 bytes** under the same limits.
These two successful samples cover 9,414 source lines and one new import
boundary. They do not establish that all 50 modules compile together.

An earlier sample under a 4,096 MiB Lean cap failed after 30.56 seconds with
Lean's `memory_exception` from the interpreter. This was a configured Lean
memory-limit failure, not evidence that the smaller file contained a proof
error or that the operating system ran out of memory. The successful retry
used a 6,144 MiB process-tree RSS guard and a 2,048 MiB available-memory
reserve. This sample does not establish compilation of every new helper,
independent kernel replay, or protected acceptance.

The continuing original build completed the full `GeometricTarget` module
successfully on 12 November 2026: exit 0, 1,047.63 seconds, sampled peak
process-tree RSS 5,500,706,816 bytes. Its source SHA-256 was
`c8fdd4b50a68e3d28e5ce8ddf352200d87a4dedf5858b80346b854558a89a595`.
That result is evidence about the source before this split.

## Historical monolithic compilation checkpoint — 12 November 2026

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

## Earlier Lean source continuation — 12 November 2026

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

All 55 `Current*.lean` files are preserved unchanged at
[the source checkpoint before modularization](https://github.com/fqlx/sextics/tree/2cb80949c1d060bd884bef43cae335ee188d245e/data/cycle-q2).
They are outside the active geometric proof's dependency closure and have
been removed from this proposal's submitted file set to make room for the
smaller geometric helpers.
[CurrentData.lean](https://github.com/fqlx/sextics/blob/2cb80949c1d060bd884bef43cae335ee188d245e/data/cycle-q2/CurrentData.lean) retains its 13,874
expressions and literal `transportError`, whose vanishing is not assumed.
[CurrentCorrection.lean](https://github.com/fqlx/sextics/blob/2cb80949c1d060bd884bef43cae335ee188d245e/data/cycle-q2/CurrentCorrection.lean) retains reconstruction and
`originalGoal_iff_actual_current_correction`: a future completed geometric
proof would imply that correction existential as well.

The denominator, normal-gauge, tangent and ambient-lift developments remain
available at the same immutable checkpoint. No claim about the unresolved
current correction changes in this refactor.

## Source layout

The five formerly large files retain their names as compatibility modules
or the final entry point. Their declarations now live in numbered helper
modules, ordered as in the original sources. `Workspace` and `GeometricSeed`
retain their original source bodies. Each helper imports its predecessor,
and the first helper in a group imports the original prerequisite modules.

| Compatibility module or entry point | Numbered helpers | Largest helper, lines | Mathematical scope |
| --- | --- | ---: | --- |
| [GeometricFormalInputs.lean](GeometricFormalInputs.lean) | `GeometricFormalInputs01`–`04` (4) | 4,758 | Affine residue/certificate bridge, foundational inputs, pole reduction, and exterior differentials. |
| [GeometricTarget.lean](GeometricTarget.lean) | `GeometricTarget01`–`11` (11) | 4,795 | Target actions, finite descent, incidence and seed calculations, projectors, and finite top de Rham constructions. |
| [Assembly.lean](Assembly.lean) | `Assembly01`–`10` (10) | 4,757 | Conditional assembly, restriction calculations, actual Gaussian-action data, and Cech components. |
| [Normalization.lean](Normalization.lean) | `Normalization01`–`09` (9) | 4,621 | Radial normalization and the remaining modular-action and cubic literal data. |
| [Solution.lean](Solution.lean) | `SolutionSupport01`–`09` (9) | 4,786 | Normal and conormal classes, residue and surface comparisons, character components, and orbit trace; the final obligation remains in `Solution.lean`. |

The large basepoint, Gaussian-action, and cubic-data components are split
between complete definitions, retaining each original literal coefficient.
Every supporting declaration precedes the final admitted theorem in the
import graph, so the new helpers cannot depend on that admission. The exact
existence theorem and certificate bodies remain unchanged. Counts and the
source-preservation audit for this modular layout are recorded in the
current checkpoint above; the historical component totals below describe
their earlier consolidation checkpoints.

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

In the historical layout, 55 legacy Lean files outside the active
seven-module `Proposal` import closure had not been rebuilt against the
new import environment. They are preserved at the checkpoint linked under
[Preserved current route](#preserved-current-route) and are no longer part
of the modular geometric proposal. No new verification of those archived
sources is claimed.

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

Here is a direct geometric binding of that assertion at Fermat. The
ordinary sextic Y={F(x,t^2)=0} in P^4 is smooth near Fermat and maps to
the weighted threefold by w=t^2, as the quotient by t -> -t. Finite
quotient cohomology identifies the weighted variation with the invariant
ordinary variation. The literal Euler-volume pullback is

  phi^*Omega_weighted = 2t Omega_ordinary.

Thus a weighted Hodge numerator x^a w^b pulls back to 2x^a t^(2b+1),
of ordinary degree seven; a degree-six deformation numerator pulls
back to x^m t^(2n). The two Hodge numerators contribute the extra t^2
in the ordinary triple product. Weighted exponents sum to (4,4,4,4,1)
exactly when the corresponding ordinary exponents sum to (4,4,4,4,4),
the ordinary Fermat socle. Ordinary Griffiths residue theory identifies
multiplication with the infinitesimal period map and this socle with
the polarization, up to one common nonzero factor. Pullback multiplies
the intersection pairing by the cover degree two; this only changes
the same common normalization. All 38115 triple comparisons and the
five volume coefficients were checked exactly in the 13 November audit.

The normalized full coefficient chart has dimension 44: there are 45
invariant sextic monomials before setting the w^3 coefficient to one.
The 35 standard monomials above span its effective Jacobian tangent
directions, not the whole coefficient tangent space. The irreducibility
argument concerns rational sub-variations over that full base and its
finite etale covers. It does not assert irreducibility of an arbitrary
underlying local subsystem or of the restriction to the protected pencil.

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
The relative line bundle is an actual family, not just a collection of
fiberwise choices. Shrink Z to a contractible Stein polydisc S. The
smooth proper surface family is topologically locally trivial, and the
flat integral class lifts to H^2(D_S,Z) over this contractible base.
Grauert's theorem and Stein acyclicity identify H^2(D_S,O) with
H^0(S,R^2 pi_*O). The class maps to zero there by the Hodge-locus
condition. The exponential sequence therefore gives a holomorphic
line bundle on D_S with this first Chern class. On the central fiber
it is O_D(E), by H^1(O_D)=0. There is no global Poincare-bundle
assumption or unaccounted obstruction to this local construction.

For m sufficiently large, Serre vanishing, cohomology/base change and Bertini give a
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
genus are determined by the flat class lambda+mH. Use a sufficiently
high even Veronese embedding of the weighted ambient space, and form
the algebraic flag Hilbert scheme H parameterizing (T,D,Gamma), locally
where the surface and curve are smooth and Gamma is Cartier on D.

The analytic family has a holomorphic map to H^an. To construct the map
as a family, take a large uniform ambient twist of the nearby curve
ideals. Analytic cohomology and base change give a vector subbundle of
the fixed ambient space of homogeneous sections. Its Grassmannian map
satisfies the multiplication and incidence equations defining the
Hilbert scheme and the flag condition. Pointwise Chow's theorem alone
would not establish this family statement.

Let z=(T,D,Gamma), d=dim S, and n=h^0(D,O_D(Gamma)). The analytic
projective bundle in Section 5 has dimension d+n-1 and injective
differential to H^an: the pair coordinates recover the base tangent,
and the complete linear system embeds in the Hilbert scheme of a
fixed surface.

Conversely, every first-order flag deformation gives the line bundle
O_{D_epsilon}(Gamma_epsilon), so its pair direction lies in the kernel
of the total Noether-Lefschetz obstruction. This obstruction equals
that for E because mH is ambient. The initial class and its flat
transport are invariant, so its target is the seven-dimensional
invariant H^{0,2}. Its vertical restriction is already surjective;
the total kernel therefore has dimension d. The kernel of the map
from flag tangents to pair tangents is H^0(Gamma,N_{Gamma/D}). The
exact sequence

  0 -> O_D -> O_D(Gamma) -> N_{Gamma/D} -> 0

and H^1(O_D)=0 give dimension n-1 for this kernel. Hence

  dim T_z H <= d+n-1.

The analytic family gives the reverse inequality on local dimension.
Local dimension and embedding dimension agree; H is smooth at z.
Its projection to the full sextic base has surjective differential,
and its vertical tangent contains the chosen nonzero Abel-Jacobi
direction. The algebraic irreducible component through z therefore
dominates Bpar. This does not assume algebraicity of an arbitrary
analytic Hodge locus.

Let a>=1 be its relative dimension. In a projective completion over
an affine base open, cut by a-1 sufficiently ample relative hypersurfaces
with prescribed first jets at z, so their differentials have common
vertical kernel the chosen Abel-Jacobi line. Bertini with prescribed
finite jets supplies these cuts. The resulting component is smooth
near z and submersive over the base there. Resolve it projectively in
characteristic zero, without changing this smooth neighborhood.
Generic smoothness and properness then give, after shrinking, a smooth
projective family of parameter curves Lambda. It may be disconnected;
Stein factorization and removal of its branch locus give a finite
etale cover if connected fibers are desired.

Nonvanishing survives this shrinking even if the original base point
is removed because a distant point of its fiber was singular. Near z
the map is submersive and the derivative remains nonzero. This analytic
open meets the inverse image of every dense Zariski-open base subset.
Some retained smooth fiber therefore still has a nonzero derivative.
The universal Hilbert family pulls back through the resolved parameter
family and supplies a relative codimension-two algebraic cycle Gamma
on Lambda times_{Bpar'} T. Boundary cycle members may be singular;
smoothness of the projective parameter curves is what is needed here.

The resulting correspondence induces a morphism of rational variations

  R^1 p_{Lambda*} Q(-1) -> R^3 p_{T*} Q.

Its averaged component is nonzero, because its Abel-Jacobi differential
still pairs nontrivially with the invariant class eta_B. This supplies
the genuine nonzero subvariation used in the next Higgs step.

The invariant intermediate Jacobian is an abelian variety because
its Hodge structure has only types (2,1),(1,2). The Abel-Jacobi map of
the projective parameter curve factors through its Jacobian. If its
invariant H^1 cylinder map were zero, that homomorphism would have
zero differential, contradicting the preserved nonzero derivative.
In particular the parameter curve is not being assumed rational.

No Hodge conjecture or algebraicity theorem for arbitrary Hodge loci
is required: divisor algebraicity is Lefschetz (1,1) on surfaces,
and the actual family is obtained by the Hilbert argument above.
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

9. Optional descent to rational polynomial coefficients
--------------------------------------------------------

Although the protected existential statement permits complex
coefficients, the argument also implies existence over Q. Fix the
finite degrees of one complex witness in (8.1). All coefficient
equations are polynomial equations over Q. In the finite-dimensional
homogeneous quotient by (F), choose a rational basis and one coordinate
of the class of D that is nonzero at this witness. Adjoin a variable
whose product with this coordinate is one. This expresses D not in
(F), hence D!=0 and gcd(D,F)=1 because F is absolutely irreducible.

The resulting finite system over Q has a complex point, so it has
a Qbar point and a point over some number field. Pass to a normal
closure K0/Q and write v=N/D for that field-valued rational vector
field. Its normalized trace

  v_Q=(1/[K0:Q]) sum_sigma sigma(v)

is rational over Q. The operator v |-> -2v(F)+F div(v) is Q-linear
and commutes with coefficient conjugation and coordinate derivatives.
Therefore A-2v_Q(F)+F div(v_Q) remains divisible by F^3 in the local
ring at (F). Each conjugate denominator stays prime to F, and their
product supplies a common rational denominator prime to F.
Homogeneous degree seven of the vector components is preserved.
Clearing this product denominator gives an ordinary homogeneous
certificate over Q. This does not supply a degree bound, an expanded
coefficient tuple, or an additional Lean proof.
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
