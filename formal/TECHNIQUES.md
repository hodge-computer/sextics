# A guide to the certificate library

Start with the [formal contract](README.md), then choose the construction whose hypotheses match your `(F, q, A)`. The library supplies reusable theorems; the accepted applications show how to discharge their geometric, algebraic and target-specific hypotheses. A similar-looking equation alone does not establish those hypotheses.

This is the current account of the available techniques. Each instance’s `why.md` retains the perspective just before its solution; its `solution.md` explains the proof and credits its sources.

## Assemble and transport certificates

| Task | Import and entry point | Obligations retained |
| --- | --- | --- |
| Check an explicit tuple | [`Constructions.Explicit`](lean/HodgeComputer/Constructions/Explicit.lean): `Verify.of_normalized` | Both normalized differential identities, exact integer degree balance, nonzero homogeneous `F` and `D`, source homogeneity, and coprimality. `Q` may be nonzero. |
| Prove denominator legality on a fiber | The same module: `relPrime_of_chart_specialization` | A chart with a left inverse, unit leading coefficient of the hypersurface **before** specialization, and a coprime specialized pair. |
| Add certificates | [`CertificateOperations`](lean/HodgeComputer/CertificateOperations.lean): `Verify.add`, `HasCertificate.add` | The same hypersurface and pole parameter. Denominators and quotient remainders may differ; the theorem constructs their product denominator. |
| Apply a sign involution | [`CoordinateChanges`](lean/HodgeComputer/CoordinateChanges.lean): `Verify.sign_change` | Each coordinate multiplier squares to one. The theorem transforms the field components as well as `F`, `A`, `D` and `Q`. |
| Reorder coordinates | The same module: `HasCertificate.rename` | An equivalence of the variable indices. This works in every ambient dimension. |
| Rescale a denominator and its numerator together | [`HodgeTestbed.Algebra`](lean/HodgeTestbed/Algebra.lean): `Equations.scale` | The quotient scales by the square of the multiplier. Legality and grading of the new denominator are separate obligations. |
| Clear a rational substitution homogeneously | [`RationalFields.CommonDenominatorSubstitution`](lean/HodgeComputer/Constructions/RationalFields/CommonDenominatorSubstitution.lean): `cleared_homogeneous`, `map_cleared`, `not_dvd_cleared` | A total-degree bound and equally homogeneous coordinate numerators and common denominator. Legality follows from the displayed prime pullback test, without assuming rational denominators are nonzero beforehand. |
| Transport contraction with the Piola current | [`ResidueTransport.PiolaContraction`](lean/HodgeComputer/Constructions/ResidueTransport/PiolaContraction.lean): `HoldoutConstruction.piola_contraction` | An inverse coordinate matrix and its chain rule, for an arbitrary finite coordinate set. Together with `piola_divergence`, this transports both normalized current equations; the application supplies its chart and source. |

The accepted [holdout-q2](../data/holdout-q2/solution.md) and [quadric-contact-broken](../data/quadric-contact-broken/solution.md) proofs use the bounded homogeneous-clearing constructor for their parameter substitutions. Their specialized evaluation and good-specialization interfaces remain in the application files. The Piola contraction identity supplies the normal term of [`residue_piola_pullback`](lean/HodgeComputer/Constructions/HoldoutCover/ResiduePiolaPullback.lean), used by the accepted residue-transport constructions.

The 41 small explicit witnesses now share their assembly and legality interface. They still prove their own polynomial identities and bind the exact displayed tuple to the protected witness. Their contact, cofactor and norm interpretations are developed in [Chapter 2](../docs/02-explicit-constructions.md); a checked individual tuple is not a general existence theorem for that interpretation.

For the Fermat sextic, [`Constructions.Fermat`](lean/HodgeComputer/Constructions/Fermat.lean) supplies the stronger theorem `HodgeComputer.Fermat.certificate`: every homogeneous odd source at `q = 1` or `q = 2` has a certificate. Its subset Euler construction and finite subset assertion are proved in Lean. The original `fermat-q2` application retains its own displayed witness.

## Construct primitives and clear them

| Construction | Library | What remains with an application |
| --- | --- | --- |
| Fermat cover and moving conic for the fixed holdout sextic | [HoldoutCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md), especially `HoldoutGeneralization.certificate_of_source_pair` | The quotient-source identity, its normal derivative identity and trace-zero correction. Different quotient equations need their own geometry. |
| Lift an incidence seed and integrate on a polynomial curve | [PolynomialCurves](lean/HodgeComputer/Constructions/PolynomialCurves/README.md) | A nonsingular incidence seed, finite extension, dominance, polynomial normal and exact source transport. |
| Contract two supplied elliptic companion primitives | [EllipticCompanions](lean/HodgeComputer/Constructions/EllipticCompanions/README.md), `CrossedElliptic.product_divergence` | The companion equations and scalar primitives, independence, embeddings and physical closure. The elliptic curve here is the Fermat cubic. |
| Integrate a third-order pole along a polynomial family | [HigherResidues](lean/HodgeComputer/Constructions/HigherResidues/README.md) | The polynomial family, actual numerator/determinant jets, finite descent and certificate closure. |
| Construct a contact field over a finite algebra | [FiniteAlgebra](lean/HodgeComputer/Constructions/FiniteAlgebra/README.md) | The contact line, finite algebra, source-span calculation, specialization and denominator checks. |
| Correct a cubic-surface field from pole one to pole two | [CubicSurfaces](lean/HodgeComputer/Constructions/CubicSurfaces/README.md), `Q2Reduction.q2_equations` | A homogeneous cubic, a Jacobian representation of the source and a strict primitive for the resulting divergence. |
| Correct and homogenize a rational field | [RationalFields](lean/HodgeComputer/Constructions/RationalFields/README.md) | Commuting derivations, a normal field and primitive, actual chart rules, and the Euler degree condition. |

Several broadly reusable steps still live under `HoldoutCover`: `PolynomialNormal` constructs normals from invertible coefficient matrices; `FiniteTrace` descends primitives; `ResidueClearing`, `FiniteResidueClearing` and `HomogeneousCertificate` clear and grade their polynomial witnesses. Those modules expose explicit hypotheses. In contrast, `GeneralizedCover` fixes the holdout hypersurface. The directory name does not make every theorem a result about arbitrary hypersurfaces.

## Cubic covariants and moving maps

There are four distinct coefficient families:

- [BinaryCubic](lean/HodgeComputer/Constructions/BinaryCubic/README.md) supplies four-coefficient Hessian/discriminant identities and the radial cancellation used by the dense two-ternary witness.
- [CyclicCubic](lean/HodgeComputer/Constructions/CyclicCubic/README.md) treats `a x³ + b y³ + c z³ + d x²y + e y²z + f z²x`.
- [TransitiveCubic](lean/HodgeComputer/Constructions/TransitiveCubic/README.md) replaces the last monomial by `f x²z`.
- [PolarCubic](lean/HodgeComputer/Constructions/PolarCubic/README.md) treats `a x³ + b y³ + c z³ + d x²y + e y²z + f xy²` and its first-order `2kxyz` perturbation.

The cubic applications import their coefficient identities directly. These families have different covariants; substituting one family’s tables into another would change the mathematics.

All four Jacobian applications use the common dual-number chain rule and first variations in [`ResidueTransport.FirstJets`](lean/HodgeComputer/Constructions/ResidueTransport/FirstJets.lean). Their remaining `CubicJetCalculus.lean` files prove the family-specific cleared differential and cubic variation. [ResidueTransport](lean/HodgeComputer/Constructions/ResidueTransport/README.md) also supplies density changes, moving-map corrections, normal changes and the coordinate-independence criterion. Constructing the Jacobian primitive and checking the physical source remain application obligations.

## Accepted applications

The following index covers every accepted solve. The construction column describes the argument in its linked explanation; the shared entry column identifies the reusable code it uses. “Explicit witness” means shared checking and assembly, with the particular construction still established by its exact tuple.

| Application and explanation | Construction | Shared entry |
| --- | --- | --- |
| [block-q2](../data/block-q2/solution.md) | A binary block and its compatible degree-twelve bundle | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [cofactor-eight](../data/cofactor-eight/solution.md) | Work in a quadratic–cubic coordinate map | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [cofactor-mixed](../data/cofactor-mixed/solution.md) | Move the passive variables inside the quadratic map | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [collision-h3](../data/collision-h3/solution.md) | A line with triple contact | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [completed-square-nambu-holdout](../data/completed-square-nambu-holdout/solution.md) | Complete the square before constructing the field | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [cone-ladder-linear](../data/cone-ladder-linear/solution.md) | A hyperplane certificate from the contact ladder | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [contact46006](../data/contact46006/solution.md) | Start with a plane contact presentation | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [coupled-pair-rational-d4-strict](../data/coupled-pair-rational-d4-strict/solution.md) | Deform the sextic while retaining a logarithmic field | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [crossed-ternary-asymmetric](../data/crossed-ternary-asymmetric/solution.md) | A moving conic companion and algebraic elliptic contraction | [EllipticCompanions](lean/HodgeComputer/Constructions/EllipticCompanions/README.md) |
| [cycle-three](../data/cycle-three/solution.md) | A paired-sign cubic and its Jacobian residue primitive | [CyclicCubic and ResidueTransport](lean/HodgeComputer/Constructions/CyclicCubic/README.md) |
| [cyclic-triple-fano](../data/cyclic-triple-fano/solution.md) | A free weighted line and cubic pullback | [PolynomialCurves and coordinate changes](lean/HodgeComputer/CoordinateChanges.lean) |
| [f3-block-x0-quartic-strict](../data/f3-block-x0-quartic-strict/solution.md) | A contact conic in the square-coordinate plane | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-block-cube](../data/family-block-cube/solution.md) | An osculating cube for a binary cubic | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-hesse-web](../data/family-hesse-web/solution.md) | Three contact channels over a cubic algebra | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-passive-contact](../data/family-passive-contact/solution.md) | A linear-contact constituent of a larger family | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-root-cube](../data/family-root-cube/solution.md) | A weighted split rather than a separated sum | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-shear](../data/family-shear/solution.md) | Expose a product with opposite weights | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-sylvester-norm](../data/family-sylvester-norm/solution.md) | Diagonalize the binary cubic over its Hessian field | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [family-trace-zero](../data/family-trace-zero/solution.md) | A trace-zero rotation inside a cubic complement | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [fermat-pair-rational-d4-strict](../data/fermat-pair-rational-d4-strict/solution.md) | A quartic cofactor of two sixth powers | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [fermat-q2](../data/fermat-q2/solution.md) | A subset Euler field at pole order two | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [fixed-witness-hesse-cofactor-d4-rational](../data/fixed-witness-hesse-cofactor-d4-rational/solution.md) | Reveal a hidden cubic identity | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [hesse-radial-hesse-cofactor-d4-rational](../data/hesse-radial-hesse-cofactor-d4-rational/solution.md) | Pull back the Hesse cofactor | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [hesse-triangle](../data/hesse-triangle/solution.md) | Split the sextic into a Hesse triangle and a radial part | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [holdout](../data/holdout/solution.md) | The holdout certificate from a Fermat cover and a moving conic | [HoldoutCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-all-six](../data/holdout-all-six/solution.md) | A Fermat-cover certificate for \(X_{0} X_{1} X_{2} Y_{0} Y_{1} Y_{2}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-bundle](../data/holdout-bundle/solution.md) | Complementary diagonal quotient and moving-conic certificate | [Polynomial normals, finite trace, certificate addition](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-moving-branch](../data/holdout-moving-branch/solution.md) | A transitive Jacobian primitive for the moving branch | [TransitiveCubic and ResidueTransport](lean/HodgeComputer/Constructions/TransitiveCubic/README.md) |
| [holdout-p-y14](../data/holdout-p-y14/solution.md) | A Fermat-cover certificate for \(X_{2} Y_{1}^{4} Y_{2}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-p3](../data/holdout-p3/solution.md) | A Fermat-cover certificate for \(X_{2}^{3} Y_{2}^{3}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-q2](../data/holdout-q2/solution.md) | A finite-algebra certificate for holdout-q2 | [FiniteAlgebra and CubicSurfaces](lean/HodgeComputer/Constructions/CubicSurfaces/README.md) |
| [holdout-ternary-deformation](../data/holdout-ternary-deformation/solution.md) | A replacement conic for the ternary deformation | [PolynomialCurves and HoldoutCover](lean/HodgeComputer/Constructions/PolynomialCurves/README.md) |
| [holdout-x0-x14-y0](../data/holdout-x0-x14-y0/solution.md) | A Fermat-cover certificate for \(X_{0} X_{1}^{4} Y_{0}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-x0-y03-y12](../data/holdout-x0-y03-y12/solution.md) | A Fermat-cover certificate for \(X_{0} Y_{0}^{3} Y_{1}^{2}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-x04-p](../data/holdout-x04-p/solution.md) | A Fermat-cover certificate for \(X_{0}^{4} X_{2} Y_{2}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-x1-y04-y1](../data/holdout-x1-y04-y1/solution.md) | A Fermat-cover certificate for \(X_{1} Y_{0}^{4} Y_{1}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-x12-p-y02](../data/holdout-x12-p-y02/solution.md) | A Fermat-cover certificate for \(X_{1}^{2} X_{2} Y_{0}^{2} Y_{2}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [holdout-x13-y13](../data/holdout-x13-y13/solution.md) | A Fermat-cover certificate for \(X_{1}^{3} Y_{1}^{3}\) | [GeneralizedCover](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [klein-hesse](../data/klein-hesse/solution.md) | Move from Klein monomials to Hesse coordinates | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [klein-rational](../data/klein-rational/solution.md) | Use the cyclic monomial map | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [m3-coupled](../data/m3-coupled/solution.md) | A conic hidden in quadratic coordinates | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [mixed-biweight](../data/mixed-biweight/solution.md) | A Jacobian primitive for the asymmetric mixed biweights | [TransitiveCubic and ResidueTransport](lean/HodgeComputer/Constructions/TransitiveCubic/README.md) |
| [mixed-polar](../data/mixed-polar/solution.md) | A reverse-edge Jacobian construction for the balanced mixed-polar target | [PolarCubic and ResidueTransport](lean/HodgeComputer/Constructions/PolarCubic/README.md) |
| [one-reflection](../data/one-reflection/solution.md) | A strict certificate from a binary-cubic Hessian construction | [Coordinate changes and certificate addition](lean/HodgeComputer/CoordinateChanges.lean) |
| [one-reflection-y2-sector](../data/one-reflection-y2-sector/solution.md) | A certificate for `one-reflection-y2-sector` from a Fermat cover and a moving conic | [HoldoutCover calculus; specialized quotient](lean/HodgeComputer/Constructions/HoldoutCover/README.md) |
| [passive-quadratic-d4-strict-rational](../data/passive-quadratic-d4-strict-rational/solution.md) | A rational norm of two contact factors | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [polarized-contact-coupled-d2](../data/polarized-contact-coupled-d2/solution.md) | A contact field with two first integrals | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [polarized-contact-deformation-d2](../data/polarized-contact-deformation-d2/solution.md) | Deform by a multiple of the preserved divisor | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [quadric-contact-broken](../data/quadric-contact-broken/solution.md) | A finite-algebra contact certificate for `quadric-contact-broken` | [FiniteAlgebra](lean/HodgeComputer/Constructions/FiniteAlgebra/README.md) |
| [reflection-coupled-fano](../data/reflection-coupled-fano/solution.md) | A modular quartic, finite trace, and the reflection certificate | [PolynomialCurves](lean/HodgeComputer/Constructions/PolynomialCurves/README.md) |
| [split-ternary-q2](../data/split-ternary-q2/solution.md) | Polynomial companions and higher residues for split ternaries | [HigherResidues and EllipticCompanions](lean/HodgeComputer/Constructions/HigherResidues/README.md) |
| [ternary-collision-cb-d2](../data/ternary-collision-cb-d2/solution.md) | The first collision character | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [ternary-collision-cbp-d2](../data/ternary-collision-cbp-d2/solution.md) | The second character of a contact collision | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [ternary-tangent-residual-h2-d2](../data/ternary-tangent-residual-h2-d2/solution.md) | Contact geometry supplies a quadric | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [three-block-rational-d4-strict](../data/three-block-rational-d4-strict/solution.md) | A cyclotomic cofactor across blocks | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [tie-offblock-ytype-d4-strict-rational](../data/tie-offblock-ytype-d4-strict-rational/solution.md) | A Hesse cofactor with a passive multiplier | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [tie-singleton-3odd-strict](../data/tie-singleton-3odd-strict/solution.md) | Combine an active correction with passive radial motion | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [two-reflection-cubic-surface-d2](../data/two-reflection-cubic-surface-d2/solution.md) | A rotation field with a radial denominator | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [two-ternary-dense-two-odd-hessian-d48](../data/two-ternary-dense-two-odd-hessian-d48/solution.md) | A rational certificate from ternary cubic covariants | [BinaryCubic and RationalFields](lean/HodgeComputer/Constructions/BinaryCubic/README.md) |
| [twoblock-cubic](../data/twoblock-cubic/solution.md) | A fixed denominator serving a companion bundle | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [twoties-crossblock-hesse-cofactor-d4-rational](../data/twoties-crossblock-hesse-cofactor-d4-rational/solution.md) | Use the second tie and keep the multiplier passive | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [twoties-tie2-x2-quartic-strict](../data/twoties-tie2-x2-quartic-strict/solution.md) | Localize the contact construction to the second block | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [xtype-sparse-rational-1m142](../data/xtype-sparse-rational-1m142/solution.md) | A compatible target bundle | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [xtype-strict-rational-113](../data/xtype-strict-rational-113/solution.md) | Interpolating along a binary-cubic pencil | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [ytype-companion-231-d4-strict-rational](../data/ytype-companion-231-d4-strict-rational/solution.md) | A second rational companion | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |
| [ytype-companion-fiberA-d4-strict-rational](../data/ytype-companion-fiberA-d4-strict-rational/solution.md) | A quadratic norm in squared coordinates | [Explicit witness](lean/HodgeComputer/Constructions/Explicit.lean) |

## Reading and extending the library

Read a module’s hypotheses before adapting its worked application. Keep a new target’s constants, incidence seeds and final protected binding together in its instance folder. The shared implementation is the place for parameterized identities and established constructions, with attribution to the proofs from which they came. [MAINTAINING.md](../MAINTAINING.md) describes shared-module kernel replay and verification of dependent applications.
