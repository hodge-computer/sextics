# What the exact-target contact jets supply

This is a read-only audit of `contact/exact_target_contact_jets.py`, its
order-47, precision-400 receipt, and the maintained Lean `PolynomialCurves`
and `HoldoutCover/PolynomialFamilyBridge` interfaces. It does not claim an
actual rational primitive or a proof of `RegularGameExists`.

## 1. The actual linear map in the computation

At the exact weighted fiber with lambda equal to one, the contact equations
are 44 polynomial coefficient identities in 45 contact parameters. Fixing
rho0 supplies a square 44-variable Jacobian. The root enclosure and its
invertible Jacobian give a smooth local contact-parameter curve, with local
coordinate rho0 = 1/4 + t/4096.

After substituting u = -Q1, the script forms the degree-six negative part of
the ideal

    (Q2, G_u(-Q1), g2, A, B).

Its ordinary degree-six negative monomial space has dimension 40. There are
44 displayed ideal-multiple columns. The program selects 39 columns and
normalizes one coordinate of a functional ell to one. The weighted
degree-six negative source space has 60 monomials. Substitution of u=-Q1
pulls ell back to a functional on that 60-dimensional space.

The 48 rows in the reported nonzero minor are the Taylor coefficients of
this latter functional, in orders zero through 47. They are **not** 48
constructed vector fields or rational primitives. Exact annihilation of all
ideal columns and of the target Jacobian directions is required to identify
their common kernel with the 12-dimensional Jacobian subspace. The separate
annihilator audit and exact target Jacobian calculation address those points;
interval containment of zero alone would not establish them.

Once those algebraic identifications hold, the minor proves that the map
from the 48-dimensional negative Jacobian quotient to local functions on
the contact curve is injective. Multiplying the functional by one common
invertible local scalar does not change this conclusion: on jets it acts by
an invertible triangular matrix. Thus choosing a convenient normalizing
coordinate does not invalidate the spanning test.

## 2. Its strongest geometric consequence

Let C be a smooth projective model of the contact component, and let Gamma
be the correspondence from the family of contact curves in the weighted
threefold T. The required normal-obstruction/Abel--Jacobi formula identifies
the local functional, up to the common nonzero normalization, with the
pullback

    Gamma*: H^(2,1)(T)^- -> H^(1,0)(C).

The jet minor then proves injectivity of this entire map. It is stronger
than merely proving that the chosen protected source has nonzero pullback.
Complex conjugation gives injectivity on H^(1,2), and Poincare duality gives
surjectivity of the transpose correspondence

    Gamma_*: H^1(C)(-1) -> H^3(T)^-.

The correspondence image is supported on the surface swept out by the
contact curves. Consequently, after the geometric identifications, the
calculation proves divisor support of the entire negative sector of this
particular weighted fiber. It does not require full-family monodromy or the
Voisin rational-Hodge-density construction.

The invertible contact Jacobian and nonzero jet determinant can spread over
a nonempty open in the actual lambda pencil, after a finite base change.
The affine-base relative argument described by the other audit then handles
the original fourfold. One must use the actual algebraic family and the
resulting correspondence; a single specialized fiber is not the original
fourfold theorem by itself.

The remaining existence route therefore need not evaluate the enormous
moving-point trace algebra. It does still need the geometric correspondence
map, its Abel--Jacobi identification and duality, the relative support step,
and de Rham localization/comparison leading to a rational primitive. Those
theorems are not supplied by the present `PolynomialCurves` modules.

## 3. Why `PolynomialCurves` does not consume the jet packet

The maintained theorem
`ReflectionCoupledFano.normalized_data_from_polynomial_family` requires an
actual finite extension L of the hypersurface function field and a time
variable t. Its hypotheses include all of the following:

- a derivation with D_time(t)=1 which kills the coefficient ring;
- physical coordinate images polynomial in t (`hpolyX`);
- a polynomial normal field (`hpolypsi`);
- preservation of that polynomial subring by the other derivations
  (`hDpoly`);
- an invertible matrix of the normal and the physical tangent directions.

The exact contact computation proves none of these polynomiality hypotheses.
It computes a local algebraic branch of the **contact-parameter** curve.
Its truncated coordinate series are polynomials only after discarding their
uncomputed higher coefficients; they satisfy the incidence equations only
modulo the truncation order. They are not an exact polynomial
parameterization of physical points on T.

Moreover, each smooth norm-contact curve is a (2,3) complete intersection in
P^3 after eliminating u, hence has genus four. Its universal incidence is a
surface in T, supplying a divisor support rather than a dominant rational
curve parameterization of the threefold. The old finite moving-point algebra
is finite over the projected (r,s) plane; that fact does not turn either
curve into a rational time line.

## 4. Finite jets cannot be substituted for the separable trace construction

There are two exact elementary obstructions to that substitution.

First, in characteristic zero, differentiation with D(t)=1 does not descend
to k[t]/(t^48). Differentiating its defining relation would give

    0 = D(t^48) = 48 t^47,

although t^47 is nonzero. Thus the truncated ring cannot carry the time
derivation needed by the polynomial integration theorem.

Second, multiplication by f(t) on k[t]/(t^48), in the power basis, is
triangular with constant diagonal f(0). Its algebra trace is 48 f(0), so its
normalized trace kills every positive-order jet. It cannot recover the
48 independent coefficient functionals by the finite separable field trace
used in the current formulas. A coefficient-extracting residue functional
is a different linear functional; it does not satisfy the needed trace and
derivation identities merely because it extracts the desired Taylor term.

This does not diminish the jet-rank theorem. It explains precisely why a
finite local spanning witness can prove a global geometric rank statement
without itself being a rational primitive.

## 5. Literal source matching remains a separate operation

The canonical form eta_R on the contact curve is a pullback of the source.
Pushing it back gives the correspondence composition Gamma_* Gamma*, not
automatically R. The new full-rank result can establish invertibility of
this composition through polarization and duality, without computing it.
It does not give its inverse coefficients as rational-function trace values.

An existence proof may choose the appropriate preimage nonconstructively,
use its supported cohomology class, and then invoke the support-to-certificate
argument. An explicit-current proof instead needs a chosen closed form,
its actual pushforward, and the exact differential correction. Neither
dividing by the cover degree nor differentiating the normalized obstruction
functional supplies that correction.

No new denominator screens, geometric assumptions disguised as conclusions,
or conditional replacement for `RegularGameExists` are introduced here.
