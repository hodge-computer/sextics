# Independent audit: nonzero protected target form

The three independent replay checks passed:

1. `contact_lift_independent_audit.py` reconstructs the 46 contact and moving-point equations from the original six-variable symmetric sextic and verifies the exact contraction and incidence bounds.
2. `contact_lift_regularity_audit.py` reconstructs the four homogeneous forms and verifies the degree-10 Macaulay minor on the entire certified root ball.
3. `contact_lift_nonzero_audit.py` independently reconstructs the original target source, the four-variable Jacobian by its 24-permutation determinant, the normalized degree-9 residue system, and the root tangent enclosure. It verifies that the protected target residue functional is nonzero at the actual contact point.

These are classical exact-arithmetic certificates, not Lean proofs. The scripts use adjacent witness files; the underlying algebra uses rational real and imaginary parts throughout. NumPy is used only for supplementary numerical singular values in the first audit. Python-flint accelerates exact integer matrix products; the matrix-product helper has a pure-Python fallback.

## Target and sign

With the original sextic evaluated at

`(X0,X1,X2,Y0,Y1,Y2) = (a+v,a-v,b,c+v,c-v,d)`,

and `u = v^2`, the weighted cubic has leading coefficient `ell = 13/7` at `lambda = 1`. The monic model is the original weighted cubic divided by `ell`.

The protected homogeneous source is

`R = 2*b*d*(a^2-u)*(c^2-u)/ell^2`.

After eliminating `f1 = u+Q1`, this is exactly

`Rbar = (98/169)*b*d*(a^2+Q1)*(c^2+Q1)`.

The sign agrees with the positive six-variable coordinate Jacobian. The local protected density contains an additional chart factor `z`; that factor is not an extra homogeneous multiplier in the degree-6 source above.

## Canonical normalization

The ordered four-variable forms are

`(Q2, h=A+B, Gu(-Q1), g2)`,

of degrees `(2,3,4,4)`. The separately verified degree-10 surjectivity implies that their quotient is an Artinian complete intersection. Its Hilbert function is

`[1,4,9,15,19,19,15,9,4,1]`,

so its length is `96` and its socle degree is `9`. The selected 219 independent ideal columns span the degree-9 ideal. Appending the Jacobian and normalizing the final equation to `tau(Jac) = 96` therefore specifies the canonical residue functional, rather than an arbitrary functional annihilating only some selected relations.

Eliminating the first form `u+Q1` from the ordered five-variable system has positive determinant sign: the `u` cofactor is row 0, column 4. There is no additional factor of two in this normalization.

## Tangent and nonzero result

The tangent is normalized by `D(rho0)=1`. If `Jactive` is the 46-by-46 root Jacobian and `F_rho0` is the omitted parameter column, its other coordinates are

`-Jactive^(-1) * F_rho0`.

The independent audit recomputes its enclosure directly from the original equations and the stored rational root inverse. It does not take the root receipt's numerical bounds on trust.

The exact rational center of `tau(Rbar * D(h))` has decimal approximation

`0.015943842399174287 + 0.0047796044116877505 i`.

The rigorous scalar one-norm error is less than `10^-8`. The residue-vector error is less than `10^-11`, and the tangent error is less than `10^-23`. The real-part interval is strictly positive, proving nonzero at the actual certified contact point.

The complete exact inequalities and witness hashes are recorded in `contact_lift_nonzero_audit_receipt.json`. The replay took approximately 3.52 seconds with Python-flint.

## Scope

This supplies a positive, target-specific nonvanishing result on an actual certified contact component. It does not evaluate the global finite-field trace of the moving-point current, establish the nine required source-coefficient trace identities, produce a legal rational primitive for the original verifier, or prove `HasCertificate`. The complete-intersection certificate concerns the ordered four-form system above; it is not by itself a proof that the contact curve is globally smooth.
