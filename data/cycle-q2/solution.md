# A nonconstructive geometric route for cycle-q2

## Status and protected goal

**Draft; not a completed Lean proof.** The active route is now the geometric
existence argument. One explicit admission remains:
`Submission.missing_geometric_existence`. The protected theorem therefore
still depends on `sorryAx` and must not be accepted. Changing the route does
not discharge the existence obligation.

The exact \(F,A,q=2\) remain those of the [instance record](instance.rec), in
coordinate order \((X_0,X_1,X_2,Y_0,Y_1,Y_2)\). The goal is a nonzero
homogeneous denominator \(D\), homogeneous numerators of degree
\(\deg D+7\), and unrestricted polynomial \(Q\), with
\(\gcd_{\mathbb C}(F,D)=1\), satisfying
\[
AD^2-2D\sum_iN_i\partial_iF+
F\left(D\sum_i\partial_iN_i-\sum_iN_i\partial_iD\right)=F^3Q.
\]
No explicit polynomial witness is exported.

## Classical argument and target checks

The references are [Chapter 3D](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/03d-hodge-loci.md)
and [Chapter 1](https://github.com/hodge-computer/sextics/blob/bab597060182b81323aadc09f3d51ff8d4448b64/docs/01-certificates.md).
These are mathematical references, not Lean imports or additional axioms.

For \(\omega^3=1\), \(\omega\ne1\), use
\[
\beta:(X_2,Y_2)\mapsto(-X_2,-Y_2),\qquad
\gamma=\operatorname{diag}(\omega^2,\omega^2,1,\omega,1,1).
\]
All nine monomials of \(F\) are fixed. The numerator has
\(\gamma\)-weight \(10\equiv1\pmod3\), whereas the projective volume form
has determinant weight \(5\equiv2\pmod3\). Their product is invariant.
Under \(\beta\), the source has pair-degree four and the determinant is
positive. Thus the actual asymmetric residue
\(\alpha=\operatorname{Res}_{F=0}(A\Omega/F^3)\) is fixed by both actions.
No cyclic source sum or source-erasing invariant average is substituted.

[GeometricTarget.lean](GeometricTarget.lean) supplies proof scripts for the
protected-polynomial evaluation identities, the two actions, their orders
and commutation, and the equation and determinant-weighted source identities.
`AlgebraicInputs` retains these facts, the nonzero equation, homogeneous
degrees, and protected pole parameter. Polynomial equivariance is not itself
a formalization of residues or cohomology.

Classically, smoothness follows by choosing a maximum-modulus coordinate
\(M>0\) at a hypothetical nonzero gradient zero. The pure derivative has
modulus \(6M^5\); mixed derivatives contribute at most \(2M^5\) for an
\(X\)-coordinate and \(M^5\) for a \(Y\)-coordinate. This estimate is not
yet encoded in the new Lean helpers.

Chapter 3D.5 supplies
\[
H^4(X,\mathbb Q)^{\langle\beta,\gamma\rangle}
\subset N^1H^4(X,\mathbb Q).
\]
Its coordinate order is
\((x_0,x_1,x_2,x_3,u,v)=(X_0,X_1,Y_0,Y_1,X_2,Y_2)\).
Use complexification; the individual residue need not be a rational Betti
class. Choose a squarefree homogeneous ambient support equation \(S\) of
degree \(e\), not divisible by \(F\). Chapter 1's filtered de Rham argument
and twisted Euler sequence supply
\[
\eta=-\frac{\iota_N\Omega}{F^2S^2},\qquad \deg N_i=2e+7,
\]
with \(A\Omega/F^3-d\eta\) regular along \(F=0\). Setting \(D=S^2\)
gives the original cleared identity, with its full polynomial quotient.
This is an existential choice, not an evaluated coefficient tuple.

## Finite seed algebra

Use auxiliary weighted coordinates \((x_0,x_1,x_2,x_3;w)\), not new protected
coordinates, and the sparse invariant cubic
\[
b=x_3^3+x_2^3+x_1x_2x_3+x_0x_2x_3+x_0x_1^2.
\]
For \(r^3=2\), \(i^2=-1\), put
\[
\begin{aligned}
f_1&=x_0^2-rx_1x_3,&g_1&=x_0^4+rx_0^2x_1x_3+r^2x_1^2x_3^2,\\
f_2&=w+x_2^2,&g_2&=w^2-wx_2^2+x_2^4,\\
h&=b-i(x_1^3+x_3^3),&k&=b+i(x_1^3+x_3^3).
\end{aligned}
\]
Normalize the degree-nine trace on the corresponding Artinian algebra by
\(\tau(x_0x_1^8)=1\). The invariant cubic column order is
\[
(x_3^3,x_2^3,x_1x_2x_3,x_1^3,x_0x_2x_3,x_0x_1^2,x_0^2x_1,x_0^3,x_3w).
\]
The first seven rows are \(\tau(kL\sigma)\), ordered by
\[
\sigma\in(x_2x_3^2,x_1x_2^2,x_1^2x_3,x_0x_2^2,x_0x_1x_3,x_0^2x_3,x_2w),
\]
and the last is \(\tau(x_2x_3^3wL)\). Scale the first five rows by
\(6/r^2\), the next two by three, and the last by six.

[GeometricSeed.lean](GeometricSeed.lean) records this \(8\times9\) matrix
\(M\), an explicit Gaussian-rational right inverse \(R\), and the tangent
\(\ell=ix_0^2x_1+(i-1)x_0^3\), with proof scripts for
\[
MR=I_8,\qquad M\ell=(0,0,0,0,0,0,0,2)^{\mathsf T}.
\]
These are finite matrix identities. Their identification with the trace
algebra and geometric pairings remains a separate formalization obligation;
they do not imply divisor support without the geometric argument.

## Active proof boundary

[Solution.lean](Solution.lean) defines
`CycleQ2Nonconstructive.GeometricExistenceBridge`, taking the separated
`AlgebraicInputs` and `FiniteSeedInputs` to the unchanged `HasCertificate`
statement. `certificate_of_geometric_bridge` is conditional assembly only.
The single explicit `sorry` asks for the proof of the bridge. The final
protected theorem has no new parameters or assumptions, but remains admitted.

The outstanding chain is:

| Obligation | Status of this revision |
| --- | --- |
| Smoothness and geometric setup | Classical estimate; not encoded here. |
| Trace-algebra binding and obstruction/derivative formulas | Finite matrix data separated; geometric binding not formalized. |
| Hodge-locus integration to moving curves | No Lean implementation here. |
| Higgs criterion and spanning of the invariant variation | Earlier finite calculations do not formalize the geometric statement. |
| Supported projector and specialization | Correspondence, polarization and specialization proofs required. |
| Paired-sign quotient and relative support transfer | Quotient, Leray and boundary proofs required. |
| Support-to-certificate bridge | Filtered de Rham strictness, pole bounds, Euler sequence and clearing required. |

This is a draft refactor and port of finite algebra, not completion of that chain.

## Preserved current route

All `Current*.lean` files remain unchanged, but are no longer imported by the
active entry point. [CurrentData.lean](CurrentData.lean) retains its 13,874
expressions and literal `transportError`, whose vanishing is not assumed.
[CurrentCorrection.lean](CurrentCorrection.lean) retains reconstruction and
`originalGoal_iff_actual_current_correction`: a future geometric proof would
also yield that correction existential, without making it a premise.
The denominator, normal-gauge, tangent and ambient-lift developments remain
available in their original files. No protected record, shared library,
verifier, workflow, generated file, or proof-manifest field is changed.

## Verification

The new sources have **not been Lean-compiled in the authoring runtime**.
No Lean/Lake executable was present; the direct toolchain fetch failed at DNS
resolution. No kernel-replay or protected-acceptance pass is claimed, and
historical checks of the old modules do not certify these sources.

Local exact arithmetic parses the formulas and Gaussian-rational arrays from
the new Lean source, verifies the target weights and degrees, all 64 entries
of \(MR=I_8\), all eight tangent-image entries, and rejection of a corrupted
inverse. Static checks cover the exact theorem and unchanged manifest, one
active admission, no admissions in the new helpers, allowed file names, and
local explanation links. These checks are not Lean proofs. The proposal has
63 permitted files, within the 64-file limit.

## Attribution

The geometric route is the Chapter 3D argument of `benediamond` and
collaborators in [Discussion #61](https://github.com/hodge-computer/sextics/discussions/61),
using Claire Voisin's moving-cycle strategy, Griffiths residue and Abel--Jacobi
formulas, Dolgachev's weighted residues, Aoki--Shioda-type cycles studied by
Braun--Fortin--Lopez Garcia--Villaflor Loyola, and the references of Chapters
3 and 1. The earlier work of `hodgepodgeconjecture`, `DiamondJM`, `fqlx`, and
the Hodge Computer collaborators remains preserved and credited. The sparse
seed and this draft refactor were prepared for `fqlx` with OpenAI ChatGPT assistance.
