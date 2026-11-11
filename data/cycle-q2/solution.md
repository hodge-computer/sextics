# A nonconstructive geometric route for cycle-q2

## Status and protected goal

**Draft; not a completed Lean proof.** The algebraic implication from a
rational primitive of the actual affine residue to the unchanged certificate
is proved. Its formulation in actual relative Kähler differentials and
exterior powers is now proved too, together with the formal normal residue
density and universal exterior pullback calculations. The existence of a
primitive remains unproved. The one
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

The sparse \(b\) surface is singular. These trace identities must not be
silently used as a smooth geometric seed. A smooth deformation and the
obstruction/Abel--Jacobi interpretation require separate justification.
The trace and matrix binding are algebraic progress, not a proof of
divisor support.

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
They do not prove its basepoint freeness or the required Jacobian ranks.

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
nonzero matrix entry at every nonzero field point. It does not supply the
particular seed's coordinate-power witnesses.

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
The actual projective cover, the identification with that specified bundle,
and the nonzerodivisor condition for an effective Cartier divisor remain
unproved. The construction of the projective family, its cycle class and
cylinder map, and the comparison with the Artinian trace still remain.

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
This theorem does not assert specialization to the protected target.

Applying these results to the chosen incidence system still requires the
actual quotient normal forms, seed equations, and invertible minors to be
proved in Lean. Its relations initially live in a ring localized at two
leading coefficients. If inverse variables are used to present that ring,
the inverse equations must be included, or the identities must first be
justified after clearing denominators. First-order numerical ranks alone
do not discharge these obligations. Neither lifting theorem identifies a
curve correspondence with the specified residue class.

## Remaining formal obligations

| Obligation | Status |
| --- | --- |
| Protected target, actions, degrees, nonvanishing | Proved for the exact instance. |
| Gradient condition, absolute irreducibility, affine quotient field | Proved; geometric Jacobian criterion remains. |
| Actual Fermat Jacobian bases, socle trace, finite commutant | Proved; geometric Higgs comparison remains. |
| Sparse seed quotient trace, degree-nine dimension and uniqueness, all 72 matrix entries | Proved; smooth geometric seed and obstruction/derivative comparison remain. |
| Cubic Cartier matrix factorization and periodic quotient complex | Polynomial identities and genuine exactness proved; geometric base change remains. |
| Literal Segre seed, cofactor quotients, and selected section products | Universal polynomial identities proved for the actual chosen entries. |
| Unit-entry image modules, transition units, and logarithmic differentials | Proved, including coefficient-map naturality and the homogeneous degree twist. |
| Formal and algebraic generic lifting of polynomial systems | Existence proved from actual seed equations and unit Jacobian; complementary relations force all omitted equations. |
| Actual large incidence system and moving projective curve family | Normal-form, seed-minor, and geometric binding remain. |
| Generation of the invariant variation, supported projector and specialization | Not formalized. |
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
hypotheses. The arithmetic-lifting constructor likewise needs an identified
finite polynomial incidence system and its actual invertible Jacobian
minor. The new lifting results discharge the general existence step once
those concrete hypotheses are proved; the finite Noether--Lefschetz
matrix alone supplies neither.
These interfaces cannot be used to bypass the remaining existence proof.

## Preserved current route

All `Current*.lean` files remain unchanged and are not dependencies of the
active entry point. [CurrentData.lean](CurrentData.lean) retains its 13,874
expressions and literal `transportError`, whose vanishing is not assumed.
[CurrentCorrection.lean](CurrentCorrection.lean) retains reconstruction and
`originalGoal_iff_actual_current_correction`: a future completed geometric
proof would imply that correction existential as well.

The denominator, normal-gauge, tangent and ambient-lift developments remain
available in their original files. The new formalization is consolidated
into one helper to keep all this work within the 64-file submission limit.

## Verification

Development compilation uses Lean 4.33.1 and pinned mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.
Every new component described as proved above has compiled and passed
independent `leanchecker` kernel replay. The final affine constructor's
printed axiom dependencies are exactly
`propext`, `Classical.choice`, and `Quot.sound`.
No native decision procedure or added axiom supplies these results.

The consolidated `Proposal.GeometricFormalInputs` module contains 61
components and is checked as a single module after the independently
checked components are assembled. Its 603,322-byte source has SHA-256

```text
68f06d3630e974fc8a7a0bc57ef952744bc98b00979c0092aecf2471f2640590
```

The final compilation and replay receipts bind that hash and record an
8 GiB development memory cap. The source-policy check covers all 61
helper modules.

The protected target is generated from base
`e3936ff366ae2302f21fb9e5730bbbd284c81d69`.
This revision continues PR head
`3026c51b18735109a67d602110eeb55b7b52cc33`.
The protected instance, shared library, verifier, workflows, and proof
manifest are unchanged.

The combined development checks are distinct from protected acceptance.
The full proposal fails the source-policy check because
`Solution.lean` still contains its explicitly labeled admission.
A development compile of the entry point does not turn that admission
into a proof. No accepted certificate or evaluated witness is claimed.

The proposal has 64 permitted files and remains below the 16 MiB source
limit. These format and resource conditions do not establish the remaining
existence theorem.

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
