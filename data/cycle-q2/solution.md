# A nonconstructive geometric route for cycle-q2

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
Bases of the genuine seed conormal module, actual local lifts of the
trace-family coefficient motion, and the relative Kodaira--Spencer/transition
identity are also proved.
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

The previously proved local splitting formulas already give the overlap
coefficient \((kL-A)/(g_1g_2)\), with first-chart-minus-second-chart sign.
The next concrete theorem is to identify the actual normal connecting
class in these conormal coordinates with that all-poles Čech class,
including independence of lifts and refinement. The existing paired
residue is \(-1/(3r)=-1/171\) at \(r=57\). Its interpretation as the
trace of this actual connecting class, its relative persistence, and its
subsequent Abel--Jacobi/de Rham comparison remain unproved.

There is a direct algebraic route to simplify that next comparison. The
regular order \((f_2,f_1,h)\) successively uses monicity in \(w,x_0,x_2\).
After eliminating \(w\) and quotienting by \(f_1\), the cubic is still
monic of degree three in \(x_2\), even if the coefficient ring has zero
divisors. Likewise \((h,F)\) is regular because modulo \(h\), the actual
sextic is monic of degree three in \(w\). These presentations do not
require \(r\ne0\) or \(\theta\ne0\).

The additional Lean lemma would say that for \(I=(a,b,c)\) in this
regular order,
\[
au+bv+cw\in I^2\quad\Longrightarrow\quad u,v,w\in I.
\]
It is the degree-one case of the regular-sequence implication in
[Stacks Project, Lemma 10.69.2](https://stacks.math.columbia.edu/tag/00LN).
After subtracting an \(I^2\) representation, cancellation of \(c\)
modulo \((a,b)\) writes \(w=as+bt\); cancellation of \(b\) modulo
\((a)\) writes \(v+ct=az\); cancellation of \(a\) then gives
\(u+cs=-bz\). The coefficient statement proves independence of the
actual equation classes in \(I/I^2\), and its length-two version handles
\(J/J^2\). Binding the existing `Ideal.mapCotangent` to these global
bases would identify the natural map with \(\beta\) without extra
Jacobian refinements. This is a proposed next formalization, not a
completed global-basis theorem in the submitted source. The \(g_1/g_2\)
cover and homogeneous twists would still be needed for the connecting
class, and ambient derivation lifts would still use Jacobian opens.

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
the trace parameter field. A separate
Jacobian-cover argument is still needed to use these opens as a cover
of the entire moving surface.

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

## Remaining formal obligations

| Obligation | Status |
| --- | --- |
| Protected target, actions, degrees, nonvanishing | Proved for the exact instance. |
| Gradient condition, absolute irreducibility, affine quotient field | Proved; geometric Jacobian criterion remains. |
| Actual Fermat Jacobian bases, socle trace, finite commutant | Proved; geometric Higgs comparison remains. |
| Sparse seed quotient trace, degree-nine dimension and uniqueness, all 72 matrix entries | Proved; actual all-poles Čech comparison and vanishing equivalence now proved too. |
| Actual curve chart cover and the theta-one nine-column residue functional | Proved on the actual curve; obstruction/Abel--Jacobi interpretation remains. |
| Literal cubic and r=57 seed-curve Jacobian conditions | Exact Gaussian-integer identities prove the cubic gradient condition and a normal-minor cover at every relevant curve prime. Geometric smoothness and the entire surface condition remain separate. |
| Actual seed conormal modules and normal matrix | Genuine equation-class bases are constructed on every relevant prime chart. The actual natural cotangent map and its dual are constructed; the dual's equation-coordinate matrix is the existing normal matrix. The target conormal basis is constructed on source Jacobian charts where g1 is a unit; graded gluing and the global normal-sequence comparison remain. |
| Cubic Cartier matrix factorization and periodic quotient complex | Polynomial identities and genuine exactness proved; geometric base change remains. |
| Literal Segre seed, cofactor quotients, and selected section products | Universal polynomial identities proved for the actual chosen entries. |
| Actual complex basepoint cover and local Segre exactness | Proved on every relevant prime and every nonempty coordinate localization, including homogeneous local lifts. |
| Regular linkage element and actual local factor sequence | Proved; the literal factor ideals are principal with regular generators on unit-entry charts. |
| Seed quotient Čech complex | Actual localization comparison, graded H0 gluing, H1 vanishing, and degree-zero invariant H2 dimension seven proved. |
| Chosen curves, restrictions, and orbit ideals | Actual six-term bases, two-open cover and gluing, restriction kernels, cyclic orbit identification, and the 56/23 section dimensions proved. |
| Positive graded H1 of both linkage ideals | Proved for the actual degree-ten invariant and degree-eight character-one pieces. |
| Actual relation-kernel obstruction | The actual connecting maps identify the obstruction with kernel Čech H1 and scalar Čech H2; its dimension is exactly seven. |
| Actual matrix-entry Jacobian and coefficient relations | Entry-block rank 1915, combined Jacobian rank 1922, relation-matrix rank 7600, and actual image/kernel equality proved. |
| Unit-entry image modules, transition units, and logarithmic differentials | Proved, including coefficient-map naturality, the homogeneous degree twist, and the relative Kodaira--Spencer contraction/boundary identity. |
| Local lifts of the actual trace-family motion | Constructed on each actual surface Jacobian-minor localization, with proved coefficient restriction and preservation of both equations; the global covering comparison remains. |
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

The active development contains 447 consolidated components. The original
61-component [GeometricFormalInputs.lean](GeometricFormalInputs.lean)
baseline is retained byte-for-byte, together with its checked artifact.
The 386 continuation components are grouped into four existing permitted
files, preserving their order and complete proof bodies:

| File | Components | Contents |
| --- | ---: | --- |
| [GeometricFormalInputs.lean](GeometricFormalInputs.lean) | 61 baseline | Existing affine residue/certificate bridge and foundational geometric inputs. |
| [GeometricTarget.lean](GeometricTarget.lean) | 100 continuation | `AffineFiniteDescent` through `CurveRestrictionModularLeft`, after the original target/action declarations. |
| [Assembly.lean](Assembly.lean) | 36 continuation | `CurveRestrictionModularRight` through `SegreModularActionFlat01`, after the original assembly declarations. |
| [Normalization.lean](Normalization.lean) | 11 continuation | `SegreModularActionFlat02` through `SegreModularCubicData2`, after the original normalization declarations. |
| [Solution.lean](Solution.lean) | 239 continuation | `SegreRelationsSeedCharts` through `SeedNaturalNormalMap`, followed by the existing entry-point body. |

`Workspace` and the original `GeometricSeed` precede the baseline. The
continuation then imports in the order shown in the table. The original
support declarations in the reused files are retained as well. Every
helper component in `Solution.lean` occurs before the admitted theorem,
so those proofs cannot use that later admission.

This layout keeps the complete proposal within 64 files while bounding
the amount of source elaborated in one process. Two development attempts
to compile the expanded monolithic helper ended in `SIGKILL`; neither is
reported as a successful check. The split changes imports, file placement,
and scheduling scaffolding, while preserving every component's mathematical
proof body. A standalone check of each stage and its kernel replay are
required for this final layout.

## Verification

Development compilation uses Lean 4.33.1 and pinned mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`.
The recovered 373-component continuation has matching standalone compile
and independent `leanchecker` receipts. Its printed endpoint axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

All thirteen additional local-geometry components have compiled individually.
The final four-stage source layout is being checked serially, with exact
source hashes bound to each compile and independent kernel replay. The
61-component baseline is reused from its successful recorded check.
The first three stages have completed both checks:

| Stage | Compilation, seconds | Independent replay, seconds |
| --- | ---: | ---: |
| `GeometricTarget` | 839.781 | 336.938 |
| `Assembly` | 788.955 | 372.881 |
| `Normalization` | 228.262 | 22.153 |

The final `Solution` stage, containing the remaining 239 components and
the entry point, is still being checked. Its frozen source SHA-256 is
`5bf1220b1bcb565a85e920f38b8ffe504ee562cbed2df99533c7f59d22444b62`.
No final-layout pass is asserted while that check is pending.
No native decision procedure or added axiom supplies the proved results.

The protected target is generated from base
`e3936ff366ae2302f21fb9e5730bbbd284c81d69`.
This revision continues PR head
`638af005150a402fb0638f13d6516ce1e16d5d00`.
The protected instance, shared library, verifier, workflows, and proof
manifest are unchanged.

The combined development checks are distinct from protected acceptance.
The full proposal fails the source-policy check because
`Solution.lean` still contains its explicitly labeled admission.
A development compile of the entry point does not turn that admission
into a proof. No accepted certificate or evaluated witness is claimed.

The 55 legacy Lean files outside the active seven-module import closure
have not been rebuilt in this continuation. In particular, checking the
unchanged `CurrentNormalGauge` and `CurrentTangents` in the new import
environment requires first compiling the 52-module `CurrentCorrection`
dependency chain beyond the reused `Workspace`; its artifacts are absent
from the reused cache. Static source and import checks do not replace
that compilation.
The protected verifier also compiles unused submitted helpers and applies
one shared 3,600-second deadline to all compilation, independent replay,
and final auditing. The staged development checks do not establish
compliance with that full-proposal deadline.

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
