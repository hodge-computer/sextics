# A modular quartic, finite trace, and the reflection certificate

This solution constructs a certificate for the fixed instance **reflection-coupled-fano**. Its central ingredient is an explicit weighted quartic on the characteristic-five reduction of the reflection quotient, together with an invertible \(24\times24\) deformation matrix. An étale lifting argument supplies a polynomial family through the generic complex endpoint. Polynomial integration and finite trace then produce the rational vector field required by the certificate contract.

The construction proves existence. It does not export expanded denominator and numerator polynomials or a numerical denominator degree. Every occurrence of the coupling coefficient in characteristic zero is the exact number \(5/7\); the sextic, numerator, and pole parameter remain those of [instance.rec](instance.rec).

## 1. The fixed target and the reflection quotient

Write

\[
(x_0,x_1,x_2,x_3,x_4,z)=(X_0,X_1,X_2,Y_0,Y_1,Y_2),
\qquad c=\frac57.
\]

Introduce \(u=z^2\) and define

\[
\begin{aligned}
H_c(x,u)={}&x_0^6+x_1^6+x_2^6+x_3^6+x_4^6+u^3+cP(x,u),\\
P(x,u)={}&x_0^3x_1x_3x_4+x_0x_1x_3^3x_4
 +x_0x_1x_3^2u+2x_0x_1x_4^2u\\
&+3x_0x_2^3x_3x_4+2x_1^3x_2x_3x_4
 +x_1x_2x_3x_4^3.
\end{aligned}
\]

Thus the protected physical polynomial is exactly

\[
F(x,z)=H_{5/7}(x,z^2),
\qquad q=1,
\qquad A(x,z)=x_0^3z^3.
\]

The quotient source used below is

\[
B(x,u)=x_0^3u.
\]

With \(\phi(p)=p(x,z^2)\), the source identity is \(z\phi(B)=A\). The factor \(1/2\) arising from differentiation of \(z^2\) will occur in the last numerator component, not in \(B\).

The [motivation](why.md) and [provenance](provenance.json) already explain why the reflection quotient gives a nonconstructive existence argument. In weighted projective coordinates, the five \(x_i\) have weight one, \(u\) has weight two, and \(H_c\) has weighted degree six. The present construction supplies concrete curve and deformation data and derives the finite certificate algebraically.

[CoupledDomain.lean](CoupledDomain.lean) defines the quotient and physical equations. [SourceBinding.lean](SourceBinding.lean) identifies the physical equation, source, and pole parameter with the definitions generated from the protected record. [Solution.lean](Solution.lean) is the final binding to

    Submission.certificate :
      HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A

The meaning of this statement is given by the repository's [formal contract](../../formal/README.md). It asks for a nonzero homogeneous denominator \(D\), six homogeneous numerators \(N_i\) of degree \(\deg D+1\), relative primality of \(F\) and \(D\), and a polynomial \(Q\) satisfying

\[
A D^2-D\sum_{i=0}^5N_i\partial_iF
 +F\left(D\sum_{i=0}^5\partial_iN_i
          -\sum_{i=0}^5N_i\partial_iD\right)=F^2Q.
\qquad\text{(1)}
\]

The quotient \(Q\) is allowed to be nonzero.

## 2. Coordinate domains and a legal normal chart

The proof uses actual coordinate domains before passing to function fields. Both \(H_c(x,u)\) and \(F_c(x,z)=H_c(x,z^2)\) are monic of degree six in \(x_0\).

For \(H_c\), specialize

\[
x_1=x_2=x_4=0,\qquad x_3=T+1,\qquad u=-1.
\]

The resulting polynomial in \(x_0\) is

\[
x_0^6+(T+1)^6-1.
\]

Its constant term is divisible by \(T\), and its coefficient of \(T\) is \(6\), so it is not divisible by \(T^2\) in characteristic zero. Eisenstein's criterion at \(T\), followed by the monic-specialization lemma, proves irreducibility of \(H_c\). The same specialization proves irreducibility of \(F_c\) over \(\mathbb C\) after setting \(z=i\), since \(i^6=-1\). These are irreducibility statements over the complex coefficient ring; no inference from rational irreducibility to complex coprimality is used.

The normal coordinate throughout is \(x_0\). Specializing every other coordinate to zero sends the equation to \(x_0^6\) and its \(x_0\)-derivative to \(6x_0^5\). Consequently,

\[
H_c\nmid \partial_0H_c,\qquad F_c\nmid\partial_0F_c.
\qquad\text{(2)}
\]

The corresponding normal derivatives are therefore nonzero in the quotient function fields.

The endpoint section is \(x_1=0\). With independent coordinates \(r_2,r_3,r_4,r_5\), its coordinate ring has the monic presentation

\[
R_{\mathrm{end}}
=R_0[r_2,r_3,r_4,r_5,\xi]\big/
\left(\xi^6+3c\xi r_2^3r_3r_4
 +r_2^6+r_3^6+r_4^6+r_5^3\right),
\qquad\text{(3)}
\]

where \(R_0=\mathbb Z[1/7]\) and \(c=5/7\in R_0\). Its distinguished point is

\[
e=(\xi,0,r_2,r_3,r_4,r_5).
\]

The endpoint equation is also irreducible. Setting \(r_2=r_3=0\), \(r_4=1\), and \(r_5=T-1\) gives

\[
\xi^6+T^3-3T^2+3T,
\]

which is Eisenstein at \(T\) in characteristic zero. Monicity also makes extension of the coefficient domain injective. In particular, the endpoint ring over \(R_0\) embeds in the corresponding ring over \(\mathbb C\), and then in its fraction field \(K_{\mathrm{end}}\).

These facts are proved in [EndpointDomain.lean](EndpointDomain.lean), [CoupledDomain.lean](CoupledDomain.lean), and [ArithmeticEndpoint.lean](ArithmeticEndpoint.lean). The monic presentations give

\[
\operatorname{trdeg}_{\mathbb C}K_{\mathrm{end}}=4,
\qquad
\operatorname{trdeg}_{\mathbb C}
\operatorname{Frac}\bigl(\mathbb C[x_0,\ldots,x_4,u]/(H_c)\bigr)=5.
\qquad\text{(4)}
\]

## 3. An explicit quartic in characteristic five

Because \(7\) is invertible modulo five, the exact coefficient \(c=5/7\) reduces to zero. The reduction of the quotient equation is

\[
H_0=x_0^6+x_1^6+x_2^6+x_3^6+x_4^6+u^3.
\]

Let \(j^2=2\) in characteristic five. The displayed calculation lies in
\(\mathbb F_{25}=\mathbb F_5[j]\). In homogeneous parameters \((s:t)\), take

\[
\begin{aligned}
x_0&=j(s^4+t^4),&
x_1&=(2+j)(s^3t+st^3),&
x_2&=js^2t^2,\\
x_3&=j(s^3t-st^3),&
x_4&=s^4-t^4,&
u&=s^8+s^4t^4+t^8.
\end{aligned}
\qquad\text{(5)}
\]

The first five coordinates are quartics and the last is an octic, as required by the weights. There is no common zero of the first five coordinates: the identities

\[
x_0+jx_4=2js^4,\qquad x_0-jx_4=2jt^4
\]

exclude a basepoint. At \(s=1,t=0\), the endpoint is

\[
(j,0,0,0,1,1).
\qquad\text{(6)}
\]

The coefficient of \(t\) in \(x_1(1,t)\) is \(2+j\), which is nonzero: otherwise \(j=-2\) would give \(j^2=4\), contradicting \(j^2=2\).

The equation can be checked directly. Since \(j^5=-j\), the sum of the five sixth powers in the chart \(s=1\) is

\[
4+2t^4+4t^8+3t^{12}+4t^{16}+2t^{20}+4t^{24}.
\]

This is the negative of \((1+t^4+t^8)^3\) in characteristic five. Thus (5) lies on \(H_0=0\).

[QuarticSeed.lean](QuarticSeed.lean) proves the polynomial identity over any field of characteristic five containing such a \(j\). [ArithmeticSeed.lean](ArithmeticSeed.lean) obtains a suitable root in an algebraic closure of \(\mathbb F_5\), so the formal proof needs no external finite-field oracle.

### The exact deformation matrix

Fix the endpoint and allow the coefficients of \(t,t^2,t^3,t^4\) in each of the six coordinates to vary. For \(u\), keep the coefficients of \(t^5,t^6,t^7\) zero and the coefficient of \(t^8\) equal to one. There are \(6\cdot4=24\) variables.

The substituted equation has degree at most 24. Its constant term already vanishes because the endpoint lies on the hypersurface. Requiring the coefficients of \(t^1,\ldots,t^{24}\) to vanish gives exactly 24 equations.

The six gradient polynomials along the seed, in coordinate order \(x_0,x_1,x_2,x_3,x_4,u\), are

\[
\begin{aligned}
G_0&=-j(1+t^{20}),\\
G_1&=(2-j)(t^5+t^{15}),\\
G_2&=-jt^{10},\\
G_3&=-j(t^5-t^{15}),\\
G_4&=1-t^{20},\\
G_5&=3+t^4+4t^8+t^{12}+3t^{16}.
\end{aligned}
\qquad\text{(7)}
\]

The Jacobian column corresponding to the \(t^r\)-coefficient of coordinate \(i\) is the vector of coefficients of \(G_i t^r\), for \(r=1,2,3,4\).

Here is a short exact proof of invertibility. Suppose a vector in the kernel corresponds to variations
\(\sum_{r=1}^4 a_{i,r}t^r\) in the five \(x_i\) and
\(\sum_{r=1}^4 b_rt^r\) in \(u\).

The coefficient equations at \(t^5,t^{10},t^{15},t^{20}\) are respectively

\[
b_1=0,\qquad 4b_2=0,\qquad b_3=0,\qquad 3b_4=0.
\]

Thus all four \(b_r\) vanish. For each \(r=1,2,3,4\), the remaining equations at \(t^r,t^{20+r}\) give

\[
-ja_{0,r}+a_{4,r}=0,\qquad
-ja_{0,r}-a_{4,r}=0,
\]

and those at \(t^{5+r},t^{15+r}\) give

\[
(2-j)a_{1,r}-ja_{3,r}=0,\qquad
(2-j)a_{1,r}+ja_{3,r}=0.
\]

The equation at \(t^{10+r}\) is \(-ja_{2,r}=0\).
The scalars \(2\), \(j\), and \(2-j\) are nonzero in characteristic five, so every \(a_{i,r}\) vanishes. The kernel is zero, hence the square Jacobian is invertible.

[QuarticMatrix.lean](QuarticMatrix.lean) formalizes this sparse elimination. [QuarticGradient.lean](QuarticGradient.lean) and [QuarticGradientCoefficients.lean](QuarticGradientCoefficients.lean) establish (7) and its coefficients. [QuarticSeedIncidence.lean](QuarticSeedIncidence.lean) and [QuarticSeedJacobian.lean](QuarticSeedJacobian.lean) identify this matrix with the actual derivatives of the 24 incidence equations. The proof of nonsingularity uses these exact identities.

## 4. Lifting while keeping the coefficient \(5/7\) fixed

The arithmetic incidence is defined over the endpoint ring (3), with the coefficient \(5/7\) already fixed. It does not introduce a deformation parameter that is later assigned a convenient value.

Let \(v_{i,r}\), with \(i=0,\ldots,5\) and \(r=1,\ldots,4\), be the 24 coefficient variables. Define

\[
\begin{aligned}
\varphi_i(t)&=e_i+\sum_{r=1}^4v_{i,r}t^r
 &&(0\le i<5),\\
\varphi_5(t)&=e_5+\sum_{r=1}^4v_{5,r}t^r+t^8.
\end{aligned}
\qquad\text{(8)}
\]

Let \(E_1,\ldots,E_{24}\) be the positive coefficients of \(H_c(\varphi(t))\), and let \(\Delta\) be their Jacobian determinant with respect to the \(v_{i,r}\). Start with

\[
S=R_{\mathrm{end}}[v_{i,r}]/(E_1,\ldots,E_{24})
\]

and invert both \(\Delta\) and \(v_{1,1}\). The second inversion retains transversality to the endpoint section \(x_1=0\); it is an additional condition verified at the seed.

There is a specialization of \(R_{\mathrm{end}}\) to characteristic five sending

\[
(\xi,r_2,r_3,r_4,r_5)\longmapsto(j,0,0,1,1).
\]

The endpoint relation holds because \(j^6=3\) and \(3+1+1=0\) in characteristic five. The seed (5) supplies a point of the localized incidence: all equations vanish, \(\Delta\ne0\), and \(v_{1,1}=2+j\ne0\). Therefore this localized ring is nonzero.

An invertible square Jacobian makes this finitely presented incidence étale over \(R_{\mathrm{end}}\). The further localization remains étale. Étale algebras are flat, and the injective map from the endpoint domain into \(K_{\mathrm{end}}\) consequently leaves a nonzero generic incidence algebra. This nonzero étale algebra over \(K_{\mathrm{end}}\) has a field factor \(E\) that is a finite separable extension of \(K_{\mathrm{end}}\).

The result is a finite extension \(E/K_{\mathrm{end}}\), together with a tuple (8) over \(E[t]\) satisfying

\[
H_c(\varphi)=0,\qquad
\Delta(\varphi)\ne0,\qquad
v_{1,1}\ne0.
\qquad\text{(9)}
\]

The equations and units survive in the chosen field factor. This argument uses the integral coordinate ring before passage to its generic field; it never evaluates arbitrary rational-function denominators at the modular seed.

The algebra behind this step is the square-Jacobian and étale construction in the maintained Holdout library, together with mathlib's étale and flatness results. For background, see the Stacks Project sections on [smooth ring maps](https://stacks.math.columbia.edu/tag/00T1) and [étale ring maps](https://stacks.math.columbia.edu/tag/00U0).

The target-specific implementation is [ArithmeticBase.lean](ArithmeticBase.lean), [ArithmeticEndpoint.lean](ArithmeticEndpoint.lean), [OpenIncidence.lean](OpenIncidence.lean), [ArithmeticLifting.lean](ArithmeticLifting.lean), [ArithmeticSeed.lean](ArithmeticSeed.lean), and [ArithmeticFamily.lean](ArithmeticFamily.lean). [QuarticIncidence.lean](QuarticIncidence.lean) proves the degree, substitution, and differentiation identities for (8). [QuarticFamily.lean](QuarticFamily.lean) packages the exact equations, invertible Jacobian, and nonzero transverse coefficient.

## 5. Dominance and a finite extension of the target field

Let

\[
K=\operatorname{Frac}\bigl(\mathbb C[x_0,\ldots,x_4,u]/(H_c)\bigr),
\qquad L=E(t).
\]

Substitution \(x_i\mapsto\varphi_i(t)\) first defines a homomorphism into \(E[t]\). It must be proved injective on the target coordinate domain before \(L\) can be treated as an extension of \(K\).

The constant coefficients of \(\varphi_2,\varphi_3,\varphi_4,\varphi_5\) are the four independent endpoint coordinates \(r_2,r_3,r_4,r_5\). Hence a polynomial in these four variables cannot become zero under their moving substitutions unless it was already zero: taking the constant coefficient recovers the injective endpoint coefficient map.

The fifth independent coordinate is \(\varphi_1\). It has zero constant term and is nonzero, since its coefficient of \(t\) is \(v_{1,1}\ne0\). The anchored-substitution lemma proves that these conditions preserve injectivity when adjoining \(x_1\). Its proof proceeds by polynomial recursion: the constant coefficient detects a nonzero constant-in-\(x_1\) term; after this term vanishes, multiplication by the nonzero polynomial \(\varphi_1\) can be canceled in the domain \(E[t]\). Linearity of \(\varphi_1\) is not required.

Thus substitution is injective on \(\mathbb C[x_1,x_2,x_3,x_4,u]\). The monic irreducible equation in \(x_0\), together with its root \(\varphi_0\), then gives an injective map from the full hypersurface coordinate ring into \(L\). It extends to \(K\hookrightarrow L\).

By (4), \(K\) has transcendence degree five. Since \(E/K_{\mathrm{end}}\) is finite, \(E\) has transcendence degree four, and \(E(t)\) has transcendence degree five. The extension \(L/K\) is therefore algebraic. The argument also supplies the necessary essential-finite-type property over \(\mathbb C\); this makes the algebraic extension finite. Equality of transcendence degrees alone is not used to assert finiteness.

[Lifting.lean](Lifting.lean) contains the anchored-substitution lemma. [TargetEmbedding.lean](TargetEmbedding.lean) defines the target coordinate ring and field, proves the embedding, checks its coordinate evaluation identities, and proves finiteness using the shared transcendence-degree results.

## 6. A polynomial normal and five commuting derivations

Write \(G_i(t)=(\partial_iH_c)(\varphi(t))\), now in characteristic zero, and put \(g=G_0(0)\). The endpoint normal-chart argument gives \(g\ne0\): the monic irreducible endpoint polynomial (3) has degree six in \(\xi\), while its nonzero derivative \(6\xi^5+3c r_2^3r_3r_4\) has degree five. Its class is therefore nonzero in \(K_{\mathrm{end}}\) and remains nonzero in \(E\).

The invertible incidence Jacobian produces a polynomial normal vector

\[
\psi=(\psi_0,\ldots,\psi_5)\in E[t]^6
\]

such that

\[
\sum_{i=0}^5G_i(t)\psi_i(t)=1,
\qquad
\psi_i(0)=
\begin{cases}
g^{-1}&i=0,\\
0&i\ne0.
\end{cases}
\qquad\text{(10)}
\]

One can see the construction directly. Begin with the constant vector \((g^{-1},0,\ldots,0)\). The error \(1-G_0(t)/g\) has zero constant term. The Jacobian identifies positive coefficient variations of degrees one through four with polynomials of degrees one through 24. Its inverse supplies corrections with zero constant terms whose gradient pairing is exactly this error. The degree bound makes equality of all these coefficients a polynomial identity. This is [QuarticNormal.lean](QuarticNormal.lean).

There are four canonical derivations of \(K_{\mathrm{end}}\), obtained by differentiating the independent endpoint coordinates and differentiating the monic root implicitly. Each extends uniquely through the finite separable extension \(E/K_{\mathrm{end}}\); the extensions commute. Extend them coefficientwise to \(E[t]\) and to \(E(t)\). Add the time derivation \(\partial_t\), which kills \(E\). Denote the five commuting derivations by

\[
D_0=\partial_t,\quad D_1,D_2,D_3,D_4.
\]

They kill complex scalars, preserve the polynomial ring \(E[t]\), and satisfy \(D_0(t)=1\).

Form the six-by-six matrix

\[
M=\bigl[\ \psi\mid D_0\varphi\mid D_1\varphi
                   \mid D_2\varphi\mid D_3\varphi\mid D_4\varphi\ \bigr].
\qquad\text{(11)}
\]

At \(t=0\), the normal column is supported only in row \(x_0\). In row \(x_1\), the endpoint derivatives vanish and the time derivative is \(v_{1,1}\). In the last four rows, the four endpoint-derivative columns form the identity matrix. Expansion along the first column and then the \(x_1\) row gives

\[
(\det M)(0)=g^{-1}v_{1,1}\ne0.
\qquad\text{(12)}
\]

Thus \(M\) is invertible over \(L\). [QuarticSource.lean](QuarticSource.lean) proves the derivation and determinant statements. [QuotientGradient.lean](QuotientGradient.lean) identifies the gradient used by the incidence with the formal multivariate derivative of \(H_c\).

## 7. Polynomial integration, finite trace, and denominator clearing

This step applies the polynomial-family machinery from the accepted Holdout construction, with every geometric and differential input now provided by the quartic family.

Let \(\rho\) denote substitution into \(L\). Set

\[
g_i=\rho(\partial_iH_c),\qquad
b_i=\rho(\partial_iB),\qquad
\mathcal H_{ij}=\rho(\partial_j\partial_iH_c),
\qquad J=\det M.
\]

The canonical tangent derivations of the target function field are

\[
\nabla_i=\partial_{i+1}
 -\frac{\partial_{i+1}H_c}{\partial_0H_c}\partial_0,
\qquad i=0,\ldots,4.
\]

The inverse of (11) expresses their extensions to \(L\) as linear combinations of the five \(D_k\). The normal-density identity produces the following polynomial in \(t\):

\[
\begin{aligned}
p(t)={}&J\sum_j\psi_jb_j\\
&+\rho(B)\left(
\sum_{k=0}^4\det M[k+1\leftarrow D_k\psi]
-J\sum_{j,\ell}\psi_j\mathcal H_{j\ell}\psi_\ell
\right).
\end{aligned}
\qquad\text{(13)}
\]

Here \(M[k+1\leftarrow D_k\psi]\) means that the indicated tangent column is replaced by \(D_k\psi\). Every entry in (13) belongs to \(E[t]\): the coordinate functions, the normal, the gradient and Hessian evaluations are polynomial, and all five source derivations preserve this ring.

In characteristic zero, a polynomial \(\sum a_nt^n\) has the polynomial antiderivative \(\sum a_nt^{n+1}/(n+1)\). Applying this to (13), and using the inverse tangent matrix, gives \(w_0,\ldots,w_4\in L\) satisfying

\[
\sum_{i=0}^4\left(
\nabla_iw_i-w_i\frac{\nabla_i(\partial_0H_c)}{\partial_0H_c}
\right)
=-\left(
\frac{\partial_0B}{\partial_0H_c}
-\frac{B\,\partial_0^2H_c}{(\partial_0H_c)^2}
\right).
\qquad\text{(14)}
\]

All terms in this identity are read in \(L\). The correction terms in (13) are part of the normal-density calculation; integration is applied to that complete density.

Because \(L/K\) is finite and separable, normalized trace

\[
\operatorname{tr}_{L/K}^{\mathrm{norm}}
=\frac{1}{[L:K]}\operatorname{Tr}_{L/K}
\]

commutes with the extended derivations and fixes \(K\). Applying it to the \(w_i\) preserves (14) and gives a solution in \(K\). This is the step that descends the primitive from the parameter field to the actual quotient function field.

Choose common polynomial representatives \(w_i=n_i/d\) in \(K\), with \(d\) nonzero modulo \(H_c\). Put

\[
\begin{aligned}
D_H&=(\partial_0H_c)d,\\
N_{H,0}&=Bd-\sum_{i=1}^5(\partial_iH_c)n_{i-1},\\
N_{H,i}&=(\partial_0H_c)n_{i-1}\quad(1\le i\le5).
\end{aligned}
\qquad\text{(15)}
\]

The normal identity is then exact in the polynomial ring:

\[
\sum_{i=0}^5N_{H,i}\partial_iH_c=BD_H.
\qquad\text{(16)}
\]

Equation (14) says that the divergence numerator

\[
D_H\sum_i\partial_iN_{H,i}
-\sum_iN_{H,i}\partial_iD_H
\]

vanishes modulo \(H_c\). Therefore it equals \(H_cQ_H\) for some polynomial \(Q_H\).

The denominator is legal: its image in \(K\) is the product of the two nonzero elements \(\partial_0H_c\) and \(d\). Since \(H_c\) is irreducible over \(\mathbb C\), this proves \(D_H\ne0\) and \(\gcd(H_c,D_H)=1\).

[CurveClosure.lean](CurveClosure.lean) combines the shared polynomial integration, finite trace, and clearing results. [FamilyClosure.lean](FamilyClosure.lean), in `quotient_normalized_of_quartic_family`, supplies all their hypotheses from the constructed quartic family. This produces unrestricted normalized polynomial data on the quotient; homogeneous extraction is performed after returning to the physical variables.

## 8. Exact reflection transport and homogeneous extraction

Apply \(\phi(p)=p(x,z^2)\) to the quotient data. Define

\[
\begin{aligned}
D_F&=\phi(D_H),\\
N_{F,i}&=z\phi(N_{H,i})\quad(0\le i<5),\\
N_{F,5}&=\frac12\phi(N_{H,5}),\\
Q_F&=z\phi(Q_H).
\end{aligned}
\qquad\text{(17)}
\]

The chain rule, together with \(A=z\phi(B)\), gives

\[
\sum_iN_{F,i}\partial_iF=AD_F.
\qquad\text{(18)}
\]

For every polynomial \(p\),

\[
\partial_z\phi(p)=2z\phi(\partial_up),
\qquad
\partial_{x_i}\phi(p)=\phi(\partial_{x_i}p).
\]

These identities also give the exact divergence transformation

\[
D_F\sum_i\partial_iN_{F,i}
-\sum_iN_{F,i}\partial_iD_F=FQ_F.
\qquad\text{(19)}
\]

Relative primality is checked separately. Treat \(H_c\) and \(F_c\) as monic polynomials in \(x_0\). The coefficient-ring substitution \(u\mapsto z^2\) is injective. Monic division therefore reflects divisibility: if \(F_c\mid\phi(D_H)\), then \(H_c\mid D_H\). This contradicts legality of \(D_H\). Together with complex irreducibility of \(F_c\), it proves \(\gcd(F_c,D_F)=1\).

[ReflectionLift.lean](ReflectionLift.lean) proves the substitution, derivative, divergence, and coprimality statements, and packages (18)–(19) as `reflection_normalized_data`.

The data in (17) need not yet be homogeneous. The shared [homogeneous certificate construction](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/HomogeneousCertificate.lean) applies because \(F\) and \(A\) are homogeneous of degree six, \(F\) is prime, and the normal chart (2) is legal.

This construction first chooses a denominator representative modulo \(F\) whose initial homogeneous component is legal. An exact numerator correction and multiplication by the normal derivative preserve the normalized identities. Finite homogeneous extraction then produces a nonzero homogeneous denominator \(\widetilde D\), six homogeneous numerators \(\widetilde N_i\) of degree \(\deg(\widetilde D)+1\), and a polynomial \(\widetilde Q\), with

\[
\gcd(F,\widetilde D)=1,\qquad
\sum_i\widetilde N_i\partial_iF=A\widetilde D,
\]

\[
\widetilde D\sum_i\partial_i\widetilde N_i
-\sum_i\widetilde N_i\partial_i\widetilde D
=F\widetilde Q.
\qquad\text{(20)}
\]

Substituting (20) into the left side of (1) gives \(F^2\widetilde Q\). Together with nonvanishing and degree-six homogeneity of \(F\), and degree-six homogeneity of \(A\), these are the conditions required by `HodgeComputer.Verify` at \(n=5,d=6,q=1\).

The theorem `physical_certificate_of_quartic_family` in [FamilyClosure.lean](FamilyClosure.lean) performs this assembly. The closed arithmetic family and the exact source binding then give the protected theorem in [Solution.lean](Solution.lean).

## 9. Scope, search observations, and witness information

The coefficient \(5/7\) is unchanged in the arithmetic incidence and in its complex generic fiber. Reduction modulo five is a way to certify that the same integral incidence has a nonzero étale locus.

The quartic was found after lower-degree exploration. One concrete limitation of this reduction is easy to state: for a degree-two map to the characteristic-five Fermat quotient, the fifth powers of the five quadratic coordinates span at most three functions. Their products with the degree-at-most-one variations have rank at most six. The weight-two coordinate contributes at most four further columns. Thus the twisted normal map has rank at most ten, below the twelve required for freeness. This obstructs the degree-two version of this particular modular construction. It says nothing about nonexistence of characteristic-zero free conics or of certificates with a particular denominator.

The final proof requires no classification of all free curves and no unsuccessful-search assumption. The explicit quartic and the selected invertible minor are sufficient. Auxiliary finite-field and finite-precision experiments guided the construction; the formal dependency uses the exact polynomial identities, sparse kernel proof, and algebraic lifting theorem.

No `witness.json` is supplied. The proof selects a field factor finite over the generic endpoint field, performs trace descent, chooses common representatives, and applies finite homogeneous extraction. These steps prove the existence of finite polynomials \(\widetilde D,\widetilde N_i,\widetilde Q\), without evaluating their full coefficient lists. No number-field parametrization or rational-coefficient witness is asserted. There is no claimed minimal denominator degree, no numerical denominator-degree bound, and no requirement that the final quotient be zero.

## 10. Formal organization and verification scope

The main correspondences are:

| Mathematical step | Principal submitted files |
| --- | --- |
| Exact quotient, complex irreducibility, physical homogeneity | [CoupledDomain.lean](CoupledDomain.lean) |
| Modular quartic and its exact incidence Jacobian | [QuarticSeed.lean](QuarticSeed.lean), [QuarticMatrix.lean](QuarticMatrix.lean), [QuarticSeedJacobian.lean](QuarticSeedJacobian.lean) |
| Integral endpoint and characteristic-zero lifting | [EndpointDomain.lean](EndpointDomain.lean), [ArithmeticLifting.lean](ArithmeticLifting.lean), [ArithmeticSeed.lean](ArithmeticSeed.lean), [ArithmeticFamily.lean](ArithmeticFamily.lean) |
| Polynomial normal, source derivations, nonzero evaluation determinant | [QuarticNormal.lean](QuarticNormal.lean), [QuarticFamily.lean](QuarticFamily.lean), [QuarticSource.lean](QuarticSource.lean) |
| Dominant evaluation and finite target-field extension | [Lifting.lean](Lifting.lean), [TargetEmbedding.lean](TargetEmbedding.lean) |
| Polynomial integration, trace, and legal clearing | [CurveClosure.lean](CurveClosure.lean), [FamilyClosure.lean](FamilyClosure.lean) |
| Reflection transport and exact protected target | [ReflectionLift.lean](ReflectionLift.lean), [SourceBinding.lean](SourceBinding.lean), [Solution.lean](Solution.lean) |

The submission imports the maintained shared constructions rather than duplicating an accepted proof package. All target-specific definitions and identities are in the permitted flat helper files.

The closed protected theorem compiles in the repository's pinned Lean environment, and its transitive axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The prescribed explanation check, fresh protected-target compilation, kernel replay, trusted recursive axiom audit, and complete-diff checks are separate verification obligations. Their actual commands and outcomes are recorded in the accompanying pull request. A local proof check does not itself constitute the project's acceptance receipt or owner sign-off.

## 11. Mathematical context and attribution

The [existing instance discussion](https://github.com/hodge-computer/sextics/discussions/111), [motivation](why.md), and [provenance](provenance.json) were read before the construction. At that time the discussion contained the maintainer's opening and no comments; the new partial results were subsequently shared in [the progress comment](https://github.com/hodge-computer/sextics/discussions/111#discussioncomment-19059042). The existing context distinguishes the known geometric existence result from the challenge of producing a checked finite certificate.

- **Benjamin E. Diamond and the repository authors** supplied the fixed problem, the certificate formalism, and the reflection/Fano and residue-support framework in [Chapter 1](../../docs/01-certificates.md), [Chapter 2](../../docs/02-explicit-constructions.md), and [Chapter 3](../../docs/03-geometric-support.md). **Phillip Griffiths's residue theory** underlies the geometric interpretation. Diamond's [Hodge Structures in Sextic Fourfolds Equipped with an Involution](https://arxiv.org/html/2603.29157v2#S2) explains the rational-vector-field certificate correspondence in this setting.
- The Fano-covering-curve context in the repository uses the classical rational-curve results of **Shigefumi Mori** and **Yoichi Miyaoka–Shigefumi Mori**, as expounded in **Olivier Debarre's notes**, together with the free-curve results cited there: [Theorems 7.5 and 7.7, Proposition 9.12, and Corollary 9.13](https://perso.imj-prg.fr/wp-content/uploads/debarre-pub/M22.pdf). The present Lean argument supplies its own explicit modular curve, deformation minor, and algebraic family; these geometric existence theorems serve as motivation rather than added formal axioms.
- **`fqlx`'s accepted [Holdout proposal, PR #128](https://github.com/hodge-computer/sextics/pull/128)** supplied the moving-family, polynomial-normal, integration, finite-differential-trace, legal-clearing, and homogeneous-extraction machinery reused here. The [maintained HoldoutCover library](../../formal/lean/HodgeComputer/Constructions/HoldoutCover/README.md) retains that work's declarations and attribution, including the collaborators and AI assistance recorded in the [original explanation](../holdout/solution.md). Its later maintenance and target-parameterized assembly were prepared for `benediamond` with OpenAI Codex assistance. This proposal contributes the explicit modular quartic for the fixed coupled quotient, the modular deformation certificate, the arithmetic lift, and the target-specific assembly.
- **`HeadOfNaps`'s accepted [quadric-contact-broken proposal, PR #122](https://github.com/hodge-computer/sextics/pull/122)** contributed the [fraction-derivation construction](https://github.com/hodge-computer/sextics/blob/main/data/quadric-contact-broken/FractionDerivation.lean) adapted by the shared Holdout machinery. Its disclosed collaborators and AI assistance retain their credit.
- **The Lean and mathlib contributors** supplied the polynomial, algebraic-extension, localization, étale-algebra, flatness, derivation, determinant, and transcendence-degree foundations. The proof uses the repository's pinned toolchain and mathlib revision. The [mathlib étale-algebra documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/Etale/Basic.html) and the Stacks Project references above describe relevant algebraic foundations.
- **OpenAI ChatGPT, working through collaborating agents for GitHub contributor `fqlx`**, assisted the curve search, exact calculations, mathematical construction, Lean formalization, debugging, source review, and exposition. This is an AI-assisted contribution. The mathematical dependencies and formal verification, rather than agreement among agents, support the claims.

The result requested by the proposal is the existential certificate for the exact protected triple. Project acceptance additionally requires the repository's protected checks, mathematical review, and publication process.
