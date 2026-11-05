# Complementary diagonal quotient and moving-conic certificate

This construction serves the `holdout-bundle` instance, in
the variable order `(X0,X1,X2,Y0,Y1,Y2)`, with pole parameter `q=1`:

\[
F=\sum_{j=0}^2X_j^6+\sum_{j=0}^2Y_j^6
  +X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2,
\qquad
A_{\rm bundle}=X_0^3Y_0^3+X_0^3Y_0Y_1^2.
\]

The complementary construction concerns \(A_*=X_0^3Y_0Y_1^2\). The accepted Fermat-cover
construction supplies the first summand. The certificate is an existence
proof over \(\mathbb C\), with unrestricted finite denominator degree and
an unrestricted quotient remainder \(Q\). No rational-coefficient or
strict-certificate restriction is imposed.

## 1. The change of geometry

The old cover has deck exponent zero on this source. Its trace-zero
antisymmetrization cannot supply the missing summand. Instead use the
complementary action

\[
(Y_0,Y_1,Y_2)\longmapsto(\zeta^5Y_0,\zeta Y_1,\zeta^5Y_2).
\]

Its determinant character is \(\zeta^5\), while the polynomial source
has character \(\zeta\). Thus the pole-two source including its volume
form is invariant.

For the requested initial quotient coordinates
\(p=Y_0Y_1,r=Y_2/Y_0,R=Y_0^6\), put
\(S=X_0^6+X_1^6+X_2^6\),
\(C=X_0^3X_1+rX_1^3X_2\). Then

\[
G=(1+r^6)R^2+(S+Cp)R+p^6,
\quad G(\phi)=Y_0^6F,
\quad\det(d\phi)=6Y_0^5.
\]

Consequently the downstairs density is
\(B_G=X_0^3p^2R/6\), since
\(B_G(\phi)\det(d\phi)/Y_0^{12}=A_*\).
These identities alone do not construct a primitive.

Fix \(i^2=-1\), and change the fibration birationally by

\[
v=rp=Y_1Y_2,
\qquad
\lambda=\frac{p^3}{R(1+ir^3)}
       =\frac{Y_1^3}{Y_0^3+iY_2^3}.
\]

Write \(a=\lambda+\lambda^{-1}\) and
\(b=i(\lambda-\lambda^{-1})\). The relative hypersurface is

\[
K=X_0^6+X_1^6+X_2^6+X_0^3X_1p+X_1^3X_2v+ap^3+bv^3.
\]

The identities \(G=RK\) and
\(\det\partial(p,v,\lambda)/\partial(p,r,R)=-p\lambda/R\)
give the exact density conversion

\[
\frac{B_G\,dp\wedge dr\wedge dR}{G^2}
=\frac{\rho\,dp\wedge dv\wedge d\lambda}{K^2},
\qquad \rho=-\frac{X_0^3p}{6\lambda}.
\]

The retained \(X\)-volume factors are understood on both sides. For the
direct physical map \(\theta=(X_0,X_1,X_2,p,v,\lambda)\),

\[
K(\theta)=F,\qquad
J_\theta=\det(d\theta)=-6\lambda Y_1,\qquad
J_\theta\rho(\theta)=A_*.
\]

This is a fibration over \(\mathbb C(\lambda)\). The proof makes no
Fano, rationality, or canonical-boundary assertion from the equation's
appearance. It constructs and checks the curve correspondence below.

## 2. Exact incidence through the generic endpoint

Over \(k=\mathbb C(\lambda)\), take the generic endpoint field

\[
H=\operatorname{Frac}
 k[c_0,c_2,p_0,v_0]/(c_0^6+c_2^6+ap_0^3+bv_0^3).
\]

The endpoint polynomial and \(K\) are proved irreducible; in particular
these coordinate rings are domains. The independent endpoint parameters
are \(c_2,p_0,v_0\), and \(c_0\ne0\).

Use twelve unknowns \(u_0,\ldots,u_{11}\) and the polynomial curve

\[
\begin{aligned}
\Phi_0&=c_0+u_0t+u_1t^2,&\Phi_1&=t,\\
\Phi_2&=c_2+u_2t+u_3t^2,\\
\Phi_p&=p_0+u_4t+u_5t^2+u_6t^3+u_7t^4,\\
\Phi_v&=v_0+u_8t+u_9t^2+u_{10}t^3+u_{11}t^4.
\end{aligned}
\]

Its incidence equations are exactly

\[
E_j=[t^j]K(\Phi)=0\quad(1\le j\le12).
\]

The constant equation is the endpoint relation, and all higher
coefficients vanish by the degree bound. Every one of the twelve
coefficient directions is included in the Jacobian
\(\Delta_{j\ell}=\partial E_j/\partial u_\ell\).

There is an exact nonsingular point over \(\mathbb F_5\):

\[
(a,b)=(0,3),\quad(c_0,c_2,p_0,v_0)=(1,1,4,1),
\quad u=(1,0,4,1,4,2,2,4,4,1,1,2),
\qquad\det\Delta=3.
\]

`BundleConicSeed.lean` checks all coefficients, all 144 Jacobian
entries, and an explicit inverse matrix. The modular calculation is
only an input to the characteristic-zero construction:

1. The endpoint \((1,1,4,1)\) satisfies its relation over the integers
   at \((a,b)=(0,-2)\). The Jacobian-localized square incidence is
   nonzero and étale over \(\mathbb Z\); flatness and the complex-point
   theorem produce an actual complex nonsingular conic.
2. The integral parameter ring is
   \(\mathbb C[\lambda,\lambda^{-1}]\). Specialization at \(\lambda=i\)
   gives \((a,b)=(0,-2)\), so that complex conic proves nontriviality
   of the generic incidence over the endpoint domain.
3. Étale flatness and injectivity of the endpoint-domain map preserve
   nontriviality at the generic endpoint. A maximal field factor
   gives a finite separable extension \(E/H\), its twelve
   coefficients, \(K(\Phi)=0\), and invertible \(\Delta\).

This is formalized in `BundleConicLift.lean` and `BundleIncidence.lean`.
Neither \(a\) nor \(\lambda^2+1\) is inverted at the seed.

## 3. Polynomial normal, determinant, and finite correspondence

Put \(g_j=K_j(\Phi)\). Begin with the constant normal
\(\Psi^{(0)}=e_0/(6c_0^5)\). Its pairing with \(g\) has constant
coefficient one. The inverse incidence Jacobian solves for the twelve
positive-coefficient variations that cancel every remaining coefficient.
More explicitly, let \(V_\ell=\partial\Phi/\partial u_\ell\), and set
\(\eta_j=[t^j](g\cdot\Psi^{(0)}-1)\), for \(1\le j\le12\).
Then one may take

\[
\Psi=\Psi^{(0)}-\sum_{\ell=0}^{11}(\Delta^{-1}\eta)_\ell V_\ell.
\]

All pairings have degree at most twelve, and every \(V_\ell\) has zero
constant term. Thus there is an actual polynomial vector \(\Psi\in E[t]^5\) with

\[
\sum_jg_j\Psi_j=1,
\qquad\Psi(0)=\frac{e_0}{6c_0^5}.
\]

Let \(D_t,D_{c_2},D_{p_0},D_{v_0}\) be the time derivative and the
three endpoint derivations, uniquely extended through the finite
separable coefficient field. They commute and preserve \(E[t]\).
For

\[
M=(\Psi,D_t\Phi,D_{c_2}\Phi,D_{p_0}\Phi,D_{v_0}\Phi),
\qquad J=\det M,
\]

the anchored endpoint gives

\[
J(0)=\frac1{6c_0^5}\ne0.
\]

This checks the evaluation determinant, not merely the incidence
Jacobian. The former is needed for the differential-form construction.

There is an actual embedding

\[
L=\operatorname{Frac}(k[X_0,X_1,X_2,p,v]/K)\hookrightarrow E(t)
\]

given by \(X_j\mapsto\Phi_j\). Independence of the endpoint
parameters, together with the exact coordinate \(\Phi_1=t\), proves
injectivity on the four remaining coordinates. Monicity and
irreducibility of \(K\) give the hypersurface-field embedding. Both
fields have transcendence degree four over \(k\), and the source is
finitely generated, so this extension is finite. These are proved
in `BundleConicEmbedding.lean`; dominance is not assumed.

## 4. An effective primitive

Set \(\beta=\rho(\Phi)\), \(b_j=\rho_j(\Phi)\), and
\(H_{jk}=K_{jk}(\Phi)\). Define the polynomial

\[
P=J\sum_j\Psi_jb_j+
\beta\left(\sum_{\alpha=0}^3
 \det(M[\alpha+1\leftarrow D_\alpha\Psi])
 -J\sum_{j,k}\Psi_jH_{jk}\Psi_k\right)\in E[t].
\]

Here \(D_0=D_t\), and replacing column \(\alpha+1\) uses the
normal column as column zero. Integrate coefficientwise:

\[
I(t)=\sum_{n\ge0}\frac{[t^n]P}{n+1}t^{n+1}.
\]

This sum is finite. For the four tail coordinates, put

\[
w_j=\beta\Psi_j-\frac{I}{J}D_t\Phi_j
\quad(j=X_1,X_2,p,v).
\]

The shared polynomial-family identity, with its actual hypotheses
discharged here, gives

\[
\operatorname{resDiv}_{K_0}(w)=-r_\rho,
\quad
r_\rho=\frac{\rho_0}{K_0}-\frac{\rho K_{00}}{K_0^2}
=\frac{p(4X_0^3-X_1p)}{18\lambda(2X_0^3+X_1p)^2}.
\]

Here, for \(j\in\{X_1,X_2,p,v\}\), the tangent derivation is
\(\delta_j=\partial_j-(K_j/K_0)\partial_0\), and the precise divergence is

\[
\operatorname{resDiv}_{K_0}(w)
 =\sum_j\delta_j(w_j)-\frac{\sum_jw_j\delta_j(K_0)}{K_0}
 =K_0\sum_j\delta_j\!\left(\frac{w_j}{K_0}\right).
\]

The normalized finite field trace from \(E(t)\) to \(L\) preserves
this equation. `BundleQuotientPrimitive.lean` proves the resulting
existence in the actual quotient field. Its theorem works for any
polynomial density over \(\mathbb C(\lambda)\); the final application
is exactly \(\rho=-X_0^3p/(6\lambda)\).

## 5. Physical pullback and legal denominators

The physical field embedding is constructed independently. Let
\(h=Y_0^3+iY_2^3\). In the sextic field,

\[
Y_1^6=\lambda(p^3+iv^3),\qquad
Y_0=p/Y_1,\qquad Y_2=v/Y_1.
\]

The remaining variable \(X_0\) satisfies a monic equation. Hence the
physical field is algebraic over the field generated by
\((\lambda,X_1,X_2,p,v)\). Its transcendence degree is five, so those
five parameters are algebraically independent. This proves injectivity
before localizing rational-function denominators. The monic quotient
model then gives the actual embedding of \(L\) into the sextic field.

`BundlePhysicalTransport.lean` checks the full five-tail Jacobian and
its inverse, including the \(\lambda\) coordinate, all derivative
compatibilities, its determinant \(-6\lambda Y_1\), and the
normal-source identity. The quotient vector has zero \(\lambda\)
component; its other components may depend on \(\lambda\). No physical
derivative is discarded by treating the parameter as a constant.

Choose legal rational lifts of the traced tail components and complete
them by

\[
W_0=\frac{\rho-\sum_{j\ne0}K_jW_j}{K_0},\qquad W_\lambda=0.
\]

The normal identity is then \(W(K)=\rho\), and the proved residue
equation says \(\operatorname{div}W\in(K)\) in the legal localization.
The full Piola transform is

\[
V=J_\theta(d\theta)^{-1}(W\circ\theta).
\]

In the following component formulas each \(W_j\) is evaluated at
\(\theta\), and \(\lambda=Y_1^3/h\). For example, writing
\(\Lambda=Y_0^2W_p+iY_2^2W_v\), its three \(Y\)-components are

\[
\begin{aligned}
V_{Y_0}&=-6\lambda W_p+3\lambda Y_0\Lambda/h,\\
V_{Y_1}&=-3\lambda Y_1\Lambda/h,\\
V_{Y_2}&=-6\lambda W_v+3\lambda Y_2\Lambda/h,
\end{aligned}
\]

and \(V_{X_j}=-6\lambda Y_1W_{X_j}\). The residue implementation
uses the equivalent five-tail Piola identity and normal-source binding.
It retains all six components when passing to the certificate.

The chart denominators, normal denominator, and traced coefficients
are nonzero in the actual sextic function field. The trusted residue
clearing and finite homogeneous extraction theorems therefore produce
a nonzero homogeneous \(D\) coprime to \(F\) over
\(\mathbb C\), six homogeneous \(N_j\) of degree \(\deg(D)+1\), and \(Q\)
with

\[
A_*D^2-D\sum_jN_jF_j+
F\left(D\sum_j\partial_jN_j-\sum_jN_j\partial_jD\right)=F^2Q.
\]

The final theorem has no field-map, conic, primitive, normal, or
determinant hypothesis. This route does not require \(Q=0\).

## 6. Assembly of the bundle

For certificate data \((D_0,N^{(0)},Q_0)\) of the accepted first
summand and \((D_*,N^{(*)},Q_*)\) above, use

\[
D=D_0D_*,\quad
N_j=D_*N_j^{(0)}+D_0N_j^{(*)},\quad
Q=D_*^2Q_0+D_0^2Q_*.
\]

Homogeneity, nonvanishing, complex denominator legality, and the full
identity are proved in `BundleAssembly.lean`. `BundleTarget.lean`
identifies both polynomials and the pole parameter with the generated
protected target. The exported theorem is

```lean
Submission.certificate :
  HodgeComputer.HasCertificate
    HodgeSubmission.F HodgeSubmission.A HodgeSubmission.d HodgeSubmission.q
```

`BundleCertificate.lean` assembles the new quotient primitive and the
actual physical field map; `Solution.lean` binds the result to that
protected statement.

## Sources, attribution, and verification scope

Prepared with OpenAI ChatGPT collaborating-agent assistance. The
repository's existing general moving-conic, arithmetic-lifting,
polynomial-normal, residue, Piola, finite-trace, legal-clearing, and
homogeneous-extraction machinery is used explicitly. The accepted
Fermat-cover/conic construction and its source modules are credited in
the repository to `fqlx` and collaborators; the shared finite incidence
machinery includes work credited to `fqlx` and `hodgepodgeconjecture`. The
new contribution here is this complementary quotient fibration, its
specific incidence and generic-field application, and its source and
physical transport for the missing summand.

Geometric existence for both summands was already known, as recorded in
the repository authors' Chapter 4, Section 4.6 and the instance's
[mathematical context](#case/holdout-bundle). The contribution here is the closed Lean
certificate for this fixed bundle.

The protected workflow checks the exact existential statement by compiling the submitted modules, replaying their declarations with `leanchecker`, and auditing their axiom dependencies. The accepted theorem uses only `propext`, `Classical.choice`, and `Quot.sound`. No expanded polynomial witness is supplied; the result establishes existence over complex coefficients with unrestricted finite denominator degree and a general quotient remainder.
