# A strict certificate from a binary-cubic Hessian construction

The certificate below serves the fixed instance

\[
\begin{aligned}
F={}&X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6\\
 &+X_0^3X_1Y_0Y_1+X_1^3X_2Y_0Y_1,\\
q={}&1,\qquad A=X_0^3Y_0^3.
\end{aligned}
\]

Its denominator has homogeneous degree 60, its six numerator components have
homogeneous degree 61, and its quotient is zero. All coefficients belong to
\(\mathbb Q(\sqrt3)\subset\mathbb C\). The construction supplies an explicit
strict rational vector field; no minimality of its denominator degree is
claimed.

The main step is a rational coordinate map that turns one half of the target
into a quadratic density on a cubic surface of the form
\(f(u,p)+v^3+vz^2\), where \(f\) is a binary cubic. A Hessian construction
produces an explicit field for that density. Cofactor transport returns to
the original six variables, and an exact sign symmetry supplies the other
half. The rational coordinates are used to derive the formulas; the final
certificate consists entirely of polynomials in the original variables.

## 1. Two targets related by a symmetry

Put

\[
A_+=\frac{X_0^3(Y_0^3+Y_1^3)}2,
\qquad
A_-=\frac{X_0^3(Y_0^3-Y_1^3)}2.
\]

Their sum is the prescribed \(A\). The linear involution

\[
\sigma(X_0,X_1,X_2,Y_0,Y_1,Y_2)
=(X_0,-X_1,X_2,Y_0,-Y_1,Y_2)
\]

preserves \(F\) and carries \(A_+\) to \(A_-\). Thus one explicit field
for \(A_+\), together with its transported field under \(\sigma\), suffices.

This decomposition is compatible with the hidden reflections described by
fringewidth in the [existing instance discussion][hidden-reflections] and
recorded in [why.md](why.md). The existence argument from those reflections
was already known. The contribution here is the explicit polynomial
certificate for the fixed target.

## 2. A rational map to a cubic surface

On the chart \(X_0Y_2\ne0\), use the following ordered coordinates:

\[
\Phi=
\left(
u=X_0^2,\quad p=Y_0Y_1,\quad v=Y_2^2,\quad
z=\frac{Y_0^3-Y_1^3}{Y_2},\quad
r=\frac{X_1}{X_0},\quad w=\frac{X_2}{X_0}
\right).
\]

Treat \(r,w\) as passive parameters and define

\[
a=1+r^6+w^6,\qquad b=r+r^3w,
\qquad f_0=au^3+bu^2p+2p^3.
\]

The exact identity

\[
Y_0^6+Y_1^6=(Y_0^3-Y_1^3)^2+2(Y_0Y_1)^3
\]

gives

\[
F=G_{\mathrm{cub}}\circ\Phi,
\qquad G_{\mathrm{cub}}=f_0+v^3+vz^2.
\]

The determinant in the displayed coordinate order is

\[
\det(d\Phi)=\frac{12(Y_0^3+Y_1^3)}{X_0}.
\]

Consequently the active density \(u^2/24\) pulls back with the required
Jacobian factor:

\[
\det(d\Phi)\left(\frac{u^2}{24}\circ\Phi\right)=A_+.
\]

For a rational active field \(\beta\), append zero components in the two
passive directions and set

\[
V_+=\operatorname{adj}(d\Phi)\,(\beta\circ\Phi).
\]

The rational Piola identity and the chain rule give

\[
\beta(G_{\mathrm{cub}})=u^2/24,\quad
\operatorname{div}\beta=0
\quad\Longrightarrow\quad
V_+(F)=A_+,\quad\operatorname{div}V_+=0.
\]

Derivatives of the passive coefficients are included in this full cofactor
identity. They are not discarded when returning to the original variables.
All four active coordinates have physical degree two and both passive
coordinates have degree zero. Hence an active field of degree zero becomes
a physical field of degree one, as required at \(q=1\).

## 3. The active Hessian identity and the trace of Euler fields

Fix \(\lambda\in\mathbb C\) with \(\lambda^2=3\). For the binary cubic
\(f_0\), define

\[
\begin{aligned}
\Delta&=324a^2+24b^3,\\
h_0&=-b^2u^2+18aup+6bp^2,\\
H&=(18au+12bp)\partial_u+(2b^2u-18ap)\partial_p,\\
k&=H(f_0)/3.
\end{aligned}
\]

The elementary binary-cubic identities used here are

\[
H(h_0)=0,\qquad H(k)=3\Delta f_0,\qquad
\Delta f_0^2-k^2=\frac49h_0^3,
\]

and the target decomposition

\[
\Delta u^2=108a\,\partial_u f_0+12b^2\,\partial_p f_0-12b h_0.
\qquad\text{(1)}
\]

These can all be checked by polynomial differentiation and expansion.

To explain their origin, work temporarily over the generic parameter field,
where \(\Delta\ne0\), and adjoin a square root of \(\Delta\).
The matrix of \(H\) on linear forms squares to \(\Delta I\). In its two
eigen-coordinates the cubic becomes a sum of cubes, with cubic summands

\[
f_\pm=\frac12\left(f_0\pm\frac{k}{\sqrt\Delta}\right).
\]

The other binary cubic has the explicit decomposition

\[
v^3+vz^2
=\frac12\left(v+\frac{\lambda z}{3}\right)^3
+\frac12\left(v-\frac{\lambda z}{3}\right)^3.
\]

Write \(r_0=v+\lambda z/3\) and \(g=r_0^3/2\). The Euler field on
the coordinate belonging to \(f_+\), together with the Euler field on
\(r_0\), has divergence two. It acts on \(h_0\) with eigenvalue one
and on \(f_++g\) with eigenvalue three. Therefore

\[
\frac{h_0(E_++E_{r_0})}{3(f_++g)}
\]

has zero divergence and sends \(G_{\mathrm{cub}}\) to \(h_0\). The
conjugate expression with \(f_-\) has the same target. Average these
**rational fields**, with their denominators included. Using the Hessian
identity above removes \(\sqrt\Delta\) and gives

\[
\begin{aligned}
d_0&=9\Delta g^2+9\Delta f_0g+h_0^3,\\
J&=\Delta(2g+f_0)(u,p,r_0,\lambda r_0)-k(H_u,H_p,0,0),\\
\beta_h&=\frac{3h_0J}{4d_0}.
\end{aligned}
\]

Thus \(\beta_h(G_{\mathrm{cub}})=h_0\) and
\(\operatorname{div}\beta_h=0\). Combining it with the two constant
coordinate fields from (1) gives the desired density:

\[
\beta=
\frac{(36ad_0,4b^2d_0,0,0)-3bh_0J}{8\Delta d_0},
\qquad
\beta(G_{\mathrm{cub}})=\frac{u^2}{24},
\quad\operatorname{div}\beta=0.
\qquad\text{(2)}
\]

Every component of the numerator in (2) is divisible by \(\Delta\).
For example, the two nontrivial cancellations follow from

\[
\begin{aligned}
36ah_0^2+3bkH_u
&=\Delta u(3abu^3+36ap^2u+b^2pu^2+18bp^3),\\
4b^2h_0^2+3bkH_p
&=\frac{\Delta b}{3}(-9apu^3+b^2u^4+3bp^2u^2+18p^4).
\end{aligned}
\]

Canceling this common factor before physical denominator clearing is what
leads to degree 30 for a half-target. The formulas below contain neither
\(\sqrt\Delta\) nor a discriminant denominator. Only the fixed constant
\(\lambda\) remains. The derivation on a dense chart explains the
construction; the resulting cleared polynomial identities hold without
any chart or discriminant restriction.

## 4. The explicit half-target polynomials

The following formulas use only the original variables. Define

\[
\begin{aligned}
p&=Y_0Y_1,&s&=Y_0^3-Y_1^3,&S&=Y_0^3+Y_1^3,&T&=Y_2^3,\\
G_0&=X_0^6+X_1^6+X_2^6,&c&=X_0^3X_1+X_1^3X_2,\\
\delta&=324G_0^2+24c^3,&h&=-c^2+18G_0p+6cp^2,\\
f&=G_0+cp+2p^3,&R&=T+\lambda s/3,\\
W&=R^3+fT,&Z&=R^3(R^3+2fT).
\end{aligned}
\]

In particular, \(F=f+s^2+Y_2^6\) is exactly the original sextic.
Set

\[
\begin{aligned}
D_+&=9\delta Z+4h^3T^2,\\
p_0&=G_0c+12G_0p^2+c^2p/3+6cp^3,\\
p_1&=-3G_0p+c^2/3+cp^2+6p^4,\\
U&=81G_0Z-3chWT+3hp_0T^2,\\
V&=9c^2Z-3chWpT+chp_1T^2,\\
B&=-3chWR.
\end{aligned}
\]

The six numerators, in the required variable order, are

\[
N_+=X_0^3\left(
\begin{array}{c}
3SX_0U\\
3SX_1U\\
3SX_2U\\
6Y_1^2V+Y_0(s+2\lambda T)B\\
6Y_0^2V-Y_1(s+2\lambda T)B\\
3SY_2B
\end{array}
\right).
\qquad\text{(3)}
\]

These are the cofactor transport of (2), after canceling the common
discriminant factor and clearing all coordinate denominators. In
particular, no extra factor of \(X_0\) or \(Y_2\) is needed in \(D_+\).
The two exact identities are

\[
N_+(F)=A_+D_+,
\qquad D_+\operatorname{div}N_+-N_+(D_+)=0.
\qquad\text{(4)}
\]

Here \(N(P)=\sum_iN_i\partial_iP\). Formula (4) can also be verified
directly in the polynomial ring over \(\mathbb Q(\lambda)\), using only
\(\lambda^2=3\). This direct check is independent of the coordinate-map
and diagonalization explanations.

## 5. Recovering the exact fixed target

Let \(\sigma P=P\circ\sigma\) on polynomials and put

\[
D_-=\sigma D_+,
\qquad (N_-)_i=\epsilon_i\,\sigma((N_+)_i),
\qquad \epsilon=(1,-1,1,1,-1,1).
\]

The component signs are necessary: this is transport of a vector field,
not just substitution in six unrelated polynomials. Since \(\sigma F=F\),
the chain rule and invariance of divergence imply

\[
N_-(F)=A_-D_-,
\qquad D_-\operatorname{div}N_--N_-(D_-)=0.
\]

The final certificate is

\[
\boxed{
D=D_+D_-,\qquad
N=D_-N_++D_+N_-,\qquad Q=0.
}
\qquad\text{(5)}
\]

It represents the sum of the two strict fields. In particular,

\[
N(F)=X_0^3Y_0^3D,
\qquad D\operatorname{div}N-N(D)=0.
\]

Consequently the precise cleared expression in the verifier is

\[
D(AD-N(F))+F\bigl(D\operatorname{div}N-N(D)\bigr)
=0=F^2Q.
\]

Thus (5) serves the exact statement with the original \((F,q,A)\).

## 6. Degrees, parity, nonvanishing, and relative primality

All factors above are homogeneous. Their degrees are

| Polynomials | Degree |
|---|---:|
| \(p\) | 2 |
| \(s,S,T,R\) | 3 |
| \(c\) | 4 |
| \(G_0,f\) | 6 |
| \(h,p_1\) | 8 |
| \(W\) | 9 |
| \(p_0\) | 10 |
| \(\delta\) | 12 |
| \(Z\) | 18 |
| \(U,B\) | 24 |
| \(V\) | 26 |
| \(D_+\), \((N_+)_i\) | 30, 31 |
| \(D\), \(N_i\) | 60, 61 |

Under the global involution \(\tau:(X,Y)\mapsto(X,-Y)\), the polynomials
\(s,S,T,R\) are odd. All of \(p,G_0,c,\delta,h,f,Z,p_0,p_1,U,V,B\)
are even, while \(W\) is odd. Formula (3) therefore makes \(D_+\) even,
the first three numerator components odd, and the last three even.
The involutions \(\sigma\) and \(\tau\) commute, so (5) has precisely
the same parity pattern. This symmetry is an additional property of the
construction; the unrestricted certificate contract imposes no field-parity
restriction.

Relative primality has a short explicit check. Regard \(F,D_+\) as
polynomials in \(t=Y_2\), with coefficients in the other five variables.
The leading coefficient of \(F\) is one. Specialize

\[
X_0=X_1=X_2=Y_0=Y_1=1.
\]

Then \(F\) becomes \(t^6+7\), and \(D_+\) becomes

\[
d(t)=27972t^{18}+391608t^{12}+953312t^6.
\]

They satisfy the exact Euclidean identity

\[
d(t)=(t^6+7)(27972t^{12}+195804t^6-417316)+2921212.
\qquad\text{(6)}
\]

The nonzero constant remainder gives a Bezout certificate over \(\mathbb C\).
The repository's `relPrime_of_specialization` lemma lifts this to
\(\operatorname{IsRelPrime}(F,D_+)\), using the unit leading coefficient
of \(F\). This proves relative primality, rather than merely checking
that \(F\) does not divide \(D_+\). The same specialization proves
\(D_+\ne0\).

The automorphism \(\sigma\) preserves \(F\), so relative primality and
nonvanishing also hold for \(D_-\). Relative primality is preserved under
products, and the polynomial ring over \(\mathbb C\) is a domain. Hence
\(D=D_+D_-\ne0\) and \(\operatorname{IsRelPrime}(F,D)\), completing
the denominator conditions.

## 7. Relation to the formal certificate

The main polynomial calculation can be organized in only five independent
variables \(G_0,c,p,R,T\), over \(\mathbb Q\). Define the derivations

\[
\mathcal E=6G_0\partial_{G_0}+4c\partial_c,
\qquad
\mathcal K=(3R+12T)\partial_R+9T\partial_T
\]

and the polynomial

\[
M=3\mathcal E(U)+18U+6\partial_pV+\mathcal K(B)+6B.
\]

The two identities in that smaller polynomial ring are

\[
\begin{aligned}
D_+&=6U(6G_0+4cp)+12V(c+6p^2)+36BR^2,\\
D_+M&=3U\mathcal E(D_+)+6V\partial_pD_++B\mathcal K(D_+).
\end{aligned}
\qquad\text{(7)}
\]

After substitution, direct differentiation of (3) gives

\[
\operatorname{div}N_+=X_0^3S M
\]

and

\[
N_+(D_+)=X_0^3S
\left(3U\mathcal E(D_+)+6V\partial_pD_++B\mathcal K(D_+)\right).
\]

Thus (7) supplies the two strict half-target identities. The contribution
\(18U\) in \(M\) includes differentiation of the common factor
\(X_0^3\) in (3). The polynomials \(D_+,U,V,B,M\) have respectively
18, 12, 11, 10, and 24 terms when expanded in these five variables. This
keeps the algebraic core of the verification separate from the much
larger expansion in the six original coordinates.

The displayed formulas specify all witness data: denominator degree 60,
the polynomial \(D\), the six entries of \(N\), and \(Q=0\).
For this data, `HodgeComputer.Verify` checks that \(F\ne0\), that \(F\)
and \(A\) are homogeneous of degree six, and that the witness satisfies
\(D\ne0\), homogeneity of \(D\) of degree 60, homogeneity of every
\(N_i\) of degree \(60+6q-5=61\),
\(\operatorname{IsRelPrime}(F,D)\) over \(\mathbb C\), and the exact
cleared identity with right-hand side \(F^{q+1}Q=0\).
Equations (3)–(6) isolate those algebraic and side-condition obligations.

The complete submitted Lean proof is contained in [Solution.lean](Solution.lean).
The following named sections organize its definitions and proof obligations.
The physical witness declarations are in the `OneReflectionPhysical` namespace;
the scalar identity and general certificate operations retain their own namespaces.

| Section heading in `Solution.lean` | Named declarations and proof obligations |
|---|---|
| `OneReflectionPhysical` | Defines the half-target polynomials in (3), with `P`, `G`, and `tau` representing \(p\), \(G_0\), and \(\lambda\). Proves `tau_sq` and `F_decomposition`. |
| `OneReflectionFirstIdentity` | Proves the first scalar identity in (7), groups the six derivatives of the fixed \(F\), and proves `first_identity`, namely \(N_+(F)=A_+D_+\). |
| `OneReflectionDivergenceCore` | Proves `OneReflectionDivergenceCore.divergence_core`, the second identity in (7), in five scalar variables. Its derivative definitions record the actions of \(\mathcal E\), \(\partial_p\), and \(\mathcal K\). |
| `OneReflectionDifferentiation` and `OneReflectionSecondIdentity` | Prove `normal_derivative_grouped` and `divergence_grouped`, connect the physical derivatives to the scalar identity, and obtain `second_identity`, namely \(D_+\operatorname{div}N_+-N_+(D_+)=0\). |
| `OneReflectionHomogeneity` | Proves `D_homogeneous` and `N_homogeneous`, with half-target degrees 30 and 31. |
| `OneReflectionLegality` and `OneReflectionDenominator` | Set up the univariate specialization through `OneReflectionLegality.legal_of_fiber`, prove (6), and establish `D_legal` and `D_ne_zero`. |
| Shared [coordinate changes](../../formal/lean/HodgeComputer/CoordinateChanges.lean) and [certificate operations](../../formal/lean/HodgeComputer/CertificateOperations.lean) | `HodgeComputer.Verify.sign_change` and `HodgeComputer.Verify.add` supply the symmetry and addition operations, including the homogeneous degrees and denominator conditions used in (5). |
| `OneReflectionCertificate` | Defines `fullD` and `fullN`, proves `full_verify`, and assembles the exact existential target with `certificate_from_second_identity`. |
| `Final certificate` | Supplies the proven `second_identity` to that assembly theorem and exports `Submission.certificate`. |

In particular, the final theorem has the exact protected type

```lean
theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  OneReflectionPhysical.certificate_from_second_identity
    OneReflectionPhysical.second_identity
```

The square root is a fixed complex constant satisfying \(\lambda^2=3\),
not a new variable or an assumption on any of the six original coordinates.
There is no need to formalize a general reflection theorem, the geometry
of cubic surfaces, or an abstract trace theorem to check the final
polynomial witness.

## 8. Prior work and attribution

- **fringewidth** identified the hidden reflections and the weighted
  quotient coordinates \(p=Y_0Y_1\), \(s=Y_0^3-\varepsilon Y_1^3\) in
  the [existing discussion][hidden-reflections]; that comment discloses
  assistance from **Claude Opus 5.5**. The accompanying geometric
  existence argument is recorded in [why.md](why.md).
  This quotient and the earlier unsuccessful bounded searches motivated
  the search for an explicit construction.
- The **repository authors**, including **Benjamin E. Diamond**, developed
  the rational-certificate framework, the Piola and Euler constructions,
  and the reflection and cubic-surface explanations in
  [Chapter 1][certificates], [Chapter 2][constructions], and
  [Chapter 3][geometry].
- The binary-cubic Hessian diagonalization is a classical Sylvester
  construction. The explicit field averaging here follows the same
  principle as the accepted
  [`family-sylvester-norm` solution][sylvester-solution], contributed by
  **benediamond** in [PR #30][sylvester-pr]. In particular, it is essential
  to average the rational fields with their denominators, rather than
  average the numerators alone.
- The geometric interpretation rests on **Phillip Griffiths's** residue
  theory and **Benjamin E. Diamond's** certificate bridge, as cited in
  [Chapter 1][certificates] and [Diamond's paper][diamond]. Those results
  explain why the certificate supplies divisor support. The final
  verification uses the explicit polynomial identities and side
  conditions above.
- The specific rational coordinate map, the degree-30 half-target
  formulas, the symmetry assembly, and their verification were prepared
  with **OpenAI ChatGPT assistance**, including separate agents for
  construction, independent exact arithmetic, and Lean formalization,
  for a contribution through GitHub account **fqlx**.

[hidden-reflections]: https://github.com/hodge-computer/sextics/discussions/54#discussioncomment-18986773
[certificates]: https://github.com/hodge-computer/sextics/blob/main/docs/01-certificates.md
[constructions]: https://github.com/hodge-computer/sextics/blob/main/docs/02-explicit-constructions.md
[geometry]: https://github.com/hodge-computer/sextics/blob/main/docs/03-geometric-support.md
[sylvester-solution]: https://github.com/hodge-computer/sextics/blob/main/data/family-sylvester-norm/solution.md
[sylvester-pr]: https://github.com/hodge-computer/sextics/pull/30
[diamond]: https://arxiv.org/html/2603.29157v2#S2
