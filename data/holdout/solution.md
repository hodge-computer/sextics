# The holdout certificate from a Fermat cover and a moving conic

This solution proves the existential `HodgeComputer.HasCertificate` statement for the fixed `holdout` instance. The proof is a finite algebraic construction based on an exact conic, polynomial integration, and trace between function fields.

## 1. The fixed statement and the form of the answer

We use the variable order of [the protected instance](instance.rec):
\((X_0,X_1,X_2,Y_0,Y_1,Y_2)\). The equation, source, and pole parameter are exactly

\[
\begin{aligned}
F={}&X_0^6+X_1^6+X_2^6+Y_0^6+Y_1^6+Y_2^6\\
 &+X_0^3X_1Y_0Y_1+X_1^3X_2Y_1Y_2,\\
A={}&X_0^3Y_0^3,\qquad q=1.
\end{aligned}
\qquad\text{(1)}
\]

The argument proves existence of a finite polynomial certificate over \(\mathbf C\). It does not list an expanded denominator or a numerical degree. This is the existential form explicitly allowed by the [formal contract][formal-contract] and [contribution schema][contributing].

For a six-component tuple \(N\), write

\[
N(F)=\sum_iN_i\partial_iF,\qquad
\operatorname{div}N=\sum_i\partial_iN_i,\qquad
B_D(N)=D\operatorname{div}N-N(D).
\]

We first construct legal, possibly nonhomogeneous polynomial data with

\[
N(F)=AD,\qquad B_D(N)=FQ.
\qquad\text{(2)}
\]

These normalized identities imply the full required identity

\[
AD^2-DN(F)+FB_D(N)=F^2Q.
\qquad\text{(3)}
\]

A final finite extraction makes \(D\) homogeneous and each \(N_i\) homogeneous of degree \(\deg(D)+1\), while preserving (2), \(D\ne0\), and relative primality of \(F,D\). The quotient \(Q\) is allowed to be nonzero.

The construction introduces a Fermat-curve cover on which a reflection becomes available. Its quotient has a moving polynomial conic. An exact nonsingular conic seed supplies a finite algebraic family through the generic point; along this family the residue equation becomes integration of a polynomial in one variable. Finite trace descends the solution, and a deck character isolates the exact source \(A\). All these operations construct a certificate for (1); they do not replace the protected input by another instance.

## 2. The Fermat cover, the quotient, and the source

Adjoin \(T\) with \(T^6=Y_0^6+Y_2^6\), and set

\[
\alpha=Y_0/T,\qquad \beta=Y_2/T,\qquad y=Y_1.
\]

The coefficient parameters lie on the fixed Fermat curve

\[
\alpha^6+\beta^6=1.
\qquad\text{(4)}
\]

On the cover, the sextic becomes

\[
G=X_0^6+X_1^6+X_2^6+y^6+T^6
 +yT(\alpha X_0^3X_1+\beta X_1^3X_2).
\qquad\text{(5)}
\]

Interchanging \(y,T\) preserves this equation. Together with their simultaneous sign change, the interchange has invariant coordinates

\[
S=y^2+T^2,\qquad P=yT.
\]

Since \(y^6+T^6=S^3-3SP^2\), the quotient equation is

\[
H=X_0^6+X_1^6+X_2^6
 +P(\alpha X_0^3X_1+\beta X_1^3X_2)+S^3-3SP^2.
\qquad\text{(6)}
\]

Throughout the proof its coordinate order is \((X_0,X_1,X_2,S,P)\). Its weights are \((1,1,1,2,2)\), and \(H\) has weighted degree six. The weighted projective interpretation motivates searching for moving rational curves. The formal proof instead uses the explicit conic and Jacobian below; it does not invoke a rational connectedness theorem, a classification of threefolds, or an unformalized geometric existence result.

The coefficient field is the actual function field

\[
K_b=\operatorname{Frac}
 \bigl(\mathbf C[\alpha,\beta]/(\alpha^6+\beta^6-1)\bigr).
\]

Thus \(\alpha,\beta\) are algebraic functions on a curve, not independent rational parameters. They are held constant in the five-coordinate quotient construction. Their derivatives are restored by the complete coordinate maps when the solution is returned to the six physical coordinates.

### The orientation of the source

Use \(\beta\) as the base coordinate. In the cover order \((X_0,X_1,X_2,y,T,\beta)\), the map \((Y_0,Y_1,Y_2)=(\alpha T,y,\beta T)\) has Jacobian

\[
\det\frac{\partial(Y_0,Y_1,Y_2)}{\partial(y,T,\beta)}
=-\frac{T}{\alpha^5}.
\]

The pulled-back target density is therefore \(-X_0^3T^4/\alpha^2\). The interchange of \(y,T\) has determinant \(-1\); adding the reflected pullback gives density \(X_0^3(y^4-T^4)/\alpha^2\). In the order \((S,P)\),

\[
\det\frac{\partial(S,P)}{\partial(y,T)}=2(y^2-T^2).
\]

The quotient source is consequently

\[
B=\frac{X_0^3S}{2\alpha^2}\in K_b[X_0,X_1,X_2,S,P].
\qquad\text{(7)}
\]

The positive sign in (7) uses the stated \(S,P\) order. Reversing these coordinates would reverse the density. The formal coordinate and determinant identities retain the order explicitly.

## 3. An exact conic seed

We construct one conic on one actual complex fiber of (4), with a nonzero coefficient Jacobian. The seed uses a real algebraic number \(r\in(7,8)\). Its defining degree-23 polynomial \(f\) is displayed in the appendix. The exact values

\[
f(7)=-1000427543178133743<0,\qquad
f(8)=37662822436086419543>0
\]

and continuity give a root by the intermediate value theorem.

Define

\[
\begin{aligned}
m&=r^4-4r^3+5r^2+r-2,\\
R&=\frac{r(1-r-r^2)}{1-r},&
M&=\frac{r^2m}{(r-1)^2},\\
a&=\frac{3(1-2r)}{1-r},&
b&=3(1-2r).
\end{aligned}
\qquad\text{(8)}
\]

All denominators are nonzero, and \(R,M>0\). Choose \(q_c,k_c\in\mathbf C\) with

\[
q_c^4=R,\qquad k_c^6=M/q_c^2,
\]

and put

\[
p_c=r/q_c,\qquad
\alpha_c=a/(k_cq_c),\qquad
\beta_c=b/(k_c^3q_c).
\qquad\text{(9)}
\]

Both chosen roots are nonzero. Clearing denominators in \(f(r)=0\) proves

\[
\frac{a^6}{MR}+\frac{b^6}{M^3}=1,
\]

so \(\alpha_c^6+\beta_c^6=1\). The subscript on \(q_c\) distinguishes this auxiliary seed parameter from the fixed pole parameter \(q=1\).

The weighted conic is

\[
\begin{aligned}
X_0&=s^2,&X_1&=k_cst,&X_2&=t^2,\\
S&=-(s^4+q_c^2s^2t^2+t^4),&&
P&=p_cs^3t+q_cst^3.
\end{aligned}
\qquad\text{(10)}
\]

Substitution in (6) gives zero identically. The proof checks the rational coefficient relations from (8), the complex power relations, the Fermat base relation, and the complete curve identity. At \([s:t]=[1:0]\), the curve passes through \((1,0,0,-1,0)\).

Modular experiments helped discover this seed, but no modular existence or numerical rank statement is used in the proof over \(\mathbf C\).

### The exact nonsingularity calculation

On \(s=1\), write the curve parameter as \(\tau\). Allow all positive coefficients of \(X_0,X_2\) through degree two and of \(S,P\) through degree four to vary. Keep \(X_1=k_c\tau\) fixed. There are twelve variable coefficients and twelve equations: the coefficients of degrees \(1,\ldots,12\) in \(H(\phi(\tau))\).

At the seed, parity splits the Jacobian into two six-by-six blocks. The columns can be ordered as follows.

| Block | Coordinate-monomial variations |
| --- | --- |
| Even equations | \(\delta X_0=\tau^2,\ \delta X_2=\tau^2,\ \delta S=\tau^2,\ \delta S=\tau^4,\ \delta P=\tau,\ \delta P=\tau^3\) |
| Odd equations | \(\delta X_0=\tau,\ \delta X_2=\tau,\ \delta S=\tau,\ \delta S=\tau^3,\ \delta P=\tau^2,\ \delta P=\tau^4\) |

Each column changes only the indicated coordinate. For a variation \(e_j\tau^d\), the equation of degree \(e\) has Jacobian entry

\[
[\tau^e]\bigl(H_j(\phi(\tau))\tau^d\bigr).
\qquad\text{(11)}
\]

The block determinants are nonzero scalar factors times

\[
\begin{aligned}
g_{\rm even}(r)={}&16r^{11}-80r^{10}+96r^9+144r^8-380r^7+240r^6\\
 &+84r^5-178r^4+63r^3+9r^2-8r+1,\\
g_{\rm odd}(r)={}&8r^{11}-48r^{10}+112r^9-16r^8-224r^7+352r^6\\
 &-275r^5+101r^4+11r^3-24r^2+8r-1.
\end{aligned}
\qquad\text{(12)}
\]

Substitution \(r=u+7\) expands both polynomials with strictly positive coefficients. They are therefore positive for \(r>7\). The remaining determinant factors are products and powers of the nonzero quantities in (8)–(9). Lean checks the two complete determinant identities and the link between their entries and the coefficient equations (11).

## 4. A finite algebraic family through the generic point

The generic endpoint has the form

\[
x=(x_0,0,x_2,s_0,p_0),\qquad
x_0^6+x_2^6+s_0^3-3s_0p_0^2=0.
\qquad\text{(13)}
\]

Initially work over the ring containing both the Fermat relation (4) and the endpoint relation (13). Adjoin the twelve positive coefficients, impose \([\tau^e]H(\phi)=0\) for \(e=1,\ldots,12\), and invert their Jacobian determinant, whose entries are given by (11). This is a standard étale algebra over the endpoint ring. The seed gives a map to \(\mathbf C\), because the equations vanish and the inverted determinant is nonzero. The localized algebra is therefore nontrivial.

The order of these steps is essential: specialization is performed on a finitely presented coordinate ring. No arbitrary denominator in its generic fraction field is evaluated at the seed.

Let \(K_0\) be the function field of (13) over \(K_b\). The endpoint equation is monic and irreducible, so the endpoint coefficient ring embeds in \(K_0\). Flatness of an étale algebra shows that the generic base change remains nontrivial. An étale algebra of finite type over a field is finite. Choosing a maximal ideal gives a finite field factor

\[
E/K_0.
\qquad\text{(14)}
\]

The twelve images of the coefficient variables supply an actual tuple \(\phi\in E[\tau]^5\) with

\[
H(\phi)=0,\qquad \phi(0)=x,\qquad \phi_1=k_c\tau,
\qquad\text{(15)}
\]

and invertible evaluated coefficient Jacobian. The equation \(H(\phi)=0\) follows from the constant endpoint relation, the degree bound twelve, and coverage of every positive coefficient.

This finite algebraic construction does not require an expanded eliminant for the twelve coefficients or choices of analytic branches. Classical choice selects a field factor whose required properties have already been proved.

The coordinate map also embeds

\[
K_H=\operatorname{Frac}(K_b[X_0,X_1,X_2,S,P]/(H))
\]

into \(L=\operatorname{Frac}(E[\tau])\). Injectivity is proved from the independent endpoint parameters, the identity \(\phi_1=k_c\tau\) with \(k_c\ne0\), and the monic irreducible equation in \(X_0\). Both fields have transcendence degree four over \(K_b\); \(L\) is finitely generated over \(K_b\). Consequently \(L/K_H\) is finite. This actual extension, rather than a conjectural covering degree, is used for trace descent.

## 5. A polynomial normal vector

Set \(g_j=H_j(\phi)\). At the endpoint \(x_1=0\), we have \(g_0(0)=6x_0^5\ne0\). Start with the constant vector \(\psi^{(0)}=e_0/(6x_0^5)\). The polynomial \(g\cdot\psi^{(0)}-1\) has zero constant coefficient. The inverse of (11) gives corrections in the twelve positive coordinate monomials. The resulting polynomial vector satisfies

\[
\psi\in E[\tau]^5,\qquad
\sum_jg_j\psi_j=1,\qquad
\psi(0)=\frac{e_0}{6x_0^5}.
\qquad\text{(16)}
\]

The proof includes the degree bounds and full coefficient coverage needed to turn the matrix equation into the polynomial identity (16).

There are four commuting derivations \(D_i\) on \(L\): differentiation in \(\tau\), and the three tangent derivations of the endpoint corresponding to \(x_2,s_0,p_0\). The latter extend uniquely through the finite characteristic-zero extension (14), act coefficientwise on \(E[\tau]\), and extend by the quotient rule to \(L\). They kill \(K_b\) and preserve \(E[\tau]\). Choose \(D_0=\partial_\tau\).

Form

\[
M=(\psi,D_0\phi,D_1\phi,D_2\phi,D_3\phi),\qquad J=\det M.
\qquad\text{(17)}
\]

The first column pairs with \(g\) to one. Each other column pairs to zero by differentiating \(H(\phi)=0\). At \(\tau=0\), the determinant is \(k_c/(6x_0^5)\ne0\): the three endpoint parameters give the identity derivative matrix, and the remaining tangent direction has \(X_1\)-component \(k_c\). Thus \(J\) is a nonzero polynomial.

## 6. Polynomial integration of the residue equation

For a hypersurface with distinguished coordinate \(X_0\), its tangent derivations are

\[
\mathcal E_j=\partial_{j+1}-\frac{g_{j+1}}{g_0}\partial_0.
\]

For a tangent tuple \(w\), define

\[
\operatorname{div}_{g_0}(w)
=\sum_j\left(\mathcal E_jw_j-\frac{w_j\mathcal E_jg_0}{g_0}\right).
\qquad\text{(18)}
\]

For a source \(B\), the equation to solve is

\[
\operatorname{div}_{g_0}(w)=-r_B,\qquad
r_B=\frac{\partial_0B}{g_0}-\frac{BH_{00}}{g_0^2}.
\qquad\text{(19)}
\]

Here all entries are evaluated in the hypersurface function field. Nonvanishing of \(g_0\) is an algebraic fact proved in Section 9.

Let \(N=M^{-1}\). Its first row is \(g\). The matrix

\[
T_{ij}=N_{i+1,j+1}-N_{i+1,0}\frac{g_{j+1}}{g_0}
\]

satisfies

\[
\mathcal E_j=\sum_iT_{ij}D_i.
\qquad\text{(20)}
\]

The proof establishes this first on the coefficient field and coordinate images, then on every rational function and the entire finite extension. It uses the quotient-rule generation lemma and uniqueness of derivations on separable algebraic extensions; equality just on a short list of coordinates would be insufficient on its own.

The determinant form of the Piola identity expresses the needed source density as

\[
\begin{aligned}
\mathcal P={}&J\sum_j\psi_j\partial_jB\\
 &+B\left(
 \sum_i\det M[\mathrm{column}\ i+1\leftarrow D_i\psi]
 -J\sum_{j,k}\psi_jH_{jk}\psi_k\right).
\end{aligned}
\qquad\text{(21)}
\]

Every term is in \(E[\tau]\). The family, the normal vector, and their source derivatives are polynomial in \(\tau\); their coefficients are constant for \(D_0\). Thus only a polynomial is integrated:

\[
\sum_{n\ge0}c_n\tau^n\longmapsto
\sum_{n\ge0}\frac{c_n}{n+1}\tau^{n+1}.
\]

The sums are finite and division by \(n+1\) is valid in characteristic zero. We do not assert that an arbitrary algebraic function has a rational antiderivative.

Dividing this polynomial primitive by \(J\), applying the weighted Piola identity, and including the tangent correction from \(B\psi\), yields a tuple \(w\in L^4\) satisfying (19). The formal lemmas prove (20), (21), and the final rational identity. The construction works for every polynomial source in the five active coordinates over \(K_b\), including (7).

Normalized trace from the actual finite extension \(L/K_H\) gives a solution in \(K_H\). Trace commutes with the uniquely extended derivations, and its normalization is the identity on \(K_H\). These properties are proved for finite field extensions. No coefficient functional is assumed to commute with derivatives merely because it is linear.

## 7. Physical transport and the deck trace

The quotient function field and the original physical function field embed in a common field defined by (4)–(5). The maps are proved injective from explicit presentations. The physical-to-common extension is finite: both sides have transcendence degree five over \(\mathbf C\), and the common field is finitely generated. Its exact degree is not needed.

The map from the five physical independent coordinates to \((X_1,X_2,S,P,\beta)\), with the distinguished coordinate \(X_0\) fixed, has Jacobian

\[
J_c=\frac{2\alpha^5(T^2-y^2)}{T}.
\]

It is the ratio of the two Jacobians calculated in Section 2, in the corresponding coordinate order. Substituting (7) gives the exact density identity

\[
J_cB=A\left(1-\frac{y^4}{T^4}\right).
\]

The five changed coordinate functions and \(J_c\) are independent of \(X_0\); the distinguished coordinate \(X_0\) is fixed, and \(\partial_0H\) pulls back to \(\partial_0F\). Differentiating the last identity in the distinguished direction therefore gives

\[
J_c r_B=r_A\left(1-\frac{y^4}{T^4}\right),
\qquad
r_A=\frac{\partial_0A}{\partial_0F}
 -\frac{A\partial_0^2F}{(\partial_0F)^2}.
\]

This is the normal-source identity used by the residue Piola transport. The base direction is included over \(\mathbf C\); the derivative of \(\alpha\) is governed by (4). Thus the quotient residue solution becomes a physical residue solution for the source

\[
A-\frac{X_0^3Y_0^3Y_1^4}{T^4}.
\qquad\text{(22)}
\]

The second term vanishes under normalized trace to the physical function field. Choose a sixth root \(\zeta\) with \(\zeta^4\ne1\); a nontrivial cube root of unity has these properties. The common field has a deck automorphism fixing all physical coordinates and acting by

\[
T\longmapsto\zeta T,\qquad
\alpha\longmapsto\zeta^{-1}\alpha,\qquad
\beta\longmapsto\zeta^{-1}\beta.
\qquad\text{(23)}
\]

The reflected term in (22) is an eigenvector with eigenvalue \(\zeta^{-4}\ne1\). Trace is invariant under this automorphism, so that term has trace zero. The normalized trace of \(A\), already in the physical field, is \(A\). Commutation with the physical tangent derivations therefore gives the exact residue equation for the source in (1).

This step is target-specific. The argument does not assert that every source on the original sextic is selected by this projection; it isolates \(X_0^3Y_0^3\) from its reflected companion.

## 8. Legal polynomial clearing

Let \(\rho:\mathbf C[X,Y]\to K_F=\operatorname{Frac}(\mathbf C[X,Y]/(F))\), and write \(g_i=\partial_iF\). The physical residue solution gives \(w_1,\ldots,w_5\in K_F\). Choose a common polynomial denominator \(d\) and representatives \(n_i\) with

\[
\rho(d)\ne0,\qquad \rho(n_i)=\rho(d)w_i.
\]

These representatives exist by surjectivity of the quotient map and the definition of its fraction field. Set

\[
D=g_0d,\qquad
N_0=Ad-\sum_{i=1}^5g_in_i,\qquad
N_i=g_0n_i\quad(1\le i\le5).
\qquad\text{(24)}
\]

The normal identity \(N(F)=AD\) now holds exactly in the polynomial ring. A quotient-rule calculation relates \(\rho(B_D(N))\) to the residue equation. The latter is zero, so \(B_D(N)\in\ker\rho=(F)\); a polynomial \(Q\) exists with \(B_D(N)=FQ\).

Both \(\rho(g_0)\) and \(\rho(d)\) are nonzero in a field. Hence \(\rho(D)\ne0\), which implies \(D\ne0\) and \(F\nmid D\). Irreducibility of \(F\) then gives relative primality of \(F,D\). Auxiliary denominators have been removed by trace and by representatives in the physical quotient. Their norms are not specialized in place of this nonvanishing argument.

## 9. Domain and chart side conditions

The proof uses explicit domains and their fraction fields. Irreducibility follows from monic specialization and Eisenstein's criterion. For example, (6) is monic in \(X_0\); setting \(X_1=X_2=0\) and \(P=1\) gives

\[
X_0^6+S^3-3S,
\]

which is Eisenstein at \(S\). Monicity preserves both factor degrees under specialization, so a factorization of the original polynomial would contradict this one. The endpoint equation is treated similarly. For the coefficient curve, \(\alpha^6+\beta^6-1\) is Eisenstein at \(\beta-1\).

For the physical equation, specialize \(X_1=X_2=Y_1=0\) and \(Y_2=\eta\), where \(\eta^6=-1\). The result \(X_0^6+Y_0^6-1\) is Eisenstein at \(Y_0-1\). The formal domain arguments also supply the coefficient-ring injections required in the field constructions.

The distinguished derivative is nonzero modulo the hypersurface. For either \(F\) or \(H\), restriction to the \(X_0\)-axis sends the equation to \(X_0^6\) and its derivative to \(6X_0^5\). Divisibility would survive this specialization and contradict their degrees. Thus the derivative denominators in (18)–(24) are nonzero in the corresponding function fields. No assertion is made that these affine charts contain every point of the hypersurface.

## 10. Finite homogeneous extraction

The data (24) may be nonhomogeneous. Since \(F\) is homogeneous, its principal ideal is graded. Remove the lowest homogeneous components of \(D\) that are multiples of \(F\). This finite process gives \(D_{\mathrm{red}}=D+FU\) whose least nonzero homogeneous component is legal.

To retain the normalized equations, put \(g=\partial_0F\) and replace

\[
D'=gD_{\mathrm{red}},\qquad N'=gN+AFUe_0.
\qquad\text{(25)}
\]

The normal identity stays exact. Modulo \(F\), the new differentiation terms in the divergence numerator cancel by \(N(F)=AD\). Its divergence numerator is therefore still divisible by \(F\). The least homogeneous part of \(D'\) is legal and has positive degree, since \(g\) has degree five and is relatively prime to \(F\).

Rename this pair \(D,N\), and let its legal initial denominator be \(h\), homogeneous of degree \(e>0\). Choose \(p>e+1\), and define

\[
S_p=\sum_{i=0}^{p-1}h^i(h-D)^{p-1-i},\qquad
H_p=h^p,\qquad U_p=(h-D)^p.
\]

Then \(DS_p=H_p-U_p\). Every term of \(h-D\) has degree at least \(e+1\), so \(U_p\) begins above the degrees that matter. Let \(M_i\) be the homogeneous component of degree \(pe+1\) in \(S_pN_i\). Extracting components yields

\[
M(F)=AH_p,\qquad B_{H_p}(M)=FQ'
\qquad\text{(26)}
\]

for a polynomial \(Q'\). The divergence calculation uses the exact identity

\[
D^2B_{H_p}(S_pN)
=H_p(H_p-U_p)B_D(N)
-D\bigl(H_pN(U_p)-U_pN(H_p)\bigr).
\qquad\text{(27)}
\]

All terms containing \(U_p\) begin above the component being extracted. The formal proof tracks degree lower bounds through products, derivatives, and homogeneous components. This is a finite polynomial calculation, not a convergence claim about an infinite series.

Finally, \(H_p=h^p\) is nonzero and homogeneous of degree \(pe\), each \(M_i\) is homogeneous of degree \(pe+1\), and \(F,H_p\) are relatively prime. Equation (26) implies (3). These are precisely the finite data required by the exact certificate statement. Their degree is existential; no minimal degree or optimized numerical bound is claimed.

## 11. Correspondence with the Lean proof

The submission has 59 Lean source files. Small generic components are grouped into shared files; the two large determinant calculations remain separate to control compilation memory. The tables below link the main mathematical steps to the supplied filenames. Additional polynomial, field, and derivation helpers are connected by their explicit imports. Declaration names are unchanged by this grouping.

### The quotient primitive

| Mathematical step | Supplied sources and declarations |
| --- | --- |
| Fixed equations and domains, Sections 1 and 9 | [HypersurfaceCoordinates.lean](HypersurfaceCoordinates.lean): `holdoutSextic`, `weightedHypersurface`, `holdoutSextic_irreducible`; [HomogeneousCertificate.lean](HomogeneousCertificate.lean): `holdoutSource` |
| Legal normal charts | [QuotientDerivatives.lean](QuotientDerivatives.lean): `quotient_normal_ne_zero`; [PhysicalDerivations.lean](PhysicalDerivations.lean): `physical_normal_ne_zero` |
| Exact complex conic, Section 3 | [CurveSeed.lean](CurveSeed.lean): `HoldoutConic.exists_seed`, `Seed.curve`, `Seed.base_relation`, `gEven_pos`, `gOdd_pos` |
| Exact determinant blocks and coefficient Jacobian | [CurveJacobianStaged.lean](CurveJacobianStaged.lean): `even_core_det`, `odd_core_det`; [CurveSeedIncidence.lean](CurveSeedIncidence.lean): `seed_equations`, `seedJacobian_nonsingular` |
| Polynomial coefficient equations | [CurveFamily.lean](CurveFamily.lean): `equations_pderiv`, `systemPoly_eq_constant`; [FermatIncidenceSeed.lean](FermatIncidenceSeed.lean): `fermat_incidence_nontrivial` |
| Étale algebra and finite coefficient field, Section 4 | [GenericIncidence.lean](GenericIncidence.lean): `square_system_jacobian_etale`, `genericEtale_exists_fieldFactor`; [ConicCoefficientField.lean](ConicCoefficientField.lean): `conicCoefficientFactor_exists`, `conicCoefficients_jacobian` |
| Actual family and finite target embedding | [ConicPolynomialFamily.lean](ConicPolynomialFamily.lean): `conicCurve_equation`, `conicCurve_jacobian`; [ConicEmbedding.lean](ConicEmbedding.lean): `conicTargetRingMap_injective`, `conicTargetFieldMap` |
| Polynomial normal vector and tangent matrix, Section 5 | [ConicNormal.lean](ConicNormal.lean): `exists_polynomial_normal`; [ConicSourceDerivations.lean](ConicSourceDerivations.lean): `conicNormal_pairing`, `conicSourceDerivations_commute`, `conicEvaluationMatrix_det_ne_zero` |
| Determinant and residue identities, Section 6 | [Piola.lean](Piola.lean): `piola_divergence`; [NormalDensity.lean](NormalDensity.lean): `normal_density_formula`; [PolynomialFamily.lean](PolynomialFamily.lean): `residue_solution_of_polynomial_family` |
| Complete derivative compatibility and polynomial integration | [PolynomialFamilyBridge.lean](PolynomialFamilyBridge.lean): `finite_quotient_tangent_chain`, `residue_solution_from_polynomial_curve` |
| Quotient residue solution and finite trace | [ConicResidue.lean](ConicResidue.lean): `conic_target_residue_solution`; [FiniteTrace.lean](FiniteTrace.lean): `residue_solution_descends_finite` |

### The return to the exact physical source

| Mathematical step | Supplied sources and declarations |
| --- | --- |
| Actual physical and common fields, Section 7 | [CoverFields.lean](CoverFields.lean): `physicalCoverFieldMap`, `commonCoverFunctionField_finite`; [QuotientCoverField.lean](QuotientCoverField.lean): `quotientCoverFieldMap`; [CoverCoordinates.lean](CoverCoordinates.lean): `coverAlpha_ne_zero`, `coverT_ne_zero`, `cover_square_difference_ne_zero` |
| Full physical coordinate Jacobian | [CoverDifferentials.lean](CoverDifferentials.lean): `actualCoverJacobian_det`, `actualCoverJacobian_det_ne_zero`, `coverQuotientTangent` |
| Compatibility on the entire quotient field | [FermatCoefficientDerivations.lean](FermatCoefficientDerivations.lean): `fermatCoefficient_derivation_zero`; [CoverQuotientCompatibility.lean](CoverQuotientCompatibility.lean): `coverQuotientTangent_base`, `coverQuotientTangent_compatible` |
| Exact source, normal, and sign identities | [CoverSourceBinding.lean](CoverSourceBinding.lean): `coverQuotientSource`, `cover_source_binding`, `cover_normal_binding`, `cover_normal_source_binding` |
| Deck automorphism and vanishing trace | [CoverDeckField.lean](CoverDeckField.lean): `commonDeckFieldEquiv_fixes_physical`, `commonCover_trace_inverse_fourth` |
| Residue Piola pullback and exact cover assembly | [ResiduePiolaPullback.lean](ResiduePiolaPullback.lean): `residue_solution_piola_pullback`; [CoverCertificate.lean](CoverCertificate.lean): `holdout_hasCertificate_of_quotient_divergence` |
| Legal polynomial clearing, Section 8 | [ResidueClearing.lean](ResidueClearing.lean): `residue_common_representatives`, `residue_divergence_identity`, `residue_solution_clearing`; [FiniteResidueClearing.lean](FiniteResidueClearing.lean): `finite_residue_solution_clearing_value` |
| Finite homogeneous extraction, Section 10 | [HomogeneousIdeal.lean](HomogeneousIdeal.lean): `exists_legal_initial_representative`; [HomogeneousField.lean](HomogeneousField.lean): `homogeneous_data_from_initial_denominator`; [HomogeneousCertificate.lean](HomogeneousCertificate.lean): `homogeneous_data_of_normalized`, `holdout_hasCertificate_of_normalized` |
| Trace, clearing, and homogeneity composed | [HoldoutCertificateClosure.lean](HoldoutCertificateClosure.lean): `holdout_hasCertificate_of_cover_residue` |

The final source [Solution.lean](Solution.lean) contains the closed wrapper:

```lean
theorem Submission.certificate :
    HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A
```

Its proof selects the checked complex seed, applies `conic_target_residue_solution` to the positive `coverQuotientSource`, and invokes `holdout_hasCertificate_of_quotient_divergence`. The verifier supplies the protected definitions, which are matched to (1). Classical choice selects roots and finite field factors only after their existence and properties have been proved. `Submission.certificate` is a closed theorem with no hypotheses or unproved placeholders. Compilation and kernel replay establish its proof using only the permitted axioms `propext`, `Classical.choice`, and `Quot.sound`. The detailed build and submission-check results accompany the proposal.

## Geometric scope of the Fermat cover

The accepted Lean proof above constructs the fixed \(q=1\) certificate in (1). The following geometric consequence of `fqlx`'s cover was prepared for `benediamond` with OpenAI ChatGPT assistance. It uses the book's support theorems, whose general geometric inputs are not formalized by that certificate.

**Fixed-variety theorem.** For the sextic \(F\) in (1), every \(Y\)-odd homogeneous target of degree \(6q\), for every positive \(q\), has a certificate.

### The supported quotient of the cover

On the cover (5), the commuting involutions
\[
r:(y,T)\mapsto(-y,-T),\qquad
\sigma:(y,T)\mapsto(T,y)
\]
have quotient (6). Its projective fibers over the Fermat curve are degree-six hypersurfaces in \(\mathbb P(1,1,1,2,2)\).

The generic fiber is quasismooth. Since quasismoothness is open, it suffices to check the fiber \((\alpha,\beta)=(0,1)\). A nonzero common zero of its five affine partials would satisfy
\[
X_0=0,\qquad S^2=P^2,\qquad
X_1^3X_2=6SP,\qquad
3X_1^2(2X_1^3+PX_2)=0,\qquad
6X_2^5+PX_1^3=0.
\]
If either \(X_1\) or \(X_2\) is zero, all coordinates are zero. Otherwise put \(S=\varepsilon P\), \(\varepsilon^2=1\). The equations give
\[
P=-2X_1^3/X_2,\qquad
X_1^6=3X_2^6,\qquad
X_2^3=24\varepsilon X_1^3.
\]
Squaring the last equality contradicts the preceding one.

The possible ambient quotient singularities lie at \(X_0=X_1=X_2=0\), where the equation is \(S(S^2-3P^2)=0\). These are three distinct points of local type \(\frac12(1,1,1)\). Weighted adjunction gives \(-K=\mathcal O(1)\), so the generic fiber is a normal \(\mathbb Q\)-Fano threefold. The normal-Fano theorem in [Chapter 3, §3.2][support] supplies covering rational curves. Curves in the fibers make the total fourfold uniruled even though its base curve has positive genus. A smooth projective model therefore has divisor-supported fourth cohomology. Quotient transfer, including the boundaries of the rational presentation, supports the \(r,\sigma\)-invariant part on a smooth model of the cover.

### The physical diagonal quotient and descent

Fix a primitive sixth root \(\zeta\). The deck transformation and its exchange conjugate are
\[
\begin{aligned}
d:(y,T,\alpha,\beta)&\mapsto
   (y,\zeta T,\zeta^{-1}\alpha,\zeta^{-1}\beta),\\
e=\sigma d\sigma:(y,T,\alpha,\beta)&\mapsto
   (\zeta y,T,\zeta^{-1}\alpha,\zeta^{-1}\beta).
\end{aligned}
\]
They preserve (4) and (5), commute, have order six, and satisfy \(r=d^3e^3\); \(\sigma\) interchanges \(d,e\). Thus the group they generate with \(\sigma\) is finite, a quotient of \((\mu_6\times\mu_6)\rtimes\mathbb Z/2\).

Take a smooth equivariant projective model \(Z\) resolving the cover and its projection to \(X=V(F)\). The resulting proper generically finite map \(p:Z\to X\) satisfies
\[
pd=p,\qquad pe=gp,\qquad pr=\tau p,
\]
where the physical diagonal automorphism \(g\) has weights \((0,0,0,5,1,5)\) modulo six. These identities hold in the displayed coordinates and hence on the projective models.

The automorphism \(g\) fixes \(F\). At a fixed point with only \(Y_0,Y_2\) nonzero and \(Y_0^6+Y_2^6=0\), its tangent weights are \((1,1,1,2)/6\), of age \(5/6\). The finite-quotient theorem in [Chapter 3, §3.3][support] therefore supports the \(g\)-invariant fourth cohomology. The two supported quotients now satisfy [the deck/exchange descent criterion](#technical-information/known-locus/46-descent-through-a-deck-action-and-an-exchange). Consequently
\[
H^4(X,\mathbb Q)^\tau\subseteq N^1H^4(X,\mathbb Q).
\]
The [certificate correspondence][certificates] and the all-pole extraction in [Chapter 3, §3.6][support] give the fixed-variety theorem. This argument reaches the entire invariant fourth cohomology, including its middle Hodge component.

### Target characters and the polynomial-source boundary

For an odd sextic monomial \(A=M(X)Y_0^aY_1^bY_2^c\), put \(m=a+c+1\), \(e=b-m\), and \(C=M(X)Y_0^aY_2^cY_1^m\). On the common coordinate open, the unnormalized invariant sum in [Chapter 2, §2.7][constructions] has density \(A-CT^e\). The deck trace removes the correction if \(e\not\equiv0\pmod6\). Otherwise the physical residue is \(g\)-invariant, since its character is
\[
5(a+1)+(b+1)+5(c+1)\equiv b-a-c-1=e\pmod6.
\]
The global argument supplies the support conclusion without assuming that an arbitrary rational form on the coordinate open extends to a global class.

There are 226 odd sextic monomials. The cover criterion serves 158, and the diagonal quotient serves the complementary 68. The eighteen odd Jacobian generators \(Z_j\partial_iF\), with \(i,j\) in opposite parity blocks, each have a unique leading monomial \(6Z_i^5Z_j\); their mixed terms have all exponents at most four. Hence the 208 odd sextic monomials with exponents at most four form a basis of the primitive target space. The cover and diagonal quotient account for 149 and 59 basis elements respectively. The complementary basis elements split into 47 with \(e=0\) and twelve with \(e=-6\). These exact counts can be reproduced by:

```python
from itertools import product

raw = {e for e in product(range(7), repeat=6)
       if sum(e) == 6 and sum(e[3:]) % 2 == 1}
basis = {e for e in raw if max(e) <= 4}

def cover(e):
    return (e[4]-e[3]-e[5]-1) % 6 != 0

assert len(raw) == 226 and len(basis) == 208
assert sum(map(cover, raw)) == 158
assert sum(map(cover, basis)) == 149
assert len(raw) - sum(map(cover, raw)) == 68
assert len(basis) - sum(map(cover, basis)) == 59
assert sum(e[4]-e[3]-e[5]-1 == 0 for e in raw) == 50
assert sum(e[4]-e[3]-e[5]-1 == 0 for e in basis) == 47
assert sum(e[4]-e[3]-e[5]-1 == -6 for e in basis) == 12
```

The polynomial-source construction on the complementary quotient in [Chapter 2, §2.8][constructions] serves the \(e=0\) sources, giving a finite-algebraic route to 196 of the 208 primitive basis directions together with the cover. The twelve \(e=-6\) densities have a fiber denominator and lie outside that polynomial-integration theorem. Their geometric support follows from the theorem above.

These counts concern the displayed source maps. Coordinate transport supplies further polynomial presentations: \(F\) is unchanged by exchanging \(X_2,Y_2\), which carries \(X_2Y_0^2Y_2^3\) to the cover-served \(X_2^3Y_0^2Y_2\). The same exchange serves \(X_iY_0Y_2^4\) and \(X_iY_0^3Y_2^2\), for \(i=0,1\). The constructions and their exchanged copies therefore span at least 201 primitive basis directions. A fiber pole in one presentation is not an obstruction to all finite-algebraic constructions.

The [character-separating bundle](#case/holdout-bundle), formalized by `fqlx`, combines the cover source \(X_0^3Y_0^3\) with the complementary polynomial source \(X_0^3Y_0Y_1^2\). These concrete certificates and the geometric all-target theorem have different scopes; neither asserts an expanded common denominator. The theorem is for the fixed sextic (1), and supplies no family dominating the space of all even sextics.

## 12. Context and attribution

The [motivation](why.md), [provenance](provenance.json), and full [existing holdout discussion][discussion] were read before developing this construction. They explain the oriented-chain difficulty and record substantial earlier work on supports and rational fields. The present route uses an auxiliary cover and a moving conic on its quotient. It neither infers nonexistence from a failed bounded search nor assumes that an algebraic primitive descends without checking trace and derivation compatibility.

Earlier holdout work by `fringewidth`, `rbajaj5`, and `fqlx` in the [discussion][discussion] clarified the residual symmetry sector and established bounded-support obstructions. That work supplies context for the auxiliary-cover construction. The Jacobian and deck trace in Sections 2 and 7 recover the original \(q=1\) source explicitly.

The following prior work and assistance are material to the argument.

- **The repository authors, including Benjamin E. Diamond**, supplied the benchmark, the certificate formalism, the residue interpretation, and the methods in [Chapter 1][certificates], [Chapter 2][constructions], [Chapter 3][support], and [Chapter 4][frontier]. The rational-vector-field normalization and coordinate transport build on this work.
- **Phillip Griffiths's residue theory** and **Benjamin E. Diamond's certificate correspondence** explain the geometric meaning of the identity; see the repository's development and [Diamond's paper][diamond]. The Lean proof establishes the finite certificate directly, without inserting those geometric theorems as new axioms.
- `fringewidth` identified hidden reflections and useful quotient coordinates for the earlier one-reflection instance in [its discussion][hidden-reflections], with disclosed **Claude Opus 5.5** assistance. The accepted [one-reflection solution][one-reflection] developed reflection transport and certificate assembly with **OpenAI ChatGPT** assistance for contributor `fqlx`. Those ideas motivated seeking a reflection on a cover. The Fermat-curve cover and moving-conic construction here are the new steps for the fixed holdout.
- `HeadOfNaps` contributed the accepted [quadric-contact-broken proposal][quadric-pr], including its [fraction-derivation construction][fraction-derivation]. The field-valued fraction extension used here adapts that quotient-rule proof to a derivation taking values in a fraction field. Credit also belongs to the collaborators and AI assistance disclosed in that proposal; the source retains this dependency's attribution.
- **The Lean and mathlib contributors** supplied the foundational polynomial, field, derivation, determinant, étale-algebra, localization, and real-analysis libraries. Finite trace, separability, flatness, the intermediate value theorem, and algebraic closedness of \(\mathbf C\) are proved library results. The repository's pinned toolchain and mathlib revision are used.
- **OpenAI ChatGPT**, working through collaborating agents, assisted with the conic search, exact algebra, independent checks, formalization, debugging, and exposition for a contribution through GitHub account `fqlx`. These are AI-assisted results. Kernel verification and the prescribed checks establish the formal claims; agreement among agents is not presented as independent human review.

The deliverable is an existence proof for the exact certificate. It does not export an expanded witness, a numerical degree, or a minimality theorem. The project's separate mathematical review and publication process remain part of acceptance.

## Appendix: the seed polynomial

The polynomial used in Section 3 is

\[
\begin{aligned}
f(r)={}&r^{23}-14r^{22}+86r^{21}-290r^{20}+520r^{19}-199r^{18}\\
 &-94566r^{17}+1029405r^{16}-5018220r^{15}+13903481r^{14}\\
 &-22713424r^{13}+17780092r^{12}+9399696r^{11}-47299809r^{10}\\
 &+72791853r^9-73173409r^8+54302525r^7-30776930r^6\\
 &+13325391r^5-4325886r^4+1016955r^3-163296r^2+16038r-729.
\end{aligned}
\]

Clearing the nonzero denominators in (8) shows that \(f(r)=0\) implies the base relation used in (9). The proof only needs a root in \((7,8)\); it does not require an assertion that this polynomial is irreducible.

[formal-contract]: https://github.com/hodge-computer/sextics/blob/main/formal/README.md
[contributing]: https://github.com/hodge-computer/sextics/blob/main/CONTRIBUTING.md
[discussion]: https://github.com/hodge-computer/sextics/discussions/44
[certificates]: https://github.com/hodge-computer/sextics/blob/main/docs/01-certificates.md
[constructions]: https://github.com/hodge-computer/sextics/blob/main/docs/02-explicit-constructions.md
[support]: https://github.com/hodge-computer/sextics/blob/main/docs/03-geometric-support.md
[frontier]: https://github.com/hodge-computer/sextics/blob/main/docs/04-known-locus-and-frontier.md
[diamond]: https://arxiv.org/html/2603.29157v2#S2
[hidden-reflections]: https://github.com/hodge-computer/sextics/discussions/54#discussioncomment-18986773
[one-reflection]: https://github.com/hodge-computer/sextics/blob/main/data/one-reflection/solution.md
[quadric-pr]: https://github.com/hodge-computer/sextics/pull/122
[fraction-derivation]: https://github.com/hodge-computer/sextics/blob/main/data/quadric-contact-broken/FractionDerivation.lean
