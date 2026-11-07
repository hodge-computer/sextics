# Canonical contact forms and an explicit finite trace target

## Result and scope

This packet constructs a closed rational one-form for the **actual prescribed
source** on the certified contact component. It proves that this form is
nonzero at the certified contact, and specifies a finite étale algebra and
nine coefficient rational-function trace identities that would supply the
remaining source equality.

The final nine identities have **not** been evaluated or proved. Nonvanishing
of the pullback form does not identify its pushforward with the original
source. No `HasCertificate` theorem or complete primitive is claimed here.

The root existence and source polynomial remain those in
`contact_exact_ball.json` and `contact_target_circuit.json`. No target
coefficient, source coefficient, or pole order has been changed.

## Reproduction and files

The exact verification commands, from this directory, are:

```sh
python contact_certify.py --verify-only
python contact_forms_regularity.py --verify-only
python contact_forms_nonzero.py --verify-only
python contact_forms_audit.py
```

The first command is supplied by the surrounding contact-repair packet.
The exact matrix verifiers use Python's `Fraction` and python-flint integer
matrices. Numerical QR is used only when generating a new witness, not in
`--verify-only`. The symbolic audit uses SymPy. The current shared helpers
also use NumPy/SciPy; the accompanying package declares these dependencies.

To regenerate the two portable source circuits:

```sh
python contact_forms_circuit.py
python contact_forms_global_residue.py
```

The generator finds `contact_target_circuit.json` beside itself. Its scalar
circuit helper is loaded from the sibling `research_workaround` directory,
or from the original development directory `proof_attempt3` when the former
is absent. It does not contain a session-specific absolute path.

Files supplied here:

- `contact_forms_regularity.py`, `contact_forms_regularity_witness.json`,
  `contact_forms_regularity_receipt.json`: exact residue regularity.
- `contact_forms_nonzero.py`, `contact_forms_nonzero_witness.json`,
  `contact_forms_nonzero_receipt.json`: exact nonvanishing enclosure.
- `contact_forms_circuit.py`, `contact_forms_residue_system.json`,
  `contact_forms_circuit_receipt.json`: canonical form and current numerators.
- `contact_forms_global_residue.py`, `contact_forms_global_residue.json`:
  explicit full finite-algebra trace operands.
- `contact_forms_audit.py`, `contact_forms_audit_receipt.json`: universal
  symbolic identities and exact arithmetic circuit checks.
- This README.

## 1. The exact source and residue normalization

Use the reflection-pencil equation

\[
G=G_{\rm raw}/\ell,
\qquad \ell=(14\lambda^6-10\lambda^4-5\lambda^2+14)/7,
\]

in weighted variables \((a,b,c,d,u)\) of weights \((1,1,1,1,2)\).
The protected source on this weighted threefold is

\[
R=\frac{2bd(a^2-u)(c^2-\lambda^2u)}{\ell^2}.
\]

It has weighted degree six and is negative under
\((c,d)\mapsto(-c,-d)\). On
\(a=1,b=r,c=z,d=sz,u=w\), the weighted residue volume contributes the
additional Jacobian factor \(z\). Thus its ordinary chart density is exactly

\[
\frac{2rsz^2}{\ell^2}(1-w)(z^2-\lambda^2w),
\]

the protected normal source in `general_cubic_current_derivation.md`.
The factor two and the factor \(\ell^{-2}\) are retained.

Write the norm presentation as

\[
G=(u+Q_1)g_1+Q_2g_2+A^2-B^2,\qquad h=A+B.
\]

After eliminating \(u=-Q_1\), its canonical residue sequence is

\[
\mathcal F=(Q_2,h,\bar g_1,g_2),\qquad
\bar g_1=G_u(-Q_1)=3Q_1^2-2h_2Q_1+h_4,
\]

where \(G=u^3+h_2u^2+h_4u+h_6\). These are ordinary homogeneous forms of
degrees \((2,3,4,4)\). Eliminating the first equation \(u+Q_1\) in the ordered
five-variable residue introduces **no additional factor and a positive
sign** in the coordinate order \((a,b,c,d,u)\).

## 2. Exact regularity on the actual contact

The degree-ten Macaulay map is

\[
\mathbf C[a,b,c,d]_8\oplus\mathbf C[a,b,c,d]_7
\oplus\mathbf C[a,b,c,d]_6^{\oplus2}
\longrightarrow \mathbf C[a,b,c,d]_{10}.
\]

Its matrix has 286 rows and 453 columns. The witness selects 286 columns.
Exact integer products, with common denominator scaling, establish on the
entire certified root ball

\[
\|I-BM\|_\infty<10^{-10}<1.
\]

The matrix variation uses the explicit Lipschitz bound \(160016/13\),
the radius \(10^{-35}\), and \(\|B\|_\infty\le10^3\). Every scalar norm is
\(|\Re z|+|\Im z|\), so all estimates are rational inequalities.

The minor is therefore invertible at the actual contact. All degree-ten
monomials lie in the ideal \((Q_2,h,\bar g_1,g_2)\), ruling out a nonzero
common zero. The sequence is a homogeneous complete intersection. Its
Hilbert coefficients are

\[
(1,4,9,15,19,19,15,9,4,1),
\]

so its length is 96 and its socle has degree nine.

## 3. The actual closed form

Let \(\tau\) be the degree-nine residue functional normalized by

\[
\tau\left(\det\frac{\partial(Q_2,h,\bar g_1,g_2)}
{\partial(a,b,c,d)}\right)=96.
\]

The 220 degree-nine monomials give its coordinates. The 316 columns formed
by degree-complementary multiples of the four generators give its homogeneous
linear constraints. The JSON contains every column. It also contains the
four-by-four polynomial Jacobian defining the normalization.

Define, with ambient coordinates held fixed during differentiation,

\[
\boxed{\eta_R=\tau(R\,d h).}
\]

Here \(R\) is substituted at \(u=-Q_1\) **after** coefficient
differentiation. In the intrinsic chart \(h=A+B\) has no \(u\)-dependence,
so its derivative has exactly the sixteen cubic-parameter components.
Their actual degree-nine numerator vectors are stored in the circuit.

This is a constructed form; no unknown closed form is supplied as an input.
The coefficients depend only on the contact parameters and \(\lambda\).
At fixed \(\lambda\), the contact component is a smooth curve. Every rational
one-form on its function field is closed, because its module of two-forms
over \(\mathbf Q(\lambda)\) is zero. Pullback to the moving-point incidence
preserves closedness. Including the pencil gives

\[
d(\eta_R\wedge d\lambda)=0.
\]

No arbitrary function of \(r,s\) has been multiplied into this form.

### Certified nonvanishing for the prescribed source

The normalized degree-nine solve uses 219 independent ideal columns plus
the Jacobian row. A second exact Neumann certificate bounds this 220-by-220
solve throughout the root ball. The contact tangent is normalized by
\(D(\rho_0)=1\) and bounded using the previously certified contact inverse.

The resulting exact rational enclosure is

\[
\left|\eta_R(D)-
(0.015943842399174287+0.0047796044116877505\,i)\right|_1
\le10^{-8}.
\]

The decimal center is displayed for readability; the file stores the exact
rational center and error bound. The verified real-part margin is positive.
This establishes nonvanishing on the **actual contact**, not merely at its
numerical approximation. The socle-vector error is at most \(10^{-11}\);
the tangent error is at most \(10^{-22}\).

## 4. Incidence Jacobians remove the coordinate derivatives

Let \(p\) denote contact parameters. For either the intrinsic 25-equation,
26-parameter system or the full 44-equation, 45-parameter system, let
\(K\) be the signed cofactor tangent. In the full system its convention is

\[
K_j=(-1)^{44+j}\det(H_p\text{ with column }j\text{ omitted}).
\]

Put \(q=Q_2(1,r,\alpha,s\alpha)\),
\(h=h(1,r,\alpha,s\alpha)\), and
\(\beta=-Q_1(1,r,\alpha,s\alpha)\). Subscripts below hold contact
parameters fixed. Define

\[
\begin{aligned}
u_0&=q_\alpha h_r-h_\alpha q_r,&
v_0&=q_\alpha h_s-h_\alpha q_s,\\
z_0&=q_rh_s-q_sh_r,&
y_0&=\beta_\alpha z_0+u_0\beta_s-v_0\beta_r.
\end{aligned}
\]

The full incidence determinant is

\[
J=(Kq)h_\alpha-q_\alpha(Kh).
\]

If \(\eta_R=f\omega\) in the cofactor frame, the coefficients needed by
the general-cubic current are exactly

\[
U=\frac{fu_0}{J},\quad V=\frac{fv_0}{J},\quad
Z=\frac{fz_0}{J},\quad Y=\frac{fy_0}{J}.
\]

Thus the current source is

\[
M_i=\frac{fP_i}{J},\qquad \deg_xP_1\le4,\quad\deg_xP_2\le3.
\]

All coefficients of the actual \(P_i\) are scalar DAG nodes in the JSON.
The independent `ContactIncidenceAlgebra.lean` module proves the Cramer and
annihilator identities used here. The existing general-cubic Lean module
proves its source reduction formulas.

### Exact removal of the apparent moving-point pole

Set \(F_0=G(\alpha^2,\beta)\), and let \(L_0\) be its derivative under
\(-v_0\partial_r+u_0\partial_s+z_0\partial_\alpha\), holding contact
parameters fixed. With \(v=-\alpha y_0\) and \(\dot a,\dot b\) evaluated at
\(x=\alpha^2\), the two undivided source remainders satisfy the universal
identities

\[
\begin{aligned}
N_1(\alpha^2)
&=-6F_0\{\beta\dot a+\dot b+(2a+3\beta)v\}
 -2\alpha(3a\beta+2b+3\beta^2)L_0,\\
N_2(\alpha^2)
&=-3F_0(\dot a+3v)-\alpha(a+3\beta)L_0.
\end{aligned}
\]

Both \(F_0\) and \(L_0\) belong to the incidence ideal. Indeed the norm
identity gives \(F_0=qg_2+h(A-B)\) modulo the coefficient equations, and
the displayed vector annihilates \(q,h\) identically. This proves the
divisibility used to define \(P_1,P_2\) without adding separate point or
motion assumptions.

## 5. A finite algebra for an exact global-residue computation

Work over \(K=\mathbf Q(\lambda,r,s)\). Retain the nineteen coefficients of
\(g_2\) as independent variables, giving 45 contact parameters and the moving
point coordinate \(\alpha\). Let \(H_1,\ldots,H_{44}\) be the full sextic
coefficient equations. Their exact node list is included in
`contact_forms_global_residue.json` and independently checked against the
equations used in the root certificate.

Let \(\delta\) be the determinant of the 220-by-220 socle-dual constraint
matrix, and \(D_{10}\) the selected regularity minor. Set

\[
S=\Delta J\delta D_{10}\alpha\beta G_w(\alpha^2,\beta),
\qquad
\mathcal A=K[p_0,\ldots,p_{44},\alpha,\zeta]/
(H_1,\ldots,H_{44},q,h,\zeta S-1).
\]

Every displayed open is certified nonempty at the actual contact. The
incidence Jacobian gives a dominant local component over the base.
On the indicated open all geometric points of a generic fiber have invertible
Jacobian; the resulting finite-type, zero-dimensional reduced algebra over
\(K\) is a nonzero finite étale algebra. **All** points of this localized
algebra are included. No irreducible factor or individual branch is chosen.

Writing the canonical density as \(f=f_{\rm num}/\delta\), put

\[
T_0=\Delta D_{10}\alpha\beta G_w(\alpha^2,\beta).
\]

The actual polynomial representing each current source coefficient in
\(\mathcal A\) is

\[
\zeta T_0 f_{\rm num}[x^j]P_i.
\]

This absorbs both the socle denominator and the incidence denominator:
\(\zeta T_0=1/(\delta J)\). The adjugate formula for \(f_{\rm num}\), both
determinant frames, all 46 coefficient equations, and the source and target
coefficient nodes are explicitly specified in the JSON.

If \(T_{ij}\) is the corresponding protected target coefficient, the nine
remaining identities are exactly

\[
\boxed{\operatorname{Tr}_{\mathcal A/K}
  \bigl(\zeta T_0 f_{\rm num}[x^j]P_i-T_{ij}\bigr)=0.}
\]

These are identities of rational functions in \(\lambda,r,s\). They are
not pointwise numerical comparisons.

Equivalently, the Jacobian of the 47-equation localized system is \(SJ\),
and each obligation is the global residue of the polynomial

\[
\frac S\delta f_{\rm num}[x^j]P_i-T_{ij}SJ.
\]

An exact quotient-basis/Groebner certificate and nine multiplication-matrix
traces could verify these without enumerating algebraic branches. The
arithmetic circuit avoids expanding its large determinants and adjugates.

## 6. What remains unresolved

No exact basis for the full finite algebra and no final trace value have
been computed. The canonical pullback's certified nonzero value does not
imply that its trace source equals the protected target. An additional
constant linear combination of canonical forms, or an exact differential
correction, may be required. Any proposed multiplier depending on \(r,s\)
would need its own closedness proof.

The sign convention here is the literal definition \(\eta_R=+\tau(Rdh)\)
and the established general-cubic current orientation. All trace operands
use that same convention. No unspecified scalar or geometric push-pull
inverse has been inserted to assert the source equality.
