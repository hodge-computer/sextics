# Exact symmetric weighted norm-contact circuit

This packet constructs the **actual equations for the protected
`symmetric-sextic-residual` target**. It does not assert that they have a suitable
solution, a finite or étale component, or the closed forms and trace identity
needed for a certificate.

## Files and reproduction

- `symmetric_norm_contact_inputs.json`: protected F, A, pole parameter, source
  hashes, and the exact cubic expression/coefficient snapshot from
  `general_cubic_current.py`.
- `symmetric_norm_contact_circuit.py`: builder, symbolic audit, and exact
  rational evaluator.
- `symmetric_norm_contact_circuit.json`: the portable arithmetic circuit.
- `symmetric_norm_contact_audit.json`: actual verification receipt.
- This README.

Run with Python and SymPy:

```sh
python symmetric_norm_contact_circuit.py
```

Only the input JSON and script are needed to regenerate the other files.
There are no dependencies on the repository checkout or the older public
branch-jet artifacts. The script also looks for an optional sibling
`python_deps` directory, matching the existing proof-attempt environment.

The function `evaluate_circuit(packet, assignments)` uses only Python's
standard library and exact `Fraction` arithmetic. Importing that function
does not import SymPy. The assignments must supply `lam,r,s,alpha` and the
26 parameters listed in `parameter_order`. The arithmetic audit uses four
arbitrary assignments; **none is a contact solution**.

## 1. The exact weighted equation and its normalization

Use the reflection-pencil substitution

\[
X=(a+z,a-z,b),\qquad Y=(c+\lambda z,c-\lambda z,d),\qquad u=z^2.
\]

The literal protected F becomes

\[
\begin{aligned}
G_{\rm raw}={}&2a^6+b^6+2c^6+d^6
 +30a^4u+30a^2u^2+2u^3\\
&+30\lambda^2c^4u+30\lambda^4c^2u^2+2\lambda^6u^3\\
&+\frac57(a^2+2ab-u)^2(c^2+2cd-\lambda^2u)\\
&+\frac{10}{7}(a^2+2ab-u)(c^2+2cd-\lambda^2u)^2.
\end{aligned}
\]

Its pure `u^3` coefficient is

\[
\ell=\frac{14\lambda^6-10\lambda^4-5\lambda^2+14}{7}.
\]

**The norm chart uses `G=G_raw/ell` on `ell != 0`.** This is the monic cubic
normalization used by `general_cubic_current.py`; it is not an unrecorded
change to the protected polynomial or its source. The audit separately proves
the raw identity with F and the monic identity with all nine stored cubic
coefficients.

On `a=1,b=r,c=t,d=s*t`, with `x=t^2`,

\[
G(1,r,t,st,w)=w^3+\sum_{i=0}^2\sum_{j=0}^{3-i}p_{ij}(r,s,\lambda)w^ix^j.
\]

The nine functions `p_ij` agree symbolically with the existing current
calculation. The pole parameter of the original problem remains 1.

The original source also has its exact checked binding

\[
A_{\rm protected}=(a^2-z^2)b(c^2-\lambda^2z^2)d.
\]

The contact cubics called A and B below are different objects from this
protected source. Their names follow the public norm-contact chart.

## 2. The twenty-six chart parameters

The ambient variables have weights `(1,1,1,1,2)` and the involution negates
`c,d` while fixing `a,b,u`.

Define

\[
Q_1=\rho_0a^2+\rho_1b^2+\rho_2c^2+\rho_3cd+\rho_4d^2,
\]

\[
Q_2=ab+\mu_0a^2+\mu_1b^2+\mu_2c^2+\mu_3cd+\mu_4d^2.
\]

Thus `f1=u+Q1`, `f2=Q2`. The parameter `lam` is the reflection-pencil
parameter and is **not** one of the `mu` chart coefficients.

The even cubic A uses the eight monomials

```text
a^3, b^3, a*c^2, a*c*d, a*d^2, b*c^2, b*c*d, b*d^2
```

with coefficients `A0,...,A7`. The odd cubic B uses

```text
a^2*c, a^2*d, b^2*c, b^2*d, c^3, c^2*d, c*d^2, d^3
```

with coefficients `B0,...,B7`. These are precisely the cubics of their
respective parity whose monomials are not divisible by `ab`.

The parameter order is

```text
rho0,...,rho4, mu0,...,mu4, A0,...,A7, B0,...,B7.
```

## 3. The actual twenty-five norm equations

Form the invariant ordinary sextic

\[
R=G(a,b,c,d,-Q_1)-A^2+B^2.
\]

The full general cubic in u is substituted here. The cyclic simplification
`H-Q1^3` from the public packet is **not** used for this target.

Let `m_1,...,m_19` be the lexicographically ordered even quartic monomials.
The pivot sextics are `ab*m_j`; the other twenty-five invariant sextic
monomials are the free basis. All three exponent lists are explicit in JSON.
The multiplication matrix is

\[
M_{ij}=[ab\,m_i](Q_2m_j),
\]

and `M_free` is the same coefficient map on the free sextics. Set

\[
v=M^{-1}R_{\rm pivot},\qquad
E=R_{\rm free}-M_{\rm free}v.
\]

The twenty-five entries of E are the norm equations. This is an explicit
rational arithmetic circuit: its JSON contains every coefficient node, both
matrices, the complete right-hand side, and the nineteen-by-nineteen solve
gate. No large expanded rational equations are substituted for this circuit.

The determinant is proved symbolically to be

\[
\Delta=(1-\mu_0\mu_1)(1-3\mu_0\mu_1)(1-2\mu_0\mu_1)^3.
\]

The audit verifies the block lower triangular decomposition: one block of
size five, three blocks of size three, and five scalar blocks. The cubic
normal-form determinant is `1-mu0*mu1`, already inverted by `Delta != 0`.

On this precise open, the construction gives the identity

\[
R=Q_2g_2+\sum_iE_im_i^{\rm free},\qquad
g_2=\sum_jv_jm_j.
\]

Consequently vanishing of E is equivalent to the required divisibility by
Q2 in this chart. This is a coefficient identity, not a dimension argument.

## 4. Reconstructing the full norm presentation

Write

\[
G=u^3+h_2u^2+h_4u+h_6.
\]

The circuit also supplies the actual even weighted quartic

\[
g_1=u^2+(h_2-Q_1)u+(Q_1^2-h_2Q_1+h_4).
\]

The universal polynomial division identity gives

\[
G=(u+Q_1)g_1+Q_2g_2+A^2-B^2+\sum_iE_im_i^{\rm free}.
\]

Thus the inputs needed for a later canonical residue calculation
`(f1,f2,A+B,g1,g2)` are explicitly reconstructed. No regular-sequence or
smoothness assertion for those inputs is made here.

## 5. The twenty-seven-equation moving-point incidence

Work over `Q(lam,r,s)`. Adjoin `alpha` as the twenty-seventh unknown and set

\[
(a,b,c,d)=(1,r,\alpha,s\alpha),\qquad
\beta=-Q_1(1,r,\alpha,s\alpha).
\]

The remaining two equations are

\[
q_*=Q_2(1,r,\alpha,s\alpha)=0,
\qquad h_*=(A+B)(1,r,\alpha,s\alpha)=0.
\]

In particular,

\[
q_*=r+\mu_0+\mu_1r^2+
(\mu_2+\mu_3s+\mu_4s^2)\alpha^2,
\]

\[
\beta=-\rho_0-\rho_1r^2-
(\rho_2+\rho_3s+\rho_4s^2)\alpha^2.
\]

There is no extra beta variable or extra `f1=0` equation: that equation is
already satisfied by beta's definition.

The circuit records the **unconditional equation-combination identity**

\[
\begin{aligned}
G(1,r,\alpha,s\alpha,\beta)
={}&\sum_iE_im_i^{\rm free}(1,r,\alpha,s\alpha)\\
&+q_*g_2(1,r,\alpha,s\alpha)\\
&+h_*(A-B)(1,r,\alpha,s\alpha).
\end{aligned}
\]

Therefore every solution of the twenty-seven equations on the chart is an
actual point of the exact monic cubic used by the current construction,
with `w=beta` and `x=alpha^2`. No target-membership hypothesis is silently
added to the moving-point data.

## 6. What was verified, and what remains unknown

The audit proves by symbolic polynomial calculations:

- the literal protected F and A reflection-pencil bindings;
- the arithmetic circuit's weighted G binding;
- the general-cubic chart and all nine normalized coefficients;
- every emitted R coefficient, before applying the inverse matrix;
- every entry of both emitted reduction matrices;
- the two reduction determinants;
- the universal quartic multiplication coefficient map;
- the universal u-division formula and the actual emitted g1 polynomial.

Four additional exact rational controls compare every coefficient of the
unreduced R, verify the nineteen pivot cancellations and all twenty-five
remainder coefficients, and verify the moving-point equation-combination
identity. They include nonzero `mu0*mu1`; the check does not rely only on the
identity-matrix seed. None satisfies the norm equations, and none is
represented as a contact witness.

The counts `25 equations / 26 parameters` and `27 equations / 27 unknowns`
are only counts. They prove neither nonemptiness nor the dimension, dominance,
finiteness, or étaleness of a useful component. This packet does not construct
a closed residue form or evaluate the final field trace. Those and the
actual source identity remain the next substantive obligations.

## Provenance

The chart and monomial layout are adapted from the public PR219 discussion
packet's `algebra/intrinsic_norm_incidence.py` and
`algebra/generate_norm_system_circuit.py`. Their cyclic example has been
replaced here by the exact protected symmetric quotient. The input snapshot
records the protected instance commit and source hashes so the binding is
reviewable without another repository download.
