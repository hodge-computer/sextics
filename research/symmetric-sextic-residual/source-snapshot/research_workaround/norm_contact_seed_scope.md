# Exact symmetric norm-contact seed check

These two scripts are self-contained apart from Python 3 and NumPy. They read
no downloaded witness matrices and use exact integer arithmetic in
`F5[h]/(h²-2)`. Reproduce from this directory with:

```bash
python norm_contact_exact_seed.py
python norm_contact_seed_tangent.py
```

Both scripts regenerate their JSON receipts. The second reconstructs its seed
matrix directly from the first script's code, rather than trusting the saved
JSON. Lean files remain unchanged.

## Decomposition

At the actual symmetric pencil's `lambda=1` reduction modulo five,

\[
G_0=2a^6+b^6+2c^6+d^6+4u^3.
\]

The following identity is verified exactly in `F25`:

\[
\begin{aligned}
f_1&=u+3a^2,& f_2&=ab-hcd,\\
g_1&=4(u^2-3a^2u+9a^4),&
g_2&=-4\bigl((ab)^2+h\,abcd+h^2(cd)^2\bigr),\\
A&=2a^3+b^3,&B&=2hc^3+2d^3,\\
G_0&=f_1g_1+f_2g_2+A^2-B^2.
\end{aligned}
\]

The proposed sign of `g2` is correct.

## Exact ranks and bounded family

The Jacobian of the full norm map has shape `70 x 90` and rank **68**.
The intrinsic norm equations have Jacobian shape `25 x 26` and rank **23**.
The intrinsic matrix is independently constructed by reducing

`-G_u(-Q1) deltaQ1 - g2 deltaQ2 - 2A deltaA + 2B deltaB`

modulo `Q2`. Its rank agrees with `rank(full)=45+rank(intrinsic)`.

The structured family

\[
f_1=u+ka^2,\quad f_2=ab-\chi cd,\quad
A=pa^3+b^3,\quad B=qc^3+2d^3
\]

is checked at all 120 `F25` points satisfying
`p²+4k³=2`, `q²=3`, `p chi³=2q`, and `p!=0`.
There are 108 points of intrinsic rank 23 and 12 of rank 21. None has rank 25.
This finite enumeration is not a statement about every point over an algebraic
closure or about other contact constructions.

## Quadratic obstruction and the actual target lift

The seed's intrinsic kernel has dimension three, with free coordinate indices
`[5,10,13]`. Its left cokernel has dimension two. The two quadratic obstruction
forms on the kernel are **identically zero**. The calculation includes the
first quotient correction and is independently checked in the original
quadratic `90 -> 70` norm map.

An exact Fermat presentation lift modulo 25 uses

`k=3`, `i=7`, `p=12`, `q=7h`, `chi=h`,

where `i²=-1`, `p²=2-4k³`, `q=ih`, and `p chi³=qi` modulo 25. The full
decomposition, not just these scalar conditions, is checked modulo 25.

For the actual symmetric sextic at `lambda=1`,

\[
\frac{G_{\rm actual}-G_0}{5}\bmod 5
=u(a^4+c^4)+u^2(a^2+c^2)+3Q_X^2Q_Y+Q_XQ_Y^2.
\]

This is independently reconstructed from the actual polynomial modulo 25.
After substituting `u=-3a²`, reducing modulo `ab-hcd`, and projecting to the
saved cokernel basis, the obstruction is **`(1,1)`**.

Consequently this fixed seed has neither an ordinary mod-25 lift to the actual
target nor the proposed correction with `pi²=5`: at the latter order the
quadratic obstruction remains zero while the target obstruction is nonzero.
This does **not** exclude higher ramification, another seed, or another
norm-contact component. No higher jets were computed. No trace or certificate
is asserted.
