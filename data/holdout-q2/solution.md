# A finite-algebra certificate for holdout-q2

The entry point is `Submission.certificate`, proving the protected statement
`HodgeComputer.HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A`.
The construction uses strict certificates,
so the quotient in the cleared divisibility identity is zero.

Write the protected variables as \((x,a,c,y,b,d)\). Then
\[
 F=x^6+a^6+c^6+y^6+b^6+d^6+x^3ayb+a^3cbd,
 \qquad A=x^3a^2c^2y^3b^2,\qquad q=2.
\]

## Two endpoint targets

Choose \(k\in\mathbb C\) with \(k^2+k+1=0\), and put
\(P=x^3a^2y^3b^2\) and \(\Delta_k=c^2-k^2d^2\). We construct a certificate
for each of \(P\Delta_k\) and \(P\Delta_{k^2}\). The identity
\[
 Pc^2=\frac{2+k}{3}P(c^2-k^2d^2)
       +\frac{2+k^2}{3}P(c^2-kd^2)
\]
then gives the prescribed target. The proofs use complex coefficients directly;
no rational descent is needed by the acceptance contract.

The scaled endpoint reflections motivate this decomposition, but the Lean proof
does not assume a geometric reflection theorem or a support-to-certificate theorem.
It constructs the required algebraic witnesses.

## Cubic reduction

Let
\[
 \alpha=y/x,\quad\beta=b/a,\qquad
 U=x^2,\quad V=a^2,\quad S=c^2+k^2d^2,\quad T=kcd.
\]
Use four independent coefficient parameters \(\mathsf a,\mathsf b,\mathsf c,\mathsf d\)
and the cubic
\[
 G=S^3-3ST^2+\mathsf aU^3+\mathsf bV^3
          +\mathsf cU^2V+\mathsf dV^2T.
\]
The coefficient substitution is
\[
 (\mathsf a,\mathsf b,\mathsf c,\mathsf d)
 =(1+\alpha^6,1+\beta^6,\alpha\beta,\beta k^2).
\]
It gives exactly \(F\). At \((\alpha,\beta)=(k^2,k)\), these four coefficients
are \((2,2,1,1)\). This is the common good fiber for the construction.

## Constructing lines and serving every quadratic source

Work in the localization of \(\mathbb Q[\mathsf a,\mathsf b,\mathsf c,\mathsf d]\)
at the polynomials nonzero at \((2,2,1,1)\). A line has equations
\(S=eU+fV\), \(T=gU+hV\). With \(f=re\), elimination gives an explicit
degree-27 polynomial in \(r\), whose leading coefficient is
\(729\mathsf a^{11}\). The proof normalizes this polynomial to be monic and
forms its finite free `AdjoinRoot` algebra.

The line coordinates are rational expressions in the root. Their denominator
units are proved by exact polynomial Bezout identities on the good fiber and
specialization of multiplication matrices. Universal polynomial identities
then prove all four line equations over the unspecialized coefficient ring.
No irreducibility or squarefreeness assumption is made about the eliminant.

In local coordinates \(\ell=S-eU-fV\), \(m=T-gU-hV\), write
\(G=\ell Q_1+mQ_2\). The elementary field
\[
 \frac1\ell\left((Q_2)_V\partial_U-(Q_2)_U\partial_V\right)
\]
has zero divergence and sends \(G\) to
\((Q_1)_U(Q_2)_V-(Q_1)_V(Q_2)_U\).
The local derivatives hold \(\ell,m\) fixed. `LineContact.lean` proves the
transported polynomial source, tangency, and divergence identities.

The four gradient sources and six coefficient functionals of the line source
form an invertible ten-by-ten matrix on the good fiber, in the quadratic basis
\[
 U^2,UV,US,UT,V^2,VS,VT,S^2,ST,T^2.
\]
The exact rational matrix inverse and the reductions giving its entries are
checked by Lean. Specialization proves that the generic determinant is a unit.
Thus the same finite line algebra serves every quadratic source.

The regular representation, determinant, and adjugate clear the line pole:
\[
 D_0=\det(SI-UM_e-VM_f).
\]
For any quadratic source \(h\), the construction gives numerators \(P_i\)
of degree 27 such that
\[
 \sum_iP_iG_i=D_0h,\qquad
 D_0\sum_i\partial_iP_i-\sum_iP_i\partial_iD_0=0.
\]
The proof reuses the accepted determinant/adjugate calculus rather than expanding
this degree-27 determinant.

## A small exact quintic reduction

The preliminary 56-by-56 Jacobian inversion is replaced by four explicit cubic
polynomials in `QuinticReduction.lean`. Put
\[
 R=27\mathsf a^2\mathsf b+4\mathsf c^3,
 \qquad H=R(R^4-2916\mathsf a^8\mathsf d^6).
\]
The displayed numerators \(M_i\) satisfy
\(\sum_iM_iG_i=HU^3V^2\), proved by polynomial arithmetic. At the good fiber,
\(H=515198970880\ne0\), so \(N_i=M_i/H\) is defined in the coefficient
localization. Let \(h=\operatorname{div}N\), which is quadratic.

Apply the quadratic solver to \(h\), and write \(W_1=P/D_0\). With the four-variable
Euler field \(E\), define
\[
 W_2=\frac{N+GW_1}{2}-\frac{hE}{6}.
\]
The Euler identities \(E(G)=3G\), \(E(h)=2h\), and \(\operatorname{div}E=4\)
give
\[
 2W_2(G)=U^3V^2,\qquad\operatorname{div}W_2=0.
\]
The actual cleared representation has denominator \(6D_0\) and numerators
\(3(D_0N_i+GP_i)-D_0hX_i\), of degree 30. Multiplication by the passive scalar
\(\alpha^3\beta^2/2\) gives the required downstairs source.

## Lifting and homogeneous clearing

For normalized \(T=kcd\), the four horizontal fields are
\[
\begin{aligned}
 C_U&=\frac{\Delta_k}{x}\partial_x+
             \frac{\Delta_k y}{x^2}\partial_y,&
 C_V&=\frac{\Delta_k}{a}\partial_a+
             \frac{\Delta_k b}{a^2}\partial_b,\\
 C_S&=c\partial_c-d\partial_d,&
 C_T&=-2kd\partial_c+2k^2c\partial_d.
\end{aligned}
\]
They have zero divergence, annihilate both passive ratios, and act on
\((U,V,S,T)\) as \(2\Delta_k\) times the respective coordinate derivatives.
The chain-rule proofs use derivations on the actual fraction field of the six-variable
polynomial ring. Derivatives of the passive ratios are included.

The coefficient map between the two localizations is constructed, with its
specialization law proved. A simultaneous homogeneous clearing of the finitely
many coefficients produces polynomial representatives \(Q,P_i\). If the extra
clearing exponent is \(n\), their degrees are \(2(n+27)\) and \(2(n+30)\).
The additional coordinate denominator is \(x^2a^2\). After applying the displayed
horizontal fields, the final numerator degrees exceed the denominator degree by
seven, as required for \(q=2\). Common-clearing-factor derivative terms cancel
in the divergence identity.

## Denominator legality and final combination

The exact inverse of \((e+f)^3+5\) in the good-fiber line algebra gives an
explicit matrix Bezout identity. It proves that
\[
 \det(c^2I-M_{e+f})\quad\hbox{and}\quad c^6+5
\]
are relatively prime over \(\mathbb C\).
On the specialization
\((x,a,y,b,d)=(1,1,k^2,k,0)\), the sextic is exactly \(c^6+5\), and the
cleared denominator is a nonzero scalar times that norm polynomial. The sextic
is monic in \(c\), so the specialization theorem lifts relative primality to
the full polynomial ring. It also proves denominator nonvanishing.

Finally, the two endpoint certificates are combined over a product denominator.
Relative primality, homogeneity, and the full cleared identity are preserved.
`Solution.lean` binds the resulting theorem to the generated protected target.

## Attribution

The endpoint-reflection observation and preliminary exact construction were
developed with ChatGPT assistance for Jason Long. The cubic-surface and contact
strategy was
motivated by the hodge.computer documentation and its authors' work. The proof
adapts substantial infrastructure from the accepted `quadric-contact-broken`
submission: coefficient localization, finite-free specialization, matrix
contact calculus, homogeneous clearing, and matrix Bezout identities. The
accepted `one-reflection` example also informed the approach. The
new cubic line data, arbitrary quadratic solver, explicit quintic reduction,
pole-two correction, and endpoint transfer are supplied here. OpenAI Codex
assisted with the formalization, exact calculations, and checking. The contract
and differential framework are due to the repository contributors; the general
formal algebra comes from Lean and mathlib and their contributors.
