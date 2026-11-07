# Actual common normalizer center and a current across its blowup chart

This is a new source-serving partial construction for the actual small R2
source. It is not a global primitive or protected certificate. All actual
lambda dependence is retained; the witness below additionally uses lambda=1.

## Few-polynomial critical model

Set X=P^6/U²,Y=U²,T=Z^6 and

`kappa=14XYT-5(XY+XT+YT)+2(X+Y+T)-1`, so K=Y*kappa.

The squares of the actual coefficient-torus invariants, up to constant and
lambda factors, are

`u²=XY/[64(X+1)^4(Y+1)^2]`,
`v²=YT/[64(Y+1)^4(T+1)^2]`,
`w²=lambda^6*XT/[64(X+1)^2(T+1)^4]`.

Their logarithmic Jacobian has determinant
`-2*kappa/[(X+1)(Y+1)(T+1)]`. A polynomial kernel field on kappa=0 is

`Vt=(X(X+1)(1-Y)(1-T), -Y(Y+1)(1-3X)(1-T), T(T+1)(1-3X)(1-3Y))`.

Its actual physical pullback is

`Vcrit=(P(1-T)(2X+XY-Y)/3, -U(Y+1)(1-3X)(1-T)/2, Z(T+1)(1-3X)(1-3Y)/6)`.

Use **C=Vcrit(K)** as the second center equation. It equals
`Y*Vt(kappa)` modulo K. The root factors P^6=XY,U²=Y,Z^6=T are retained;
no trace to X,Y,T is used.

On `d=14XY-5X-5Y+2!=0`, eliminate
`T=(5XY-2X-2Y+1)/d`. Then

`Vt(kappa)=2(3X-1)(3Y-1)*f(X,Y)/d²`, where

```
f=665X³Y³-753X³Y²+276X³Y-35X³
 -747X²Y³+898X²Y²-344X²Y+46X²
 +282XY³-361XY²+147XY-21X
 -35Y³+47Y²-20Y+3.
```

Thus on the stated nondegenerate torus chart the actual center is the retained
root cover of this explicit curve, not an assumed rational coefficient cover.

## Exact binding to S0,S1 and the source

For q=source,lambda,0,1 put Wq=K*Vq, and define
`alpha_q=Wq_Z/Vcrit_Z`, `Qq=(Wq-alpha_q*Vcrit)/K`.

The checker verifies that every entry of alpha_q,Qq is regular along K=0 and
emits the exact rational functions. Consequently

`Sj=alpha_j*C+K*Qj(K)`.

On the chart where Vcrit_Z and alpha0 are units, this is an explicit localized
ideal certificate

`(K,S0,S1)=(K,C)`.

It is a saturation statement on the listed chart, not a classification of
excluded rank-degenerate components. It retains lambda throughout.

Set N=K^4*R2. The exact actual source identity is

`N=Fcrit*C²+K*Gcrit`,

`Fcrit=-3*k1*alpha_source*alpha_lambda`.

Every coefficient is emitted and K-regular. No leading term was fitted.
The checker derives this from the full actual R1,R2 definitions and verifies
it as an exact rational identity. At the center,

`Gcrit = k1*alpha_source*alpha_lambda*Vcrit(C)` modulo (K,C).

In particular the fourth-pole coefficient vanishes quadratically, but the
source need not vanish to second order in the whole center ideal.

## Actual chart witness and source coefficient

At prime101 and `(P,U,Z,lambda)=(4,49,8,1)`,

`K=C=S0=S1=0`, `Jc=det d(K,C,Z)/d(P,U,Z)=26`,
`Delta=52`, `Vcrit(C)=19`,
`alpha_source=39,alpha_lambda=69,alpha0=21,alpha1=14`,
`N=0,Gcrit=6`.

The original six-by-six lift matrix has rank5; its first five rows/columns
have determinant1. Thus this is a smooth center chart with a nonzero next
kernel derivative, not a claim of corank2. The exceptional double-pole
coefficient below is Gcrit/Jc=8, nonzero. These are chart/nonvanishing
witnesses; the generic ideal and source identities have separate exact checks.

## Two actual currents remove the entire exceptional pole

Choose center coordinates (K,C,t=Z), with Jc as above. The inverse fields are

`D_K=(C_U,-C_P,0)/Jc`, `D_C=(-K_U,K_P,0)/Jc`.

They satisfy D_K(K)=1,D_K(C)=0,D_C(K)=0,D_C(C)=1. Blow up the center by
`C=K*v`. Then

`Lambda=dP dU dZ=(K/Jc)*dK dv dt`,

`partial_K|v,t = D_K+v*D_C`, `partial_v=K*D_C`.

Put B=Gcrit/Jc,H=Fcrit/Jc,e0=(1,0), and let nabla_K,nabla_C denote actual
row covariant derivatives in the original center coordinates. The transformed
source is `(B+K*v²*H)/K²*e0`. Two explicit row currents are

`h_K=-(B+K*v²*H)/K*e0`,

`h_v=[v*nabla_K(B e0)+v²*nabla_C(B e0)/2+v³*H e0/3]/K`.

Every coefficient is an actual rational function; no current equation remains
to define these rows. Their exact remaining source is

```
Rnew=-v*nabla_C*nabla_K(B e0)
 +v²*[nabla_K(H e0)-nabla_C²(B e0)/2]
 +(2/3)*v³*nabla_C(H e0).
```

It is regular along K=0 for finite v on the displayed Jc*Delta unit chart.
Thus both the exceptional double pole and the entire exceptional logarithmic
pole are served. The universal identity holds for arbitrary connection
matrices; no hidden flatness assumption or frozen amplitude is used. The
seven-check symbolic verifier proves it independently of the actual source
binding. The original-coordinate inverse Piola currents are

`J_K,old=-R2*(K D_K+C D_C)*e0`,

`J_v,old=(Jc/K)*D_C*[v*nabla_K(B e0)+v²*nabla_C(B e0)/2+v³*H e0/3]`.

The retained old-coordinate source is `(Jc/K)*Rnew`. Its apparent old K poles
at fixed nonzero C correspond to v=infinity, outside this blowup chart; they
are not silently declared removed globally. The other blowup chart, remaining
coordinate/Jc/Delta support, overlap currents and the final source closure are
still required. This is concrete input for Pro20's Cech construction.

## Literal corrections for both compact rows

Write A=Ae,Bw=Be,Delta=4A³+27Bw² and beta=(omega0,24x omega0)^t. At fixed
Weierstrass x, the exact correction vector is

`xi_D=[D(A)*R_A+D(Bw)*R_B]/y`,

where the two-entry vectors have components

`R_A0=-(2A²x+6A Bw+9Bw x²)/(2Delta)`,
`R_B0=(4A²+6A x²-9Bw x)/(2Delta)`,
`R_AH=-12(Ax-3Bw)(2Ax+3Bw)/Delta`,
`R_BH=-12(2A²x+6A Bw+9Bw x²)/Delta`.

Direct elliptic polynomial reduction verifies
`partial_D beta=M_D beta+d_f xi_D` for arbitrary actual coefficient motions.
For Lambda'=dK dv dt, the literal residue-family current is

`Pi=sum_{i=K,v}(i_partial_i Lambda') wedge (h_i beta)
    +Lambda'*(h_K xi_partialK+h_v xi_partialv)`.

Here xi_partialK=xi_DK+v*xi_DC and xi_partialv=K*xi_DC. Its derivative is
exactly Lambda' times the served compact row. All x,y differentials and the
point-map parameter motion are absolute. The existing normal-tube construction
then supplies the allowed regular normal quotient; it does not kill Rnew.

Run `critical_center_blowup.py` and `verify_blowup_current_universal.py`.
No full rational primitive, protected F³Q identity or project acceptance is
claimed.
