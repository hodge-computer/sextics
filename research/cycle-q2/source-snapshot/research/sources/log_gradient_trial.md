# Cycle-q2: logarithmic-gradient completion trial

Date: 2026-11-04. **No original certificate was obtained.** This packet records one new explicit original-coordinate polynomial candidate, its complete-identity rejection, and an exact exclusion of a specified 20-dimensional constant-coefficient completion family. It is not a disproof of unrestricted existence, not a successful certificate, and not a Lean proof.

## 1. Protected original statement

Use ordered coordinates `z=(X0,X1,X2,Y0,Y1,Y2)` and exactly

```
F = sum_i (Xi^6+Yi^6)
    +(X0^3*X1*Y0*Y1+X1^3*X2*Y1*Y2+X2^3*X0*Y2*Y0)/2,
A = X0^2*X1^2*X2^3*Y0^2*Y1^2*Y2.
```

The requested tuple has homogeneous `D != 0`, `gcd_C(D,F)=1`, homogeneous `Ni` of degree `deg(D)+7`, and unrestricted polynomial `Q`, with

```
E(D,N) = A D^2 - 2D sum_i Ni Fi
         +F(D sum_i partial_i Ni - sum_i Ni partial_i D) = F^3 Q.
```

The complete identity is required. Cancellation of its first or second normal orders is not a certificate. No alternative F or A, deformation value, source averaging, or assumption Q=0 is used.

Primary public specifications inspected during this attempt:

- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
- https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/why.md
- https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md
- https://github.com/hodge-computer/sextics/discussions/61

The supplied Round-5 synthesis explicitly reports no completed original tuple. Its local file references do not provide an accessible completed solution. Earlier saved reports were read to identify failed constructions and avoid presenting them as new. Their global geometric exclusions are not premises of the new calculation below.

## 2. Source-normal construction

Define

```
H = Hess(F), h = det H, K = adj H,
M = (5/24) K grad A,
v0 = M/h,
B0 = h div M - M.grad h,
b = B0/h^2 = div(v0).
```

Here `B0` is a polynomial and `b` a homogeneous rational function. The name `B0` is unrelated to the earlier four-coordinate tangent field B.

Euler's formulas give

```
H z = 5 grad F,
z.grad A = 12 A,
v0(F) = (5/24)*(z.grad A)/5 = A/2.
```

For any rational vector field `w` homogeneous of degree one, put `v=v0+F w`. Direct product-rule differentiation gives the literal rational identity

```
A - 2v(F) + F div v = F*(b-w(F)) + F^2 div w.       (1)
```

Thus a completion with `w(F)=b` cancels the first two normal orders. It still requires `div w` to vanish modulo F; that last requirement cannot be omitted.

The former Hessian-gradient repair `w=(5/6)H^(-1)grad b` is included as one comparison direction below. Its prior verification is not rerun or claimed as a new result.

## 3. A new explicit homogeneous polynomial tuple

Choose the source-serving field

```
w_i = b/(6 Fi),
v_i = M_i/h + F*b/(6 Fi).
```

It satisfies `w(F)=b` exactly. This choice is the constant average of the six logarithmic-gradient fields for the factors Fi, because `H^(-1)grad Fi` is the i-th coordinate vector.

Write

```
P = product_i Fi,
P_i = product_{j != i} Fj,
D = h^2 P,
Ni = h P M_i + F B0 P_i/6.                         (2)
```

These are explicit polynomial circuits in the original six coordinates, with rational coefficients. No indefinite integral or unspecified denominator clearing appears. They have

```
deg h = 24, deg P = 30, deg M_i = 31,
deg B0 = 54, deg P_i = 25,
deg D = 78, deg Ni = 85 = deg D + 7.
```

The entire original expression for this tuple is

```
E(D,N) = F^2 D^2 div w
       = F^2*h/6 * [sum_i P*P_i*(h*partial_i B0 - 2B0*partial_i h)
                    -h*B0*sum_i P_i^2*F_ii].       (3)
```

Formula (3) is an identity of polynomials. The bracket is not silently discarded as a regular remainder. A genuine certificate would require another factor F. A possible quotient Q, if divisibility held, would have degree 150; Q is not preset to zero.

### Denominator legality over C

F is smooth projectively: at a nonzero common gradient zero choose a coordinate of maximal modulus m. Its diagonal derivative has modulus `6m^5`; all its coupling derivatives combined have modulus at most `2m^5` for an X coordinate and at most `m^5` for a Y coordinate. This is a contradiction. Consequently F is geometrically irreducible: distinct projective hypersurface components would intersect and make F singular.

Every Fi is a nonzero degree-five polynomial, so none is divisible by F. To check h, set `z=(1,1,1,a,a,a)` and `r(a)=2a^6+a^2+2`. Then

```
F(z)=3r(a)/2,
h(z)=125/2*(18a^6+90a^4-a^2+3)*(18a^6+360a^4-a^2-6)^2,
h(z) mod r = 429615000a^4 + 901358750a^2 + 647522500.
```

An exact Bezout identity with r and this remainder equals 1; both coefficients are saved in `LEGALITY_EXACT.json`. Therefore h is not divisible by F. It follows that D is nonzero and `gcd_C(D,F)=1`.

The sixth-root weights `(2,1,0,3,2,1)` give weight 5 for A and weight 3 for the volume, so the residue has weight 2. The Hessian transforms covariantly, h has weight 0, Fi has weight minus the coordinate weight, and P has weight 3. Thus D has weight 3 and Ni has weight `2+weight(z_i)`, as required by the rational field `Ni/D`. This construction does not replace the original character by the invariant character.

## 4. Full original-identity rejection of (2)

An independent standard-library program builds F and A directly from their exponent lists and differentiates all six components and the moving denominator. It evaluates the literal expression E(D,N) to second order in `z -> z+epsilon*e_Y2`.

First good reduction:

```
p=101, z=(1,1,1,23,23,23),
F(z)=0, F_Y2(z)=24, h(z)=45, D(z)=79,
(F_X0,F_X1,F_X2,F_Y0,F_Y1,F_Y2)=(54,54,54,24,24,24),
div w(z)=70,
E(z+epsilon e_Y2) = 64 epsilon^2 mod (101,epsilon^3).
```

A second independently evaluated reduction gives

```
p=107, z=(1,1,1,15,15,15),
F(z)=0, F_Y2(z)=98, h(z)=67, D(z)=12,
(F_X0,F_X1,F_X2,F_Y0,F_Y1,F_Y2)=(28,28,28,98,98,98),
div w(z)=49,
E(z+epsilon e_Y2) = 49 epsilon^2 mod (107,epsilon^3).
```

The program checks the literal expanded differential expression, not only the shortcut (3). It then cross-checks its quadratic coefficient against `D(z)^2 F_Y2(z)^2 div w(z)`.

### Why this rejects the rational polynomial tuple in characteristic zero

F and E have coefficients in `Z[1/6]`, and F is monic as a polynomial in Y2. If F^3 divided E over Q, monic division would give a quotient over `Z[1/6]` in the remaining variables as well. Divisibility would therefore persist modulo 101 and 107. At each displayed point F has a simple zero, so F^3 times any polynomial vanishes to order at least three. The nonzero quadratic coefficients contradict this.

Divisibility over C of polynomials defined over Q is the same test: the monic division remainder is defined over Q. Hence **no complex polynomial Q makes (2) a certificate**. This is a positive nonvanishing witness for one completely specified polynomial candidate, not an inference from a finite-field search failure.

No fully expanded generic list of all coefficients of the enormous degree-85 Ni was generated. Their exact polynomial circuits are (2), and the independent checker evaluates these circuits and their derivatives. No nonexistent Q was produced.

## 5. A larger targeted logarithmic completion was also tested

Let f range over the following twenty homogeneous factors/functions:

1. The six coordinates zi, of degree one.
2. The six partial derivatives Fi, of degree five.
3. For i cyclic in 0,1,2,
   `di=H_XiXi/(3Xi)=10Xi^3+X_(i+1)*Yi*Y_(i+1)`, degree three.
4. For i cyclic in 0,1,2,
   `ei=2H_XiYi=3Xi^2*X_(i+1)*Y_(i+1)+X_(i-1)^3*Y_(i-1)`, degree four.
5. h, degree 24.
6. b, homogeneous rational degree six.

For each define

```
w_f = b H^(-1) grad(log f).
```

The final field is interpreted after cancellation as `w_b=H^(-1)grad b`; there is no additional b-pole. Consider **constant** coefficients `c_f in C` and `w=sum_f c_f w_f`. The coefficient functions are not allowed to be arbitrary rational functions in this test.

For a homogeneous factor of degree delta,

```
w_f(F)=delta*b/5.
```

Since b is nonzero on F=0 (verified in the saved evaluations), (1) forces

```
sum_f delta_f*c_f=5,
sum_f c_f div(w_f)=0 on F=0.                       (4)
```

Every field and derivative in (4) is reconstructed from the literal F,A. A common legal homogeneous denominator for this family exists: one may take `h^4` times the product of the eighteen ordinary factors in items 1-4. This has degree 153, and the resulting numerator degree is 160. That observation does not rescue the incompatible family.

### Finite exact determinant witness

The twenty evaluation points stored in `LOG_CURRENT_DISCOVERY.json` are smooth F-points modulo 101, with nonzero `F_Y2`, h, and all ordinary factor denominators. Their twenty equations in (4), together with the degree equation, give a 21-by-20 system. The augmented 21-by-21 determinant is

```
66 modulo 101, nonzero.
```

The independent verifier reconstructs all **441 augmented entries** from explicit derivatives of the inverse Hessian, without importing the producer's Taylor arithmetic, and reproduces 66.

### Characteristic-zero lifting argument (essential)

For each saved finite-field point, fix its first five coordinates as integers. The polynomial in the sixth coordinate is monic of degree six over `Z[1/2]`; its indicated root is simple modulo 101. Hensel's lemma lifts it to a root in Q_101. Each lift is algebraic over Q, hence all twenty lifts lie in a common finite number field embedded in Q_101. The denominators remain units. The corresponding augmented determinant has reduction 66, so is nonzero in that number field and under any embedding into C.

A hypothetical complex constant tuple satisfying the rational identity (4) would solve all twenty-one equations at those algebraic points. This is impossible because the coefficient matrix has only twenty columns while its augmentation has a nonzero twenty-one-square determinant.

This proves an exclusion over C of the stated constant logarithmic family. It does **not** assume that a smaller observed modular coefficient rank is the characteristic-zero rank. Its universal rank upper bound is the number of columns, and the nonzero augmented minor is lifted at explicitly justified smooth points.

## 6. Exact scope and what remains missing

Established in this packet:

- the explicit degree-78 D and degree-85 Ni of (2), with legal denominator;
- the exact polynomial identity (3), including the complete residual;
- a literal original-identity second-jet witness proving this tuple fails;
- incompatibility of the twenty constant logarithmic-gradient completions, with an independent determinant witness and a characteristic-zero lifting proof.

Not established:

- any valid original D,Ni,Q;
- nonexistence for arbitrary numerator corrections using the same D;
- nonexistence for all Hessian-supported denominators;
- nonexistence for rationally varying coefficients c_f(z), other tangent fields, or the original unrestricted certificate;
- any successful completion of the auxiliary genus-two, proper K3, or three-base elliptic reductions;
- a closed Lean existence proof.

The unresolved step in direct original coordinates remains an actual rational tangential completion that cancels the last F^2 residue, or a different complete construction. This report does not assert such a completion exists in a selected remaining ansatz or that the original certificate is close.

## 7. Execution and reproducibility

Successful executions:

```
python search_log_currents.py
python independent_verify.py
python verify_legality.py
```

`search_log_currents.py` uses SymPy 1.14.0 to initialize exact polynomials and modular Taylor arithmetic for discovery. `independent_verify.py` uses only the Python standard library and independently reconstructs the entire matrix, both original-identity jets, and their derivative cross-checks. `verify_legality.py` uses exact SymPy polynomial arithmetic and checks the saved Bezout identity. Read `SEARCH.log`, `INDEPENDENT.log`, `CHECKS.json`, and `LEGALITY_EXACT.json` for actual outputs.

A different direct-fraction checker over Q(a) was started but did not finish within its 200-second execution limit. It is preserved under `exploratory/`; **no result from that unfinished run is used**. The successful rejection proof is the monic-polynomial good-reduction argument in Section 4, not an invented completed Q(a) calculation.

An old Hessian helper was inspected for comparison and is retained under `prior_code/`. It was not executed in this attempt or counted among new verification results. No Lean executable, Sage, Singular, Macaulay2, or FLINT was used. No outside messages, published repository changes, or new scheduled tasks were made.
