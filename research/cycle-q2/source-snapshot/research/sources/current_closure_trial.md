# A source-closing solve against the compiled cycle-q2 current system

Date: 2026-11-04. **Verdict: CURRENT NOT CLOSED.** No original
`(D,N0,...,N5,Q)` and no Lean existence proof were obtained. This is a fresh
solve attempt using the compiled mathematical model, not a repetition of its
software build/calibration tests.

## 1. Unchanged target and provenance

The ordered physical coordinates are `(X0,X1,X2,Y0,Y1,Y2)`, with

```
F = sum_i (Xi^6+Yi^6)
    +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2,
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2, q=2.
```

The acceptance target remains nonzero homogeneous D, gcd_C(D,F)=1,
homogeneous Ni of degree degD+7, unrestricted Q, and the complete identity

```
A D^2-2D sum Ni Fi+F(D divN-N.gradD)=F^3 Q.
```

The current public instance and formal acceptance contract were read. The
actual computational input is the user's compiled 119,215-node 2+2+5 model:

```
proper_boundary_2_2_5_system.json.gz
SHA256 6f91f942aff1f8e136d878dc6f1f8b3c395d6dd1569b75a1aa0729611b34def1
```

This is not the separate 1,905,243-node full-source circuit. The supplied
model encodes rational functions over Q(P,U,Z), all three 9x9 connection
matrices, the source, frame changes, and reconstruction inputs. Its physical
source binding is an inherited input; it was not independently re-proved
here. The new exclusion below is an exact statement about this explicitly
serialized rational system, regardless of an outside interpretation of it.
No claimed older broad support obstruction is used as a mathematical premise.

## 2. The actual equation being solved

With columns, use the supplied matrices and source:

```
Nabla_i = partial_i + Gamma_i, i=P,U,Z,
sum_i Nabla_i J_i = C, J_i in C(P,U,Z)^9.
```

The first two rows are proper elliptic classes. The next two and last five
are the infinity and finite-branch residue channels. All nine source entries
are read from the input circuit. No boundary row or connecting matrix is
dropped. All ordinary and moving-frame derivatives are included.

A solution to this equation would still require the supplied fibre
homotopies/physical adapter, normal regular remainder, legal homogeneous
clearing, and literal original verification. No such solution was obtained.

## 3. Source-adapted construction rather than a guessed denominator sweep

Let A_i be the top-left 2x2 proper block of Gamma_i and c the first two
components of C. Define six rational scalar functions by

```
x^(P) = A_P^(-1)c,
x^(U) = A_U^(-1)c,
x^(Z) = A_Z^(-1)c.
```

Their existence over Q(P,U,Z) is witnessed by nonzero good reductions of
all three determinants at the exact rational parameter point (2,3,1),
recorded in results/INVERSE_SEED.json. This is a positive nonvanishing
witness, not a rank-transfer assumption.

These choices are motivated by the source: putting x^(i) in the proper
part of the i-current matches the algebraic connection contribution to c.
It generally leaves a derivative error. The inverses also introduce
source/connection-defined pole factors; no list of unrelated denominators
was swept.

The principal, larger test did NOT require the algebraic connection part
and ordinary derivative part to match separately. It allowed the full
coupled equation and all 27 current components. For each i=P,U,Z and
component a=0,...,8, it tested

    J_i,a = sum_(d=P,U,Z; k=0,1; m=0,1,2)
               x^(d)_k(P,U,Z) Z^m H_(i,a,d,k,m)(P,U).         (FAMILY)

There are **486 independent unknown coefficient functions**, each allowed
to be an arbitrary rational function in C(P,U), with no P,U degree or pole
bound. Their Z dependence is restricted to the explicitly displayed fixed
rational generators and powers 0,1,2. Consequently this is NOT every
rational current. In particular, freely chosen new Z-dependent pole
factors and higher Z-degree multipliers are outside this family.

No physical character averaging was imposed. The family is larger than
its source-character projection, so the rejection does not result from
silently deleting another symmetry sector.

## 4. Necessary differential system, with all mixed derivatives retained

For a scalar generator phi=x^(d)_k Z^m, the contribution of phi H e_a
in direction i is

    (partial_i phi e_a + phi Gamma_i e_a) H
         + phi e_a (partial_i H).

Here partial_Z H=0, but neither partial_P H nor partial_U H is frozen.
The complete nine equations are differentiated once in P and once in U.
Their unknowns are the six shared jets

    H, H_P, H_U, H_PP, H_PU, H_UU

for each of the 486 functions. H_PU is the SAME unknown in both derivative
orders. The source and all rational inverse coefficients are differentiated
before evaluating any parameters.

Evaluate these 27 equations at the seventy fixed integer Z values in
results/EXACT_SCOPE_WITNESS.json. Before specialization in P,U, this gives

    M(P,U) h = r(P,U),
    M of size 1890 x 2916 over Q(P,U).                         (JET)

Every rational solution of (FAMILY) supplies a solution of (JET) over
C(P,U). A successful pointwise jet fit would only be necessary; the mixed
and parameter derivative requirements cannot be discarded.

## 5. Characteristic-zero inconsistency for this family

The rational coefficient rank has a universal, elementary upper bound.
For each fixed component a and scalar generator phi:

* In direction P, the H_UU column is identically zero.
* In direction U, the H_PP column is identically zero.
* In direction Z, all three second-derivative columns are identically zero.
* The P-current H_PP column equals the U-current H_PU column.
* The P-current H_PU column equals the U-current H_UU column.

These identities follow directly from differentiating the divergence
expression above. They are not guessed from finite-field ranks. There are
9*6*3=162 component/generator pairs, hence 5*162=810 zero columns and
2*162=324 redundant duplicate columns. Therefore

    rank_(C(P,U)) M <= 2916-810-324 = 1782.                    (BOUND)

The actual coefficient arithmetic at P=2,U=3, modulo the good prime 1009,
finds rank 1782 and augmented rank 1783. More importantly, it produces an
explicit **1783 x 1783 augmented minor**, whose determinant is

    680 modulo 1009, nonzero.                                (WITNESS)

Every input constant denominator, circuit division, and selected proper
inverse is defined at each saved arithmetic point. Thus WITNESS proves
that the corresponding rational determinant is nonzero in characteristic
zero. Combining it with BOUND yields generic inconsistency over C(P,U).

**Theorem:** No rational coefficient functions H(P,U) in FAMILY close the
specified complete nine-class current equation.

This argument does not require a hypothetical H to be regular at the
sample parameter point: the nonzero determinant proves a generic rank
contradiction over the function field. It also does not infer a
characteristic-zero rank upper bound from a smaller observed modular rank.
The upper bound is the explicit zero/duplicate-column count.

The complete row and column sets, zero columns, duplicate pairs, parameter
values, and determinant value are in EXACT_SCOPE_WITNESS.json.

## 6. Independent verification actually executed

The primary Python producer uses ordinary first and second derivatives.
It differentiates the rational inverse by

    x_i = A^(-1)(c_i-A_i x),
    x_ij = A^(-1)(c_ij-A_ij x-A_i x_j-A_j x_i).

The separate C++17 consumer instead evaluates the serialized rational
circuit in the normalized Taylor algebra

    F_1009[eP,eU,eZ]/(total degree >=3).

It obtains the inverses by explicit 2x2 adjugates INSIDE that algebra. It
multiplies by each formal H-jet basis and differentiates the resulting
Taylor polynomials. It does not import the producer's differentiated
matrices or inverse-derivative formulas.

It reconstructed and compared **5,513,130 entries**: all 1890 rows and
2916 coefficient columns plus the source column. It then independently
computed the specified 1783-square determinant by row Gaussian elimination,
not the supplied sparse-column solver or its checkpoint data.

Executed output:

```
PASS independent matrix and determinant=680
```

INDEPENDENT_REPLAY.json records the actual run and entry count. This verifies
the modular positive determinant. The characteristic-zero implication is
the mathematical argument in section 5.

## 7. Other stages tried in the same turn

These stages are discovery history, not additional claims of closure.

1. An algebraic right inverse of [Gamma_P Gamma_U Gamma_Z] was built, with
   all eighteen kernel directions retained. A source-scaled affine
   polynomial correction fit failed (144 versus 145 at the good prime).
2. Those corrections were allowed arbitrary rational coefficients in P,U,
   with polynomial Z-degree two. The unprolonged coefficient/first-jet test
   was consistent: ranks 266 and 266. This was NOT accepted as a solution.
3. Enforcing the actual mixed derivatives made the same fit inconsistent:
   594 versus 595, with a universal 594 rank bound.
4. The separate algebraic-matching restriction was removed entirely. A
   full 27-component test with one inverse frame and powers through Z^6
   failed (1386 versus 1387, with a structural rank bound).
5. The principal test in sections 3-6 enlarged the rational generators to
   all three source-matched inverse frames, retaining the entire coupled
   nine-class equation. Its independent positive-minor verification is
   the final result reported here.

The initial successful frozen fit was not promoted into a rational
function or physical certificate. No unevaluated characteristic integral,
formal Taylor solution, or finite-field success was presented as closure.

## 8. Exact remaining gap and limitations

The unrestricted compiled equation still asks for arbitrary rational
J_P,J_U,J_Z in C(P,U,Z)^9. The family tested here has no solution; this
neither decides that unrestricted equation nor proves the original
certificate impossible. The supplied nine-class model itself does not
include every possible new fibre-pole divisor of the original problem.

No completed cubic current exists from this attempt to transport. Therefore
no physical denominator, graded Ni, quotient Q, or full original E=F^3Q
check was performed on a new complete tuple. No Lean compiler was available
or run. The private Math-project working tree was not accessed; the
conversation's mounted compiled archive was accessible and used.

The new verifier is useful as a rejection test for a precise source-adapted
family, not as evidence that a complete solution is close. The current is
still open. Nothing was posted, sent externally, or scheduled.

## Sources used this turn

* Supplied cycle_q2_compiled_build.zip, README, source DAG, block description,
  TARGET.json, and C++ checkpoint solver. Mathematical input kept unchanged.
* Supplied Round-5 summary explicitly records that no original tuple was
  produced; its large prior geometric claims were not used as premises.
* Public immutable instance:
  https://raw.githubusercontent.com/hodge-computer/sextics/main/data/cycle-q2/instance.rec
* Public acceptance contract:
  https://raw.githubusercontent.com/hodge-computer/sextics/main/formal/README.md
* Public discussion (context only, no claim of a newer accepted solution):
  https://github.com/hodge-computer/sextics/discussions/61
