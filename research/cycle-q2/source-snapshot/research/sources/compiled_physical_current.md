# Cycle-q2 — continuation of the compiled physical current

**Date: November 4, 2026. Status: NOT A COMPLETED CERTIFICATE.**

This work continues the recovered, source-bound physical Hermite-current circuit. It does not introduce another Hessian or logarithmic-gradient guess. It produces explicit division-free homogeneous polynomial circuits, an independently checked exact compiler translation, a compiled C++ checker of the original identity, and an unrestricted rational tangent-correction interface. The saved current still has a nonzero second-normal remainder. No rational correction closing it, original certificate, or Lean existence proof was obtained.

## 1. Exact target and provenance

The coordinate order is `(X0,X1,X2,Y0,Y1,Y2)` and the target is

```
F = sum_i(Xi^6+Yi^6)
    +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2,
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2,  q=2.
```

A completed certificate must have nonzero homogeneous D, gcd_C(D,F)=1, homogeneous Ni of degree deg(D)+7, and an unrestricted polynomial Q with

```
E(D,N) = A D^2-2D sum_i Ni Fi
         +F(D sum_i partial_i Ni-sum_i Ni partial_i D) = F^3 Q.
```

The public acceptance contract was retrieved through the GitHub connector. It imposes no denominator-degree bound; a zero numerator component is allowed. This packet's circuit format is a working polynomial representation, **not the project's accepted witness/export schema and not a protected Lean proof**.

Three actual Library archives were materialized. The selected input is

```
cycle_q2_continuation_20261029/
 inputs/04-cycle-q2-pro20-constructions/k3-transverse/
 cycle_q2_k3_transverse/ambient_lift/
 hermite_physical_partial_current_circuit.json
```

Its SHA-256 is

```
d40b27cc3e3c0fe96b306424781da54b43f6693676d62027eefa88442dcce4e0
```

It has 177,246 ordinary rational arithmetic nodes, with roots for all six physical current components, F, A, the residual r, the regular quotient q, and differentiated checks. The saved source identity is

```
A-2 v(F)+F div(v) = -F^2 r+F^3 q.
```

The archive supplies a compositional derivation using its source binding, universal adjoint lift, and Piola transform. **That generic ambient source proof is inherited. This run does not claim to have independently expanded the entire identity as a six-variable polynomial proof.** It newly verifies the exact rational-to-polynomial translation and directly rejects the resulting tuple using the literal original E. Finite-point checks of the retained identity are implementation audits, not a substitute for a generic source proof.

The later 1.9-million-node compact-source export named in the consolidated report, hash `2bdd39e00eb756a41c44d6938fbcd9a0245385ece0c4f9651566daca8057d683`, was not materialized here. Do not identify it with the selected physical circuit. All source archive hashes and access limitations are in `PROVENANCE.json`.

## 2. What was compiled, exactly

The input uses 31,890 nodes for the selected current, F,A, remainder and quotient roots. The other nodes mainly encode differentiated audit expressions.

`compile_polynomials.py` represents each rational expression as a rational scalar times a signed product of shared polynomial atoms. At an addition, it extracts the common Laurent monomial, combines identical terms, and introduces a polynomial sum atom. At an inversion, it changes signed exponents. Consequently every atom is an ordinary polynomial, and a final root with only nonnegative powers is an ordinary polynomial too.

The selected denominator D uses the componentwise maximum of the current denominators and half-rounded-up bounds for the remainder/quotient denominators. Therefore

```
Ni = D vi,
R = D^2 r,
Q0 = D^2 q
```

are all polynomials. There are **13,874 shared polynomial atoms** and 21 denominator atoms. The resulting degrees are

| Output | Degree |
|---|---:|
| D | 3726 |
| Nonzero Ni | 3733 |
| R | 7452 |
| Q0 | 7446 |

`N_X2` is zero. No minimal-degree claim is made. The main polynomial circuit is about 159 KiB compressed; its compactness comes from shared subexpressions, not omission of polynomial coefficients or unspecified functions.

The preserved partial identity is

```
E(D,N) = -F^2 R+F^3 Q0.
```

**R is a separate, nonzero output. It is not silently absorbed into Q0.**

### Exact generic compiler verification

`verify_translation.py` imports no compiler code. It checks every selected input operation using rational arithmetic. Each nontrivial addition is checked as an identity in a formal Laurent-polynomial ring in the existing polynomial atoms; each multiplication and integer power is checked directly. It also verifies the emitted polynomial roots, atom ancestry, homogeneity and character.

The verified operation counts are:

```
39 constants, 6 variables, 220 powers,
12,942 products, 18,683 sums; total 31,890.
```

This is an exact algebraic translation proof, not interpolation or floating-point fitting. It proves that the exported polynomials represent the stored rational expressions. It does not turn a partial input into a completed certificate.

## 3. Denominator legality and the unchanged target

`check_target.py` independently expands only the small F and A roots. They agree coefficient-for-coefficient with the user's nine-term sextic and one-term monomial.

For the complex smoothness argument, choose a nonzero coordinate of maximal modulus M at a hypothetical gradient zero. Its pure derivative has magnitude 6 M^5. The total mixed derivative has magnitude at most 2 M^5 for an X coordinate and M^5 for a Y coordinate. Thus it cannot cancel. The projective sextic is smooth over C and is geometrically irreducible: two positive-degree projective hypersurface components would intersect and create singularities.

The exact modular witness below has F=0 and D nonzero. All rational constants are units at that prime, and F is monic in Y2. If F divided D in characteristic zero, monic polynomial division would preserve that divisibility after this good reduction. It does not. Geometric irreducibility therefore proves **gcd_C(D,F)=1**, not merely a rational gcd assertion.

The independent raw-input evaluator also confirms that all 135 used negative-power nodes (59 distinct inverse bases) are units at both chosen F=0 charts. It checks all six current values and both remainder values against the compiled polynomials. There is no hidden inverse of F in the selected expression.

## 4. Literal original-identity verdict: rejection

The Python and C++ evaluators independently rebuild the protected F,A and differentiate all six Ni and D. Neither uses the input's saved `actual_ambient_defect` or `claimed_ambient_defect` roots.

At the regular point modulo 1009

```
z*=(982,776,604,497,616,182)
```

one has

```
F(z*)=0,  F_Y2(z*)=380,  D(z*)=322,  R(z*)=14.
```

Along `Y2=182+epsilon`, the literal output is

```
E = 436 epsilon^2 + 795 epsilon^3 mod (1009, epsilon^4).
```

In particular the coefficient of epsilon^2 is nonzero. A polynomial F^3 Q would have order at least three because F has a simple zero. Hence **this tuple is not a certificate**, for any Q.

An independent point modulo 1013 gives

```
z*=(634,836,152,51,690,652),
F_Y2=856, D=802, R=452,
E=639 epsilon^2+936 epsilon^3 mod epsilon^4.
```

This is a positive nonzero-remainder witness, not a finite-field rank failure promoted into a complex nonexistence theorem. Monicity and the good denominators transfer the rejection to characteristic zero. Since the input polynomials are rational, divisibility over C would already imply the same monic division identity over Q.

`literal_checker.cpp` was compiled and run. It retains first derivatives in **all six variables** and Taylor coefficients through order three. A deliberately falsified zero-remainder file is rejected with `partial source identity mismatch`. Passing the software checks means **the arithmetic and rejection were validated**, not that a certificate was found.

## 5. A completion attempt using the full diagonal character projector

Rather than assume the remainder was removable by averaging, `check_full_symmetry.py` enumerates all actual diagonal sixth-root symmetries of the original F. There are 432 before radial identification and 72 representatives with weight_X2=0.

It checks every polynomial atom's character and proves for every representative g that

```
g^(-1) v(g z) = chi_A(g) v(z),
r(g z) = chi_A(g) r(z).
```

The source-character projector therefore leaves this entire current and residual unchanged. Averaging in this diagonal group does not complete this current. This is not a statement about all possible currents, all correspondences, or original nonexistence. The source's nontrivial residue character is retained, not replaced by the invariant average.

## 6. A compiled normal gauge, with all six components

The next-stage input should not rely on an implicit normal division. From the explicit polynomials above define

```
B = D div(N)-N(grad D),
K = B+F R-F^2 Q0,
Dhat = D^2,
Nhat_i = D Ni-z_i K/12,
Rhat=D^2 R,  Qhat=D^2 Q0.
```

Using the inherited partial identity and Euler's relations, these formulas give

```
2 sum_i Nhat_i Fi = A Dhat,
E(Dhat,Nhat)=-F^2 Rhat+F^3 Qhat.
```

Indeed `2D N(grad F)=A D^2+F K`, while `sum z_i Fi=6F`. For the moving denominator, Euler gives `z(D)=dD` and `z(K)=(2d+6)K`. Direct substitution yields

```
Dhat div(Nhat)-Nhat(grad Dhat)
   =D^2(B-K)=-F D^2 R+F^2 D^2 Q0.
```

No derivative of D or K is suppressed. These universal algebraic identities are checked symbolically in `verify_closure_interface.py`.

The new normal-gauge polynomial circuit has 64,946 polynomial atoms, six nonzero numerator components, denominator degree 7452 and numerator degree 7459. It is **not** a source closure: it is a normalization of the same partial current. At the two witness charts the first-normal residual is zero through the checked jets, but the literal E coefficients at epsilon^2 remain nonzero: 1006 modulo 1009 and 840 modulo 1013.

A Python-only jet run on this larger circuit timed out and yielded no conclusion. The C++17 implementation completed. An interrupted full replay was subsequently completed in the documented chunks; final per-command receipts are in `CHECKS.json` and `RUN.log`. No successful result is inferred from an unfinished process.

## 7. Exact remaining equation, without a fixed pole-support restriction

Write

```
vbar=Nhat/Dhat,
r=Rhat/Dhat^2,
q=Qhat/Dhat^2.
```

Thus `vbar(F)=A/2` and `div(vbar)=-F r+F^2 q`. Let Fi=partial_i F, use coordinate 5=Y2 as pivot, and define the five polynomial tangent derivations

```
Ti = F5 partial_i-Fi partial_5,  i=0,...,4.
```

They annihilate F and have zero divergence because mixed partials commute. The exact completion equation is

```
sum_{i=0}^4 Ti(t_i) = F r+F^2 s.                 (CLOSE)
```

Here the five t_i are arbitrary homogeneous rational functions of degree 2 with no pole along F, and s is a homogeneous rational function of degree -6 with no pole along F. Additional denominator factors are **not** restricted to the 21 factors of this export.

A solution gives the complete rational current

```
v_complete = vbar + sum_i t_i (F5 e_i-Fi e_5),
q_complete = q+s.
```

The full identity follows literally, not only after restriction to F=0:

```
A-2 v_complete(F)+F div(v_complete)=F^3(q+s).
```

This interface loses no rational-current freedom given the partial source identity. To see necessity, take any hypothetical homogeneous complete current v*. Add the radial gauge z*h with

```
h=(A-2v*(F))/(12F)=-div(v*)/12+F^2 q*/12.
```

The second expression proves h is regular along F. Homogeneity gives degree(h)=6, so this gauge preserves the entire source expression and makes v*(F)=A/2 exactly. Its difference w from vbar is tangent to F. Since F5 is not divisible by the irreducible sextic F, it is invertible in the allowed localization, and every such w is

```
w=sum_{i=0}^4 (w_i/F5)(F5 e_i-Fi e_5).
```

Its divergence is exactly the left side of (CLOSE), with s=q*-q. Conversely the displayed reconstruction proves sufficiency. Complex coefficients are allowed in this mathematical statement; the emitted concrete candidate and current compiler use rational coefficients.

**No t_i,s solving (CLOSE) were found.** This is a fully specified continuation interface, not a certificate or a proof of existence. A solution must still be cleared and subjected to the original exact polynomial identity. The current package makes that boundary explicit; it does not bypass it.

## 8. Files, reproduction and non-repetition

The essential outputs are:

- `compiled_partial_polynomials.json.gz`: D, six Ni, R,Q0; no variable inverse operations.
- `normal_gauge_polynomials.json.gz`: normalized six-component polynomial tuple and the explicit five-operator completion interface.
- `translation_witness.json.gz`, `verify_translation.py`: exact generic algebraic compiler certificate and independent checker.
- `literal_checker.cpp`, `export_checker_program.py`: independent compiled original-identity test.
- `CHECKS.json`, `CPP_LITERAL_CHECK.json`, `LITERAL_POLYNOMIAL_CHECK.json`, `FULL_CHARACTER_CHECK.json`, `FAIL_CLOSED_CHECK.json`, `INPUT_SPECIALIZATION_CHECK.json`.
- `input_physical_current.json.gz` and `PROVENANCE.json`: exact selected upstream bytes and archive hashes.

Run `python run_checks.py` in this directory. For execution environments with short individual-call limits, use

```
python run_checks.py --to-step 4
python run_checks.py --from-step 4 --to-step 8
python run_checks.py --from-step 8
python check_input_specializations.py
```

Python 3, g++ with C++17, and SymPy for the small universal-interface check suffice. The direct compiler, exact translation proof, target/character checks and compiled literal checker do not require FLINT, Sage, Macaulay2, a private checkout, or a network service. No Lean compilation is claimed.

Do not repeat the clearing, the degree/character audits, these rejection points, or the same diagonal projector as a new construction. The saved problem to solve is (CLOSE) with its actual circuit source and unrestricted new legal denominators—or another independently source-bound primitive. Retain the regular q+s term. Never rename R as zero or label the working circuit an accepted certificate.

No external messages, repository changes, publications, or scheduled tasks were made. These outputs are saved locally in the conversation deliverable, not claimed newly uploaded to Library.
