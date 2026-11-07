# Same-denominator normalization of the cycle-q2 proof obligation

**Status:** algebraic normalization derived and implementation tested over exact rational polynomials.
Lean proof source supplied, but NOT compiled because the required Lean/Lake executables are absent.
One intentionally admitted existence lemma remains. No cycle-q2 certificate is constructed.

## Exact unchanged target

Coordinates are z=(X0,X1,X2,Y0,Y1,Y2), with

```
F = sum_i(Xi^6+Yi^6)
    +(X0^3 X1 Y0 Y1+X1^3 X2 Y1 Y2+X2^3 X0 Y2 Y0)/2
A = X0^2 X1^2 X2^3 Y0^2 Y1^2 Y2
q = 2
E(F,A,D,N) = A D^2 - 2D sum_i Ni Fi
             + F(D sum_i partial_i Ni - sum_i Ni partial_i D).
```

A legal witness has D nonzero, homogeneous of degree d, coprime to F over C,
Ni homogeneous of degree d+7, and E=F^3 Q with unrestricted polynomial Q.
The protected definitions and both upstream Lean sources have not been changed.

## 1. Exact same-denominator radial normalization

Assume only the first divisibility F | E for a legal, correctly graded candidate.
Put

```
S = A D - 2 sum_i Ni Fi.
B = D div(N) - N(grad D).
E = D S + F B.
```

Thus F | D S. Since gcd_C(F,D)=1, F | S. There is an actual polynomial H with

```
S = F H.
```

This is EXACT polynomial division, not permission to introduce 1/F as a pole.
Since S is homogeneous of degree d+12 and F is nonzero homogeneous of degree 6,
H is homogeneous of degree d+6 (the zero polynomial also satisfies this degree predicate).

Define

```
D_normal = D
N_normal,i = Ni + zi H/12.
```

Euler's identity sum zi Fi = 6F gives

```
2 sum_i N_normal,i Fi
 = 2 sum_i Ni Fi + F H
 = A D.
```

All six numerator degrees remain d+7. D is literally unchanged, so nonzeroness,
homogeneity, and coprimality over C are retained without a new geometric argument.
No support or degree bound on D is introduced.

## 2. The COMPLETE defect, not just its first order, is preserved

Let delta N= z H/12. Euler's identities for H and D give

```
div(delta N) = (d+12) H/12,
delta N(grad D) = d D H/12,
delta N(grad F) = F H/2.
```

Therefore

```
B(D,N_normal) - B(D,N) = D H,
E(F,A,D,N_normal) - E(F,A,D,N)
  = -2D(FH/2)+F(DH) = 0.
```

This identity retains every derivative of D and H. It does not depend on the
existence of a full certificate. It also shows why this step cannot fix a failing
current: its entire nonzero defect is unchanged.

If E=F^3 Q, the SAME polynomial Q remains valid and, after first normalization,

```
D div(N_normal) - N_normal(grad D) = F^2 Q.
```

If instead E=-F^2 R+F^3 Q is a partial identity, normalization leaves

```
D div(N_normal) - N_normal(grad D) = -F R+F^2 Q.
```

The R term cannot be erased. No regular quotient or residual is discarded.

The normalization is idempotent: an already first-normal tuple has S=H=0.
It is the unique representative within this fixed-denominator radial gauge
satisfying the first-normal equation. It is not uniqueness of all certificate currents.

## 3. Equivalence of the existence questions

A full original witness normalizes as above without changing d, D, or Q.
Conversely, a legal tuple satisfying

```
2 sum_i Ni Fi = A D,
D div(N) - N(grad D) = F^2 Q
```

immediately satisfies the original E=F^3 Q equation. Thus the normalized
existential question is equivalent to the original one; it is not a smaller ansatz.

The single mathematical hole in the development draft remains

```
theorem missing_rational_solution : Nonempty NormalizedRationalSolution := by
  sorry
```

The data in this structure still require all denominator legality and grading
obligations. No first-normal solution for an arbitrary chosen denominator is assumed.

## 4. Lean source and precise verification boundary

`formal/CycleQ2Normalization.lean` supplies proof bodies for:

- radial_gauge_preserves_defect;
- normalize_of_first_divisibility;
- normalize_verify (same d,D,Q);
- originalGoal_iff_normalized.

It also supplies the quotient-homogeneity argument, Euler identities, and exact
homogeneity/nonzeroness checks for the original F and A.

`CycleQ2Draft.lean` now imports this normalization module and obtains the original
goal via the equivalence. Only its named missing existence theorem is admitted.
`check_draft.py` builds the helper module separately and audits its axioms before
building the deliberately incomplete draft. Strict mode rejects the remaining hole.

These are uncompiled Lean proof bodies. No successful type-check, kernel replay,
or actual axiom-output audit is claimed. Hidden type/elaboration issues may remain
until the real pinned compiler runs. Static source scans cannot exclude synthetic
admissions introduced by failed elaboration, so compiler/audit checks remain mandatory.

The input workspace's giant physical-current circuit was NOT re-expanded or
re-exported here. This task normalizes the formulation and provides the exact
conversion, not another normalization pass of that already-known partial current.

## 5. Checks actually run

Ten exact SymPy/QQ checks passed, including literal original F and A, all six
moving derivatives, the universal gauge identity, a nonzero-defect original-source
example, idempotence, and a manufactured-source calibration with nonzero Q retained.
The manufactured source is NOT the cycle-q2 monomial and is not a certificate attempt.

Ten build-guard unit tests passed. The current source audit finds exactly one explicit
hole in CycleQ2Draft.lean, and strict mode rejects it. Original target/source/pin
hashes match the parent workspace.

Fresh actual launch attempts of `lean --version` and `lake build CycleQ2Draft`
failed with missing-executable errors. A raw GitHub network probe also failed DNS
resolution. No installation or compilation success is inferred from these attempts.

## Reproduce

```
python3 normalization/check_normalization.py
python3 scripts/test_draft_guard.py
python3 scripts/check_draft.py --static-only
# With the existing pinned toolchain and dependencies installed:
python3 scripts/check_draft.py
```

The user has authorized a single admitted mathematical gap for development.
A later successful draft build will still not be a certificate while that gap remains.
