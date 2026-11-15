# Cycle-q2: closed seed-nonemptiness assembly in Lean source

Date: 15 November 2026.
Base commit: `24a6caa8d3e9254f01f8f8e33e0d0fcd0d65a29f`.
Branch: `fqlx/cycle-q2-modular`.

## Status and endpoints

The previously omitted assembly is now written as a closed proof-source
chain. **None of the five new modules has been elaborated, compiled, or
kernel-replayed.** No usable Lean/Lake executable is present in this
workspace. Source completion is not a checked Lean proof or an acceptance
receipt. Elaboration errors in this continuation or its existing source-only
imports may still require repair.

The endpoint in `GeometricSeedSectionNonempty.lean` is:

```lean
theorem seed_specializedCurve_nonempty (t : Fin 3 → ℂ) :
    Nonempty (specializedCurve (seedPoint (57 : ℂ) Complex.I) t)
```

There is no premise supplying a nonunit, a point, a compatible inverse,
regularity of the section, or a negative-degree section. The same actual
curve and literal r=57 incidence seed are retained. In particular, the
statement covers the previously chosen regular vector, without choosing
a different vector to secure nonemptiness.

`GeometricFirstOrderNonemptyFlatCurve.lean` combines it with the existing
first-order flatness result. Its closed endpoint retains one nonzero
vector t, properness and flatness of `firstOrderCurveToBase t`, the original
seed-fiber isomorphism, and nonemptiness of both the original specialized
curve and that actual first-order closed fiber.

**The protected residue exactness theorem is not proved by this increment.**
`Solution.lean`, the target, manifest, shared library, verifier, and
workflows are not edited. The original final admission remains.

## A simpler assembly than the negative-degree route

The preceding account used normalized projective inverses and the
transition of degree minus four. That argument remains useful, but the
new assembly does not need to prove that a chosen inverse has a prescribed
character or signed homogeneous degree.

Instead, work with the raw matrix and raw ideal generators on the cone.
Let A be the unchanged quotient

    C[z0,z1,z2,z3,w] / (smoothH I, smoothF 57 I),

with weights (1,1,1,1,2). Let B_i=A[1/z_(i+1)], i=0,1,2. These are the
existing `CycleQ2SegreFactorChartExact.Chart {i}` rings. Write S_a=(M*t)_a
for the original degree-fourteen rows and L_a for the original degree-ten
left linkage generators.

### 1. Emptiness supplies the actual Bezout identities

`GeometricEmptySectionRows.row_span_of_isEmpty` starts from emptiness of
`specializedCurve y t`. The existing chart-kernel theorem then makes
every actual projective fraction `(M*t)_a/M_ab` a unit.

For any complex-algebra map f from the original surface ring whose nine
matrix-entry images generate one, suppose the three row images generate
a proper ideal. Choose a maximal ideal containing it. In its residue
field, some matrix entry is nonzero, hence invertible. The actual map
`projectiveToOverlap` maps the corresponding projective fraction to zero,
since its numerator is a row. It also maps that fraction to a unit, a
contradiction. Thus the row images generate one.

This argument neither assumes a complex rational point nor asserts that
an arbitrary quotient localization is nonzero.

### 2. The original seed maps are explicitly retained

`GeometricSeedConeSection.literalToSeed` is the composition of the existing
identity-on-polynomials equivalences:

    PointSurface (seedPoint 57 I) -> SurfaceRing 57 1 -> SeedRing 57 I.

`toCone` then uses the original coordinate localization. The seed has zero
matrix perturbation, so `incidenceMatrix_zero` identifies its actual matrix
with `rawSeedMatrix 57`. The polynomial, pivot, row, and left-generator
bindings are included in the new source. The supplied `factorData` proves
the entry-generation hypothesis on every nonempty coordinate-index chart.
Consequently, under the temporary emptiness assumption, the three literal
rows span the unit ideal on all those charts.

### 3. Construct the inverse and prove its compatibility

For the actual linkage ideal I_i and actual functional phi_i, the existing
inverse-ideal theorem produces a_i in I_i with phi_i(a_i)=1. Its evaluation
on the left generators is S_a. The elementary ideal balance identity

    x * phi_i(y) = y * phi_i(x)

therefore gives the three scalar identities

    S_a * a_i = L_a.

On an overlap both restrictions solve these same scalar equations. Since
the rows span one there, these equations determine the scalar uniquely.
This proves compatibility under the original restriction maps. No
compatibility is an additional theorem hypothesis.

The original `CycleQ2SeedCechGlobalGluing.existsUnique_gluing` now constructs
p in A with p|B_i=a_i. Its proof is based on the actual rank-nine free basis
over C[z1,z2,z3], not an assumed extension across the missing cone vertex.
Faithfulness of each coordinate localization proves, in A,

    S_a * p = L_a     for all a.

### 4. Degree 10 versus degree 14 supplies the contradiction

Choose any polynomial representative P of p. The ideal defining A is
homogeneous. Extract weighted degree 10 from

    S_a * P - L_a in (smoothH I, smoothF 57 I).

All variable weights are nonnegative, S_a has degree 14, and L_a has degree
10. The degree-10 component of S_a*P is therefore zero, irrespective of
the degree or character of P. The component of L_a is L_a itself.
Hence every L_a has zero class in A.

The generic proof `GeometricSectionDegreeGap.lower_class_zero_of_multiple`
checks this inference for an arbitrary homogeneous polynomial quotient;
no integrality hypothesis is used. On one nonzero coordinate chart the
actual left ideal is thus zero. Its inverse a_i must be zero, contrary to
phi_i(a_i)=1. Nontriviality of A comes from its existing basis, and
nontriviality of the chart from the existing localization injection.

This completes the written proof and the intended closed Lean source
assembly. It does not replace elaboration and kernel checking.

## New-module dependency order

1. `GeometricSectionDegreeGap.lean`: low-degree extraction in homogeneous quotients.
2. `GeometricEmptySectionRows.lean`: emptiness implies actual row Bezout identities.
3. `GeometricSeedConeSection.lean`: actual maps, inverses, restrictions, and ungraded gluing.
4. `GeometricSeedSectionNonempty.lean`: closed nonemptiness endpoint.
5. `GeometricFirstOrderNonemptyFlatCurve.lean`: same-vector first-order corollary.

Modules 1 and 2 are independent. Module 3 uses the two previously saved
inverse-ideal helpers through `GeometricSeedSectionInverse`. Module 4 uses
1 and 3; module 5 uses 4 and the existing first-order flatness module.
The new files contain no admission, new axiom, unsafe declaration, or
native-decision proof. This lexical statement is not an axiom audit of
compiled declarations.

## Deferred bounded verification

Prerequisites: Lean 4.33.1, pinned Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`, the verifier-style `Proposal`
layout, generated unchanged `HodgeTarget`, and compatible compiled imports.
Do not launch a full build merely because a prerequisite is missing.

With those prerequisites already available, emit each module's object
before checking the next dependent module. For example:

```sh
mkdir -p .lake/build/lib/lean/Proposal
timeout --signal=TERM --kill-after=3s 45s \
  lake env lean -M4096 \
    -o .lake/build/lib/lean/Proposal/GeometricSectionDegreeGap.olean \
    Proposal/GeometricSectionDegreeGap.lean
```

Apply that same single-module command in the dependency order above,
changing both matching filenames. Stop on the first error or resource
limit. No such compilation was run in this checkpoint. The final endpoint
has a `#print axioms` command, but its output has not been obtained.

## Remaining certificate boundary

The same-vector nonempty first-order family is not by itself a smooth
family of curves over a reduced base, an Abel--Jacobi computation, a
supported correspondence, or an affine de Rham comparison. In particular,
none of these new endpoints supplies

    Submission.missing_geometric_existence :
      CycleQ2Nonconstructive.AffineResidueFormExact.

The full certificate still requires its genuine geometric/source
comparisons or a direct primitive, with the protected statement unchanged.

Prepared for fqlx with OpenAI ChatGPT assistance. The geometric strategy
and retained constructions remain attributed as in `solution.md`.
