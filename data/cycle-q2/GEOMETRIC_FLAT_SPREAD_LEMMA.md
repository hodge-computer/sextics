# Cycle-q2: flat spreading from the literal seed to a reduced parameter curve

**Mathematical checkpoint (2026-11-15).** This records one classical geometric implication with a complete proof and its exact application obligations. It is **not** a Lean-compiled theorem, a nonempty-cycle construction, an Abel–Jacobi comparison, or a certificate. It adds no axioms or admissions and does not edit `Solution.lean`.

## Proposition: relative Cartier spreading near one proper fiber

Let `f : X → S` be proper and smooth (hence flat and locally of finite presentation) on a neighborhood of a point `s ∈ S`. Let `i : Z ↪ X` be a closed immersion with `Z → S` proper. Suppose, at every point of the scheme-theoretic closed fiber `Z_s`:

1. `Z` is a **locally principal** closed subscheme of `X` in a neighborhood of the point;
2. `Z_s ↪ X_s` is an **effective Cartier divisor** in a neighborhood of the point (its local equation is a nonzerodivisor, not merely a nonzero function).

Then there is an open neighborhood `V ⊂ S` of `s` such that `Z_V ↪ X_V` is a *relative effective Cartier divisor*: its ideal is locally invertible, `Z_V → V` is flat, and `Z_V → V` is proper. All its base changes have effective-Cartier fibers.

**Proof.** First restrict `S` so `X → S` is flat and locally finitely presented. At each `x ∈ Z_s`, apply Stacks Project, Divisors, Lemma **31.19.9(3)** (tag [056P](https://stacks.math.columbia.edu/tag/056P)). Its hypotheses are exactly flat finite presentation of the ambient morphism, effective-Cartier special fiber at `x`, and local principality of `Z` at `x`. It supplies an open `U_x ⊂ X` around `x` on which the **actual Z**, not merely an auxiliary divisor with the same fiber, is a relative effective Cartier divisor. Put `U = ⋃_{x∈Z_s} U_x`. The subset `B = Z \setminus (Z ∩ U)` is closed in `Z` and misses its entire fiber above `s`. Since `Z → S` is proper, `f(B)` is closed in `S`. Let `V = S \setminus f(B)`. Then `s ∈ V` and every point of `Z_V` belongs to `U`; the desired flatness and Cartier properties are local on its source. Properness survives base change. The effective-Cartier statement under subsequent arbitrary base changes follows from Stacks Lemma **31.19.1** (same section). QED.

The empty special fiber is allowed: the proposition does **not** imply that `Z_s`, `Z_V`, or any moving cycle is nonempty.

## Application to the actual PR #245 declarations

Use the **unchanged** `r=57`, `θ=1` incidence seed, not the distinct sparse trace parameter satisfying `r³=2`.

- `S := Spec ParameterAlgebra`, `s := seedBasePoint`, `X := surface incidencePoint`, `Z_t := relativeCurve incidencePoint t`.
- `CycleQ2IncidenceSmoothNeighborhood.exists_seed_smooth_neighborhood` supplies, at **source level**, a base neighborhood of `s` with smooth and proper `X → S`; the original graded quotient gives finite presentation.
- `CycleQ2RelativeCartierFamily.exists_incidence_and_seed_cartier` supplies, at **source level**, one **same nonzero** `t : Fin 3 → ℂ` for which the total-space `Z_t ↪ X` has a regular principal covering and the literal specialized `specializedCurve (seedPoint 57 Complex.I) t` has a regular principal covering inside the seed surface.
- `CycleQ2RelativeCurveSeedFiberIso.seedCurveFiberIso` (used by `CycleQ2FirstOrderCurveSeedFiber.firstOrderCurveSeedFiberIso`) identifies the actual scheme-theoretic fiber `(Z_t)_s` with **that same** specialized zero locus. The regular principal equations therefore supply the required special-fiber effective-Cartier condition.
- Properness of `Z_t → S` comes from its closed immersion into the proper projective surface (also recorded in `CycleQ2IncidenceProjectiveProper` for the universal section scheme).

**Consequent mathematical implication, subject to elaboration of those source-level premises:** the original fixed-section family `Z_t`, for one nonzero fixed `t`, restricts to a **proper flat relative Cartier family over an open neighborhood of the original seed in the full coefficient/parameter scheme**. This is stronger than flatness solely over `ℂ[ε]/(ε²)` and does not rely on the auxiliary cubic-square parameter family.

The restriction to the fixed-sextic coefficient fiber is an actual reduced parameter curve through `s`: `CycleQ2IncidenceTimeCurve.parameterToSextics_smooth_relative_one` gives relative smoothness of dimension one, and `CycleQ2IncidenceSeedTangent.seedVelocity_eq_parameterDirection` plus `seed_trace_one` identifies a nonzero coefficient-direction tangent at the same seed. Base change of the relative Cartier family to an open of that smooth curve is again proper and flat. **This is movement of the parameter, not yet a proof that the embedded cycle moves nontrivially.**

## Verification scope and next exact implication

The abstract spreading proposition is a classical theorem proved above from Stacks 31.19.9(3), proper closed-image, and Stacks 31.19.1. The repository declarations cited in the application are presently **source-only/uncompiled** in this chain. No Lean elaboration, full build, kernel replay, or protected acceptance is asserted for this checkpoint.

The *first new geometric goal* after compiling the premises is **nonemptiness of the specialized zero locus for the same chosen regular vector `t`**. An actionable sufficient lemma is that the rank-one matrix's induced projective row-line map `X_s → ℙ²` has positive-dimensional image and that the actual zero locus is the inverse image of the hyperplane `H_t`. The image of a proper positive-dimensional complex scheme cannot lie inside `ℙ² \setminus H_t ≅ 𝔸²`, so this would give nonemptiness. The required nonconstant-image statement is **not** proved here.

If the special fiber is nonempty, openness (flat and locally finitely presented) and closedness (proper) of the image show that the moving family has nonempty fibers along the connected component of the restricted base curve. Smoothness of the individual Cartier fibers, comparison of this family's Kodaira–Spencer/Abel–Jacobi derivative with `CycleQ2IncidenceFirstOrderCohomology.firstOrderDifferentialClass`, support on the original fourfold, and **exactness of the protected affine residue** remain wholly unproved.

No alteration to `Submission.missing_geometric_existence : CycleQ2Nonconstructive.AffineResidueFormExact` is made.
