import Proposal.GeometricFirstOrderCurve
import Proposal.GeometricRelativeCurveSeedFiberIso

/-!
# The unchanged seed curve is the closed fiber of the first-order curve

The actual first-order curve is reduced along the original closed point
of the dual-number spectrum. Pasting its genuine pullback square with
the original parameter square identifies this reduction with the seed
fiber of the original relative curve. The existing global seed-fiber
isomorphism then identifies it with the existing specialized projective
curve, retaining the same complex section vector and literal seed.

Both fiber projections are explicit. The map into the first-order curve
is independently constructed from its actual pullback property, with
the original seed-curve map as projection to the original relative curve.
No flatness, regularity, or nonemptiness hypothesis is used.

Source-only draft: no elaboration, compilation, or kernel replay was run.
Prepared for fqlx with OpenAI ChatGPT assistance, following Ben Diamond
and the geometric strategy credited in solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FirstOrderCurveSeedFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceFirstOrder CycleQ2IncidenceChartFiberScheme
  CycleQ2RelativeConstantCurve CycleQ2RelativeCurveSeedProj
  CycleQ2RelativeCurveSeedFiberIso CycleQ2SpecializedProjectiveCurve
  CycleQ2FirstOrderCurve

variable (t : Fin 3 → ℂ)

/-- The actual scheme-theoretic closed fiber, in closed-point-first order. -/
abbrev FirstOrderCurveSeedFiber :=
  pullback firstOrderClosedPoint (firstOrderCurveToBase t)

/-- Pasting the two actual base changes gives the original seed fiber. -/
theorem firstOrderCurveSeedFiber_isPullback :
    IsPullback
      (pullback.fst firstOrderClosedPoint (firstOrderCurveToBase t))
      (pullback.snd firstOrderClosedPoint (firstOrderCurveToBase t) ≫
        firstOrderCurveToOriginalCurve t)
      seedParameterMorphism (relativeCurveToBase incidencePoint t) := by
  have h := (IsPullback.of_hasPullback firstOrderClosedPoint
      (firstOrderCurveToBase t)).paste_vert (firstOrderCurve_isPullback t).flip
  rw [firstOrderParameterPoint_at_seed] at h
  exact h

/-- The existing specialized curve is the reduction of the same first-order curve. -/
def firstOrderCurveSeedFiberIso :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ≅ FirstOrderCurveSeedFiber t :=
  seedCurveFiberIso t ≪≫ (firstOrderCurveSeedFiber_isPullback t).isoPullback.symm

@[reassoc, simp] theorem firstOrderCurveSeedFiberIso_hom_fst :
    (firstOrderCurveSeedFiberIso t).hom ≫
        pullback.fst firstOrderClosedPoint (firstOrderCurveToBase t) =
      specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t := by
  rw [firstOrderCurveSeedFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, IsPullback.isoPullback_inv_fst, seedCurveFiberIso_hom_fst]

@[reassoc, simp] theorem firstOrderCurveSeedFiberIso_hom_original :
    (firstOrderCurveSeedFiberIso t).hom ≫
        (pullback.snd firstOrderClosedPoint (firstOrderCurveToBase t) ≫
          firstOrderCurveToOriginalCurve t) = seedCurveToRelative t := by
  rw [firstOrderCurveSeedFiberIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, IsPullback.isoPullback_inv_snd, seedCurveFiberIso_hom_snd]

/-- The original seed map lifts into the actual first-order curve. -/
def seedCurveToFirstOrderCurve :
    specializedCurve (seedPoint (57 : ℂ) Complex.I) t ⟶ firstOrderCurve t :=
  (firstOrderCurve_isPullback t).lift (seedCurveToRelative t)
    (specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t ≫ firstOrderClosedPoint) (by
      rw [Category.assoc, firstOrderParameterPoint_at_seed]
      exact seedCurveToRelative_overBase t)

@[reassoc, simp] theorem seedCurveToFirstOrderCurve_original :
    seedCurveToFirstOrderCurve t ≫ firstOrderCurveToOriginalCurve t =
      seedCurveToRelative t := by
  simp only [seedCurveToFirstOrderCurve, IsPullback.lift_fst]

@[reassoc, simp] theorem seedCurveToFirstOrderCurve_overBase :
    seedCurveToFirstOrderCurve t ≫ firstOrderCurveToBase t =
      specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t ≫ firstOrderClosedPoint := by
  simp only [seedCurveToFirstOrderCurve, IsPullback.lift_snd]

/-- The second fiber projection is the independently constructed original-seed lift. -/
@[reassoc, simp] theorem firstOrderCurveSeedFiberIso_hom_snd :
    (firstOrderCurveSeedFiberIso t).hom ≫
        pullback.snd firstOrderClosedPoint (firstOrderCurveToBase t) =
      seedCurveToFirstOrderCurve t := by
  apply (firstOrderCurve_isPullback t).hom_ext
  · rw [Category.assoc, seedCurveToFirstOrderCurve_original]
    exact firstOrderCurveSeedFiberIso_hom_original t
  · rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      firstOrderCurveSeedFiberIso_hom_fst, seedCurveToFirstOrderCurve_overBase]

@[reassoc] theorem firstOrderCurveSeedFiberIso_inv_fst :
    (firstOrderCurveSeedFiberIso t).inv ≫
        specializedCurveToBase (seedPoint (57 : ℂ) Complex.I) t =
      pullback.fst firstOrderClosedPoint (firstOrderCurveToBase t) := by
  rw [← firstOrderCurveSeedFiberIso_hom_fst, Iso.inv_hom_id_assoc]

@[reassoc] theorem firstOrderCurveSeedFiberIso_inv_snd :
    (firstOrderCurveSeedFiberIso t).inv ≫ seedCurveToFirstOrderCurve t =
      pullback.snd firstOrderClosedPoint (firstOrderCurveToBase t) := by
  rw [← firstOrderCurveSeedFiberIso_hom_snd, Iso.inv_hom_id_assoc]

#print axioms firstOrderCurveSeedFiber_isPullback
#print axioms firstOrderCurveSeedFiberIso
#print axioms firstOrderCurveSeedFiberIso_hom_fst
#print axioms firstOrderCurveSeedFiberIso_hom_snd
#print axioms firstOrderCurveSeedFiberIso_hom_original

end CycleQ2FirstOrderCurveSeedFiber
end
