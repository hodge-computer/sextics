import Proposal.GeometricHodgeTwistAnchorBase
import Proposal.GeometricHodgeTwistFaceRings
import Proposal.GeometricHodgeTwistTorus

/-!
# Restriction of a native twisted section to the common Laurent torus

The normalized base coordinates and the cubic root restrict to the
projective fractions xₐ/xᵢ and w/xᵢ². The universal property of the
product localization then computes the restriction of every coefficient.
The finite localized power basis gives the full restriction formula.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistAnchor

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2HodgeTwistCech CycleQ2HodgeTwistFaces
open CycleQ2HodgeTwistCubicFaces CycleQ2HodgeTwistRatios CycleQ2HodgeTwistMonomials
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2SeedCechLocalization (coordinateLocalization localizationToLaurent)
open CycleQ2HodgeEulerChartBinding (chartEquiv_ratio_succAbove)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient)) (B : Finset (Fin 3))

theorem torus_le_native : torus φ ≤ face φ i B := by
  rw [face_eq]
  exact le_inf (torus_le φ i) (Finset.le_inf fun q _ => torus_le φ (faceVertex i q))

def restrictStage : AwayStage φ i h (powers (R := R) B) →+* Γ(threefold φ,torus φ) :=
  (res (threefold φ).sheaf (torus_le_native φ i B)).comp
    ((sectionsEquiv φ i B).toRingHom.comp (faceStage φ i h B).symm.toRingHom)

private theorem restrictStage_chart (p : ChartRing φ i) :
    restrictStage φ i h B (algebraMap _ _ (stageEquiv φ i h p)) =
      res (threefold φ).sheaf (torus_le φ i) ((Proj.awayToSection _ _) p) := by
  rw [← faceStage_toFace]
  change res _ _ (sectionsEquiv φ i B ((faceStage φ i h B).symm (faceStage φ i h B _))) = _
  rw [RingEquiv.symm_apply_apply, toFace_section]
  exact res_comp _ _ _ _

private theorem restrictStage_root :
    restrictStage φ i h B (algebraMap _ _ (AdjoinRoot.root (cubic φ i h))) =
      weightTwo φ (torus φ) (torus_le φ) i := by
  have hi : i.castSucc.succAbove (Fin.last 3) = Fin.last 4 := by fin_cases i <;> decide
  have he : stageEquiv φ i h (CycleQ2HodgeEulerChartBinding.ratio φ i (Fin.last 4)) =
      AdjoinRoot.root (cubic φ i h) := by
    rw [← hi]
    exact (congrArg (chartEquivAdjoinRoot φ i h) (chartEquiv_ratio_succAbove φ i _)).trans
      (chartEquivAdjoinRoot_weightTwo φ i h)
  rw [← he, restrictStage_chart]
  rfl

private def baseRestriction : coordinateLocalization R B →+* Γ(threefold φ,torus φ) :=
  (restrictStage φ i h B).comp (algebraMap (AwayBase (powers (R := R) B)) (AwayStage φ i h _))

private theorem baseRestriction_base (p : Base R) :
    baseRestriction φ i h B (algebraMap (Base R) (coordinateLocalization R B) p) =
      restrictStage φ i h B (algebraMap (Stage φ i h) _ (algebraMap (Base R) (Stage φ i h) p)) := by
  change restrictStage φ i h B (algebraMap (AwayBase (powers (R := R) B)) _ (algebraMap _ _ p)) = _
  simp only [← IsScalarTower.algebraMap_apply]

private theorem baseRestriction_scalar (c : R) :
    baseRestriction φ i h B (algebraMap (Base R) (coordinateLocalization R B) (C c)) =
      commonCoefficient φ c := by
  rw [baseRestriction_base]
  have hc : stageEquiv φ i h (chartCoefficient φ i c) = algebraMap (Base R) (Stage φ i h) (C c) := by
    rw [show chartCoefficient φ i c = algebraMap R (ChartRing φ i) c from rfl, AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply R (Base R) (Stage φ i h) c
  rw [← hc, restrictStage_chart]
  exact RingHom.congr_fun (frameCoefficient_eq φ i) c

def nativeUnits (q : Fin 3) : Γ(threefold φ,torus φ)ˣ :=
  transition φ i (i.succAbove q) (torus φ) (torus_le φ i) (torus_le φ _)

private theorem baseRestriction_variable (q : Fin 3) :
    baseRestriction φ i h B (algebraMap (Base R) (coordinateLocalization R B) (X q)) =
      (nativeUnits φ i q).val := by
  rw [baseRestriction_base, ← stageEquiv_variable φ i h q, restrictStage_chart]
  apply congrArg (res (threefold φ).sheaf (torus_le φ i))
  apply congrArg (Proj.awayToSection (grade φ) (coord φ i.castSucc))
  apply HomogeneousLocalization.val_injective
  simp only [CycleQ2HodgeEulerChartBinding.ratio, CycleQ2HodgeEulerChartBinding.fraction,
    CycleQ2SeedFermatProj.geometricWeight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

variable [Nontrivial R]

theorem stage_expansion (x : AwayStage φ i h (powers (R := R) B)) :
    restrictStage φ i h B x = ∑ j, CycleQ2HodgeTwistTorus.evaluate (commonCoefficient φ) (nativeUnits φ i)
      (localizationToLaurent R B ((localizedBasis φ i h _).repr x j)) * weightTwo φ (torus φ) (torus_le φ) i ^ j.val := by
  let b := localizedBasis φ i h (powers (R := R) B)
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Algebra.smul_def, map_mul]
  have he := CycleQ2HodgeTwistTorus.evaluate_restriction (commonCoefficient φ) (nativeUnits φ i) B
    (baseRestriction φ i h B) (baseRestriction_scalar φ i h B) (baseRestriction_variable φ i h B) (b.repr x j)
  rw [he]
  congr 1
  rw [show b j = _ from localizedBasis_apply φ i h _ j, map_pow, map_pow, restrictStage_root]

end CycleQ2HodgeTwistAnchor
end

#print axioms CycleQ2HodgeTwistAnchor.stage_expansion
