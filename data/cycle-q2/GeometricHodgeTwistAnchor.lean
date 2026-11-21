import Proposal.GeometricHodgeTwistFaceRings
import Proposal.GeometricHodgeTwistLocalization
import Proposal.GeometricHodgeTwistChartRestriction
import Proposal.GeometricModuleLocalIso
import Proposal.GeometricHodgeTwistAnchorBase
import Proposal.GeometricHodgeThreefoldTwist

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
namespace CycleQ2HodgeTwistCubicFaces
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeTwistFaces CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2HodgeTwistLocalization CycleQ2HodgeTwistCech
open CycleQ2SeedCechLocalization (baseProduct)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient))

variable [Nontrivial R]
def structureCoordinates (S : Finset Vertex) (hi : i ∈ S) (t : ℤ) :
    Γ(threefold φ, face φ i (inverted i S)) ≃+ sections R t S :=
  (sectionsEquiv φ i _).symm.toAddEquiv.trans ((faceStage φ i h _).toAddEquiv.trans
    ((localizedBasis φ i h _).equivFun.toAddEquiv.trans (intersectionCoordinates R i S t hi).symm))

end CycleQ2HodgeTwistCubicFaces

namespace CycleQ2HodgeTwistAnchor

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2HodgeTwistCech CycleQ2HodgeTwistLocalization CycleQ2HodgeTwistFaces
open CycleQ2HodgeTwistCubicFaces CycleQ2HodgeTwistRatios CycleQ2HodgeTwistMonomials
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2SeedCechLocalization (coordinateLocalization localizationToLaurent)
open CycleQ2HodgeEulerChartBinding (chartEquiv_ratio_succAbove)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient)) (B : Finset (Fin 3))

variable [Nontrivial R]

omit [Nontrivial R] in
private theorem units_product (e : Exp) : units φ (torus φ) (torus_le φ) i e =
    ∏ q, nativeUnits φ i q ^ e (i.succAbove q) := by
  rw [units, Fin.prod_univ_succAbove _ i, transition_self, one_zpow, one_mul]
  rfl

omit [Nontrivial R] in
private theorem expression (S : Finset Vertex) (hi : i ∈ S) (k : ℤ) (p : sections R k S) :
    (∑ j, CycleQ2HodgeTwistTorus.evaluate (commonCoefficient φ) (nativeUnits φ i)
      (localizationToLaurent R _ (intersectionCoordinates R i S k hi p j)) *
        weightTwo φ (torus φ) (torus_le φ) i ^ j.val) =
      evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) i p.val := by
  unfold evaluate
  apply Finset.sum_congr rfl
  intro j _
  rw [CycleQ2HodgeTwistTorus.evaluate_sum, sum_intersection, Finsupp.sum_mul]
  unfold Finsupp.sum
  apply Finset.sum_congr rfl
  intro e _
  let c := (commonCoefficient φ) (p.val j e)
  let w := weightTwo φ (torus φ) (torus_le φ) i ^ j.val
  change (c * ((∏ q, nativeUnits φ i q ^ e (i.succAbove q) : Γ(threefold φ,torus φ)ˣ) :
    Γ(threefold φ,torus φ))) * w = c * ((units φ (torus φ) (torus_le φ) i e).val * w)
  rw [units_product]
  exact mul_assoc _ _ _

theorem structure_face_evaluation (S : Finset Vertex) (hi : i ∈ S) (k : ℤ)
    (s : Γ(threefold φ, face φ i (inverted i S))) :
    res (threefold φ).sheaf (torus_le_native φ i _) s =
      evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) i ((structureCoordinates φ i h S hi k s).val) := by
  let B := inverted i S
  let x := faceStage φ i h B ((sectionsEquiv φ i B).symm s)
  let p := structureCoordinates φ i h S hi k s
  have hx : restrictStage φ i h B x = res (threefold φ).sheaf (torus_le_native φ i B) s := by
    change res _ _ (sectionsEquiv φ i B ((faceStage φ i h B).symm (faceStage φ i h B _))) = _
    rw [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
    rfl
  rw [← hx, stage_expansion, ← expression φ i S hi k p]
  apply Finset.sum_congr rfl
  intro j _
  have hj : intersectionCoordinates R i S k hi p j = (localizedBasis φ i h _).repr x j := by
    exact congrFun ((intersectionCoordinates R i S k hi).apply_symm_apply
      ((localizedBasis φ i h (powers (R := R) B)).equivFun x)) j
  rw [hj]


end CycleQ2HodgeTwistAnchor

namespace CycleQ2HodgeTwistCubicFaces
open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeTwistFaces CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2HodgeTwistLocalization CycleQ2HodgeTwistCech
open CycleQ2SeedCechLocalization (baseProduct)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient))

variable [Nontrivial R]
/-- Sections of the native line bundle on each actual standard intersection. -/
def twistCoordinates (S : Finset Vertex) (hi : i ∈ S) (t : ℤ) :
    Γ(CycleQ2HodgeThreefoldTwist.twist φ t, S.inf (coordinateOpen φ)) ≃+ sections R t S :=
  (CycleQ2HodgeThreefoldTwist.chartFrame φ t i _ (Finset.inf_le hi)).toAddEquiv.trans
    ((CycleQ2GeometricProjectiveCurve.Twisted.resEquiv (threefold φ).sheaf
      (face_inf φ i S hi).le (face_inf φ i S hi).ge).toAddEquiv.trans (structureCoordinates φ i h S hi t))

end CycleQ2HodgeTwistCubicFaces

namespace CycleQ2HodgeTwistAnchor

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2HodgeTwistCech CycleQ2HodgeTwistLocalization CycleQ2HodgeTwistFaces
open CycleQ2HodgeTwistCubicFaces CycleQ2HodgeTwistRatios CycleQ2HodgeTwistMonomials
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2SeedCechLocalization (coordinateLocalization localizationToLaurent)
open CycleQ2HodgeEulerChartBinding (chartEquiv_ratio_succAbove)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient)) (B : Finset (Fin 3))

variable [Nontrivial R]

open CycleQ2HodgeThreefoldTwist
open CycleQ2GeometricModuleLocalIso (addSheaf)

theorem face_frame_evaluation (S : Finset Vertex) (hi : i ∈ S) (k : ℤ)
    (s : Γ(twist φ k, S.inf (coordinateOpen φ))) :
    chartFrame φ k i (torus φ) (torus_le φ i)
      (CycleQ2GeometricSheafLocalIso.res (addSheaf (twist φ k)) (torus_le_face φ S) s) =
      evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) i ((twistCoordinates φ i h S hi k s).val) := by
  let E := face_inf φ i S hi
  let z := chartFrame φ k i _ (Finset.inf_le hi) s
  have hw : chartFrame φ k i (torus φ) (torus_le φ i)
      (CycleQ2GeometricSheafLocalIso.res (addSheaf (twist φ k)) (torus_le_face φ S) s) =
      res (threefold φ).sheaf (torus_le_face φ S) z :=
    CycleQ2HodgeAtlasLine.coordinate_restrict (cocycle φ k) i (Finset.inf_le hi) _ s
  rw [hw]
  have he := structure_face_evaluation φ i h S hi k (res (threefold φ).sheaf E.le z)
  exact (CycleQ2GeometricProjectiveCurve.Twisted.res_comp (threefold φ).sheaf E.le
    (torus_le_native φ i (inverted i S)) z).symm.trans he

end CycleQ2HodgeTwistAnchor
end

#print axioms CycleQ2HodgeTwistAnchor.face_frame_evaluation
