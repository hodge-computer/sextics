import Proposal.GeometricHodgeTwistFaces
import Proposal.GeometricHodgeTwistCech
import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricHodgeEulerChartBinding
import Proposal.GeometricHodgeThreefoldCubicChart
import Proposal.GeometricHodgeThreefoldCubicRestriction

/-!
# Native rings of the localized moving cubic

The projective product open is a principal localization inside its chosen
anchor chart. The chart isomorphism sends its denominator to the product
of the other inverted base coordinates. This identifies the sections on
the projective face with a localization of the cubic chart ring.

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
open CycleQ2HodgeTwistCech
open CycleQ2SeedCechLocalization (baseProduct)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Vertex)
variable (h : IsUnit (φ vertexCoefficient))

def stageEquiv : ChartRing φ i ≃ₐ[R] Stage φ i h :=
  (chartEquiv φ i).trans (chartEquivAdjoinRoot φ i h)

@[simp] theorem stageEquiv_variable (q : Fin 3) :
    stageEquiv φ i h (CycleQ2HodgeEulerChartBinding.ratio φ i (i.succAbove q).castSucc) =
      algebraMap (Base R) (Stage φ i h) (X q) := by
  have he : i.castSucc.succAbove q.castSucc = (i.succAbove q).castSucc := by
    fin_cases i <;> fin_cases q <;> decide
  rw [← he]
  exact (congrArg (chartEquivAdjoinRoot φ i h) (chartEquiv_ratio_succAbove φ i q.castSucc)).trans
    (chartEquivAdjoinRoot_weightOne φ i h q)

private def polyProduct (B : Finset (Fin 3)) : MvPolynomial (Fin 5) R :=
  ∏ q ∈ B, X (i.succAbove q).castSucc

private theorem polyProduct_homogeneous (B : Finset (Fin 3)) :
    (polyProduct (R := R) i B).IsWeightedHomogeneous CycleQ2GeometricIncidenceProj.geometricWeight B.card := by
  simpa [polyProduct] using
    (MvPolynomial.IsWeightedHomogeneous.prod B (fun q => (X (i.succAbove q).castSucc : MvPolynomial (Fin 5) R))
      (fun _ => 1) (w := CycleQ2GeometricIncidenceProj.geometricWeight) fun q _ => by
        simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using
          (isWeightedHomogeneous_X R CycleQ2GeometricIncidenceProj.geometricWeight (i.succAbove q).castSucc))

theorem stageEquiv_denominator (B : Finset (Fin 3)) :
    stageEquiv φ i h (denominator φ i B) = algebraMap (Base R) (Stage φ i h) (baseProduct R B) := by
  have he : denominator φ i B = fraction φ i B.card (polyProduct i B) (polyProduct_homogeneous i B) := by
    apply HomogeneousLocalization.val_injective
    simp only [denominator, Away.isLocalizationElem, fraction, Away.val_mk, pow_one,
      polyProduct, map_prod, coord, product, faceVertex]
  rw [he]
  change chartEquivAdjoinRoot φ i h (chartEquiv φ i _) = _
  rw [chartEquiv_fraction]
  simp only [polyProduct, baseProduct, map_prod]
  apply Finset.prod_congr rfl
  intro q _
  have hq : i.castSucc.succAbove q.castSucc = (i.succAbove q).castSucc := by
    fin_cases i <;> fin_cases q <;> decide
  rw [← hq, dehom_X_succAbove, chartEquivAdjoinRoot_weightOne]

variable (B : Finset (Fin 3))
abbrev powers := Submonoid.powers (baseProduct R B)

private theorem denominator_powers :
    (Submonoid.powers (denominator φ i B)).map (stageEquiv φ i h).toRingEquiv.toMonoidHom =
      Algebra.algebraMapSubmonoid (Stage φ i h) (powers (R := R) B) := by
  change _ = Submonoid.map _ (Submonoid.powers _)
  rw [Submonoid.map_powers, Submonoid.map_powers]
  exact congrArg Submonoid.powers (stageEquiv_denominator φ i h B)

/-- The original homogeneous localization is the localization of the actual moving cubic. -/
def faceStage : FaceRing φ i B ≃+* AwayStage φ i h (powers (R := R) B) := by
  letI := (toFace φ i B).toAlgebra
  letI := face_localization φ i B
  exact IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (denominator φ i B))
    (T := Algebra.algebraMapSubmonoid (Stage φ i h) (powers (R := R) B))
    (FaceRing φ i B) (AwayStage φ i h (powers (R := R) B))
    (stageEquiv φ i h).toRingEquiv (denominator_powers φ i h B)

@[simp] theorem faceStage_toFace (p : ChartRing φ i) :
    faceStage φ i h B (toFace φ i B p) =
      algebraMap (Stage φ i h) (AwayStage φ i h (powers (R := R) B)) (stageEquiv φ i h p) := by
  letI := (toFace φ i B).toAlgebra
  letI := face_localization φ i B
  exact IsLocalization.ringEquivOfRingEquiv_eq (M := Submonoid.powers (denominator φ i B))
    (T := Algebra.algebraMapSubmonoid (Stage φ i h) (powers (R := R) B))
    (S := FaceRing φ i B) (Q := AwayStage φ i h (powers (R := R) B))
    (j := (stageEquiv φ i h).toRingEquiv) (denominator_powers φ i h B) p

end CycleQ2HodgeTwistCubicFaces
end

#print axioms CycleQ2HodgeTwistCubicFaces.faceStage_toFace
