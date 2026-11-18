import Proposal.ConicFlow
import Proposal.FermatParameters
import Proposal.DeformedQuotient
import HodgeComputer.Constructions.HoldoutCover.PolynomialFieldMap
import Mathlib.RingTheory.MvPolynomial.Localization

/-!
Dominance of the replacement family. The three independent endpoint
parameters survive coefficient localization to the Fermat function field;
the anchored coordinate x1=t supplies the fourth coordinate. The argument
uses fqlx's polynomial-family injectivity and monic-root embedding lemmas.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedConic
open HoldoutConstruction Polynomial

def endpointEmbedding : MvPolynomial (Fin 3) BaseField →+* CoefficientField :=
  MvPolynomial.eval₂Hom (algebraMap BaseField CoefficientField) scalarParameter

lemma endpointEmbedding_map (p : ParameterRing) :
    endpointEmbedding (MvPolynomial.map (algebraMap FermatRing BaseField) p)=
      algebraMap ParameterRing CoefficientField p := by
  have h : endpointEmbedding.comp (MvPolynomial.map (algebraMap FermatRing BaseField))=
      algebraMap ParameterRing CoefficientField := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,MvPolynomial.map_C,endpointEmbedding,MvPolynomial.eval₂Hom_C]
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    · intro i
      simp [endpointEmbedding,scalarParameter,parameter]
  exact congrArg (fun f : ParameterRing →+* CoefficientField => f p) h

lemma endpointEmbedding_injective : Function.Injective endpointEmbedding := by
  let M : Submonoid ParameterRing := (nonZeroDivisors FermatRing).map MvPolynomial.C
  letI : Algebra ParameterRing (MvPolynomial (Fin 3) BaseField) := MvPolynomial.algebraMvPolynomial
  letI : IsLocalization M (MvPolynomial (Fin 3) BaseField) := MvPolynomial.isLocalization _ _
  apply IsLocalization.injective_of_map_algebraMap_zero
    (S := MvPolynomial (Fin 3) BaseField) (M := M) endpointEmbedding
  intro p hp
  change endpointEmbedding (MvPolynomial.map (algebraMap FermatRing BaseField) p)=0 at hp
  rw [endpointEmbedding_map] at hp
  have hz : p=0 := parameterField_algebraMap_injective (hp.trans (map_zero _).symm)
  simp [hz]

def remainingCurveMap : MvPolynomial (Fin 3) BaseField →+* Polynomial CoefficientField :=
  MvPolynomial.eval₂Hom (C.comp (algebraMap BaseField CoefficientField))
    ![conicCurve 2,conicCurve 3,conicCurve 4]
lemma remainingCurveMap_constant : Polynomial.constantCoeff.comp remainingCurveMap=endpointEmbedding := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [remainingCurveMap,endpointEmbedding]
  · intro i
    simp only [RingHom.comp_apply,remainingCurveMap,endpointEmbedding,MvPolynomial.eval₂Hom_X',
      Polynomial.constantCoeff_apply]
    have hi : ![conicCurve 2,conicCurve 3,conicCurve 4] i=conicCurve i.succ.succ := by
      fin_cases i <;> rfl
    rw [hi,conicCurve_endpoint]

def targetCoefficientMap : MvPolynomial (Fin 4) BaseField →+* Polynomial CoefficientField :=
  (Polynomial.eval₂RingHom remainingCurveMap X).comp (MvPolynomial.finSuccEquiv BaseField 3).toRingHom
lemma targetCoefficientMap_injective : Function.Injective targetCoefficientMap := by
  have hconst : Function.Injective (Polynomial.constantCoeff.comp remainingCurveMap) := by
    rw [remainingCurveMap_constant]
    exact endpointEmbedding_injective
  have h := polynomial_family_injective remainingCurveMap hconst 1 one_ne_zero
  simp only [Polynomial.C_1,one_mul] at h
  exact h.comp (MvPolynomial.finSuccEquiv BaseField 3).injective
@[simp] lemma targetCoefficientMap_C (r : BaseField) :
    targetCoefficientMap (MvPolynomial.C r)=C (algebraMap BaseField CoefficientField r) := by
  simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_apply,remainingCurveMap]
@[simp] lemma targetCoefficientMap_X (i : Fin 4) :
    targetCoefficientMap (MvPolynomial.X i)=conicCurve i.succ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [targetCoefficientMap,MvPolynomial.finSuccEquiv_X_zero,conicCurve_time]
  · change (Polynomial.eval₂RingHom remainingCurveMap X)
      (MvPolynomial.finSuccEquiv BaseField 3 (MvPolynomial.X j.succ))=_
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ remainingCurveMap X (C (MvPolynomial.X j))=_
    rw [Polynomial.eval₂_C]
    simp only [remainingCurveMap,MvPolynomial.eval₂Hom_X']
    fin_cases j <;> rfl

end DeformedConic
#print axioms DeformedConic.targetCoefficientMap_injective
