import Proposal.GeometricHodgeThreefold

/-!
# Binding the full sextic to the original incidence family

For an incidence parameter point, evaluating the independent sextic
coefficients returns its actual defining polynomial. Equality of the
homogeneous ideals identifies the two projective schemes, their structure
morphisms and all four weight-one coordinate opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefoldIncidence

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold CycleQ2IncidenceFamilyContainment
open CycleQ2GenericSexticGradient (CoeffRing universalF)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R : Type} [CommRing R] [Algebra ℂ R] (y : ParameterIndex → R)

def sexticEval : CoeffRing →+* R := (aeval (pointSextic y)).toRingHom

theorem equation_eq : equation (sexticEval y) = pointEquationF y := by
  rw [equation, universalF, map_fullInvariantPolynomial, pointEquationF, pointMap_familyF]
  congr 1
  funext j
  simp [sexticEval]

def nativeOpen (i : Fin 4) : (weightedThreefold y).Opens :=
  Proj.basicOpen (sexticGrade y) (Ideal.Quotient.mk (sexticIdeal y) (X i.castSucc))

private structure Model (R : Type) [CommRing R] where
  space : Scheme
  structureMap : space ⟶ Spec (CommRingCat.of R)
  opens : Fin 4 → space.Opens

private def model (I : {I : Ideal (MvPolynomial (Fin 5) R) // I.IsHomogeneous (PolynomialGrade R)}) :
    Model R := by
  let g := CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade (PolynomialGrade R) I.val
  letI : GradedRing g := CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing _ _ I.property
  exact ⟨Proj g, Proj.toSpecZero g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (g 0))),
    fun i => Proj.basicOpen g (Ideal.Quotient.mk I.val (X i.castSucc))⟩

private def fromFamily : Model R :=
  ⟨threefold (sexticEval y), toBase (sexticEval y), coordinateOpen (sexticEval y)⟩

private def fromPoint : Model R :=
  ⟨weightedThreefold y, weightedThreefoldToBase y, nativeOpen y⟩

private theorem model_eq : fromFamily y = fromPoint y := by
  let I := Ideal.span ({equation (sexticEval y)} : Set (MvPolynomial (Fin 5) R))
  have hi : I.IsHomogeneous (PolynomialGrade R) :=
    Ideal.homogeneous_span _ _ (by
      rintro p (rfl : p = equation (sexticEval y))
      exact ⟨6, equation_homogeneous _⟩)
  change model ⟨I, hi⟩ = model ⟨sexticIdeal y, sexticIdeal_homogeneous y⟩
  apply congrArg model
  apply Subtype.ext
  exact congrArg (fun p : MvPolynomial (Fin 5) R => Ideal.span {p}) (equation_eq y)

private def modelIso {a b : Model R} (h : a = b) : a.space ≅ b.space :=
  eqToIso (congrArg Model.space h)

def nativeIso : threefold (sexticEval y) ≅ weightedThreefold y := modelIso (model_eq y)

theorem nativeIso_overBase : (nativeIso y).hom ≫ weightedThreefoldToBase y = toBase (sexticEval y) := by
  have e {a b : Model R} (h : a = b) : (modelIso h).hom ≫ b.structureMap = a.structureMap := by
    subst b
    simp [modelIso]
  exact e (model_eq y)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4500 in
theorem nativeIso_preimage (i : Fin 4) :
    (nativeIso y).hom ⁻¹ᵁ nativeOpen y i = coordinateOpen (sexticEval y) i := by
  have e {a b : Model R} (h : a = b) : (modelIso h).hom ⁻¹ᵁ b.opens i = a.opens i := by
    subst b
    simp [modelIso]
  exact @e (fromFamily y) (fromPoint y) (model_eq y)

end CycleQ2GeometricHodgeThreefoldIncidence
end

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_overBase
#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_preimage
