import Proposal.GeometricIncidenceFamilyContainment

/-!
# Coefficient specialization of the weighted sextic hypersurface

An exact identity between the two sextic equations defines a morphism of
their weighted projective hypersurfaces over the specified coefficient
map. The homogeneous ring map fixes each of the five geometric variables.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldCoefficientMap

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2GeometricIncidenceProj
  CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart CycleQ2IncidenceImageLine
  CycleQ2IncidenceFamilyContainment

variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]
    (φ : R →+* S) (y : ParameterIndex → R) (u : ParameterIndex → S)
    (hF : map φ (pointEquationF y) = pointEquationF u)

def graded : sexticGrade y →+*ᵍ sexticGrade u where
  toRingHom := Ideal.Quotient.lift (sexticIdeal y)
    ((Ideal.Quotient.mk _).comp (map φ)) <| by
      change Ideal.span {pointEquationF y} ≤ RingHom.ker _
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change Ideal.Quotient.mk (sexticIdeal u) (map φ (pointEquationF y)) = 0
      rw [hF, weightedThreefold_equation_zero]
  map_mem := by
    intro n q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨map φ p, (polynomialCoefficientMap φ).map_mem hp, rfl⟩

theorem irrelevant_le :
    HomogeneousIdeal.irrelevant (sexticGrade u) ≤
      (HomogeneousIdeal.irrelevant (sexticGrade y)).map (graded φ y u hF) := by
  let J := ((HomogeneousIdeal.irrelevant (sexticGrade y)).map (graded φ y u hF)).toIdeal
  have hvars : Ideal.span (Set.range (X : Fin 5 → MvPolynomial (Fin 5) S)) ≤
      Ideal.comap (Ideal.Quotient.mk (sexticIdeal u)) J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hx := HomogeneousIdeal.mem_irrelevant_of_mem (sexticGrade y) (geometricWeight_pos j)
      (show Ideal.Quotient.mk (sexticIdeal y) (X j) ∈ sexticGrade y (geometricWeight j) from
        ⟨X j, isWeightedHomogeneous_X R geometricWeight j, rfl⟩)
    have hc := Ideal.mem_map_of_mem (graded φ y u hF) hx
    change Ideal.Quotient.mk (sexticIdeal u) (map φ (X j)) ∈ J at hc
    change Ideal.Quotient.mk (sexticIdeal u) (X j) ∈ J
    simpa only [map_X] using hc
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (sexticGrade u)).mpr
  intro n hn z hz
  obtain ⟨p, hp, rfl⟩ := hz
  exact hvars (homogeneous_mem_variableIdeal hn hp)

def morphism : weightedThreefold u ⟶ weightedThreefold y :=
  Proj.map (graded φ y u hF) (irrelevant_le φ y u hF)

theorem morphism_overBase :
    morphism φ y u hF ≫ weightedThreefoldToBase y =
      weightedThreefoldToBase u ≫ Spec.map (CommRingCat.ofHom φ) := by
  unfold morphism weightedThreefoldToBase
  rw [← Category.assoc, projectiveMap_toSpecZero, Category.assoc, ← Spec.map_comp,
    Category.assoc, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  change Ideal.Quotient.mk (sexticIdeal u) (map φ (C c)) = Ideal.Quotient.mk _ (C (φ c))
  rw [map_C]

end CycleQ2ThreefoldCoefficientMap
end

#print axioms CycleQ2ThreefoldCoefficientMap.morphism_overBase
