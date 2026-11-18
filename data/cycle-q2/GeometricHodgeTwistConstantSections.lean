import Proposal.GeometricHodgeTwistTorusChart

/-!
# The sole Laurent coefficient of a global degree-zero section

With no poles and weighted degree zero, the cubic generator has exponent
zero and all four weight-one exponents vanish. Thus the actual global
structure-sheaf coordinates are determined by one original coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeTwistConstantSections

open CycleQ2HodgeTwistCech

private theorem allowed_zero_iff (j : Fin 3) (e : Exp) :
    Allowed 0 ∅ j e ↔ j = 0 ∧ e = 0 := by
  constructor
  · intro h
    have he (i : Vertex) : 0 ≤ e i := by
      by_contra hn
      have hm := h.2 i (lt_of_not_ge hn)
      simpa using hm
    have hs : 0 ≤ ∑ i : Vertex, e i := Finset.sum_nonneg (fun i _ => he i)
    have hw := h.1
    have hj : j = 0 := Fin.ext (by omega)
    have hsum : ∑ i : Vertex, e i = 0 := by
      have hw := h.1
      have hv : (j.val : ℤ) = 0 := by rw [hj]; rfl
      omega
    refine ⟨hj, funext fun i => ?_⟩
    have hi : e i ≤ ∑ k : Vertex, e k :=
      Finset.single_le_sum (fun k _ => he k) (Finset.mem_univ i)
    change e i = 0
    rw [hsum] at hi
    exact le_antisymm hi (he i)
  · rintro ⟨rfl,rfl⟩
    simp [Allowed]

variable {A : Type} [AddCommGroup A]

def constant (a : A) : sections A 0 ∅ := by
  classical
  refine ⟨fun j => if j = 0 then Finsupp.single 0 a else 0, ?_⟩
  intro j e hn
  by_cases hj : j = 0
  · subst j
    have he : e ≠ 0 := by
      intro h
      exact hn ((allowed_zero_iff 0 e).mpr ⟨rfl,h⟩)
    simp [he]
  · simp [hj]

def coefficient : sections A 0 ∅ →+ A where
  toFun p := p.val 0 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coefficient_constant (a : A) : coefficient (constant a) = a := by
  change (constant a).val 0 0 = a
  simp [constant]

theorem constant_coefficient (p : sections A 0 ∅) : constant (coefficient p) = p := by
  classical
  apply Subtype.ext
  funext j
  apply Finsupp.ext
  intro e
  by_cases hj : j = 0
  · subst j
    by_cases he : e = 0
    · subst e
      exact (show (constant (coefficient p)).val 0 0 = coefficient p from
        coefficient_constant (coefficient p)).trans (by rfl)
    · have hp : p.val 0 e = 0 := p.property 0 e ((allowed_zero_iff 0 e).not.mpr (by simp [he]))
      simp [constant, he, hp]
  · have hp : p.val j e = 0 := p.property j e ((allowed_zero_iff j e).not.mpr (by simp [hj]))
    simp [constant, hj, hp]

/-- The actual polynomial normal forms in weighted degree zero have one coefficient. -/
def degreeZeroEquiv : sections A 0 ∅ ≃+ A :=
  AddEquiv.ofBijective coefficient ⟨fun p q h =>
    (constant_coefficient p).symm.trans ((congrArg constant h).trans (constant_coefficient q)),
      fun a => ⟨constant a, coefficient_constant a⟩⟩

open CategoryTheory AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen vertexCoefficient)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2HodgeTwistTorusChart (structureLaurentSections)

/-- The original structure-sheaf global sections are determined by this coefficient.
This assertion includes the actual Laurent/gluing comparison; it does not identify
an arbitrary additive equivalence with a ring or module structure. -/
def structureSections {R : Type} [CommRing R] [Nontrivial R]
    (φ : CoeffRing →+* R) (h : IsUnit (φ vertexCoefficient)) :
    CycleQ2InjectiveCech.Sections (structureAdditiveSheaf (threefold φ)) ⊤ ≃+ R :=
  (CycleQ2HodgeTwistGlobal.globalCoordinates (structureLaurentSections φ h)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)).trans degreeZeroEquiv

end CycleQ2HodgeTwistConstantSections
end

#print axioms CycleQ2HodgeTwistConstantSections.constant_coefficient
#print axioms CycleQ2HodgeTwistConstantSections.structureSections
