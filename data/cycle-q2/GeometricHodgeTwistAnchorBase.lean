import Proposal.GeometricHodgeTwistMonomials

/-!
# Coefficients on the common open of the moving threefold

Degree-zero constants on the cone have the same projective fraction in
each weight-one frame. This gives one ring map of parameters for all
Laurent evaluations on the quadruple intersection.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistAnchor
open AlgebraicGeometry CategoryTheory TopologicalSpace HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeTwistRatios CycleQ2HodgeTwistCech
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev torus : (threefold φ).Opens := Finset.univ.inf (coordinateOpen φ)

theorem torus_le (i : Vertex) : torus φ ≤ coordinateOpen φ i :=
  Finset.inf_le (Finset.mem_univ i)

theorem torus_le_face (S : Finset Vertex) : torus φ ≤ S.inf (coordinateOpen φ) :=
  Finset.le_inf fun i _ => torus_le φ i

def frameCoefficient (i : Vertex) : R →+* Γ(threefold φ,torus φ) :=
  ((res (threefold φ).sheaf (torus_le φ i)).comp
    (Proj.awayToSection (grade φ) (coord φ i.castSucc)).hom).comp (chartCoefficient φ i)

def commonCoefficient : R →+* Γ(threefold φ,torus φ) := frameCoefficient φ 0

private theorem coefficient_fraction (i : Vertex) (c : R) :
    chartCoefficient φ i c =
      Away.mk (grade φ) (weightOne_mem_grade φ i) 0 (coefficient φ c).val (by
        simpa using (coefficient φ c).property) := by
  apply HomogeneousLocalization.val_injective
  rw [chartCoefficient_val, Away.val_mk]
  simp only [pow_zero]
  change algebraMap (cone φ) (Localization.Away (coord φ i.castSucc)) (quotient φ (MvPolynomial.C c)) =
    Localization.mk (quotient φ (MvPolynomial.C c)) 1
  exact (Localization.mk_one_eq_algebraMap _).symm

theorem frameCoefficient_eq (i : Vertex) : frameCoefficient φ i = commonCoefficient φ := by
  apply RingHom.ext
  intro c
  have h (a : Vertex) : frameCoefficient φ a c =
      normalized φ a (coefficient φ c).val (coefficient φ c).property (torus φ) (torus_le φ a) := by
    change (res _ _) ((Proj.awayToSection _ _) (chartCoefficient φ a c)) = _
    rw [coefficient_fraction]
    rfl
  rw [commonCoefficient, h i, h 0]
  simpa only [pow_zero, one_mul] using normalized_change φ i 0 (coefficient φ c).val
    (coefficient φ c).property (torus φ) (torus_le φ i) (torus_le φ 0)

end CycleQ2HodgeTwistAnchor
end

#print axioms CycleQ2HodgeTwistAnchor.frameCoefficient_eq
