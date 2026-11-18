import Proposal.GeometricHodgeCotangentChartPresentation
import Proposal.GeometricHodgeEuler
import Mathlib.Tactic.LinearCombination

/-!
# The cotangent Euler and conormal maps on the original charts

Dropping the chosen weight-one slot identifies the radial-zero ambient
tuples with four arbitrary coefficients. The map to the actual Kähler
module is surjective, and its kernel consists exactly of multiples of the
original homogeneous gradient. These are chart assertions; gluing them
to the global cotangent sequence is a separate step.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerChart

open MvPolynomial
open scoped KaehlerDifferential

section Radial
variable {S : Type} [CommRing S] (p : Fin 5) (r : Fin 5 → S)

def radialRow : (Fin 5 → S) →ₗ[S] S := ∑ j : Fin 5, r j • LinearMap.proj j

theorem radialRow_apply (a : Fin 5 → S) : radialRow r a = ∑ j, r j * a j := by
  simp [radialRow]

def complete (v : Fin 4 → S) : Fin 5 → S :=
  p.insertNth (-(∑ j : Fin 4, r (p.succAbove j) * v j)) v

theorem complete_mem (hp : r p = 1) (v : Fin 4 → S) : radialRow r (complete p r v) = 0 := by
  rw [radialRow_apply, Fin.sum_univ_succAbove _ p]
  simp [complete,hp]

/-- A weight-one anchor completes the omitted coefficient uniquely. -/
def radialEquiv (hp : r p = 1) : (radialRow r).ker ≃ₗ[S] (Fin 4 → S) where
  toFun a j := a.val (p.succAbove j)
  invFun v := ⟨complete p r v, complete_mem p r hp v⟩
  left_inv a := by
    apply Subtype.ext
    funext j
    refine Fin.succAboveCases p ?_ (fun k => ?_) j
    · have ha := a.property
      change radialRow r a.val = 0 at ha
      rw [radialRow_apply, Fin.sum_univ_succAbove _ p, hp, one_mul] at ha
      change complete p r (fun k => a.val (p.succAbove k)) p = a.val p
      rw [complete, Fin.insertNth_apply_same]
      linear_combination -ha
    · simp [complete]
  right_inv v := by funext j; simp [complete]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Radial

open CycleQ2HodgeEuler
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeCotangentChartPresentation (coordinateMap gradientVector)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)

abbrev AmbientKernel := (radialRow (radial φ i)).ker

def drop : AmbientKernel φ i ≃ₗ[chart φ i] (Fin 4 → chart φ i) :=
  radialEquiv i.castSucc (radial φ i) (radial_self φ i)

def toCotangent : AmbientKernel φ i →ₗ[chart φ i] Ω[chart φ i⁄R] :=
  (coordinateMap (F φ i)).comp (drop φ i).toLinearMap

/-- This is the ordinary coordinate differential used in the anchor-change identity. -/
theorem toCotangent_apply (a : AmbientKernel φ i) :
    toCotangent φ i a = ∑ j : Fin 5,
      a.val j • KaehlerDifferential.D R (chart φ i) (coordinate φ i j) := by
  rw [Fin.sum_univ_succAbove _ i.castSucc]
  have hi : coordinate φ i i.castSucc = 1 := by simp [coordinate]
  rw [hi, Derivation.map_one_eq_zero, smul_zero, zero_add]
  change coordinateMap (F φ i) (drop φ i a) = _
  rw [CycleQ2HodgeCotangentChartPresentation.coordinateMap_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [coordinate, dehom_X_succAbove]
  rfl

theorem toCotangent_surjective : Function.Surjective (toCotangent φ i) := by
  intro z
  obtain ⟨v,hv⟩ := CycleQ2HodgeCotangentChartPresentation.coordinateMap_surjective (F φ i) z
  refine ⟨(drop φ i).symm v, ?_⟩
  change coordinateMap (F φ i) (drop φ i ((drop φ i).symm v)) = z
  rw [LinearEquiv.apply_symm_apply,hv]

/-- The full original gradient lies in the weighted Euler kernel. -/
def normal : AmbientKernel φ i := ⟨conePartial φ i, by
  change radialRow (radial φ i) (conePartial φ i) = 0
  rw [radialRow_apply]
  simpa only [mul_comm] using radial_equation φ i⟩

theorem drop_normal : drop φ i (normal φ i) = gradientVector (F φ i) := by
  funext j
  exact partial_succAbove φ i j

/-- Exactness of the actual affine conormal presentation, before any cohomology. -/
theorem toCotangent_eq_zero_iff (a : AmbientKernel φ i) :
    toCotangent φ i a = 0 ↔ ∃ c : chart φ i, c • normal φ i = a := by
  change coordinateMap (F φ i) (drop φ i a) = 0 ↔ _
  rw [CycleQ2HodgeCotangentChartPresentation.coordinateMap_eq_zero_iff]
  constructor
  · rintro ⟨c,hc⟩
    refine ⟨c,(drop φ i).injective ?_⟩
    rw [map_smul,drop_normal,hc]
  · rintro ⟨c,rfl⟩
    exact ⟨c,by rw [map_smul,drop_normal]⟩

end CycleQ2HodgeCotangentEulerChart
end

#print axioms CycleQ2HodgeCotangentEulerChart.radialEquiv
#print axioms CycleQ2HodgeCotangentEulerChart.toCotangent_apply
#print axioms CycleQ2HodgeCotangentEulerChart.toCotangent_surjective
#print axioms CycleQ2HodgeCotangentEulerChart.toCotangent_eq_zero_iff
