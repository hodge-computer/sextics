import Proposal.GeometricHodgeTwistMultiplication
import Proposal.GeometricHodgeEulerSheafCoefficients

/-!
# The Euler and normal maps of the moving weighted threefold

The weighted coordinate sections define the radial map into the five
twists. The derivatives of the actual sextic define its normal map. The
composition of these morphisms of sheaves of modules vanishes by the
weighted Euler formula on every one of the original projective charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerSheaf

open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeAtlasLine CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev pieces := fun j : Fin 5 => twist φ (geometricWeight j : ℤ)
abbrev raw := ∏ᶜ pieces φ

def radialComponent (j : Fin 5) : twist φ 0 ⟶ pieces φ j :=
  geometricWeight j • multiply φ (coord φ j) (coord_mem_grade φ j) 0 _ (by simp)

def radialMap : twist φ 0 ⟶ raw φ := Pi.lift (radialComponent φ)

private theorem normalWeight (j : Fin 5) :
    ((6 - geometricWeight j : ℕ) : ℤ) + (geometricWeight j : ℤ) = 6 := by fin_cases j <;> decide

def normalComponent (j : Fin 5) : pieces φ j ⟶ twist φ 6 :=
  multiply φ (partialValue φ j) (partial_mem φ j) _ 6 (normalWeight j)

def normalMap : raw φ ⟶ twist φ 6 := ∑ j, Pi.π (pieces φ) j ≫ normalComponent φ j

private def ev {Y : Scheme.{0}} {M N : Y.Modules} (V : Y.Opens) (s : Γ(M,V)) : (M ⟶ N) →+ Γ(N,V) where
  toFun f := f.app V s
  map_zero' := rfl
  map_add' _ _ := rfl

private def componentAdd (k : ℤ) (i : Fin 4) (V : (threefold φ).Opens) :
    Γ(twist φ k,V) →+ Γ(threefold φ,V ⊓ U φ i) := ((projection (cocycle φ k) i).app V).hom

theorem multiply_component {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (k m : ℤ) (hm : n + k = m)
    (i : Fin 4) (V : (threefold φ).Opens) (s : Γ(twist φ k,V)) :
    component (cocycle φ m) i V ((multiply φ p hp k m hm).app V s) =
      normalized φ i p hp (V ⊓ U φ i) inf_le_right * component (cocycle φ k) i V s := by
  change component (cocycle φ m) i V (product φ n k m hm V (homogeneousSection φ p hp V) s) = _
  rw [product_component]
  change component _ i V (pack _ _ _ _) * _ = _
  rw [component_pack]

theorem radial_component (j : Fin 5) (i : Fin 4) (V : (threefold φ).Opens) (s : Γ(twist φ 0,V)) :
    component (cocycle φ (geometricWeight j)) i V ((Pi.π (pieces φ) j).app V ((radialMap φ).app V s)) =
      (geometricWeight j : Γ(threefold φ,V ⊓ U φ i)) *
      normalized φ i (coord φ j) (coord_mem_grade φ j) _ inf_le_right *
      component (cocycle φ 0) i V s := by
  change component _ i V ((radialMap φ ≫ Pi.π (pieces φ) j).app V s) = _
  rw [radialMap, Pi.lift_π, radialComponent]
  change (componentAdd φ _ i V) (ev V s (geometricWeight j • _)) = _
  rw [map_nsmul, map_nsmul, nsmul_eq_mul]
  change _ * component (cocycle φ (geometricWeight j)) i V
    ((multiply φ (coord φ j) (coord_mem_grade φ j) 0 _ (by simp)).app V s) = _
  rw [multiply_component, mul_assoc]

theorem normal_component (i : Fin 4) (V : (threefold φ).Opens) (s : Γ(raw φ,V)) :
    component (cocycle φ 6) i V ((normalMap φ).app V s) = ∑ j : Fin 5,
      normalized φ i (partialValue φ j) (partial_mem φ j) (V ⊓ U φ i) inf_le_right *
        component (cocycle φ (geometricWeight j)) i V ((Pi.π (pieces φ) j).app V s) := by
  change (componentAdd φ 6 i V) (ev V s (∑ j, Pi.π (pieces φ) j ≫ normalComponent φ j)) = _
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun j _ =>
    multiply_component φ (partialValue φ j) (partial_mem φ j) _ 6 (normalWeight j) i V ((Pi.π (pieces φ) j).app V s)

theorem normal_frame (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(raw φ,V)) :
    chartFrame φ 6 i V hi ((normalMap φ).app V s) = ∑ j : Fin 5,
      normalized φ i (partialValue φ j) (partial_mem φ j) V hi *
        chartFrame φ (geometricWeight j) i V hi ((Pi.π (pieces φ) j).app V s) := by
  change chartFrame φ 6 i V hi (ev V s (∑ j, Pi.π (pieces φ) j ≫ normalComponent φ j)) = _
  rw [map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact multiply_frame φ (partialValue φ j) (partial_mem φ j) _ 6 (normalWeight j) i V hi ((Pi.π (pieces φ) j).app V s)

theorem radial_normal : radialMap φ ≫ normalMap φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := O.unop
  change (normalMap φ).app V ((radialMap φ).app V s) = 0
  apply component_injective (cocycle φ 6) V
  intro i
  rw [normal_component]
  simp_rw [radial_component, ← mul_assoc _ _ (component (cocycle φ 0) i V s)]
  change _ = (componentAdd φ 6 i V) 0
  rw [map_zero]
  rw [← Finset.sum_mul, normalized_euler, zero_mul]

end CycleQ2HodgeEulerSheaf
end

#print axioms CycleQ2HodgeEulerSheaf.radial_normal
