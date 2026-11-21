import Proposal.GeometricHodgeEulerSheaf

/-!
# The actual negative-twist cotangent Euler complex

The weighted coordinate row maps the five negative twists to O(0).
Its sheaf kernel is the ambient cotangent object. The original gradient
defines the conormal map from O(-6) into that kernel, by the weighted
Euler equation on the actual scheme. No intrinsic cotangent comparison
or cohomology conclusion is assumed in this construction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerSheaf

open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeAtlasLine CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEulerSheaf (partialValue partial_mem normalized_euler multiply_component)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev pieces := fun j : Fin 5 => twist φ (-(geometricWeight j : ℤ))
abbrev raw := ∏ᶜ pieces φ

def eulerComponent (j : Fin 5) : pieces φ j ⟶ twist φ 0 :=
  geometricWeight j • multiply φ (coord φ j) (coord_mem_grade φ j) _ 0 (by simp)

def eulerMap : raw φ ⟶ twist φ 0 := ∑ j, Pi.π (pieces φ) j ≫ eulerComponent φ j

abbrev ambient := kernel (eulerMap φ)

private theorem normalWeight (j : Fin 5) :
    ((6 - geometricWeight j : ℕ) : ℤ) + (-6) = -(geometricWeight j : ℤ) := by
  fin_cases j <;> decide

def normalComponent (j : Fin 5) : twist φ (-6) ⟶ pieces φ j :=
  multiply φ (partialValue φ j) (partial_mem φ j) (-6) _ (normalWeight j)

def normalRaw : twist φ (-6) ⟶ raw φ := Pi.lift (normalComponent φ)

private def ev {Y : Scheme.{0}} {M N : Y.Modules} (V : Y.Opens) (s : Γ(M,V)) : (M ⟶ N) →+ Γ(N,V) where
  toFun f := f.app V s
  map_zero' := rfl
  map_add' _ _ := rfl

private def componentAdd (k : ℤ) (i : Fin 4) (V : (threefold φ).Opens) :
    Γ(twist φ k,V) →+ Γ(threefold φ,V ⊓ U φ i) := ((projection (cocycle φ k) i).app V).hom

theorem normal_component (j : Fin 5) (i : Fin 4) (V : (threefold φ).Opens)
    (s : Γ(twist φ (-6),V)) :
    component (cocycle φ (-(geometricWeight j : ℤ))) i V
        ((Pi.π (pieces φ) j).app V ((normalRaw φ).app V s)) =
      normalized φ i (partialValue φ j) (partial_mem φ j) _ inf_le_right *
        component (cocycle φ (-6)) i V s := by
  change component _ i V ((normalRaw φ ≫ Pi.π (pieces φ) j).app V s) = _
  rw [normalRaw, Pi.lift_π]
  exact multiply_component φ (partialValue φ j) (partial_mem φ j) (-6) _ (normalWeight j) i V s

theorem euler_component (i : Fin 4) (V : (threefold φ).Opens) (s : Γ(raw φ,V)) :
    component (cocycle φ 0) i V ((eulerMap φ).app V s) = ∑ j : Fin 5,
      (geometricWeight j : Γ(threefold φ,V ⊓ U φ i)) *
        normalized φ i (coord φ j) (coord_mem_grade φ j) _ inf_le_right *
          component (cocycle φ (-(geometricWeight j : ℤ))) i V ((Pi.π (pieces φ) j).app V s) := by
  change (componentAdd φ 0 i V) (ev V s (∑ j, Pi.π (pieces φ) j ≫ eulerComponent φ j)) = _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (componentAdd φ 0 i V) (ev V ((Pi.π (pieces φ) j).app V s) (geometricWeight j • _)) = _
  rw [map_nsmul,map_nsmul,nsmul_eq_mul]
  change (geometricWeight j : Γ(threefold φ,V ⊓ U φ i)) *
    component (cocycle φ 0) i V
      ((multiply φ (coord φ j) (coord_mem_grade φ j) _ 0 (by simp)).app V
        ((Pi.π (pieces φ) j).app V s)) = _
  rw [multiply_component,mul_assoc]

theorem euler_frame (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(raw φ,V)) :
    chartFrame φ 0 i V hi ((eulerMap φ).app V s) = ∑ j : Fin 5,
      (geometricWeight j : Γ(threefold φ,V)) * normalized φ i (coord φ j) (coord_mem_grade φ j) V hi *
        chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((Pi.π (pieces φ) j).app V s) := by
  change (chartFrame φ 0 i V hi).toAddMonoidHom (ev V s (∑ j, Pi.π (pieces φ) j ≫ eulerComponent φ j)) = _
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (chartFrame φ 0 i V hi).toAddMonoidHom
    (ev V ((Pi.π (pieces φ) j).app V s) (geometricWeight j • _)) = _
  rw [map_nsmul,map_nsmul,nsmul_eq_mul]
  change (geometricWeight j : Γ(threefold φ,V)) *
    chartFrame φ 0 i V hi
      ((multiply φ (coord φ j) (coord_mem_grade φ j) _ 0 (by simp)).app V
        ((Pi.π (pieces φ) j).app V s)) = _
  rw [multiply_frame,mul_assoc]

theorem normal_euler : normalRaw φ ≫ eulerMap φ = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  let V := O.unop
  change (eulerMap φ).app V ((normalRaw φ).app V s) = 0
  apply component_injective (cocycle φ 0) V
  intro i
  rw [euler_component]
  simp_rw [normal_component, ← mul_assoc _ _ (component (cocycle φ (-6)) i V s)]
  change _ = (componentAdd φ 0 i V) 0
  rw [map_zero, ← Finset.sum_mul]
  have he : (∑ j : Fin 5,
      (geometricWeight j : Γ(threefold φ,V ⊓ U φ i)) *
        normalized φ i (coord φ j) (coord_mem_grade φ j) _ inf_le_right *
          normalized φ i (partialValue φ j) (partial_mem φ j) _ inf_le_right) = 0 := by
    calc
      _ = ∑ j : Fin 5,
          normalized φ i (partialValue φ j) (partial_mem φ j) _ inf_le_right *
            ((geometricWeight j : Γ(threefold φ,V ⊓ U φ i)) *
              normalized φ i (coord φ j) (coord_mem_grade φ j) _ inf_le_right) := by
        apply Finset.sum_congr rfl
        intro j _
        exact mul_comm _ _
      _ = 0 := normalized_euler φ i (V ⊓ U φ i) inf_le_right
  rw [he,zero_mul]

/-- The original conormal map is a morphism into the genuine sheaf kernel. -/
def conormalMap : twist φ (-6) ⟶ ambient φ :=
  kernel.lift (eulerMap φ) (normalRaw φ) (normal_euler φ)

theorem conormalMap_ι : conormalMap φ ≫ kernel.ι (eulerMap φ) = normalRaw φ :=
  kernel.lift_ι _ _ _

def pieceMap (j : Fin 5) : ambient φ ⟶ pieces φ j := kernel.ι (eulerMap φ) ≫ Pi.π (pieces φ) j

def coefficient (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) (j : Fin 5) : Γ(threefold φ,V) :=
  chartFrame φ (-(geometricWeight j : ℤ)) i V hi ((pieceMap φ j).app V a)

/-- Every section of this actual sheaf kernel has weighted radial coefficient zero. -/
theorem coefficient_radial_zero (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (a : Γ(ambient φ,V)) :
    ∑ j : Fin 5, (geometricWeight j : Γ(threefold φ,V)) *
      normalized φ i (coord φ j) (coord_mem_grade φ j) V hi * coefficient φ i V hi a j = 0 := by
  have hz : (eulerMap φ).app V ((kernel.ι (eulerMap φ)).app V a) = 0 := by
    change (kernel.ι (eulerMap φ) ≫ eulerMap φ).app V a = 0
    rw [kernel.condition]
    rfl
  have hf := congrArg (chartFrame φ 0 i V hi) hz
  rw [euler_frame,map_zero] at hf
  exact hf

end CycleQ2HodgeCotangentEulerSheaf
end

#print axioms CycleQ2HodgeCotangentEulerSheaf.normal_euler
#print axioms CycleQ2HodgeCotangentEulerSheaf.conormalMap_ι
#print axioms CycleQ2HodgeCotangentEulerSheaf.coefficient_radial_zero
