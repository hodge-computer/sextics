import Proposal.GeometricHodgeThreefoldTwist

/-!
# Multiplication between twists of the original moving threefold

Sections multiply in every one of the four coordinate frames. Their transition
powers add, so this descends to the sheaf kernel. Multiplication by a fixed
homogeneous element is a morphism of sheaves of modules, with its ordinary
normalized polynomial as the coefficient on each frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeThreefoldTwist

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold (threefold grade cone)
open CycleQ2HodgeAtlasLine CycleQ2HodgeTwistRatios
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

private theorem component_restrict (d : ℤ) (i : Fin 4) {V W : (threefold φ).Opens} (hW : W ≤ V)
    (s : Γ(twist φ d,V)) :
    component (cocycle φ d) i W (moduleRes (twist φ d) hW s) =
      restrictRing (X := threefold φ) (inf_le_inf_right _ hW) (component (cocycle φ d) i V s) :=
  (moduleRes_app (projection (cocycle φ d) i) hW s).symm

def product (k l m : ℤ) (hm : k + l = m) (V : (threefold φ).Opens)
    (s : Γ(twist φ k,V)) (t : Γ(twist φ l,V)) : Γ(twist φ m,V) := by
  refine pack (cocycle φ m) V
    (fun i => component (cocycle φ k) i V s * component (cocycle φ l) i V t) ?_
  intro i j
  rw [map_mul, map_mul, component_compatible _ V s i j, component_compatible _ V t i j]
  change ((transition φ i j _ _ _ ^ k : Γ(threefold φ,_)ˣ).val * _) *
      ((transition φ i j _ _ _ ^ l : Γ(threefold φ,_)ˣ).val * _) =
    (transition φ i j _ _ _ ^ m : Γ(threefold φ,_)ˣ).val * _
  rw [← hm, zpow_add, Units.val_mul]
  ring

theorem product_component (k l m : ℤ) (hm : k + l = m) (i : Fin 4) (V : (threefold φ).Opens)
    (s : Γ(twist φ k,V)) (t : Γ(twist φ l,V)) :
    component (cocycle φ m) i V (product φ k l m hm V s t) =
      component (cocycle φ k) i V s * component (cocycle φ l) i V t :=
  component_pack ..

theorem product_frame (k l m : ℤ) (hm : k + l = m) (i : Fin 4)
    (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(twist φ k,V)) (t : Γ(twist φ l,V)) :
    chartFrame φ m i V hi (product φ k l m hm V s t) =
      chartFrame φ k i V hi s * chartFrame φ l i V hi t := by
  change restrictRing (X := threefold φ) _ (component _ i V _) =
    restrictRing (X := threefold φ) _ (component _ i V _) * restrictRing (X := threefold φ) _ (component _ i V _)
  rw [product_component, map_mul]

theorem product_restrict (k l m : ℤ) (hm : k + l = m) {V W : (threefold φ).Opens} (hW : W ≤ V)
    (s : Γ(twist φ k,V)) (t : Γ(twist φ l,V)) :
    moduleRes _ hW (product φ k l m hm V s t) =
      product φ k l m hm W (moduleRes _ hW s) (moduleRes _ hW t) := by
  apply component_injective (cocycle φ m) W
  intro i
  let r := restrictRing (X := threefold φ) (inf_le_inf_right (U φ i) hW)
  calc
    _ = r (component (cocycle φ m) i V (product φ k l m hm V s t)) :=
      component_restrict φ m i hW _
    _ = r (component (cocycle φ k) i V s * component (cocycle φ l) i V t) :=
      congrArg r (product_component φ k l m hm i V s t)
    _ = r (component (cocycle φ k) i V s) * r (component (cocycle φ l) i V t) := map_mul r _ _
    _ = component (cocycle φ k) i W (moduleRes (twist φ k) hW s) *
      component (cocycle φ l) i W (moduleRes (twist φ l) hW t) :=
      congrArg₂ (·*·) (component_restrict φ k i hW s).symm (component_restrict φ l i hW t).symm
    _ = _ := (product_component φ k l m hm i W _ _).symm

def multiplySection {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (k m : ℤ) (hm : n + k = m)
    (V : (threefold φ).Opens) : Γ(twist φ k,V) →ₗ[Γ(threefold φ,V)] Γ(twist φ m,V) where
  toFun s := product φ n k m hm V (homogeneousSection φ p hp V) s
  map_add' s t := by
    apply component_injective (cocycle φ m) V
    intro i
    rw [component_add, product_component, product_component, product_component, component_add, mul_add]
  map_smul' a s := by
    apply component_injective (cocycle φ m) V
    intro i
    change component _ i V _ = component _ i V (a • _)
    rw [component_smul, product_component, product_component, component_smul]
    ring

def multiply {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (k m : ℤ) (hm : n + k = m) :
    twist φ k ⟶ twist φ m where
  val.app O := ModuleCat.ofHom (multiplySection φ p hp k m hm O.unop)
  val.naturality {O P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change product φ n k m hm P.unop (homogeneousSection φ p hp P.unop)
        (moduleRes _ (leOfHom f.unop) s) =
      moduleRes _ (leOfHom f.unop) (product φ n k m hm O.unop (homogeneousSection φ p hp O.unop) s)
    rw [product_restrict, homogeneousSection_restrict]

theorem multiply_frame {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (k m : ℤ) (hm : n + k = m)
    (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(twist φ k,V)) :
    chartFrame φ m i V hi ((multiply φ p hp k m hm).app V s) =
      normalized φ i p hp V hi * chartFrame φ k i V hi s := by
  change chartFrame φ m i V hi (product φ n k m hm V (homogeneousSection φ p hp V) s) = _
  rw [product_frame, homogeneousSection_coordinate]

end CycleQ2HodgeThreefoldTwist
end

#print axioms CycleQ2HodgeThreefoldTwist.multiply_frame
