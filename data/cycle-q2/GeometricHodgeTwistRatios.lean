import Proposal.GeometricHodgeThreefold
import Proposal.GeometricTwistedSheaf

/-!
# Homogeneous sections in the four weight-one frames

A degree-n element of the full-family cone gives the section p/xᵢⁿ on
D(xᵢ). At a homogeneous prime its value is the literal fraction. The
frame changes xⱼ/xᵢ are units on all common subopens and satisfy the
multiplicative cocycle, including under all further restrictions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistRatios

open AlgebraicGeometry CategoryTheory Opposite HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev X := threefold φ
abbrev U (i : Fin 4) := coordinateOpen φ i
abbrev x (i : Fin 4) := coord φ i.castSucc

def normalized (i : Fin 4) {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n)
    (V : (X φ).Opens) (hi : V ≤ U φ i) : Γ(X φ,V) :=
  res (X φ).sheaf hi ((Proj.awayToSection (grade φ) (x φ i))
    (Away.mk (grade φ) (weightOne_mem_grade φ i) n p (by simpa using hp)))

theorem normalized_restrict (i : Fin 4) {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n)
    {V W : (X φ).Opens} (hi : V ≤ U φ i) (hW : W ≤ V) :
    res (X φ).sheaf hW (normalized φ i p hp V hi) =
      normalized φ i p hp W (hW.trans hi) := res_comp _ _ _ _

private abbrev den {V : (X φ).Opens} (i : Fin 4) (hi : V ≤ U φ i) (q : V) :
    q.val.asHomogeneousIdeal.toIdeal.primeCompl := ⟨x φ i, hi q.property⟩

private theorem value {V : (X φ).Opens} (i : Fin 4) (hi : V ≤ U φ i) {n : ℕ}
    (p : cone φ) (hp : p ∈ grade φ n) (q : V) :
    ((normalized φ i p hp V hi).val q).val = Localization.mk p (den φ i hi q ^ n) := rfl

def ratio (i j : Fin 4) (V : (X φ).Opens) (hi : V ≤ U φ i) : Γ(X φ,V) :=
  normalized φ i (x φ j) (weightOne_mem_grade φ j) V hi

theorem ratio_self (i : Fin 4) (V : (X φ).Opens) (hi : V ≤ U φ i) : ratio φ i i V hi = 1 := by
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  change ((normalized φ i (x φ i) _ V hi).val q).val = (1 : HomogeneousLocalization _ _).val
  rw [value, pow_one, HomogeneousLocalization.val_one]
  exact Localization.mk_self (den φ i hi q)

/-- Identity of sections p/xᵢⁿ = (xⱼ/xᵢ)ⁿ(p/xⱼⁿ) on every common subopen. -/
theorem normalized_change (i j : Fin 4) {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n)
    (V : (X φ).Opens) (hi : V ≤ U φ i) (hj : V ≤ U φ j) :
    normalized φ i p hp V hi = ratio φ i j V hi ^ n * normalized φ j p hp V hj := by
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  change ((normalized φ i p hp V hi).val q).val =
    (((ratio φ i j V hi).val q) ^ n * ((normalized φ j p hp V hj).val q)).val
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow, ratio, value, value, value,
    pow_one, Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow, one_mul, den]
  ring

theorem ratio_comp (i j k : Fin 4) (V : (X φ).Opens) (hi : V ≤ U φ i) (hj : V ≤ U φ j) :
    ratio φ i j V hi * ratio φ j k V hj = ratio φ i k V hi := by
  simpa only [ratio, pow_one] using
    (normalized_change φ i j (x φ k) (weightOne_mem_grade φ k) V hi hj).symm

def transition (i j : Fin 4) (V : (X φ).Opens) (hi : V ≤ U φ i) (hj : V ≤ U φ j) :
    Γ(X φ,V)ˣ where
  val := ratio φ i j V hi
  inv := ratio φ j i V hj
  val_inv := (ratio_comp φ i j i V hi hj).trans (ratio_self φ i V hi)
  inv_val := (ratio_comp φ j i j V hj hi).trans (ratio_self φ j V hj)

theorem transition_self (i : Fin 4) (V : (X φ).Opens) (hi : V ≤ U φ i) :
    transition φ i i V hi hi = 1 := Units.ext (ratio_self φ i V hi)

theorem transition_comp (i j k : Fin 4) (V : (X φ).Opens)
    (hi : V ≤ U φ i) (hj : V ≤ U φ j) (hk : V ≤ U φ k) :
    transition φ i j V hi hj * transition φ j k V hj hk = transition φ i k V hi hk :=
  Units.ext (ratio_comp φ i j k V hi hj)

theorem transition_restrict (i j : Fin 4) {V W : (X φ).Opens}
    (hi : V ≤ U φ i) (hj : V ≤ U φ j) (hW : W ≤ V) :
    Units.map (res (X φ).sheaf hW).toMonoidHom (transition φ i j V hi hj) =
      transition φ i j W (hW.trans hi) (hW.trans hj) :=
  Units.ext (normalized_restrict φ i (x φ j) (weightOne_mem_grade φ j) hi hW)

end CycleQ2HodgeTwistRatios
end

#print axioms CycleQ2HodgeTwistRatios.normalized_change
#print axioms CycleQ2HodgeTwistRatios.transition_comp
