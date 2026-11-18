import Proposal.GeometricLiteralThreefoldChartLift

/-!
# Coordinate invariance of the tangent difference

Subtracting the infinitesimal parts of two ambient lifts over the same point
gives an ordinary dual-number point of the fixed sextic. Subtraction commutes
with the weighted projective coordinate change, including normalization by
the lifted inverse coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldTangentCoordinates

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldResidueCoordinates

variable {S : Type*} [CommRing S]

/-- The ordinary tangent point associated to two lifts of a common point. -/
def difference (x y : Jet S) : Jet S := (x.fst, x.snd - y.snd)

@[simp] theorem difference_one : difference (1 : Jet S) 1 = 1 := by
  apply TrivSqZeroExt.ext <;> simp [difference]

private theorem difference_mul (a b c d : Jet S) (hab : a.fst = b.fst) (hcd : c.fst = d.fst) :
    difference (a*c) (b*d) = difference a b * difference c d := by
  apply TrivSqZeroExt.ext
  · rfl
  · change a.fst*c.snd + a.snd*c.fst - (b.fst*d.snd + b.snd*d.fst) =
      a.fst * (c.snd-d.snd) + (a.snd-b.snd)*c.fst
    rw [← hab, ← hcd]
    ring

private theorem difference_pow (a b : Jet S) (h : a.fst = b.fst) (n : ℕ) :
    difference (a^n) (b^n) = (difference a b)^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ b, difference_mul _ _ _ _ (by simp [h]) h, ih, pow_succ]

variable [Algebra ℂ S]

def differenceHom {A : Type*} [CommRing A] [Algebra ℂ A] (x y : A →ₐ[ℂ] Jet S)
    (h : ∀ a, (x a).fst = (y a).fst) : A →ₐ[ℂ] Jet S where
  toFun p := difference (x p) (y p)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp [difference]
  map_one' := by simp
  map_mul' a b := by rw [map_mul, map_mul, difference_mul _ _ _ _ (h a) (h b)]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · simp [difference]
    · simp only [map_add, difference, TrivSqZeroExt.snd_mk, TrivSqZeroExt.snd_add]
      abel
  commutes' a := by
    rw [AlgHom.commutes, AlgHom.commutes]
    apply TrivSqZeroExt.ext
    · rfl
    · change 0 - 0 = (0 : S)
      rw [sub_zero]

theorem aeval_fst_eq (x y : Index → Jet S) (h : ∀ a, (x a).fst = (y a).fst) (p : P) :
    (aeval x p).fst = (aeval y p).fst := by
  have he : (TrivSqZeroExt.fstHom ℂ S S).comp (aeval x) =
      (TrivSqZeroExt.fstHom ℂ S S).comp (aeval y) := by
    apply MvPolynomial.algHom_ext
    intro a
    simpa only [AlgHom.comp_apply, aeval_X, TrivSqZeroExt.fstHom_apply] using h a
  exact AlgHom.congr_fun he p

theorem difference_aeval (x y : Index → Jet S) (h : ∀ a, (x a).fst = (y a).fst) (p : P) :
    aeval (fun a => difference (x a) (y a)) p = difference (aeval x p) (aeval y p) := by
  have he : aeval (fun a => difference (x a) (y a)) =
      differenceHom (aeval x) (aeval y) (aeval_fst_eq x y h) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [aeval_X, differenceHom, AlgHom.coe_mk, RingHom.coe_mk, MonoidHom.coe_mk,
      OneHom.coe_mk]
  exact AlgHom.congr_fun he p

/-- An actual dual-number point of the fixed hypersurface obtained from two
points of its ambient deformation. -/
def tangentPoint {i : Fin 4} (x y : Lift i S) (h : ∀ a, (x.x a).fst = (y.x a).fst) :
    T i →ₐ[ℂ] Jet S := by
  let f : P →ₐ[ℂ] Jet S := aeval (fun a => difference (x.x a) (y.x a))
  have hz : seedF i ∈ RingHom.ker f.toRingHom := by
      change aeval (fun a => difference (x.x a) (y.x a)) (seedF i) = 0
      rw [difference_aeval x.x y.x h, x.equation, y.equation]
      apply TrivSqZeroExt.ext
      · change 0 * _ = (0 : S)
        rw [zero_mul]
      · change (0 * _ + 1 * (aeval x.x (test i)).fst) -
            (0 * _ + 1 * (aeval y.x (test i)).fst) = 0
        simp only [zero_mul, one_mul, zero_add, aeval_fst_eq x.x y.x h, sub_self]
  exact Ideal.Quotient.liftₐ (fixedIdeal i) f
    ((Ideal.span_singleton_le_iff_mem (RingHom.ker f.toRingHom)).mpr hz)

theorem tangentPoint_mk {i : Fin 4} (x y : Lift i S) (h : ∀ a, (x.x a).fst = (y.x a).fst) (p : P) :
    tangentPoint x y h (q i p) = difference (aeval x.x p) (aeval y.x p) :=
  difference_aeval _ _ h _

omit [Algebra ℂ S] in
private theorem fst_linearValues (i j : Fin 4) (x y : Index → Jet S)
    (h : ∀ a, (x a).fst = (y a).fst) : (linearValues i x j).fst = (linearValues i y j).fst := by
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp [linearValues, h]

omit [Algebra ℂ S] in
private theorem linearValues_difference (i j : Fin 4) (x y : Index → Jet S) :
    linearValues i (fun a => difference (x a) (y a)) j =
      difference (linearValues i x j) (linearValues i y j) := by
  refine Fin.succAboveCases i ?_ (fun k => ?_) j <;> simp [linearValues]

omit [Algebra ℂ S] in
theorem inverse_fst_eq (x y u v : Jet S) (h : x.fst = y.fst)
    (hu : u*x = 1) (hv : v*y = 1) : u.fst = v.fst := by
  have h₁ : u.fst * x.fst = 1 := congrArg TrivSqZeroExt.fst hu
  have h₂ : v.fst * x.fst = 1 := h ▸ congrArg TrivSqZeroExt.fst hv
  calc
    u.fst = u.fst * (v.fst * x.fst) := by rw [h₂, mul_one]
    _ = v.fst * (u.fst * x.fst) := by ring
    _ = v.fst := by rw [h₁, mul_one]

omit [Algebra ℂ S] in
/-- Weighted chart normalization commutes with extracting the intrinsic tangent. -/
theorem difference_change (i j : Fin 4) (x y : Index → Jet S) (u v : Jet S)
    (h : ∀ a, (x a).fst = (y a).fst)
    (hu : u * linearValues i x j = 1) (hv : v * linearValues i y j = 1) :
    difference u v * linearValues i (fun a => difference (x a) (y a)) j = 1 ∧
      (fun a => difference (changedCoordinate i j x u a) (changedCoordinate i j y v a)) =
        changedCoordinate i j (fun a => difference (x a) (y a)) (difference u v) := by
  have huv := inverse_fst_eq _ _ _ _ (fst_linearValues i j x y h) hu hv
  constructor
  · rw [linearValues_difference, ← difference_mul _ _ _ _ huv (fst_linearValues i j x y h),
      hu, hv, difference_one]
  · funext a
    cases a with
    | none =>
      change difference (x none * u^2) (y none * v^2) = _
      rw [difference_mul _ _ _ _ (h none) (by simp [huv]), difference_pow u v huv]
      rfl
    | some k =>
      change difference (linearValues i x (j.succAbove k) * u)
          (linearValues i y (j.succAbove k) * v) =
        linearValues i (fun a => difference (x a) (y a)) (j.succAbove k) * _
      rw [linearValues_difference, difference_mul _ _ _ _ (fst_linearValues i _ x y h) huv]

end CycleQ2LiteralThreefoldTangentCoordinates
end

#print axioms CycleQ2LiteralThreefoldTangentCoordinates.tangentPoint_mk
#print axioms CycleQ2LiteralThreefoldTangentCoordinates.difference_change
