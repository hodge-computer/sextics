import PackedRankData
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace WeightedSupport.PackedCheck

open scoped BigOperators

theorem foldl_range_eq_sum (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).foldl (fun s k => s + f k) 0 = ∑ k : Fin n, f k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ih]
    rw [Fin.sum_univ_castSucc]
    rfl

theorem dot_cast (n a b : ℕ) :
    (dot n a b : ZMod 101) =
      ∑ k : Fin n, (digit a k : ZMod 101) * (digit b k : ZMod 101) := by
  unfold dot
  rw [ZMod.natCast_mod, foldl_range_eq_sum]
  simp only [Nat.cast_sum, Nat.cast_mul]

theorem checkRow_sound (n a : ℕ) (bs : Array ℕ) (i : ℕ)
    (h : checkRow n a bs i = true) (j : Fin n) :
    (∑ k : Fin n, (digit a k : ZMod 101) * (digit bs[j.val]! k : ZMod 101)) =
      if i = j.val then 1 else 0 := by
  have he := List.all_eq_true.mp h j.val (List.mem_range.mpr j.isLt)
  have hn : dot n a bs[j.val]! = (if i = j.val then 1 else 0) := by
    simpa only [beq_iff_eq] using he
  have hc := congrArg (fun v : ℕ => (v : ZMod 101)) hn
  rw [dot_cast] at hc
  simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using hc

end WeightedSupport.PackedCheck

#print axioms WeightedSupport.PackedCheck.checkRow_sound
