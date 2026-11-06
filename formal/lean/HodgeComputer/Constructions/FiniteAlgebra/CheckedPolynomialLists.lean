import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Ring

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

namespace CheckedPolynomialLists
open Polynomial

def add : List ℚ → List ℚ → List ℚ
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys => (x+y) :: add xs ys

def scale (c : ℚ) (xs : List ℚ) : List ℚ := xs.map (c * ·)

def mul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | x :: xs, ys => add (scale x ys) (0 :: mul xs ys)

def neg (xs : List ℚ) := scale (-1) xs

def sub (xs ys : List ℚ) := add xs (neg ys)

def pow (xs : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n+1 => mul xs (pow xs n)

def pad (n : ℕ) (xs : List ℚ) := xs ++ List.replicate (n-xs.length) 0

noncomputable def encode : List ℚ → Polynomial ℚ
  | [] => 0
  | x :: xs => C x + X * encode xs

lemma encode_add (xs ys : List ℚ) : encode (add xs ys) = encode xs + encode ys := by
  induction xs generalizing ys with
  | nil => simp [add, encode]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add, encode]
    | cons y ys => simp only [add, encode, ih, map_add]; ring

lemma encode_scale (c : ℚ) (xs : List ℚ) : encode (scale c xs) = C c * encode xs := by
  induction xs with
  | nil => simp [scale, encode]
  | cons x xs ih =>
    change C (c*x) + X*encode (scale c xs) = C c*(C x+X*encode xs)
    rw [ih, map_mul]
    ring

lemma encode_mul (xs ys : List ℚ) : encode (mul xs ys) = encode xs * encode ys := by
  induction xs with
  | nil => simp [mul, encode]
  | cons x xs ih =>
    simp only [mul, encode_add, encode_scale, encode, map_zero, zero_add, ih]
    ring

lemma encode_neg (xs : List ℚ) : encode (neg xs) = -encode xs := by
  rw [neg, encode_scale]
  simp

lemma encode_sub (xs ys : List ℚ) : encode (sub xs ys) = encode xs - encode ys := by
  rw [sub, encode_add, encode_neg, sub_eq_add_neg]

lemma encode_pow (xs : List ℚ) (n : ℕ) : encode (pow xs n) = (encode xs)^n := by
  induction n with
  | zero => simp [pow, encode]
  | succ n ih => rw [pow, encode_mul, ih, pow_succ']

lemma encode_append (xs ys : List ℚ) :
    encode (xs ++ ys) = encode xs + X^xs.length * encode ys := by
  induction xs with
  | nil => simp [encode]
  | cons x xs ih => simp only [List.cons_append, encode, ih, List.length_cons, pow_succ]; ring

lemma encode_zeros (n : ℕ) : encode (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, encode, ih]

lemma encode_pad (n : ℕ) (xs : List ℚ) : encode (pad n xs) = encode xs := by
  simp [pad, encode_append, encode_zeros]

lemma eq_of_pad_eq {n : ℕ} {xs ys : List ℚ} (h : pad n xs = pad n ys) :
    encode xs = encode ys := by
  rw [← encode_pad n xs, h, encode_pad]

end CheckedPolynomialLists

