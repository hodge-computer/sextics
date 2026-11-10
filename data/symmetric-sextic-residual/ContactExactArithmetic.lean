import Proposal.ContactPolynomialBounds
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-! Integer arithmetic and its interpretation in the complex contact system. -/

namespace ContactExactArithmetic

open scoped BigOperators

abbrev IntPolynomial (n : ℕ) := List (ℤ × List (Fin n))

def monomialInt {n : ℕ} : List (Fin n) → (Fin n → GaussianInt) → GaussianInt
  | [], _ => 1
  | i :: m, C => C i * monomialInt m C

def partialInt {n : ℕ} : List (Fin n) → (Fin n → GaussianInt) → Fin n → GaussianInt
  | [], _, _ => 0
  | i :: m, C, j => C i * partialInt m C j + if i = j then monomialInt m C else 0

def evalScaled {n : ℕ} (k D : ℕ) (p : IntPolynomial n)
    (C : Fin n → GaussianInt) : GaussianInt :=
  (p.map fun t => (t.1 : GaussianInt) * monomialInt t.2 C *
    (D : GaussianInt) ^ (k - t.2.length)).sum

def jacobianScaled {n : ℕ} (k D : ℕ) (p : IntPolynomial n)
    (C : Fin n → GaussianInt) (j : Fin n) : GaussianInt :=
  (p.map fun t => (t.1 : GaussianInt) * partialInt t.2 C j *
    (D : GaussianInt) ^ (k - t.2.length)).sum

def mass (z : GaussianInt) : ℕ := z.re.natAbs + z.im.natAbs

def dotInt {n : ℕ} (v w : Fin n → GaussianInt) : GaussianInt :=
  ∑ i, v i * w i

def rowMass {n : ℕ} (v : Fin n → GaussianInt) : ℕ := ∑ i, mass (v i)

def hessianMassInt {n : ℕ} (M : ℕ) (p : IntPolynomial n) : ℕ :=
  (p.map fun t => t.1.natAbs * t.2.length * (t.2.length - 1) *
    M ^ (t.2.length - 2)).sum

noncomputable def complexPoly {n : ℕ} (p : IntPolynomial n) :
    ContactPolynomialBounds.Polynomial n :=
  p.map fun t => ((t.1 : ℂ), t.2)

noncomputable def scaledPoint {n : ℕ} (D : ℕ) (C : Fin n → GaussianInt) : Fin n → ℂ :=
  fun i => (C i : ℂ) / (D : ℂ)

theorem monomialInt_cast {n : ℕ} (m : List (Fin n)) (C : Fin n → GaussianInt) :
    (monomialInt m C : ℂ) = ContactPolynomialBounds.monomial m (fun i => (C i : ℂ)) := by
  induction m with
  | nil => simp [monomialInt, ContactPolynomialBounds.monomial, GaussianInt.toComplex_one]
  | cons i m ih =>
    simp [monomialInt, ContactPolynomialBounds.monomial, GaussianInt.toComplex_mul, ih]

theorem monomial_scaled {n : ℕ} (m : List (Fin n)) (D : ℕ)
    (C : Fin n → GaussianInt) :
    ContactPolynomialBounds.monomial m (scaledPoint D C) =
      (monomialInt m C : ℂ) / (D : ℂ) ^ m.length := by
  induction m with
  | nil => simp [ContactPolynomialBounds.monomial, monomialInt, GaussianInt.toComplex_one]
  | cons i m ih =>
    simp only [ContactPolynomialBounds.monomial, List.map_cons, List.prod_cons,
      List.length_cons, monomialInt, GaussianInt.toComplex_mul] at *
    rw [ih]
    simp only [scaledPoint, pow_succ]
    field_simp

theorem monomial_scaled_cast {n : ℕ} (k D : ℕ) (hD : 0 < D)
    (m : List (Fin n)) (hm : m.length ≤ k) (C : Fin n → GaussianInt) :
    ((monomialInt m C * (D : GaussianInt) ^ (k - m.length) : GaussianInt) : ℂ) =
      (D : ℂ) ^ k * ContactPolynomialBounds.monomial m (scaledPoint D C) := by
  have hd : (D : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  rw [GaussianInt.toComplex_mul, map_pow GaussianInt.toComplex,
    map_natCast GaussianInt.toComplex, monomial_scaled]
  have hk : (D : ℂ) ^ k = (D : ℂ) ^ m.length * (D : ℂ) ^ (k - m.length) := by
    rw [← pow_add, Nat.add_sub_of_le hm]
  rw [hk]
  field_simp

theorem evalScaled_cast {n : ℕ} (k D : ℕ) (hD : 0 < D)
    (p : IntPolynomial n) (hp : ∀ t ∈ p, t.2.length ≤ k)
    (C : Fin n → GaussianInt) :
    (evalScaled k D p C : ℂ) =
      (D : ℂ) ^ k * ContactPolynomialBounds.poly (complexPoly p) (scaledPoint D C) := by
  induction p with
  | nil => simp [evalScaled, complexPoly, ContactPolynomialBounds.poly, GaussianInt.toComplex_zero]
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ t ∈ p, t.2.length ≤ k := by
      intro s hs
      exact hp s (List.mem_cons_of_mem _ hs)
    have hs := monomial_scaled_cast k D hD t.2 ht C
    simp only [evalScaled, List.map_cons, List.sum_cons, GaussianInt.toComplex_add] at *
    rw [ih htail]
    simp only [complexPoly, List.map_cons, ContactPolynomialBounds.poly]
    have hc : ((t.1 : GaussianInt) : ℂ) = (t.1 : ℂ) := map_intCast GaussianInt.toComplex _
    simp only [GaussianInt.toComplex_mul, map_pow, map_natCast] at hs ⊢
    rw [hc]
    linear_combination (t.1 : ℂ) * hs

theorem mass_cast (z : GaussianInt) :
    (mass z : ℝ) = |(z : ℂ).re| + |(z : ℂ).im| := by
  simp only [mass, Nat.cast_add, Nat.cast_natAbs, Int.cast_abs,
    ← GaussianInt.intCast_re, ← GaussianInt.intCast_im]

theorem norm_cast_le_mass (z : GaussianInt) : ‖(z : ℂ)‖ ≤ (mass z : ℝ) := by
  rw [mass_cast]
  exact Complex.norm_le_abs_re_add_abs_im _

end ContactExactArithmetic
