import Proposal.ContactExactArithmetic

/-! Exact Gaussian-integer numerators for the analytic contact Jacobian. -/

noncomputable section

namespace ContactExactArithmetic

open ContactPolynomialBounds

set_option backward.isDefEq.respectTransparency false

theorem partialInt_cast {n : ℕ} (m : List (Fin n))
    (C : Fin n → GaussianInt) (j : Fin n) :
    (partialInt m C j : ℂ) =
      monomialDeriv m (fun i => (C i : ℂ)) (Pi.single j 1) := by
  induction m with
  | nil => simp [partialInt, monomialDeriv, GaussianInt.toComplex_zero]
  | cons i m ih =>
    by_cases hij : i = j
    · subst i
      simp [partialInt, monomialDeriv, GaussianInt.toComplex_add,
        GaussianInt.toComplex_mul, monomialInt_cast, ih]
    · simp [partialInt, monomialDeriv, GaussianInt.toComplex_mul, hij, ih]

theorem partial_scaled_cast {n : ℕ} (D : ℕ) (hD : 0 < D)
    (m : List (Fin n)) (hm : m.length ≤ 3) (C : Fin n → GaussianInt) (j : Fin n) :
    ((partialInt m C j * (D : GaussianInt) ^ (3 - m.length) : GaussianInt) : ℂ) =
      (D : ℂ) ^ 2 * monomialDeriv m (scaledPoint D C) (Pi.single j 1) := by
  have hd : (D : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  rcases m with _ | ⟨a, m⟩
  · simp [partialInt, monomialDeriv, GaussianInt.toComplex_zero]
  rcases m with _ | ⟨b, m⟩
  · simp only [List.length_cons, List.length_nil, Nat.reduceSub,
      partialInt, monomialInt, monomialDeriv, monomial, List.map_nil, List.prod_nil,
      GaussianInt.toComplex_mul, map_pow, map_natCast, add_apply, smul_apply,
      zero_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
      mul_zero, zero_add, one_mul, scaledPoint, Pi.single_apply]
    split_ifs <;> simp_all
  rcases m with _ | ⟨d, m⟩
  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      partialInt, monomialInt, monomialDeriv, monomial, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, GaussianInt.toComplex_mul, GaussianInt.toComplex_add,
      map_pow, map_natCast, add_apply, smul_apply, zero_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, mul_zero, zero_add, one_mul, scaledPoint, Pi.single_apply]
    split_ifs <;> simp_all <;> field_simp
  rcases m with _ | ⟨e, m⟩
  · simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
      partialInt, monomialInt, monomialDeriv, monomial, List.map_cons, List.prod_cons,
      List.map_nil, List.prod_nil, GaussianInt.toComplex_mul, GaussianInt.toComplex_add,
      map_pow, map_natCast, add_apply, smul_apply, zero_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, mul_zero, zero_add, one_mul, scaledPoint, Pi.single_apply]
    split_ifs <;> simp_all <;> field_simp
  · simp only [List.length_cons] at hm
    omega

theorem jacobianScaled_cast {n : ℕ} (D : ℕ) (hD : 0 < D)
    (p : IntPolynomial n) (hp : ∀ t ∈ p, t.2.length ≤ 3)
    (C : Fin n → GaussianInt) (j : Fin n) :
    (jacobianScaled 3 D p C j : ℂ) =
      (D : ℂ) ^ 2 * polyDeriv (complexPoly p) (scaledPoint D C) (Pi.single j 1) := by
  induction p with
  | nil => simp [jacobianScaled, complexPoly, polyDeriv, GaussianInt.toComplex_zero]
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ t ∈ p, t.2.length ≤ 3 := by
      intro s hs
      exact hp s (List.mem_cons_of_mem _ hs)
    have hs := partial_scaled_cast D hD t.2 ht C j
    have hc : ((t.1 : GaussianInt) : ℂ) = (t.1 : ℂ) :=
      map_intCast GaussianInt.toComplex _
    change (((t.1 : GaussianInt) * partialInt t.2 C j *
      (D : GaussianInt) ^ (3 - t.2.length) + jacobianScaled 3 D p C j : GaussianInt) : ℂ) = _
    simp only [GaussianInt.toComplex_add, GaussianInt.toComplex_mul,
      map_pow GaussianInt.toComplex, map_natCast GaussianInt.toComplex, hc]
    rw [ih htail]
    simp only [complexPoly, List.map_cons, polyDeriv, add_apply, smul_apply, smul_eq_mul]
    simp only [GaussianInt.toComplex_mul, map_pow GaussianInt.toComplex,
      map_natCast GaussianInt.toComplex] at hs
    linear_combination (t.1 : ℂ) * hs

theorem secondMass_cast (M k : ℕ) (hk : k ≤ 3) :
    secondMass (M : ℝ) k = (k * (k - 1) * M ^ (k - 2) : ℕ) := by
  interval_cases k <;> simp [firstMass, secondMass]
  ring

theorem complexMass_intCast (c : ℤ) : complexMass (c : ℂ) = (c.natAbs : ℝ) := by
  simp [complexMass, Nat.cast_natAbs, Int.cast_abs]

theorem hessianMassInt_cast {n : ℕ} (M : ℕ) (p : IntPolynomial n)
    (hp : ∀ t ∈ p, t.2.length ≤ 3) :
    hessianMass (complexPoly p) (M : ℝ) = (hessianMassInt M p : ℝ) := by
  induction p with
  | nil => simp [hessianMassInt, complexPoly, hessianMass]
  | cons t p ih =>
    have ht := hp t (by simp)
    have htail : ∀ t ∈ p, t.2.length ≤ 3 := by
      intro s hs
      exact hp s (List.mem_cons_of_mem _ hs)
    change complexMass (t.1 : ℂ) * secondMass (M : ℝ) t.2.length +
      hessianMass (complexPoly p) (M : ℝ) =
      (t.1.natAbs * t.2.length * (t.2.length - 1) * M ^ (t.2.length - 2) +
        hessianMassInt M p : ℕ)
    rw [ih htail, complexMass_intCast, secondMass_cast M t.2.length ht]
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow]
    ring

end ContactExactArithmetic
