import SymmetricSmoothness
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
A uniform, characteristic-zero obstruction to normalized certificates whose
denominator has degree at most three.  A symbolic square coefficient minor is
diagonal modulo five.  No large concrete matrix is materialized.

The final theorem applies to the actual unrestricted `HodgeComputer.Verify`
record for the protected target.  It proves that its denominator must have
degree at least four, including Euler normalization and an arbitrary residual
quotient.  It does not construct a certificate or exclude larger degrees.
-/

noncomputable section
namespace SmallDenominatorObstruction
open MvPolynomial Matrix SexticModFive
open scoped BigOperators


abbrev Degree (n : ℕ) := {e : Exponents // e.degree = n}
instance (n : ℕ) : Fintype (Degree n) := (Finsupp.finite_of_degree_eq (σ := Vars) n).fintype

abbrev Columns (d : ℕ) := (Vars × Degree (d+1)) ⊕ Degree d

def ones : Exponents := ∑ i : Vars, Finsupp.single i 1

@[simp] theorem ones_apply (i : Vars) : ones i = 1 := by
  simp [ones, Finsupp.finsetSum_apply]

def rowExponent {d : ℕ} : Columns d → Exponents
  | .inl (i,e) => e.val + Finsupp.single i 5
  | .inr e => e.val + ones


theorem rowExponent_injective {d : ℕ} (hd : d ≤ 3) :
    Function.Injective (rowExponent (d := d)) := by
  rintro (⟨i,e⟩ | e) (⟨j,f⟩ | f) h
  · change e.val + Finsupp.single i 5 = f.val + Finsupp.single j 5 at h
    have hij : i = j := by
      by_contra hn
      have he := congrArg (fun a : Exponents => a i) h
      have hf := Finsupp.le_degree i f.val
      rw [f.property] at hf
      simp [hn] at he
      omega
    subst j
    have hef : e = f := Subtype.ext (add_right_cancel h)
    simp [hef]
  · change e.val + Finsupp.single i 5 = f.val + ones at h
    have he := congrArg (fun a : Exponents => a i) h
    have hf := Finsupp.le_degree i f.val
    rw [f.property] at hf
    simp at he
    omega
  · change e.val + ones = f.val + Finsupp.single j 5 at h
    have he := congrArg (fun a : Exponents => a j) h
    have hb := Finsupp.le_degree j e.val
    rw [e.property] at hb
    simp at he
    omega
  · change e.val + ones = f.val + ones at h
    have hef : e = f := Subtype.ext (add_right_cancel h)
    simp [hef]


def columnPolynomial {d : ℕ} (g : Vars → MvPolynomial Vars ℤ) :
    Columns d → MvPolynomial Vars ℤ
  | .inl (i,e) => monomial e.val 1 * g i
  | .inr e => -monomial (e.val + ones) 1

def minor {d : ℕ} (g : Vars → MvPolynomial Vars ℤ) :
    Matrix (Columns d) (Columns d) ℤ :=
  fun a b => coeff (rowExponent a) (columnPolynomial g b)

def diagonalValue {d : ℕ} : Columns d → ZMod 5
  | .inl _ => 2
  | .inr _ => -1

theorem column_mod_five {d : ℕ} (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5)
    (a : Columns d) :
    map (Int.castRingHom (ZMod 5)) (columnPolynomial g a) =
      monomial (rowExponent a) (diagonalValue a) := by
  rcases a with ⟨i,e⟩ | e
  · rw [columnPolynomial, map_mul, map_monomial, map_one, hmod]
    rw [C_mul_X_pow_eq_monomial, monomial_mul, one_mul]
    rfl
  · simp [columnPolynomial, rowExponent, diagonalValue]


theorem minor_mod_five {d : ℕ} (hd : d ≤ 3) (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5) :
    (minor (d := d) g).map (Int.castRingHom (ZMod 5)) = diagonal diagonalValue := by
  classical
  ext a b
  change (Int.castRingHom (ZMod 5)) (coeff (rowExponent a) (columnPolynomial g b)) = _
  rw [← coeff_map, column_mod_five g hmod]
  simp only [coeff_monomial, diagonal_apply]
  by_cases h : a = b
  · subst b
    simp
  · have hab : rowExponent b ≠ rowExponent a :=
      fun he => h ((rowExponent_injective hd he).symm)
    simp [h, hab]


theorem minor_det_ne_zero {d : ℕ} (hd : d ≤ 3) (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5) :
    (minor (d := d) g).det ≠ 0 := by
  intro hz
  have he := (Int.castRingHom (ZMod 5)).map_det (minor (d := d) g)
  change ((minor (d := d) g).det : ZMod 5) =
    ((minor (d := d) g).map (Int.castRingHom (ZMod 5))).det at he
  rw [hz, Int.cast_zero, minor_mod_five hd g hmod, Matrix.det_diagonal] at he
  have hn : (∏ a : Columns d, diagonalValue a) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a _
    rcases a with a | a <;> simp only [diagonalValue] <;> decide
  exact hn he.symm


theorem homogeneous_expansion {K : Type*} [CommRing K] {n : ℕ}
    (P : MvPolynomial Vars K) (hP : P.IsHomogeneous n) :
    P = ∑ e : Degree n, monomial e.val (coeff e.val P) := by
  classical
  ext e
  rw [coeff_sum]
  by_cases he : e.degree = n
  · let a : Degree n := ⟨e,he⟩
    rw [Finset.sum_eq_single a]
    · simp [a]
    · intro b _ hba
      have hbe : b.val ≠ e := fun h => hba (Subtype.ext h)
      simp [hbe]
    · simp
  · have hc : coeff e P = 0 := by
      by_contra hn
      apply he
      rw [Finsupp.degree_eq_weight_one]
      exact hP hn
    rw [hc]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hbe : b.val ≠ e := fun h => he (h ▸ b.property)
    simp [hbe]


def coefficientVector {K : Type*} [CommRing K] {d : ℕ}
    (N : Vars → MvPolynomial Vars K) (D : MvPolynomial Vars K) : Columns d → K
  | .inl (i,e) => coeff e.val (N i)
  | .inr e => coeff e.val D

theorem column_expansion {K : Type*} [CommRing K] {d : ℕ}
    (g : Vars → MvPolynomial Vars ℤ)
    (N : Vars → MvPolynomial Vars K) (D : MvPolynomial Vars K)
    (hN : ∀ i, (N i).IsHomogeneous (d+1)) (hD : D.IsHomogeneous d) :
    (∑ a : Columns d, C (coefficientVector N D a) *
      map (Int.castRingHom K) (columnPolynomial g a)) =
      (∑ i : Vars, N i * map (Int.castRingHom K) (g i)) -
        D * monomial ones 1 := by
  classical
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [coefficientVector, columnPolynomial, map_mul, map_monomial, map_one,
    map_neg, mul_neg]
  have hn (i : Vars) :
      (∑ e : Degree (d+1), C (coeff e.val (N i)) * (monomial e.val 1 *
        map (Int.castRingHom K) (g i))) = N i * map (Int.castRingHom K) (g i) := by
    conv_rhs => rw [homogeneous_expansion (N i) (hN i)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    rw [← mul_assoc, C_mul_monomial, mul_one]
  simp_rw [hn]
  rw [Finset.sum_neg_distrib, sub_eq_add_neg]
  congr 1
  congr 1
  conv_rhs => rw [homogeneous_expansion D hD]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  rw [C_mul_monomial, mul_one, monomial_mul, mul_one]


/-- No nonzero pair of the specified homogeneous degrees can satisfy the
normalized first equation, over any characteristic-zero field. -/
theorem normalized_first_equation_trivial {K : Type*} [Field K] [CharZero K]
    {d : ℕ} (hd : d ≤ 3) (g : Vars → MvPolynomial Vars ℤ)
    (hmod : ∀ i, map (Int.castRingHom (ZMod 5)) (g i) = C 2 * X i ^ 5)
    (N : Vars → MvPolynomial Vars K) (D : MvPolynomial Vars K)
    (hN : ∀ i, (N i).IsHomogeneous (d+1)) (hD : D.IsHomogeneous d)
    (heq : (∑ i : Vars, N i * map (Int.castRingHom K) (g i)) = D * monomial ones 1) :
    N = 0 ∧ D = 0 := by
  classical
  let M : Matrix (Columns d) (Columns d) K := (minor g).map (Int.castRingHom K)
  have hdet : M.det ≠ 0 := by
    rw [show M.det = ((minor (d := d) g).det : K) from
      ((Int.castRingHom K).map_det (minor g)).symm]
    exact_mod_cast minor_det_ne_zero hd g hmod
  let v : Columns d → K := coefficientVector N D
  have hpoly : (∑ a : Columns d, C (v a) *
      map (Int.castRingHom K) (columnPolynomial g a)) = 0 := by
    rw [column_expansion g N D hN hD, heq, sub_self]
  have hzero : M *ᵥ v = 0 := by
    funext a
    have hc := congrArg (coeff (rowExponent a)) hpoly
    simpa [coeff_sum, coeff_C_mul, M, minor, Matrix.mulVec, dotProduct,
      coeff_map, mul_comm] using hc
  have hv : v = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    simpa using hzero
  constructor
  · funext i
    rw [homogeneous_expansion (N i) (hN i)]
    apply Finset.sum_eq_zero
    intro e _
    have h := congrFun hv (Sum.inl (i,e))
    change coeff e.val (N i) = 0 at h
    simp [h]
  · rw [homogeneous_expansion D hD]
    apply Finset.sum_eq_zero
    intro e _
    have h := congrFun hv (Sum.inr e)
    change coeff e.val D = 0 at h
    simp [h]

theorem protected_source_eq_monomial :
    HodgeSubmission.A = monomial ones (1 : ℂ) := by
  rw [ones, monomial_sum_one]
  change HodgeSubmission.A = ∏ i : Vars, (X i : MvPolynomial Vars ℂ)
  rw [SymmetricReflections.exactA_compact]
  simp [SymmetricReflections.compactA, Fin.prod_univ_succ]
  ring

/-- The preceding uniform obstruction specialized to the protected sextic. -/
theorem protected_normalized_first_equation_trivial
    {d : ℕ} (hd : d ≤ 3)
    (N : Vars → MvPolynomial Vars ℂ) (D : MvPolynomial Vars ℂ)
    (hN : ∀ i, (N i).IsHomogeneous (d+1)) (hD : D.IsHomogeneous d)
    (heq : HodgeTestbed.directional HodgeSubmission.F N = HodgeSubmission.A * D) :
    N = 0 ∧ D = 0 := by
  have hg (i : Vars) : map (Int.castRingHom ℂ)
      (pderiv i SymmetricSmoothness.integerSextic) =
      C (7 : ℂ) * pderiv i HodgeSubmission.F := by
    rw [← pderiv_map, SymmetricSmoothness.integerSextic_complex_binding]
    simp
  have hfirst : (∑ i : Vars, N i * map (Int.castRingHom ℂ)
      (pderiv i SymmetricSmoothness.integerSextic)) =
        (C (7 : ℂ) * D) * monomial ones 1 := by
    simp_rw [hg]
    calc
      _ = C (7 : ℂ) * HodgeTestbed.directional HodgeSubmission.F N := by
        simp only [HodgeTestbed.directional, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [heq, protected_source_eq_monomial]; ring
  have h := normalized_first_equation_trivial hd
    (fun i => pderiv i SymmetricSmoothness.integerSextic)
    SymmetricSmoothness.derivative_mod_five N (C (7 : ℂ) * D) hN (hD.C_mul 7) hfirst
  exact ⟨h.1, (mul_eq_zero.mp h.2).resolve_left (by norm_num)⟩

/-- Taking a homogeneous component commutes with a homogeneous left factor. -/
theorem homogeneousComponent_mul_of_left {K : Type*} [CommRing K]
    {F : MvPolynomial Vars K} {m : ℕ} (hF : F.IsHomogeneous m)
    (H : MvPolynomial Vars K) (n : ℕ) :
    homogeneousComponent (m+n) (F*H) = F * homogeneousComponent n H := by
  classical
  ext e
  rw [coeff_homogeneousComponent, coeff_mul, coeff_mul]
  by_cases he : e.degree = m+n
  · rw [if_pos he]
    apply Finset.sum_congr rfl
    rintro ⟨a,b⟩ hab
    by_cases hc : coeff a F = 0
    · simp [hc]
    have ha : a.degree = m := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hF hc
    have hsum := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hab)
    simp only [map_add] at hsum
    have hb : b.degree = n := by omega
    simp [coeff_homogeneousComponent, hb]
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    rintro ⟨a,b⟩ hab
    by_cases hc : coeff a F = 0
    · simp [hc]
    have ha : a.degree = m := by
      simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hF hc
    have hsum := congrArg Finsupp.degree (Finset.mem_antidiagonal.mp hab)
    simp only [map_add] at hsum
    have hb : b.degree ≠ n := by omega
    simp [coeff_homogeneousComponent, hb]

/-- A certificate in the actual unrestricted `Verify` format must have
denominator degree at least four.  Euler normalization is proved here; the
residual quotient is arbitrary and is not set to zero. -/
theorem verified_denominator_degree_ge_four
    {D Q : HodgeComputer.AmbientPoly 5} {N : Vars → HodgeComputer.AmbientPoly 5}
    (h : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A 6 1 D N Q) :
    4 ≤ D.totalDegree := by
  classical
  by_contra hlarge
  have hd : D.totalDegree ≤ 3 := by omega
  have hN (i : Vars) : (N i).IsHomogeneous (D.totalDegree+1) := by
    have hi := (h.numerator_homogeneous i).isHomogeneous (by omega)
    convert hi using 1; omega
  have hmul : HodgeSubmission.F ∣ D *
      (HodgeSubmission.A * D - HodgeTestbed.directional HodgeSubmission.F N) := by
    refine ⟨HodgeSubmission.F * Q - HodgeTestbed.divergenceNumerator D N, ?_⟩
    have hi := h.identity
    simp only [HodgeComputer.defect, Nat.cast_one, one_mul] at hi
    linear_combination hi
  obtain ⟨H,hH⟩ := h.denominator_legal.dvd_of_dvd_mul_left hmul
  have hdir : (HodgeTestbed.directional HodgeSubmission.F N).IsHomogeneous
      (6+D.totalDegree) := by
    unfold HodgeTestbed.directional
    apply IsHomogeneous.sum
    intro i _
    have hi := (SymmetricSmoothness.target_homogeneous.pderiv (i := i)).mul (hN i)
    simpa only [show 6-1+(D.totalDegree+1) = 6+D.totalDegree by omega] using hi
  have hR : (HodgeSubmission.A * D -
      HodgeTestbed.directional HodgeSubmission.F N).IsHomogeneous (6+D.totalDegree) :=
    (SymmetricSmoothness.source_homogeneous.mul h.denominator_homogeneous).sub hdir
  have hH0 := congrArg (homogeneousComponent (6+D.totalDegree)) hH
  rw [homogeneousComponent_eq_self hR,
    homogeneousComponent_mul_of_left SymmetricSmoothness.target_homogeneous] at hH0
  let H0 := homogeneousComponent D.totalDegree H
  have hh0 : H0.IsHomogeneous D.totalDegree := homogeneousComponent_isHomogeneous _ _
  let N' : Vars → MvPolynomial Vars ℂ :=
    fun i => N i + C (1/6 : ℂ) * (H0 * X i)
  have hn' (i : Vars) : (N' i).IsHomogeneous (D.totalDegree+1) :=
    (hN i).add ((hh0.mul (isHomogeneous_X ℂ i)).C_mul (1/6 : ℂ))
  have heuler : (∑ i : Vars, X i * pderiv i HodgeSubmission.F) =
      6 * HodgeSubmission.F := by
    simpa only [nsmul_eq_mul, Nat.cast_ofNat] using SymmetricSmoothness.target_homogeneous.sum_X_mul_pderiv
  have hunit : (C (1/6 : ℂ) : MvPolynomial Vars ℂ) * 6 = 1 := by
    rw [show (6 : MvPolynomial Vars ℂ) = C (6 : ℂ) from (map_natCast C 6).symm, ← map_mul]
    norm_num
  have hcorrection : (∑ i : Vars, pderiv i HodgeSubmission.F *
      (C (1/6 : ℂ) * (H0 * X i))) = HodgeSubmission.F * H0 := by
    calc
      _ = (C (1/6 : ℂ) * H0) * (∑ i : Vars, X i * pderiv i HodgeSubmission.F) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [heuler]; calc
        _ = (C (1/6 : ℂ) * 6) * (HodgeSubmission.F * H0) := by ring
        _ = _ := by rw [hunit, one_mul]
  have hfirst : HodgeTestbed.directional HodgeSubmission.F N' = HodgeSubmission.A * D := by
    simp only [HodgeTestbed.directional, N', mul_add, Finset.sum_add_distrib]
    rw [hcorrection]
    change HodgeTestbed.directional HodgeSubmission.F N + HodgeSubmission.F * H0 = _
    change HodgeSubmission.A * D - HodgeTestbed.directional HodgeSubmission.F N =
      HodgeSubmission.F * H0 at hH0
    linear_combination -hH0
  exact h.denominator_ne_zero
    (protected_normalized_first_equation_trivial hd N' D hn' h.denominator_homogeneous hfirst).2

/-- The preceding result uses precisely the hypersurface degree and pole
parameter appearing in the protected target's certificate definition. -/
theorem protected_verified_denominator_degree_ge_four
    {D Q : HodgeComputer.AmbientPoly 5} {N : Vars → HodgeComputer.AmbientPoly 5}
    (h : HodgeComputer.Verify HodgeSubmission.F HodgeSubmission.A
      HodgeSubmission.F.totalDegree HodgeSubmission.q D N Q) :
    4 ≤ D.totalDegree := by
  apply verified_denominator_degree_ge_four
  simpa only [SymmetricSmoothness.target_totalDegree, HodgeSubmission.q] using h

#print axioms normalized_first_equation_trivial
#print axioms protected_normalized_first_equation_trivial
#print axioms protected_verified_denominator_degree_ge_four
end SmallDenominatorObstruction
