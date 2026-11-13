import Proposal.GeometricFormalInputs02Part02

/-! Continuation of GeometricFormalInputs02.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: seed_trace/SparseSeedDegreeNineCertificates.lean -/
section
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

/-- Every displayed normal monomial is proved to lie on the normalization line. -/
theorem degreeNineMonomial_mem_line (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 32) :
    reducedQuotient r (degreeNineMonomial i) ∈ degreeNineLine r := by
  fin_cases i
  · change reducedQuotient r (mon 0 0 0 9) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness0_0 r) (degreeNineWitness0_1 r)
      (degreeNineWitness0_2 r) (degreeNineWitness0_3 r)
    rw [← degreeNineCertificate0 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 1 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness1_0 r) (degreeNineWitness1_1 r)
      (degreeNineWitness1_2 r) (degreeNineWitness1_3 r)
    rw [← degreeNineCertificate1 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 2 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness2_0 r) (degreeNineWitness2_1 r)
      (degreeNineWitness2_2 r) (degreeNineWitness2_3 r)
    rw [← degreeNineCertificate2 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 0 3 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness3_0 r) (degreeNineWitness3_1 r)
      (degreeNineWitness3_2 r) (degreeNineWitness3_3 r)
    rw [← degreeNineCertificate3 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness4_0 r) (degreeNineWitness4_1 r)
      (degreeNineWitness4_2 r) (degreeNineWitness4_3 r)
    rw [← degreeNineCertificate4 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness5_0 r) (degreeNineWitness5_1 r)
      (degreeNineWitness5_2 r) (degreeNineWitness5_3 r)
    rw [← degreeNineCertificate5 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness6_0 r) (degreeNineWitness6_1 r)
      (degreeNineWitness6_2 r) (degreeNineWitness6_3 r)
    rw [← degreeNineCertificate6 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 1 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness7_0 r) (degreeNineWitness7_1 r)
      (degreeNineWitness7_2 r) (degreeNineWitness7_3 r)
    rw [← degreeNineCertificate7 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 5 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness8_0 r) (degreeNineWitness8_1 r)
      (degreeNineWitness8_2 r) (degreeNineWitness8_3 r)
    rw [← degreeNineCertificate8 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness9_0 r) (degreeNineWitness9_1 r)
      (degreeNineWitness9_2 r) (degreeNineWitness9_3 r)
    rw [← degreeNineCertificate9 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 6 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness10_0 r) (degreeNineWitness10_1 r)
      (degreeNineWitness10_2 r) (degreeNineWitness10_3 r)
    rw [← degreeNineCertificate10 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness11_0 r) (degreeNineWitness11_1 r)
      (degreeNineWitness11_2 r) (degreeNineWitness11_3 r)
    rw [← degreeNineCertificate11 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 7 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness12_0 r) (degreeNineWitness12_1 r)
      (degreeNineWitness12_2 r) (degreeNineWitness12_3 r)
    rw [← degreeNineCertificate12 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((2 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness13_0 r) (degreeNineWitness13_1 r)
      (degreeNineWitness13_2 r) (degreeNineWitness13_3 r)
    rw [← degreeNineCertificate13 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 8 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness14_0 r) (degreeNineWitness14_1 r)
      (degreeNineWitness14_2 r) (degreeNineWitness14_3 r)
    rw [← degreeNineCertificate14 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 0 9 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness15_0 r) (degreeNineWitness15_1 r)
      (degreeNineWitness15_2 r) (degreeNineWitness15_3 r)
    rw [← degreeNineCertificate15 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((-4 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 0 8) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness16_0 r) (degreeNineWitness16_1 r)
      (degreeNineWitness16_2 r) (degreeNineWitness16_3 r)
    rw [← degreeNineCertificate16 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (4 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 1 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness17_0 r) (degreeNineWitness17_1 r)
      (degreeNineWitness17_2 r) (degreeNineWitness17_3 r)
    rw [← degreeNineCertificate17 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * Complex.I + (-1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 2 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness18_0 r) (degreeNineWitness18_1 r)
      (degreeNineWitness18_2 r) (degreeNineWitness18_3 r)
    rw [← degreeNineCertificate18 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 0 3 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness19_0 r) (degreeNineWitness19_1 r)
      (degreeNineWitness19_2 r) (degreeNineWitness19_3 r)
    rw [← degreeNineCertificate19 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 0 7) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness20_0 r) (degreeNineWitness20_1 r)
      (degreeNineWitness20_2 r) (degreeNineWitness20_3 r)
    rw [← degreeNineCertificate20 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 1 6) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness21_0 r) (degreeNineWitness21_1 r)
      (degreeNineWitness21_2 r) (degreeNineWitness21_3 r)
    rw [← degreeNineCertificate21 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 2 5) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness22_0 r) (degreeNineWitness22_1 r)
      (degreeNineWitness22_2 r) (degreeNineWitness22_3 r)
    rw [← degreeNineCertificate22 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (2 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 1 3 4) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness23_0 r) (degreeNineWitness23_1 r)
      (degreeNineWitness23_2 r) (degreeNineWitness23_3 r)
    rw [← degreeNineCertificate23 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (12 : ℂ) ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 4 3 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness24_0 r) (degreeNineWitness24_1 r)
      (degreeNineWitness24_2 r) (degreeNineWitness24_3 r)
    rw [← degreeNineCertificate24 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2 * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 2 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness25_0 r) (degreeNineWitness25_1 r)
      (degreeNineWitness25_2 r) (degreeNineWitness25_3 r)
    rw [← degreeNineCertificate25 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 5 3 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness26_0 r) (degreeNineWitness26_1 r)
      (degreeNineWitness26_2 r) (degreeNineWitness26_3 r)
    rw [← degreeNineCertificate26 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (3 : ℂ) ((1 : ℂ) * Complex.I) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 1 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness27_0 r) (degreeNineWitness27_1 r)
      (degreeNineWitness27_2 r) (degreeNineWitness27_3 r)
    rw [← degreeNineCertificate27 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 6 2 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness28_0 r) (degreeNineWitness28_1 r)
      (degreeNineWitness28_2 r) (degreeNineWitness28_3 r)
    rw [← degreeNineCertificate28 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 0 1) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness29_0 r) (degreeNineWitness29_1 r)
      (degreeNineWitness29_2 r) (degreeNineWitness29_3 r)
    rw [← degreeNineCertificate29 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (6 : ℂ) ((-1 : ℂ) * r ^ 2) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 7 1 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness30_0 r) (degreeNineWitness30_1 r)
      (degreeNineWitness30_2 r) (degreeNineWitness30_3 r)
    rw [← degreeNineCertificate30 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((0 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)
  · change reducedQuotient r (mon 1 8 0 0) ∈ degreeNineLine r
    have hmem := fourRelationSum_mem r
      (degreeNineWitness31_0 r) (degreeNineWitness31_1 r)
      (degreeNineWitness31_2 r) (degreeNineWitness31_3 r)
    rw [← degreeNineCertificate31 r hr] at hmem
    exact class_mem_line_of_scaled_relation r (1 : ℂ) ((1 : ℂ)) _ (by norm_num)
      (by simpa only [map_ofNat, map_one] using hmem)

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNineMonomial_mem_line
end
end


/- Component: seed_trace/SparseSeedDegreeNine.lean -/
section
/-!
# The actual degree-nine quotient component has a unique normalized trace

Every degree-nine polynomial class is reduced using the concrete ideal
relations and finite polynomial membership certificates. The component is
then proved to be a nonzero line, and the previously constructed normalized
trace is proved unique on it.

This is a finite algebra theorem for the sparse seed. No smoothness or
geometric residue comparison is asserted.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem degreeNine_normal_complete_fin :
    ∀ a : Fin 2, ∀ b : Fin 10, ∀ c : Fin 4, ∀ d : Fin 10,
      a.val + b.val + c.val + d.val = 9 → (b.val < 2 ∨ d.val < 2) →
      ∃ i : Fin 32, degreeNineExponent i = ![a.val, b.val, c.val, d.val] := by
  intro a b c d
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide +kernel

theorem degreeNine_normal_complete (a b c d : ℕ)
    (ha : a < 2) (hc : c < 4) (hbd : b < 2 ∨ d < 2)
    (hdegree : a + b + c + d = 9) :
    ∃ i : Fin 32, degreeNineMonomial i = mon a b c d := by
  have hb : b < 10 := by omega
  have hd : d < 10 := by omega
  obtain ⟨i, hi⟩ := degreeNine_normal_complete_fin
    ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩ ⟨d, hd⟩ hdegree hbd
  exact ⟨i, by simp [degreeNineMonomial, hi]⟩

theorem degreeNine_mon_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    (a b c d : ℕ) (hdegree : a + b + c + d = 9) :
    reducedQuotient r (mon a b c d) ∈ degreeNineLine r := by
  induction a using Nat.strong_induction_on generalizing b c d with
  | h a ih =>
      by_cases ha : a < 2
      · by_cases hc : c < 4
        · by_cases hbd : b < 2 ∨ d < 2
          · obtain ⟨i, hi⟩ := degreeNine_normal_complete a b c d ha hc hbd hdegree
            rw [← hi]
            exact degreeNineMonomial_mem_line r hr i
          · have hb : b = (b - 2) + 2 := by omega
            have hd : d = (d - 2) + 2 := by omega
            rw [hb, hd, quotient_mon_bd_add_two_zero]
            exact Submodule.zero_mem _
        · have hc' : c = (c - 4) + 4 := by omega
          rw [hc', quotient_mon_c_add_four_zero]
          exact Submodule.zero_mem _
      · have ha' : a = (a - 2) + 2 := by omega
        rw [ha', quotient_mon_add_two]
        apply Submodule.smul_mem
        exact ih (a - 2) (by omega) (b + 1) c (d + 1) (by omega)

theorem monomial_eq_C_mul_mon (d : Exp) (z : ℂ) :
    monomial d z = C z * mon (d 0) (d 1) (d 2) (d 3) := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]
  apply congrArg (fun e : Exp => monomial e z)
  ext i
  fin_cases i <;> rfl

theorem homogeneous_degreeNine_class_mem_line (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    reducedQuotient r p ∈ degreeNineLine r := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (degreeNineLine r).zero_mem
  | add p q _ _ hp hq =>
      simpa only [map_add] using (degreeNineLine r).add_mem hp hq
  | monomial d z hd =>
      rw [monomial_eq_C_mul_mon, ← smul_eq_C_mul, map_smul]
      apply Submodule.smul_mem
      apply degreeNine_mon_class_mem_line r hr
      have hdegree : d.degree = 9 := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      rw [Finsupp.degree_eq_sum] at hdegree
      norm_num [Fin.sum_univ_succ] at hdegree
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl] at hdegree
      omega

theorem degreeNinePiece_eq_line (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNinePiece r = degreeNineLine r := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact homogeneous_degreeNine_class_mem_line r hr hp
  · unfold degreeNineLine
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact normalizationClass_mem_piece r

/-- The actual homogeneous degree-nine component of the ideal quotient is
one-dimensional. -/
theorem degreeNinePiece_finrank (r : ℂ) (hr : r ^ 3 = 2) :
    Module.finrank ℂ (degreeNinePiece r) = 1 := by
  rw [degreeNinePiece_eq_line r hr]
  exact finrank_span_singleton (normalizationClass_ne_zero r hr)

@[simp] theorem reducedTrace_normalizationClass (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (normalizationClass r) = 1 := trace_normalized r hr

theorem degreeNine_class_eq_trace_smul (r : ℂ) (hr : r ^ 3 = 2)
    {x : ReducedAlgebra r} (hx : x ∈ degreeNinePiece r) :
    x = reducedTrace r hr x • normalizationClass r := by
  rw [degreeNinePiece_eq_line r hr] at hx
  obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rw [map_smul, reducedTrace_normalizationClass, smul_eq_mul, mul_one]

/-- Uniform polynomial ideal-membership statement, beyond the finite list. -/
theorem homogeneous_degreeNine_mod_trace (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p.IsHomogeneous 9) :
    p - C (traceLinear r p) * mon 1 8 0 0 ∈ reducedIdeal r := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change reducedQuotient r (p - C (traceLinear r p) * mon 1 8 0 0) = 0
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero]
  exact degreeNine_class_eq_trace_smul r hr ⟨p, hp, rfl⟩

def degreeNineTrace (r : ℂ) (hr : r ^ 3 = 2) : degreeNinePiece r →ₗ[ℂ] ℂ :=
  (reducedTrace r hr).comp (degreeNinePiece r).subtype

def degreeNineNormalization (r : ℂ) : degreeNinePiece r :=
  ⟨normalizationClass r, normalizationClass_mem_piece r⟩

@[simp] theorem degreeNineTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    degreeNineTrace r hr (degreeNineNormalization r) = 1 := trace_normalized r hr

/-- Any complex-linear trace on this component with the stated normalization
is the constructed trace. No trace values remain as free input data. -/
theorem degreeNineTrace_unique (r : ℂ) (hr : r ^ 3 = 2)
    (τ : degreeNinePiece r →ₗ[ℂ] ℂ)
    (hτ : τ (degreeNineNormalization r) = 1) : τ = degreeNineTrace r hr := by
  ext x
  let c : ℂ := reducedTrace r hr (x : ReducedAlgebra r)
  have hx : x = c • degreeNineNormalization r := by
    apply Subtype.ext
    exact degreeNine_class_eq_trace_smul r hr x.property
  calc
    τ x = τ (c • degreeNineNormalization r) := congrArg τ hx
    _ = c := by rw [map_smul, hτ, smul_eq_mul, mul_one]
    _ = degreeNineTrace r hr x := rfl

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.degreeNinePiece_finrank
#print axioms CycleQ2SeedTrace.homogeneous_degreeNine_mod_trace
#print axioms CycleQ2SeedTrace.degreeNineTrace_unique
end
end


/- Component: euler_lift/EulerKoszulLift.lean -/
section
/-!
# Polynomial Euler lift of a horizontal four-form

In six homogeneous coordinates, a horizontal four-form is described dually
by a skew array B satisfying X_l B_ij - X_i B_lj + X_j B_li = 0.
For homogeneous entries of degree k+1, differentiating that relation gives
an explicit polynomial lift N_j = (sum_l partial_l B_lj)/(k+5).

The theorem proves the lift and its exact grading. It does not assert the
existence of a primitive or the geometric support of the protected residue.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2EulerLift

open MvPolynomial HodgeComputer
open scoped BigOperators

abbrev Poly := AmbientPoly 5
abbrev SkewCoefficients := Fin 6 → Fin 6 → Poly

def columnDivergence (B : SkewCoefficients) (j : Fin 6) : Poly :=
  ∑ i, pderiv i (B i j)

def numeratorLift (k : ℕ) (B : SkewCoefficients) (j : Fin 6) : Poly :=
  C (((k + 5 : ℕ) : ℂ)⁻¹) * columnDivergence B j

theorem sum_partial_coordinate_mul (v : Fin 6 → Poly) (i : Fin 6) :
    (∑ j, pderiv j (X i * v j)) = v i + X i * ∑ j, pderiv j (v j) := by
  classical
  simp [pderiv_X, Pi.single_apply, Finset.sum_add_distrib,
    Finset.mul_sum, add_comm]

theorem sum_radial_derivative {P : Poly} {d : ℕ} (hP : P.IsHomogeneous d) :
    (∑ j : Fin 6, pderiv j (X j * P)) = C ((d + 6 : ℕ) : ℂ) * P := by
  simp only [pderiv_mul, pderiv_X_self, one_mul, Finset.sum_add_distrib]
  rw [hP.sum_X_mul_pderiv]
  simp [nsmul_eq_mul, map_ofNat]
  ring

theorem columnDivergence_homogeneous {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1)) (j : Fin 6) :
    (columnDivergence B j).IsHomogeneous k := by
  unfold columnDivergence
  apply IsHomogeneous.sum Finset.univ
  intro i _
  simpa only [Nat.add_sub_cancel] using (hB i j).pderiv (i := i)

theorem numeratorLift_homogeneous {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1)) (j : Fin 6) :
    (numeratorLift k B j).IsHomogeneous k :=
  (columnDivergence_homogeneous hB j).C_mul _

/-- The differentiated Koszul relation, before division by its nonzero scalar. -/
theorem differentiated_horizontal {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (i j : Fin 6) :
    C ((k + 5 : ℕ) : ℂ) * B i j =
      X i * columnDivergence B j - X j * columnDivergence B i := by
  have hd : (∑ l : Fin 6,
      pderiv l (X l * B i j - X i * B l j + X j * B l i)) = 0 := by
    simp_rw [hhor]
    simp
  simp only [map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hd
  rw [sum_radial_derivative (hB i j), sum_partial_coordinate_mul,
    sum_partial_coordinate_mul, hskew i j] at hd
  change C (((k + 1) + 6 : ℕ) : ℂ) * B i j -
    (B i j + X i * columnDivergence B j) +
    (-B i j + X j * columnDivergence B i) = 0 at hd
  simp only [Nat.cast_add, Nat.cast_ofNat, map_add, map_natCast, map_ofNat] at hd ⊢
  linear_combination hd

/-- Explicit Koszul exactness with the numerator degree required by Verify. -/
theorem numeratorLift_wedge {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (i j : Fin 6) :
    B i j = X i * numeratorLift k B j - X j * numeratorLift k B i := by
  have hc : ((k + 5 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : k + 5 ≠ 0)
  have hinv : C (((k + 5 : ℕ) : ℂ)⁻¹) * C ((k + 5 : ℕ) : ℂ) = (1 : Poly) := by
    rw [← map_mul, inv_mul_cancel₀ hc, map_one]
  have hd := differentiated_horizontal hB hskew hhor i j
  have hh := congrArg (fun P : Poly => C (((k + 5 : ℕ) : ℂ)⁻¹) * P) hd
  rw [← mul_assoc, hinv, one_mul] at hh
  rw [hh]
  unfold numeratorLift
  ring

/-- Every homogeneous horizontal skew array has polynomial numerator data. -/
theorem exists_homogeneous_lift {k : ℕ} {B : SkewCoefficients}
    (hB : ∀ i j, (B i j).IsHomogeneous (k + 1))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0) :
    ∃ N : Fin 6 → Poly, (∀ i, (N i).IsHomogeneous k) ∧
      (∀ i j, B i j = X i * N j - X j * N i) :=
  ⟨numeratorLift k B, numeratorLift_homogeneous hB,
    numeratorLift_wedge hB hskew hhor⟩

end CycleQ2EulerLift

#print axioms CycleQ2EulerLift.exists_homogeneous_lift
end
end


/- Component: euler_lift/RationalCartan.lean -/
section
/-!
# The coordinate Cartan identity for the bounded primitive

All derivatives here are the actual fraction-field extensions of polynomial
coordinate derivations. The skew coefficients of a rational four-form are
represented in complementary indices. Their exterior derivative in those
coordinates is the column divergence. This file proves the coordinate
identity and its grading; no geometric primitive is assumed to exist.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2Cartan

open MvPolynomial HodgeComputer HodgeTestbed.Conic CycleQ2Bridge
open scoped BigOperators

abbrev Poly := AmbientPoly 5
abbrev RF := RationalFunction 5

local instance : Algebra ℚ RF := DivisionRing.toRatAlgebra
local instance : Module ℚ RF := Algebra.toModule

abbrev coordinate (i : Fin 6) : RF := polynomialMap 5 (X i)
abbrev coordinateDeriv (i : Fin 6) : Derivation ℚ RF RF := rationalPartial 5 i

def radial : Derivation ℚ RF RF := fieldAction coordinateDeriv coordinate

def div (v : Fin 6 → RF) : RF := fieldDivergence coordinateDeriv v

def skewCoefficient (v : Fin 6 → RF) (i j : Fin 6) : RF :=
  coordinate i * v j - coordinate j * v i

theorem radial_polynomial {P : Poly} {d : ℕ} (hP : P.IsHomogeneous d) :
    radial (polynomialMap 5 P) = (d : RF) * polynomialMap 5 P := by
  have h := congrArg (polynomialMap 5) hP.sum_X_mul_pderiv
  simpa only [radial, fieldAction_apply, rationalPartial_map,
    coordinate, coordinateDeriv, map_sum, map_mul, map_nsmul, nsmul_eq_mul,
    map_natCast] using h

theorem radial_quotient {P D : Poly} {p d : ℕ}
    (hP : P.IsHomogeneous p) (hD : D.IsHomogeneous d) (hD0 : D ≠ 0) :
    radial (polynomialMap 5 P / polynomialMap 5 D) =
      ((p : RF) - (d : RF)) * (polynomialMap 5 P / polynomialMap 5 D) := by
  rw [Derivation.leibniz_div, radial_polynomial hP, radial_polynomial hD]
  have hD' := polynomialMap_ne_zero hD0
  simp only [smul_eq_mul]
  field_simp

theorem sum_partial_radial_mul (a : RF) :
    (∑ i : Fin 6, coordinateDeriv i (coordinate i * a)) = 6 * a + radial a := by
  simp only [Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  have hd : ∀ i : Fin 6, coordinateDeriv i (coordinate i) = 1 := by
    intro i
    simp only [coordinateDeriv, coordinate, rationalPartial_map, pderiv_X_self, map_one]
  simp only [hd, mul_one]
  simp [radial, fieldAction_apply, nsmul_eq_mul, add_comm]

theorem sum_partial_coordinate_mul (v : Fin 6 → RF) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (coordinate j * v i)) = v j + coordinate j * div v := by
  classical
  have hd : ∀ i : Fin 6, coordinateDeriv i (coordinate j) = if j = i then 1 else 0 := by
    intro i
    simp [coordinateDeriv, coordinate, rationalPartial_map, pderiv_X, Pi.single_apply]
  simp [Derivation.leibniz, smul_eq_mul, hd, div, fieldDivergence,
    Finset.sum_add_distrib, Finset.mul_sum, add_comm]

/-- The ungraded Cartan coefficient identity. -/
theorem skew_divergence (v : Fin 6 → RF) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (skewCoefficient v i j)) =
      5 * v j + radial (v j) - coordinate j * div v := by
  simp only [skewCoefficient, map_sub, Finset.sum_sub_distrib]
  rw [sum_partial_radial_mul, sum_partial_coordinate_mul]
  ring

theorem skew_divergence_of_weight (v : Fin 6 → RF)
    (hv : ∀ j, radial (v j) = -5 * v j) (j : Fin 6) :
    (∑ i : Fin 6, coordinateDeriv i (skewCoefficient v i j)) =
      -coordinate j * div v := by
  rw [skew_divergence, hv]
  ring

def primitiveVector (F D : Poly) (N : Fin 6 → Poly) : Fin 6 → RF :=
  rationalField (F ^ 2 * D) N

theorem primitiveVector_eq (F D : Poly) (N : Fin 6 → Poly) (j : Fin 6) :
    primitiveVector F D N j = rationalField D N j / (polynomialMap 5 F)^2 := by
  simp only [primitiveVector, rationalField, map_mul, map_pow, div_eq_mul_inv,
    mul_inv_rev]
  ring

theorem primitiveVector_weight {F D : Poly} {m : ℕ} {N : Fin 6 → Poly}
    (hF : F.IsHomogeneous 6) (hF0 : F ≠ 0)
    (hD : D.IsHomogeneous m) (hD0 : D ≠ 0)
    (hN : ∀ j, (N j).IsHomogeneous (m + 7)) (j : Fin 6) :
    radial (primitiveVector F D N j) = -5 * primitiveVector F D N j := by
  have hden : (F ^ 2 * D).IsHomogeneous (m + 12) := by
    simpa only [Nat.mul_one, Nat.reduceMul, Nat.add_comm] using (hF.pow 2).mul hD
  have heq := radial_quotient (hN j) hden (mul_ne_zero (pow_ne_zero 2 hF0) hD0)
  change radial (polynomialMap 5 (N j) / polynomialMap 5 (F ^ 2 * D)) =
    -5 * (polynomialMap 5 (N j) / polynomialMap 5 (F ^ 2 * D))
  rw [heq]
  push_cast
  ring

/-- Divergence of v/F^2 in the actual rational-function differential algebra. -/
theorem div_scaled_square (v : Fin 6 → RF) (f : RF) (hf : f ≠ 0) :
    div (fun j => v j / f ^ 2) =
      (f * div v - 2 * fieldAction coordinateDeriv v f) / f ^ 3 := by
  have hi : ∀ i : Fin 6,
      coordinateDeriv i (v i / f ^ 2) = coordinateDeriv i (v i) / f ^ 2 -
        2 * (v i * coordinateDeriv i f) / f ^ 3 := by
    intro i
    simp only [Derivation.leibniz_div, Derivation.leibniz_pow,
      smul_eq_mul, nsmul_eq_mul]
    norm_num
    field_simp
  simp only [div, fieldDivergence, hi, fieldAction_apply,
    Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  field_simp

/-- The exact coordinate form of omega - d beta = (defect/F^3) Omega. -/
theorem primitive_defect_coefficient {F D : Poly} (A : Poly) {m : ℕ}
    {N : Fin 6 → Poly}
    (hF : F.IsHomogeneous 6) (hF0 : F ≠ 0)
    (hD : D.IsHomogeneous m) (hD0 : D ≠ 0)
    (hN : ∀ j, (N j).IsHomogeneous (m + 7)) (j : Fin 6) :
    coordinate j * polynomialMap 5 A / (polynomialMap 5 F)^3 -
        (∑ i : Fin 6, coordinateDeriv i (skewCoefficient (primitiveVector F D N) i j)) =
      coordinate j * rationalDefect F A 2 (rationalField D N) /
        (polynomialMap 5 F)^3 := by
  rw [skew_divergence_of_weight _ (primitiveVector_weight hF hF0 hD hD0 hN)]
  have hw : primitiveVector F D N = fun j => rationalField D N j / (polynomialMap 5 F)^2 := by
    funext j
    exact primitiveVector_eq F D N j
  rw [hw, div_scaled_square _ _ (polynomialMap_ne_zero hF0)]
  simp only [rationalDefect, div]
  ring

end CycleQ2Cartan

#print axioms CycleQ2Cartan.primitive_defect_coefficient
end
end


/- Component: euler_lift/ComplexCoordinateDerivations.lean -/
section
/-!
# The actual fraction-field coordinate derivations over the complex numbers

The reused fraction-derivation extension was packaged over the rationals.
It annihilates every mapped complex constant. The Leibniz rule therefore
proves complex linearity and gives an actual complex derivation with exactly
the same underlying function and rational scalar restriction.

This resolves the coefficient-field typing needed for a later comparison
with relative complex differentials. No exterior-form comparison or geometric
primitive is asserted here.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2ComplexDerivations
open MvPolynomial HodgeComputer CycleQ2Bridge

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

theorem rationalPartial_complex_constant (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    rationalPartial n i (algebraMap ℂ (RationalFunction n) c) = 0 := by
  rw [IsScalarTower.algebraMap_apply ℂ (AmbientPoly n) (RationalFunction n)]
  change rationalPartial n i (polynomialMap n (C c)) = 0
  rw [rationalPartial_map, pderiv_C, map_zero]

theorem rationalPartial_complex_smul (n : ℕ) (i : Fin (n + 1))
    (c : ℂ) (x : RationalFunction n) :
    rationalPartial n i (c • x) = c • rationalPartial n i x := by
  simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
    rationalPartial_complex_constant, mul_zero, add_zero]
  simp

/-- The same coordinate differential operator, now with its true complex
scalar linearity included in the type. -/
def complexRationalPartial (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℂ (RationalFunction n) (RationalFunction n) where
  toFun := rationalPartial n i
  map_add' := (rationalPartial n i).map_add
  map_smul' := rationalPartial_complex_smul n i
  map_one_eq_zero' := (rationalPartial n i).map_one_eq_zero
  leibniz' := (rationalPartial n i).leibniz

@[simp] theorem complexRationalPartial_apply (n : ℕ) (i : Fin (n + 1))
    (x : RationalFunction n) : complexRationalPartial n i x = rationalPartial n i x := rfl

/-- Restricting this complex derivation recovers the exact original operator. -/
theorem complexRationalPartial_restrictScalars (n : ℕ) (i : Fin (n + 1)) :
    (complexRationalPartial n i).restrictScalars ℚ = rationalPartial n i := by
  ext x
  rfl

@[simp] theorem complexRationalPartial_map (n : ℕ) (i : Fin (n + 1))
    (P : AmbientPoly n) :
    complexRationalPartial n i (polynomialMap n P) = polynomialMap n (pderiv i P) :=
  rationalPartial_map i P

@[simp] theorem complexRationalPartial_constant (n : ℕ) (i : Fin (n + 1)) (c : ℂ) :
    complexRationalPartial n i (algebraMap ℂ (RationalFunction n) c) = 0 :=
  rationalPartial_complex_constant n i c

end CycleQ2ComplexDerivations

#print axioms CycleQ2ComplexDerivations.rationalPartial_complex_smul
#print axioms CycleQ2ComplexDerivations.complexRationalPartial_restrictScalars
end
end


/- Component: pole_reduction/RationalDerivationRegularity.lean -/
section
/-!
# Actual fraction regularity and commuting coordinate derivations

Regularity is represented by a polynomial denominator relatively prime to F.
All closure statements use actual fraction-field arithmetic and the actual
extended coordinate derivations. No regularity or commutation axiom is used.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2Regularity

open MvPolynomial HodgeComputer CycleQ2Bridge
open scoped BigOperators

variable {n : ℕ}

local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

/-- An actual rational function represented with an F-coprime denominator. -/
def RegularAlong (F : AmbientPoly n) (z : RationalFunction n) : Prop :=
  ∃ (P T : AmbientPoly n), T ≠ 0 ∧ IsRelPrime F T ∧
    z = polynomialMap n P / polynomialMap n T

theorem regular_polynomial (F P : AmbientPoly n) :
    RegularAlong F (polynomialMap n P) := by
  exact ⟨P, 1, one_ne_zero, isRelPrime_one_right, by simp⟩

@[simp] theorem regular_zero (F : AmbientPoly n) : RegularAlong F 0 := by
  simpa only [map_zero] using regular_polynomial F 0

@[simp] theorem regular_one (F : AmbientPoly n) : RegularAlong F 1 := by
  simpa only [map_one] using regular_polynomial F 1

theorem RegularAlong.add {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x + y) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  obtain ⟨Q, U, hU, hFU, rfl⟩ := hy
  refine ⟨P * U + Q * T, T * U, mul_ne_zero hT hU, hFT.mul_right hFU, ?_⟩
  have hT' := polynomialMap_ne_zero hT
  have hU' := polynomialMap_ne_zero hU
  simp only [map_add, map_mul]
  field_simp

theorem RegularAlong.neg {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) : RegularAlong F (-x) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  exact ⟨-P, T, hT, hFT, by simp only [map_neg, div_eq_mul_inv]; ring⟩

theorem RegularAlong.sub {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

theorem RegularAlong.mul {F : AmbientPoly n} {x y : RationalFunction n}
    (hx : RegularAlong F x) (hy : RegularAlong F y) : RegularAlong F (x * y) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  obtain ⟨Q, U, hU, hFU, rfl⟩ := hy
  exact ⟨P * Q, T * U, mul_ne_zero hT hU, hFT.mul_right hFU,
    by simp only [map_mul, mul_div_mul_comm]⟩

theorem RegularAlong.pow {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) (k : ℕ) : RegularAlong F (x ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using regular_one F
  | succ k ih => simpa only [pow_succ] using ih.mul hx

theorem RegularAlong.sum {ι : Type*} {F : AmbientPoly n}
    (s : Finset ι) (z : ι → RationalFunction n)
    (hz : ∀ i ∈ s, RegularAlong F (z i)) : RegularAlong F (∑ i ∈ s, z i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using regular_zero F
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hz i (Finset.mem_insert_self i s)).add
      (ih fun j hj => hz j (Finset.mem_insert_of_mem hj))

theorem regular_inv_polynomial (F T : AmbientPoly n)
    (hT : T ≠ 0) (hFT : IsRelPrime F T) :
    RegularAlong F (polynomialMap n T)⁻¹ := by
  exact ⟨1, T, hT, hFT, by simp⟩

/-- Coordinate differentiation preserves actual regularity along F;
the new legal denominator is exactly the square of the old denominator. -/
theorem RegularAlong.rationalPartial {F : AmbientPoly n} {x : RationalFunction n}
    (hx : RegularAlong F x) (i : Fin (n + 1)) :
    RegularAlong F (CycleQ2Bridge.rationalPartial n i x) := by
  obtain ⟨P, T, hT, hFT, rfl⟩ := hx
  refine ⟨pderiv i P * T - P * pderiv i T, T ^ 2,
    pow_ne_zero 2 hT, hFT.pow_right, ?_⟩
  rw [Derivation.leibniz_div]
  simp only [CycleQ2Bridge.rationalPartial_map,
    smul_eq_mul, map_sub, map_mul, map_pow, div_eq_mul_inv, inv_pow]
  ring

/-- Polynomial mixed partials commute, proved directly coefficientwise. -/
theorem polynomial_partials_commute (i j : Fin (n + 1)) (P : AmbientPoly n) :
    pderiv i (pderiv j P) = pderiv j (pderiv i P) := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  ext m
  simp only [coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply,
    if_neg hij, if_neg (Ne.symm hij), add_zero]
  rw [show m + Finsupp.single i 1 + Finsupp.single j 1 =
    m + Finsupp.single j 1 + Finsupp.single i 1 by abel]
  ring

/-- The commutator is a derivation; this elementary construction avoids
requiring a Lie-algebra infrastructure import. -/
private def derivationCommutator
    (D E : Derivation ℚ (RationalFunction n) (RationalFunction n)) :
    Derivation ℚ (RationalFunction n) (RationalFunction n) :=
  Derivation.mk'
    (D.toLinearMap.comp E.toLinearMap - E.toLinearMap.comp D.toLinearMap)
    (by
      intro x y
      change D (E (x * y)) - E (D (x * y)) =
        x * (D (E y) - E (D y)) + y * (D (E x) - E (D x))
      simp only [Derivation.leibniz, smul_eq_mul, map_add]
      ring)

private theorem derivationCommutator_apply
    (D E : Derivation ℚ (RationalFunction n) (RationalFunction n))
    (z : RationalFunction n) :
    derivationCommutator D E z = D (E z) - E (D z) := rfl

/-- The actual extended coordinate derivations commute on every rational
function, with no commutation hypothesis. -/
theorem rationalPartials_commute (i j : Fin (n + 1)) :
    Function.Commute (CycleQ2Bridge.rationalPartial n i)
      (CycleQ2Bridge.rationalPartial n j) := by
  let D := derivationCommutator (CycleQ2Bridge.rationalPartial n i)
    (CycleQ2Bridge.rationalPartial n j)
  have hmap : ∀ P : AmbientPoly n, D (polynomialMap n P) = 0 := by
    intro P
    dsimp only [D]
    rw [derivationCommutator_apply]
    simp only [CycleQ2Bridge.rationalPartial_map]
    rw [polynomial_partials_commute i j P, sub_self]
  intro z
  have hz : D z = 0 := by
    obtain ⟨P, T, _hT, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly n) z
    rw [Derivation.leibniz_div, hmap P, hmap T]
    simp
  exact sub_eq_zero.mp hz

end CycleQ2Regularity

#print axioms CycleQ2Regularity.RegularAlong.rationalPartial
#print axioms CycleQ2Regularity.rationalPartials_commute
end
end


/- Component: euler_lift/HorizontalPrimitiveCertificate.lean -/
section
/-!
# A homogeneous horizontal primitive gives the protected certificate

The inputs here are actual rational coefficient arrays and regular fractions.
Euler lifting supplies the polynomial numerators; the coordinate differential
identity supplies the defect; legality of one coordinate lets us remove its
factor at the generic point of F. This closes the algebraic implication from
a bounded homogeneous primitive, but does not prove that primitive exists.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2HorizontalPrimitive

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open CycleQ2EulerLift CycleQ2Cartan
open scoped BigOperators

local instance : Algebra ℚ (RationalFunction 5) := DivisionRing.toRatAlgebra
local instance : Module ℚ (RationalFunction 5) := Algebra.toModule

def boundedCoefficient (F S : AmbientPoly 5)
    (B : SkewCoefficients) (i j : Fin 6) : RationalFunction 5 :=
  polynomialMap 5 (B i j) / polynomialMap 5 (F ^ 2 * S ^ 2)

def residualCoefficient (F A S : AmbientPoly 5)
    (B : SkewCoefficients) (j : Fin 6) : RationalFunction 5 :=
  coordinate j * polynomialMap 5 A / (polynomialMap 5 F) ^ 3 -
    ∑ i, rationalPartial 5 i (boundedCoefficient F S B i j)

/-- One nonvanishing homogeneous coordinate is a unit at the generic
point of F, so regularity of its coefficient implies the localized equation. -/
theorem localizedEquation_of_regular_coefficient
    {F A D : AmbientPoly 5} {N : Fin 6 → AmbientPoly 5} (j : Fin 6)
    (hF0 : F ≠ 0) (hX : IsRelPrime F (X j))
    (hregular : RegularAlong F
      (coordinate j * rationalDefect F A 2 (rationalField D N) /
        (polynomialMap 5 F) ^ 3)) :
    LocalizedEquation F A 2 D N := by
  obtain ⟨P, T, hT, hFT, heq⟩ := hregular
  refine ⟨P, X j * T, mul_ne_zero (X_ne_zero j) hT, hX.mul_right hFT, ?_⟩
  have hF := polynomialMap_ne_zero hF0
  have hX0 := polynomialMap_ne_zero (X_ne_zero j : (X j : AmbientPoly 5) ≠ 0)
  have hT0 := polynomialMap_ne_zero hT
  simp only [coordinate] at heq
  simp only [map_mul]
  field_simp at heq ⊢
  linear_combination heq

theorem boundedCoefficient_eq_skew
    (F S : AmbientPoly 5) (B : SkewCoefficients) (N : Fin 6 → AmbientPoly 5)
    (hB : ∀ i j, B i j = X i * N j - X j * N i) (i j : Fin 6) :
    boundedCoefficient F S B i j = skewCoefficient (primitiveVector F (S ^ 2) N) i j := by
  rw [boundedCoefficient, hB]
  simp only [skewCoefficient, primitiveVector, rationalField, coordinate,
    map_sub, map_mul, div_eq_mul_inv]
  ring

/-- A concrete homogeneous horizontal coefficient array with a regular
residual gives the unchanged protected theorem, with no extra axioms. -/
theorem protected_certificate_of_horizontal_primitive
    (e : ℕ) (S : AmbientPoly 5) (B : SkewCoefficients)
    (hS : S.IsHomogeneous e) (hlegal : ¬ HodgeSubmission.F ∣ S)
    (hB : ∀ i j, (B i j).IsHomogeneous (2 * e + 8))
    (hskew : ∀ i j, B j i = -B i j)
    (hhor : ∀ l i j, X l * B i j - X i * B l j + X j * B l i = 0)
    (hregular : RegularAlong HodgeSubmission.F
      (residualCoefficient HodgeSubmission.F HodgeSubmission.A S B 0)) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  have hS0 : S ≠ 0 := by
    intro hz
    exact hlegal (hz ▸ dvd_zero _)
  have hB' : ∀ i j, (B i j).IsHomogeneous ((2 * e + 7) + 1) := by
    simpa only [Nat.add_assoc] using hB
  obtain ⟨N, hN, hwedge⟩ := exists_homogeneous_lift hB' hskew hhor
  have hDhom : (S ^ 2).IsHomogeneous (2 * e) := by
    simpa only [Nat.mul_comm] using hS.pow 2
  have hres : residualCoefficient HodgeSubmission.F HodgeSubmission.A S B 0 =
      coordinate 0 * rationalDefect HodgeSubmission.F HodgeSubmission.A 2
        (rationalField (S ^ 2) N) / (polynomialMap 5 HodgeSubmission.F)^3 := by
    unfold residualCoefficient
    simp_rw [boundedCoefficient_eq_skew HodgeSubmission.F S B N hwedge]
    exact primitive_defect_coefficient HodgeSubmission.A
      CycleQ2Workspace.originalF_homogeneous CycleQ2Workspace.originalF_ne_zero
      hDhom (pow_ne_zero 2 hS0) hN 0
  rw [hres] at hregular
  have hX : IsRelPrime HodgeSubmission.F (X (0 : Fin 6)) :=
    CycleQ2ExactIrreducible.protected_F_irreducible.isRelPrime_iff_not_dvd.mpr
      (CycleQ2SupportEquation.not_dvd_coordinate_of_degree_gt_one
        HodgeSubmission.F
        (by rw [CycleQ2Workspace.originalF_totalDegree]; norm_num) 0)
  have hlocal := localizedEquation_of_regular_coefficient 0
    CycleQ2Workspace.originalF_ne_zero hX hregular
  exact (CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
    HodgeSubmission.F HodgeSubmission.A
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
    (Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous)).mpr
    ⟨e, S, N, hS, hlegal, (fun i => by
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        Homogeneous.of_isHomogeneous (hN i)), hlocal⟩

end CycleQ2HorizontalPrimitive

#print axioms CycleQ2HorizontalPrimitive.protected_certificate_of_horizontal_primitive
end
end


/- Component: pole_reduction/VectorPoleReduction.lean -/
section
/-!
# Elementary pole reduction for rational primitives

This is a calculation in a genuine differential field. Subtracting an exact
lower-degree form is represented by adding the divergence of a skew array.
Commutation of the coordinate derivations proves that this changes no top
differential. When the normal contraction is divisible by f, the formula
lowers the primitive's f-pole by one. No Hodge filtration is used.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2PoleReduction

open HodgeTestbed.Conic
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [CharZero K] [Algebra ℚ K]

def skewDiv (δ : ι → Derivation ℚ K K) (B : ι → ι → K) (i : ι) : K :=
  ∑ j, δ j (B i j)

/-- Commuting partial derivatives annihilate the divergence of a skew array. -/
theorem divergence_skewDiv (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (B : ι → ι → K) (hskew : ∀ i j, B j i = -B i j) :
    fieldDivergence δ (skewDiv δ B) = 0 := by
  have hs : fieldDivergence δ (skewDiv δ B) =
      -fieldDivergence δ (skewDiv δ B) := by
    simp only [fieldDivergence, skewDiv, map_sum]
    calc
      (∑ i, ∑ j, δ i (δ j (B i j))) = ∑ i, ∑ j, δ j (δ i (B j i)) :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, -δ i (δ j (B i j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        calc
          δ j (δ i (B j i)) = δ j (δ i (-B i j)) :=
            congrArg (fun z => δ j (δ i z)) (hskew i j)
          _ = -δ i (δ j (B i j)) := by rw [map_neg, map_neg, hcomm j i]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  have ht : (2 : K) * fieldDivergence δ (skewDiv δ B) = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp ht).resolve_left (by norm_num)

def coordinateSkew (r : ι) (a : ι → K) (i j : ι) : K :=
  (if j = r then a i else 0) - (if i = r then a j else 0)

theorem coordinateSkew_skew (r : ι) (a : ι → K) (i j : ι) :
    coordinateSkew r a j i = -coordinateSkew r a i j := by
  simp only [coordinateSkew]
  ring

theorem skewDiv_coordinateSkew (δ : ι → Derivation ℚ K K)
    (r : ι) (a : ι → K) (i : ι) :
    skewDiv δ (coordinateSkew r a) i =
      δ r (a i) - if i = r then fieldDivergence δ a else 0 := by
  by_cases hi : i = r
  · subst i
    simp [skewDiv, coordinateSkew, fieldDivergence,
      Finset.sum_sub_distrib, apply_ite]
  · simp [skewDiv, coordinateSkew, hi, fieldDivergence,
      Finset.sum_sub_distrib, apply_ite]

/-- Adding this correction preserves the actual top differential. -/
theorem coordinate_correction_preserves_divergence
    (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (r : ι) (a v : ι → K) :
    fieldDivergence δ
      (fun i => v i + δ r (a i) - if i = r then fieldDivergence δ a else 0) =
      fieldDivergence δ v := by
  have hc : (fun i => v i + δ r (a i) -
      if i = r then fieldDivergence δ a else 0) =
      fun i => v i + skewDiv δ (coordinateSkew r a) i := by
    funext i
    rw [skewDiv_coordinateSkew]
    ring
  rw [hc, fieldDivergence_add, divergence_skewDiv δ hcomm _
    (coordinateSkew_skew r a), add_zero]

/-- The quotient rule in the form used by a pole-lowering correction. -/
theorem derivative_over_power (δ : Derivation ℚ K K)
    (a f : K) (p : ℕ) (hp : p ≠ 0) (hf : f ≠ 0) :
    δ (a / ((p : K) * f ^ p)) =
      δ a / ((p : K) * f ^ p) - a * δ f / f ^ (p + 1) := by
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have hpred : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp)
  have hpow : f ^ (p - 1) * f = f ^ p := by rw [← pow_succ, hpred]
  simp only [Derivation.leibniz_div, Derivation.leibniz, Derivation.map_natCast,
    Derivation.leibniz_pow, smul_eq_mul, nsmul_eq_mul, mul_zero, add_zero]
  simp only [pow_succ, ← hpow]
  field_simp

theorem derivative_div_power (δ : Derivation ℚ K K)
    (a f : K) (p : ℕ) (hf : f ≠ 0) :
    δ (a / f ^ p) = δ a / f ^ p - (p : K) * a * δ f / f ^ (p + 1) := by
  by_cases hp : p = 0
  · subst p
    simp
  have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have h := derivative_over_power δ ((p : K) * a) f p hp hf
  have harg : (p : K) * a / ((p : K) * f ^ p) = a / f ^ p := by field_simp
  rw [harg] at h
  simpa only [Derivation.leibniz, Derivation.map_natCast, smul_eq_mul,
    mul_zero, add_zero, mul_div_mul_left _ _ hp'] using h

theorem divergence_div_power (δ : ι → Derivation ℚ K K)
    (b : ι → K) (f : K) (p : ℕ) (hf : f ≠ 0) :
    fieldDivergence δ (fun i => b i / f ^ p) =
      fieldDivergence δ b / f ^ p -
        (p : K) * fieldAction δ b f / f ^ (p + 1) := by
  simp only [fieldDivergence, derivative_div_power _ _ _ _ hf,
    fieldAction_apply, Finset.sum_sub_distrib, ← Finset.sum_div, Finset.mul_sum]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A third-order pole in the top differential forces the normal
contraction to be divisible by f whenever the primitive has a higher pole. -/
theorem normal_divisibility_of_triple_pole
    (δ : ι → Derivation ℚ K K) (b : ι → K) (f a r : K) (p : ℕ)
    (hp : 2 ≤ p) (hf : f ≠ 0)
    (hdiv : fieldDivergence δ (fun i => b i / f ^ (p + 1)) = a / f ^ 3 + r) :
    fieldAction δ b f = f *
      ((fieldDivergence δ b - a * f ^ (p - 2) - r * f ^ (p + 1)) / (p + 1 : ℕ)) := by
  rw [divergence_div_power δ b f (p + 1) hf] at hdiv
  have hp' : ((p + 1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have he : p = p - 2 + 2 := by omega
  have hpow : f ^ (p + 1) = f ^ (p - 2) * f ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hpow2 : f ^ (p + 1 + 1) = f ^ (p - 2) * f ^ 4 := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow, hpow2] at hdiv
  rw [hpow]
  have hbase : f ^ (p - 2) ≠ 0 := pow_ne_zero _ hf
  field_simp at hdiv ⊢
  linear_combination -hdiv

def reducedNumerator (δ : ι → Derivation ℚ K K)
    (r : ι) (b : ι → K) (g c : K) (p : ℕ) (i : ι) : K :=
  if i = r then
    c / g - (∑ j ∈ Finset.univ.erase r, δ j (b j / g)) / (p : K)
  else δ r (b i / g) / (p : K)

/-- One exact pole reduction. The normal contraction hypothesis is the
leading-pole cancellation forced by a bounded top differential. -/
theorem pole_drop (δ : ι → Derivation ℚ K K)
    (hcomm : ∀ i j, Function.Commute (δ i) (δ j))
    (r : ι) (b : ι → K) (f c : K) (p : ℕ)
    (hp : p ≠ 0) (hf : f ≠ 0) (hg : δ r f ≠ 0)
    (hnormal : fieldAction δ b f = f * c) :
    fieldDivergence δ (fun i => b i / f ^ (p + 1)) =
      fieldDivergence δ
        (fun i => reducedNumerator δ r b (δ r f) c p i / f ^ p) := by
  let g := δ r f
  let a : ι → K := fun i => (b i / g) / ((p : K) * f ^ p)
  have hcor := coordinate_correction_preserves_divergence δ hcomm r a
    (fun i => b i / f ^ (p + 1))
  have heq : (fun i => b i / f ^ (p + 1) + δ r (a i) -
      if i = r then fieldDivergence δ a else 0) =
      (fun i => reducedNumerator δ r b g c p i / f ^ p) := by
    funext i
    by_cases hi : i = r
    · subst i
      have hsum : fieldDivergence δ a = δ r (a r) +
          ∑ j ∈ Finset.univ.erase r, δ j (a j) := by
        exact (Finset.add_sum_erase Finset.univ (fun j => δ j (a j))
          (Finset.mem_univ r)).symm
      rw [hsum]
      simp only [reducedNumerator, if_true]
      have hd : ∀ j, δ j (a j) = δ j (b j / g) / ((p : K) * f ^ p) -
          (b j / g) * δ j f / f ^ (p + 1) := by
        intro j
        exact derivative_over_power (δ j) (b j / g) f p hp hf
      simp only [hd, Finset.sum_sub_distrib, ← Finset.sum_div]
      have hn : b r * g + ∑ j ∈ Finset.univ.erase r, b j * δ j f = f * c := by
        rw [fieldAction_apply] at hnormal
        rw [← Finset.add_sum_erase Finset.univ (fun j => b j * δ j f)
          (Finset.mem_univ r)] at hnormal
        exact hnormal
      have hfactor : (∑ j ∈ Finset.univ.erase r, (b j / g) * δ j f) =
          (∑ j ∈ Finset.univ.erase r, b j * δ j f) / g := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      rw [hfactor]
      have hp' : (p : K) ≠ 0 := Nat.cast_ne_zero.mpr hp
      have hg' : g ≠ 0 := hg
      field_simp
      linear_combination (p : K) * f ^ p * hn
    · simp only [hi, if_false, sub_zero, reducedNumerator]
      change b i / f ^ (p + 1) +
        δ r ((b i / g) / ((p : K) * f ^ p)) = _
      rw [derivative_over_power (δ r) (b i / g) f p hp hf]
      have hg' : g ≠ 0 := hg
      dsimp [g]
      field_simp
      ring
  rw [heq] at hcor
  exact hcor.symm

end CycleQ2PoleReduction

#print axioms CycleQ2PoleReduction.pole_drop
end
end


/- Component: pole_reduction/PoleNormalization.lean -/
section
/-!
# Double-pole normalization over the actual fraction field

Every rational vector admits a common finite pole order along an irreducible
F. If its top differential is A/F^3 plus an F-regular remainder, repeated
elementary pole reduction gives a vector with pole order at most two.
The proof keeps the same differential and permits unrestricted additional
denominators coprime to F. It requires no Hodge-filtration strictness.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2PoleNormalization

open MvPolynomial HodgeComputer CycleQ2Bridge CycleQ2Regularity
open HodgeTestbed.Conic CycleQ2PoleReduction
open scoped BigOperators

variable {n : ℕ}

local instance : Algebra ℚ (RationalFunction n) := DivisionRing.toRatAlgebra
local instance : Module ℚ (RationalFunction n) := Algebra.toModule

theorem regular_constant (F : AmbientPoly n) (c : ℂ) :
    RegularAlong F (polynomialMap n (C c)) := regular_polynomial F (C c)

theorem regular_nat_inverse (F : AmbientPoly n) (p : ℕ) :
    RegularAlong F ((p : RationalFunction n)⁻¹) := by
  have h := regular_constant F ((p : ℂ)⁻¹)
  have he : polynomialMap n (C ((p : ℂ)⁻¹)) = (p : RationalFunction n)⁻¹ := by
    change ((polynomialMap n).comp C) ((p : ℂ)⁻¹) = _
    rw [map_inv₀, map_natCast]
  simpa only [he] using h

/-- Extracting the maximal power of F from a denominator gives an actual
F-regular numerator and a finite pole order. -/
theorem exists_regular_pole_representation
    {F : AmbientPoly n} (hF : Irreducible F) (z : RationalFunction n) :
    ∃ (m : ℕ) (b : RationalFunction n), RegularAlong F b ∧
      z = b / (polynomialMap n F)^m := by
  obtain ⟨P, T, hT, rfl⟩ := IsFractionRing.div_surjective (AmbientPoly n) z
  have hT0 : T ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hT
  obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hT0 hF
  have hU : U ≠ 0 := by
    intro h
    apply hT0
    simp [hfactor, h]
  refine ⟨m, polynomialMap n P / polynomialMap n U,
    ⟨P, U, hU, hF.isRelPrime_iff_not_dvd.mpr hFU, rfl⟩, ?_⟩
  simp only [hfactor, map_mul, map_pow, div_eq_mul_inv, mul_inv_rev]
  ring

theorem exists_uniform_pole_representation
    {F : AmbientPoly n} (hF : Irreducible F)
    (v : Fin (n + 1) → RationalFunction n) :
    ∃ (m : ℕ) (b : Fin (n + 1) → RationalFunction n),
      (∀ i, RegularAlong F (b i)) ∧
      v = fun i => b i / (polynomialMap n F)^m := by
  classical
  choose m b hb heq using fun i => exists_regular_pole_representation hF (v i)
  let M := Finset.univ.sup m
  have hm : ∀ i, m i ≤ M := fun i => Finset.le_sup (Finset.mem_univ i)
  refine ⟨M, fun i => b i * (polynomialMap n F)^(M - m i),
    (fun i => (hb i).mul ((regular_polynomial F F).pow _)), ?_⟩
  funext i
  rw [heq i]
  have hF0 := polynomialMap_ne_zero hF.ne_zero
  have hpow : (polynomialMap n F)^M =
      (polynomialMap n F)^(M - m i) * (polynomialMap n F)^(m i) := by
    rw [← pow_add, Nat.sub_add_cancel (hm i)]
  rw [hpow]
  field_simp

theorem regular_divergence {F : AmbientPoly n}
    {b : Fin (n + 1) → RationalFunction n} (hb : ∀ i, RegularAlong F (b i)) :
    RegularAlong F (fieldDivergence (rationalPartial n) b) := by
  exact RegularAlong.sum Finset.univ _ (fun i _ => (hb i).rationalPartial i)

/-- The explicit new numerator remains regular along F. -/
theorem regular_reducedNumerator {F : AmbientPoly n}
    (r : Fin (n + 1)) {b : Fin (n + 1) → RationalFunction n}
    {c : RationalFunction n} (p : ℕ)
    (hb : ∀ i, RegularAlong F (b i)) (hc : RegularAlong F c)
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F)) (i : Fin (n + 1)) :
    RegularAlong F (reducedNumerator (rationalPartial n) r b
      (rationalPartial n r (polynomialMap n F)) c p i) := by
  have hginv : RegularAlong F (rationalPartial n r (polynomialMap n F))⁻¹ := by
    rw [rationalPartial_map]
    exact regular_inv_polynomial F _ hg0 hg
  have hbdiv : ∀ j, RegularAlong F (b j /
      rationalPartial n r (polynomialMap n F)) := fun j => by
    simpa only [div_eq_mul_inv] using (hb j).mul hginv
  unfold reducedNumerator
  split
  · apply RegularAlong.sub
    · simpa only [div_eq_mul_inv] using hc.mul hginv
    · simpa only [div_eq_mul_inv] using
        (RegularAlong.sum (Finset.univ.erase r) _
          (fun j _ => (hbdiv j).rationalPartial j)).mul (regular_nat_inverse F p)
  · simpa only [div_eq_mul_inv] using
      ((hbdiv i).rationalPartial r).mul (regular_nat_inverse F p)

/-- Induction lowers an arbitrary finite pole order to two. The remainder
and the top differential are preserved exactly throughout the induction. -/
theorem normalize_pole_order
    {F : AmbientPoly n} (hF0 : F ≠ 0) (r : Fin (n + 1))
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F))
    (a t : RationalFunction n) (ha : RegularAlong F a) (ht : RegularAlong F t)
    (m : ℕ) (b : Fin (n + 1) → RationalFunction n)
    (hb : ∀ i, RegularAlong F (b i))
    (hdiv : fieldDivergence (rationalPartial n)
      (fun i => b i / (polynomialMap n F)^m) = a / (polynomialMap n F)^3 + t) :
    ∃ c : Fin (n + 1) → RationalFunction n,
      (∀ i, RegularAlong F (c i)) ∧
      fieldDivergence (rationalPartial n)
        (fun i => c i / (polynomialMap n F)^2) = a / (polynomialMap n F)^3 + t := by
  have hf := polynomialMap_ne_zero hF0
  induction m using Nat.strong_induction_on generalizing b with
  | h m ih =>
    by_cases hm : m ≤ 2
    · refine ⟨fun i => b i * (polynomialMap n F)^(2 - m),
        (fun i => (hb i).mul ((regular_polynomial F F).pow _)), ?_⟩
      have hv : (fun i => b i * (polynomialMap n F)^(2 - m) /
          (polynomialMap n F)^2) = fun i => b i / (polynomialMap n F)^m := by
        funext i
        have hpow : (polynomialMap n F)^2 =
            (polynomialMap n F)^(2 - m) * (polynomialMap n F)^m := by
          rw [← pow_add, Nat.sub_add_cancel hm]
        rw [hpow]
        field_simp
      rw [hv]
      exact hdiv
    · obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hp : 2 ≤ p := by omega
      let c := (fieldDivergence (rationalPartial n) b -
        a * (polynomialMap n F)^(p - 2) - t * (polynomialMap n F)^(p + 1)) /
          ((p + 1 : ℕ) : RationalFunction n)
      have hc : RegularAlong F c := by
        exact ((regular_divergence hb).sub
          (ha.mul ((regular_polynomial F F).pow _)) |>.sub
          (ht.mul ((regular_polynomial F F).pow _))).mul (regular_nat_inverse F (p + 1))
      have hn := normal_divisibility_of_triple_pole (rationalPartial n)
        b (polynomialMap n F) a t p hp hf hdiv
      have hgnz : rationalPartial n r (polynomialMap n F) ≠ 0 := by
        rw [rationalPartial_map]
        exact polynomialMap_ne_zero hg0
      have hdrop := pole_drop (rationalPartial n) rationalPartials_commute
        r b (polynomialMap n F) c p (by omega) hf hgnz hn
      let b' := reducedNumerator (rationalPartial n) r b
        (rationalPartial n r (polynomialMap n F)) c p
      apply ih p (by omega) b'
      · exact regular_reducedNumerator r p hb hc hg0 hg
      · exact hdrop.symm.trans hdiv

/-- Unrestricted rational primitives can always be normalized to double
poles along F. This is an existence theorem about an actual differential,
and does not assert that the initial rational primitive exists. -/
theorem double_pole_primitive_of_rational_primitive
    {F : AmbientPoly n} (hF : Irreducible F) (r : Fin (n + 1))
    (hg0 : pderiv r F ≠ 0) (hg : IsRelPrime F (pderiv r F))
    (a t : RationalFunction n) (ha : RegularAlong F a) (ht : RegularAlong F t)
    (v : Fin (n + 1) → RationalFunction n)
    (hdiv : fieldDivergence (rationalPartial n) v =
      a / (polynomialMap n F)^3 + t) :
    ∃ c : Fin (n + 1) → RationalFunction n,
      (∀ i, RegularAlong F (c i)) ∧
      fieldDivergence (rationalPartial n)
        (fun i => c i / (polynomialMap n F)^2) = a / (polynomialMap n F)^3 + t := by
  obtain ⟨m, b, hb, hv⟩ := exists_uniform_pole_representation hF v
  rw [hv] at hdiv
  exact normalize_pole_order hF.ne_zero r hg0 hg a t ha ht m b hb hdiv

end CycleQ2PoleNormalization

#print axioms CycleQ2PoleNormalization.double_pole_primitive_of_rational_primitive
end
end


/- Component: pole_reduction/ResiduePrimitiveClosure.lean -/
section
/-!
An explicit algebraic closure of a second normal-residue primitive.

The source coefficient and weighted residue divergence are the actual
definitions from the protected HigherResidues and HoldoutCover libraries.
The construction below derives its complete pole-two defect; the defect
identity is not an input. An application still has to prove existence of
the residue primitive and regularity of its lifts along the hypersurface.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace CycleQ2ResidueClosure

open HoldoutConstruction SplitHigherResidue
open scoped BigOperators

variable {K : Type*} [Field K] [CharZero K]
variable {ι : Type*} [Fintype ι]

/-- Tangent derivations obtained from the actual ambient coordinate derivatives. -/
def ambientTangent (D₀ : Derivation ℤ K K) (D : ι → Derivation ℤ K K)
    (f : K) (i : ι) : Derivation ℤ K K :=
  D i - (D i f / D₀ f) • D₀

@[simp] theorem ambientTangent_apply (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f x : K) (i : ι) :
    ambientTangent D₀ D f i x = D i x - D i f / D₀ f * D₀ x := rfl

theorem ambientTangent_f (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f : K) (hg : D₀ f ≠ 0) (i : ι) :
    ambientTangent D₀ D f i f = 0 := by
  rw [ambientTangent_apply]
  field_simp
  ring

/-- The existing second normal source is the second differentiated density. -/
theorem normalSourceTwo_eq_derivative (D₀ : Derivation ℤ K K)
    (a g : K) (hg : g ≠ 0) :
    normalSourceTwo a (D₀ a) (D₀ (D₀ a)) g (D₀ g) (D₀ (D₀ g)) =
      D₀ (D₀ (a / g) / (2 * g)) := by
  have htwo : D₀ (2 : K) = 0 := D₀.map_natCast 2
  simp only [normalSourceTwo, Derivation.leibniz_div, Derivation.leibniz_inv,
    Derivation.leibniz, Derivation.leibniz_pow, map_sub, map_add,
    htwo, smul_eq_mul, nsmul_eq_mul]
  ring_nf
  field_simp [hg]
  ring

private theorem half_density_derivative (D₀ : Derivation ℤ K K)
    (a g : K) (hg : g ≠ 0) :
    D₀ (a / (2 * g)) = D₀ (a / g) / 2 := by
  have htwo : D₀ (2 : K) = 0 := D₀.map_natCast 2
  simp only [Derivation.leibniz_div, Derivation.leibniz,
    htwo, smul_eq_mul]
  field_simp [hg]
  ring

/-- The normal component of the rational vector field. -/
def closureNormal (D₀ : Derivation ℤ K K) (D : ι → Derivation ℤ K K)
    (f a : K) (w : ι → K) : K :=
  a / (2 * D₀ f) + f * (D₀ (a / D₀ f) / (2 * D₀ f) -
    ∑ i, D i f * w i / D₀ f)

/-- The tangent ambient components of the rational vector field. -/
def closureTangent (f : K) (w : ι → K) (i : ι) : K := f * w i

theorem closure_action (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) :
    2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) = a + f * D₀ (a / D₀ f) := by
  unfold closureNormal closureTangent
  rw [← Finset.sum_div]
  have hs : (∑ i, f * w i * D i f) = f * ∑ i, D i f * w i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hs]
  field_simp
  ring

private theorem tangent_quotient_derivative (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) (i : ι) :
    D i (w i) - D₀ (D i f * w i / D₀ f) =
      ambientTangent D₀ D f i (w i) -
        w i * ambientTangent D₀ D f i (D₀ f) / D₀ f := by
  simp only [ambientTangent_apply, Derivation.leibniz_div,
    Derivation.leibniz, smul_eq_mul, mixed]
  field_simp
  ring

theorem closure_divergence (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) :
    D₀ (closureNormal D₀ D f a w) + ∑ i, D i (closureTangent f w i) =
      D₀ (a / D₀ f) + f *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) := by
  have hs : (∑ i, D i (w i)) - ∑ i, D₀ (D i f * w i / D₀ f) =
      residueDivergence (ambientTangent D₀ D f) (D₀ f) w := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [tangent_quotient_derivative D₀ D f w hg mixed]
    simp only [residueDivergence, fieldDivergence, Finset.sum_sub_distrib,
      Finset.sum_div]
  rw [normalSourceTwo_eq_derivative D₀ a (D₀ f) hg]
  unfold closureNormal closureTangent
  simp only [map_add, map_sub, map_sum, Derivation.leibniz, smul_eq_mul,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [half_density_derivative D₀ a (D₀ f) hg]
  rw [← hs]
  rw [← Finset.sum_div]
  have hswap : (∑ i, w i * D i f) = ∑ i, D i f * w i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hswap]
  field_simp [hg]
  ring

/-- The complete pole-two defect of the explicitly constructed field. -/
theorem closure_defect (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f)) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) =
      f ^ 2 *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) := by
  rw [closure_action D₀ D f a w hg, closure_divergence D₀ D f a w hg mixed]
  ring

/-- Vanishing of the residue equation modulo f gives third-order divisibility. -/
theorem closure_defect_of_residue (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K) (t : K)
    (hg : D₀ f ≠ 0) (mixed : ∀ i, D₀ (D i f) = D i (D₀ f))
    (residue : normalSourceTwo a (D₀ a) (D₀ (D₀ a))
        (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
        residueDivergence (ambientTangent D₀ D f) (D₀ f) w = f * t) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) = f ^ 3 * t := by
  rw [closure_defect D₀ D f a w hg mixed, residue]
  ring

/-- Commuting actual coordinate derivations supply the required mixed identity. -/
theorem closure_defect_of_commute (D₀ : Derivation ℤ K K)
    (D : ι → Derivation ℤ K K) (f a : K) (w : ι → K)
    (hg : D₀ f ≠ 0) (commute : ∀ i, Function.Commute D₀ (D i)) :
    a - 2 * (closureNormal D₀ D f a w * D₀ f +
      ∑ i, closureTangent f w i * D i f) +
      f * (D₀ (closureNormal D₀ D f a w) +
        ∑ i, D i (closureTangent f w i)) =
      f ^ 2 *
        (normalSourceTwo a (D₀ a) (D₀ (D₀ a))
          (D₀ f) (D₀ (D₀ f)) (D₀ (D₀ (D₀ f))) +
          residueDivergence (ambientTangent D₀ D f) (D₀ f) w) :=
  closure_defect D₀ D f a w hg (fun i => commute i f)

#print axioms normalSourceTwo_eq_derivative
#print axioms closure_defect
#print axioms closure_defect_of_residue

end CycleQ2ResidueClosure
end
end


