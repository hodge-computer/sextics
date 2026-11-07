import Proposal.Assembly
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Same-denominator radial normalization for the original pole parameter q = 2.

The radial correction preserves the whole cleared defect. Existence of a legal
normalized rational solution remains the open obligation in Solution.lean.
-/

noncomputable section
namespace CycleQ2Normalization
open MvPolynomial HodgeComputer HodgeTestbed CycleQ2Workspace CycleQ2Assembly
open scoped BigOperators

abbrev coordinates : Fin 6 → Poly := fun i => X i

def euler (P : Poly) : Poly := directional P coordinates

def radial (H : Poly) : Fin 6 → Poly :=
  fun i => C (1 / 12 : ℂ) * H * X i

def normalizeNumerators (N : Fin 6 → Poly) (H : Poly) : Fin 6 → Poly :=
  fun i => N i + radial H i

lemma euler_add (P Q : Poly) : euler (P + Q) = euler P + euler Q := by
  simp [euler, directional, map_add, add_mul, Finset.sum_add_distrib]

lemma euler_mul (P Q : Poly) : euler (P * Q) = Q * euler P + P * euler Q := by
  exact HodgeTestbed.directional_product Q P coordinates

lemma euler_C (c : ℂ) : euler (C c) = 0 := by
  simp [euler, directional, coordinates]

lemma euler_of_homogeneous {P : Poly} {n : ℕ} (h : P.IsHomogeneous n) :
    euler P = C (n : ℂ) * P := by
  calc
    euler P = ∑ i : Fin 6, X i * pderiv i P := by
      simp [euler, directional, coordinates, mul_comm]
    _ = n • P := h.sum_X_mul_pderiv
    _ = C (n : ℂ) * P := by simp only [nsmul_eq_mul, map_natCast]

lemma euler_monomial (m : Fin 6 →₀ ℕ) (c : ℂ) :
    euler (monomial m c) = C (m.degree : ℂ) * monomial m c := by
  exact euler_of_homogeneous (isHomogeneous_monomial c rfl)

lemma coeff_euler (P : Poly) (m : Fin 6 →₀ ℕ) :
    coeff m (euler P) = (m.degree : ℂ) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      rw [euler_monomial, coeff_C_mul]
      by_cases hd : d = m
      · subst d
        rfl
      · simp [coeff_monomial, hd]
  | add P Q hP hQ =>
      rw [euler_add, coeff_add, hP, hQ, coeff_add]
      ring

lemma homogeneous_of_euler {P : Poly} {n : ℕ}
    (h : euler P = C (n : ℂ) * P) : P.IsHomogeneous n := by
  classical
  intro m hm
  have hc := congrArg (coeff m) h
  rw [coeff_euler, coeff_C_mul] at hc
  have hn : (m.degree : ℂ) = (n : ℂ) := (mul_right_cancel₀ hm) hc
  have hd : m.degree = n := Nat.cast_injective hn
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd

/-- The quotient of homogeneous polynomials has the forced homogeneous degree.
No homogeneity condition on the certificate's unrestricted Q is used. -/
lemma homogeneous_quotient {F H : Poly} {m n : ℕ}
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous m)
    (hFH : (F * H).IsHomogeneous (m + n)) : H.IsHomogeneous n := by
  apply homogeneous_of_euler
  apply mul_left_cancel₀ hF0
  have ht := euler_of_homogeneous hFH
  rw [euler_mul, euler_of_homogeneous hF] at ht
  simp only [Nat.cast_add, map_add] at ht
  linear_combination ht

lemma divergence_coordinates : divergence coordinates = (6 : Poly) := by
  simp [divergence, coordinates]

lemma directional_radial (P H : Poly) :
    directional P (radial H) = C (1 / 12 : ℂ) * H * euler P := by
  exact HodgeTestbed.directional_mul P (C (1 / 12 : ℂ) * H) coordinates

lemma divergence_radial (H : Poly) :
    divergence (radial H) = C (1 / 12 : ℂ) * (euler H + 6 * H) := by
  change divergence (fun i => (C (1 / 12 : ℂ) * H) * coordinates i) = _
  rw [HodgeTestbed.divergence_mul, divergence_coordinates]
  change euler (C (1 / 12 : ℂ) * H) + (C (1 / 12 : ℂ) * H) * 6 = _
  rw [euler_mul, euler_C]
  ring

lemma divergenceNumerator_radial (D H : Poly) :
    divergenceNumerator D (radial H) =
      C (1 / 12 : ℂ) * (D * euler H + 6 * D * H - H * euler D) := by
  unfold divergenceNumerator
  rw [divergence_radial, directional_radial]
  ring

/-- A radial correction of the forced degree leaves the ENTIRE defect unchanged. -/
theorem radial_gauge_preserves_defect (F A D H : Poly) (N : Fin 6 → Poly)
    {d : ℕ} (hF : F.IsHomogeneous 6) (hD : D.IsHomogeneous d)
    (hH : H.IsHomogeneous (d + 6)) :
    defect F A D 2 (normalizeNumerators N H) = defect F A D 2 N := by
  unfold normalizeNumerators defect
  rw [CycleQ2Workspace.directional_add, CycleQ2Workspace.divergenceNumerator_add,
      directional_radial, divergenceNumerator_radial,
      euler_of_homogeneous hF, euler_of_homogeneous hD, euler_of_homogeneous hH]
  simp only [Nat.cast_add, map_add, map_natCast]
  ring

lemma first_normal_after_gauge (F A D H : Poly) (N : Fin 6 → Poly)
    (hF : F.IsHomogeneous 6)
    (hH : A * D - 2 * directional F N = F * H) :
    2 * directional F (normalizeNumerators N H) = A * D := by
  have hc : (12 : Poly) * C (1 / 12 : ℂ) = 1 := by
    calc
      _ = C (12 : ℂ) * C (1 / 12 : ℂ) := by rw [_root_.map_ofNat]
      _ = C ((12 : ℂ) * (1 / 12)) := by rw [map_mul]
      _ = 1 := by norm_num
  unfold normalizeNumerators
  rw [CycleQ2Workspace.directional_add, directional_radial, euler_of_homogeneous hF]
  simp only [map_natCast]
  linear_combination -hH + (F * H) * hc

lemma directional_homogeneous {F : Poly} {N : Fin 6 → Poly} {d : ℕ}
    (hF : F.IsHomogeneous 6) (hN : ∀ i, (N i).IsHomogeneous (d + 7)) :
    (directional F N).IsHomogeneous (d + 12) := by
  unfold directional
  apply IsHomogeneous.sum
  intro i _
  simpa only [show 6 - 1 + (d + 7) = d + 12 by omega] using
    (hF.pderiv (i := i)).mul (hN i)

lemma normalizeNumerators_homogeneous {N : Fin 6 → Poly} {H : Poly} {d : ℕ}
    (hN : ∀ i, (N i).IsHomogeneous (d + 7)) (hH : H.IsHomogeneous (d + 6)) :
    ∀ i, (normalizeNumerators N H i).IsHomogeneous (d + 7) := by
  intro i
  apply (hN i).add
  change (C (1 / 12 : ℂ) * H * X i).IsHomogeneous (d + 7)
  simpa only [Nat.add_assoc] using
    (hH.C_mul (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ i)

/-- Already F-divisibility (not the unknown F^3 closure) suffices for normalization.
The denominator is kept literally unchanged. -/
theorem normalize_of_first_divisibility
    {F A D : Poly} {N : Fin 6 → Poly} {d : ℕ}
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 12)
    (hD : D.IsHomogeneous d) (hN : ∀ i, (N i).IsHomogeneous (d + 7))
    (hlegal : IsRelPrime F D) (hdiv : F ∣ defect F A D 2 N) :
    ∃ H : Poly, H.IsHomogeneous (d + 6) ∧
      A * D - 2 * directional F N = F * H ∧
      (∀ i, (normalizeNumerators N H i).IsHomogeneous (d + 7)) ∧
      2 * directional F (normalizeNumerators N H) = A * D ∧
      defect F A D 2 (normalizeNumerators N H) = defect F A D 2 N := by
  classical
  obtain ⟨W, hW⟩ := hdiv
  have hprod : F ∣ D * (A * D - 2 * directional F N) := by
    refine ⟨W - divergenceNumerator D N, ?_⟩
    unfold defect at hW
    linear_combination hW
  obtain ⟨H, hH⟩ := hlegal.dvd_of_dvd_mul_left hprod
  have hS : (A * D - 2 * directional F N).IsHomogeneous (d + 12) := by
    apply IsHomogeneous.sub
    · simpa [Nat.add_comm] using hA.mul hD
    · simpa only [map_ofNat] using (directional_homogeneous hF hN).C_mul (2 : ℂ)
  have hFH : (F * H).IsHomogeneous (6 + (d + 6)) := by
    rw [← hH]
    convert hS using 1 <;> omega
  have hh := homogeneous_quotient hF0 hF hFH
  exact ⟨H, hh, hH, normalizeNumerators_homogeneous hN hh,
    first_normal_after_gauge F A D H N hF hH,
    radial_gauge_preserves_defect F A D H N hF hD hh⟩

/-- Every legal certificate can be normalized with the same denominator and quotient. -/
theorem normalize_verify {F A D Q : Poly} {N : Fin 6 → Poly}
    (h : Verify F A 6 2 D N Q) :
    ∃ N' : Fin 6 → Poly, Verify F A 6 2 D N' Q ∧
      2 * directional F N' = A * D ∧ divergenceNumerator D N' = F ^ 2 * Q := by
  have hN : ∀ i, (N i).IsHomogeneous (D.totalDegree + 7) := by
    intro i
    have hn : HodgeComputer.Homogeneous (N i) ((D.totalDegree + 7 : ℕ) : ℤ) := by
      convert h.numerator_homogeneous i using 1 <;> omega
    simpa only [Int.toNat_natCast] using hn.isHomogeneous (by omega)
  have hA : A.IsHomogeneous 12 := by
    simpa using h.source_homogeneous.isHomogeneous (by norm_num)
  have hdvd : F ∣ defect F A D 2 N := by
    refine ⟨F ^ 2 * Q, ?_⟩
    rw [h.identity]
    ring
  obtain ⟨H, _, _, hhom, hfirst, hsame⟩ :=
    normalize_of_first_divisibility h.hypersurface_ne_zero h.hypersurface_homogeneous
      hA h.denominator_homogeneous hN h.denominator_legal hdvd
  let N' := normalizeNumerators N H
  have hidentity : defect F A D 2 N' = F ^ 3 * Q := by
    exact hsame.trans h.identity
  have hv : Verify F A 6 2 D N' Q := {
    hypersurface_ne_zero := h.hypersurface_ne_zero
    hypersurface_homogeneous := h.hypersurface_homogeneous
    source_homogeneous := h.source_homogeneous
    denominator_ne_zero := h.denominator_ne_zero
    denominator_homogeneous := h.denominator_homogeneous
    numerator_homogeneous := by
      intro i
      convert HodgeComputer.Homogeneous.of_isHomogeneous (hhom i) using 1 <;> omega
    denominator_legal := h.denominator_legal
    identity := hidentity
  }
  have hs : divergenceNumerator D N' = F ^ 2 * Q := by
    apply mul_left_cancel₀ h.hypersurface_ne_zero
    calc
      F * divergenceNumerator D N' = defect F A D 2 N' := by
        unfold defect
        linear_combination D * hfirst
      _ = F ^ 3 * Q := hidentity
      _ = F * (F ^ 2 * Q) := by ring
  exact ⟨N', hv, hfirst, hs⟩

/-- The normalization does not narrow the original existential target. -/
theorem originalGoal_iff_normalized :
    OriginalGoal ↔ Nonempty NormalizedRationalSolution := by
  constructor
  · intro h
    change HasCertificate originalF 2 originalA at h
    obtain ⟨D, N, Q, h⟩ := h
    rw [originalF_totalDegree] at h
    obtain ⟨N', hv, hfirst, hsecond⟩ := normalize_verify h
    refine ⟨{
      degree := D.totalDegree
      denominator := D
      numerators := N'
      quotient := Q
      denominator_ne_zero := hv.denominator_ne_zero
      denominator_homogeneous := hv.denominator_homogeneous
      numerator_homogeneous := ?_
      denominator_legal := hv.denominator_legal
      first_normal := hfirst
      second_normal := hsecond
    }⟩
    intro i
    have hn : HodgeComputer.Homogeneous (N' i) ((D.totalDegree + 7 : ℕ) : ℤ) := by
      convert hv.numerator_homogeneous i using 1 <;> omega
    simpa only [Int.toNat_natCast] using hn.isHomogeneous (by omega)
  · rintro ⟨s⟩
    exact certificate_of_normalized_solution s

end CycleQ2Normalization
