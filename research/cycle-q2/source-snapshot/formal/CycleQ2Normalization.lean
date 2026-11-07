import CycleQ2Assembly
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Same-denominator radial normalization for the original pole parameter q = 2.

Every declaration below has a proof body and no admitted step. These are
PREPARED SOURCE, NOT COMPILER-CHECKED in the delivery environment. The accompanying
mathematical account proves the algebra and the Python tests verify its implementation.
The only intentionally admitted theorem in the workspace is in CycleQ2Draft.lean.
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
  simpa [euler, directional, coordinates, mul_comm, nsmul_eq_mul] using
    h.sum_X_mul_pderiv

lemma euler_monomial (m : Fin 6 →₀ ℕ) (c : ℂ) :
    euler (monomial m c) = C (m.degree : ℂ) * monomial m c := by
  exact euler_of_homogeneous (isHomogeneous_monomial c rfl)

lemma coeff_euler (P : Poly) (m : Fin 6 →₀ ℕ) :
    coeff m (euler P) = (m.degree : ℂ) * coeff m P := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
      by_cases hd : d = m
      · subst d
        simp [euler_monomial]
      · simp [euler_monomial, coeff_monomial, hd, Ne.symm hd]
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
  simpa only [Finsupp.degree_eq_weight_one] using hd

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
  simp only [Nat.cast_add, map_add, map_ofNat]
  ring

lemma first_normal_after_gauge (F A D H : Poly) (N : Fin 6 → Poly)
    (hF : F.IsHomogeneous 6)
    (hH : A * D - 2 * directional F N = F * H) :
    2 * directional F (normalizeNumerators N H) = A * D := by
  have hc : (12 : Poly) * C (1 / 12 : ℂ) = 1 := by
    calc
      _ = C ((12 : ℂ) * (1 / 12)) := by simp
      _ = 1 := by norm_num
  unfold normalizeNumerators
  rw [CycleQ2Workspace.directional_add, directional_radial, euler_of_homogeneous hF]
  simp only [map_ofNat]
  linear_combination -hH + (F * H) * hc

lemma directional_homogeneous {F : Poly} {N : Fin 6 → Poly} {d : ℕ}
    (hF : F.IsHomogeneous 6) (hN : ∀ i, (N i).IsHomogeneous (d + 7)) :
    (directional F N).IsHomogeneous (d + 12) := by
  unfold directional
  apply IsHomogeneous.sum
  intro i _
  convert (hF.pderiv (i := i)).mul (hN i) using 1 <;> omega

lemma normalizeNumerators_homogeneous {N : Fin 6 → Poly} {H : Poly} {d : ℕ}
    (hN : ∀ i, (N i).IsHomogeneous (d + 7)) (hH : H.IsHomogeneous (d + 6)) :
    ∀ i, (normalizeNumerators N H i).IsHomogeneous (d + 7) := by
  intro i
  apply (hN i).add
  change (C (1 / 12 : ℂ) * H * X i).IsHomogeneous (d + 7)
  convert (hH.C_mul (1 / 12 : ℂ)).mul (isHomogeneous_X ℂ i) using 1 <;> omega

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

/-- Every legal certificate can be normalized with the SAME D, d, and Q. -/
theorem normalize_verify {F A D Q : Poly} {N : Fin 6 → Poly} {d : ℕ}
    (hF0 : F ≠ 0) (hF : F.IsHomogeneous 6) (hA : A.IsHomogeneous 12)
    (h : Verify F A 2 d D N Q) :
    ∃ N' : Fin 6 → Poly, Verify F A 2 d D N' Q ∧
      2 * directional F N' = A * D ∧ divergenceNumerator D N' = F ^ 2 * Q := by
  have hN : ∀ i, (N i).IsHomogeneous (d + 7) := by
    intro i
    have hd : d + 6 * 2 - 5 = d + 7 := by omega
    simpa only [hd] using h.numerator_homogeneous i
  have hdvd : F ∣ defect F A D 2 N := by
    refine ⟨F ^ 2 * Q, ?_⟩
    rw [h.identity]
    ring
  obtain ⟨H, _, _, hhom, hfirst, hsame⟩ :=
    normalize_of_first_divisibility hF0 hF hA h.denominator_homogeneous hN
      h.denominator_legal hdvd
  let N' := normalizeNumerators N H
  have hidentity : defect F A D 2 N' = F ^ 3 * Q := by
    exact hsame.trans h.identity
  have hv : Verify F A 2 d D N' Q := {
    denominator_ne_zero := h.denominator_ne_zero
    denominator_homogeneous := h.denominator_homogeneous
    numerator_homogeneous := by
      intro i
      have hd : d + 6 * 2 - 5 = d + 7 := by omega
      simpa only [hd] using hhom i
    denominator_legal := h.denominator_legal
    identity := hidentity
  }
  have hs : divergenceNumerator D N' = F ^ 2 * Q := by
    apply mul_left_cancel₀ hF0
    calc
      F * divergenceNumerator D N' = defect F A D 2 N' := by
        unfold defect
        linear_combination D * hfirst
      _ = F ^ 3 * Q := hidentity
      _ = F * (F ^ 2 * Q) := by ring
  exact ⟨N', hv, hfirst, hs⟩

lemma originalF_homogeneous : originalF.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  have hm0 : ((X 0 : Poly)^3 * X 1 * X 3 * X 4).IsHomogeneous 6 := by
    simpa using ((((hx 0).pow 3).mul (hx 1)).mul (hx 3)).mul (hx 4)
  have hm1 : ((X 1 : Poly)^3 * X 2 * X 4 * X 5).IsHomogeneous 6 := by
    simpa using ((((hx 1).pow 3).mul (hx 2)).mul (hx 4)).mul (hx 5)
  have hm2 : ((X 2 : Poly)^3 * X 0 * X 5 * X 3).IsHomogeneous 6 := by
    simpa using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)
  unfold originalF z
  exact ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (((hm0.add hm1).add hm2).C_mul (1 / 2 : ℂ))

lemma originalA_homogeneous : originalA.IsHomogeneous 12 := by
  unfold originalA z
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa using ((((((hx 0).pow 2).mul ((hx 1).pow 2)).mul ((hx 2).pow 3)).mul
    ((hx 3).pow 2)).mul ((hx 4).pow 2)).mul (hx 5)

lemma originalF_ne_zero : originalF ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval
    (fun i : Fin 6 => if i = 0 then (1 : ℂ) else 0)) h
  norm_num [originalF, z] at hh

/-- The normalization does not narrow the original existential target. -/
theorem originalGoal_iff_normalized :
    OriginalGoal ↔ Nonempty NormalizedRationalSolution := by
  constructor
  · rintro ⟨d, D, N, Q, h⟩
    obtain ⟨N', hv, hfirst, hsecond⟩ :=
      normalize_verify originalF_ne_zero originalF_homogeneous originalA_homogeneous h
    refine ⟨{
      degree := d
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
    have hd : d + 6 * 2 - 5 = d + 7 := by omega
    simpa only [hd] using hv.numerator_homogeneous i
  · rintro ⟨s⟩
    exact certificate_of_normalized_solution s

#print axioms radial_gauge_preserves_defect
#print axioms normalize_of_first_divisibility
#print axioms normalize_verify
#print axioms originalGoal_iff_normalized
end CycleQ2Normalization
