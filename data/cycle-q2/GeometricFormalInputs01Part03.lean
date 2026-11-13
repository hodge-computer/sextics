import Proposal.GeometricFormalInputs01Part02

/-! Continuation of GeometricFormalInputs01.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: algebra/FiniteAveraging.lean -/
section
/-!+# Finite linear combinations with an explicit legal denominator

The denominator is the product of the supplied denominators. The numerator
and quotient are finite sums with the corresponding complementary products.
No denominator-degree bound, strictness condition, or coefficient search is
introduced. The final averaging theorem retains the original source whenever
the scalar weights sum to one.
-/

noncomputable section

namespace HodgeComputer

open HodgeTestbed MvPolynomial
open scoped BigOperators

theorem divergenceNumerator_C_mul {n : ℕ} (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    divergenceNumerator D (fun i => C c * N i) =
      C c * divergenceNumerator D N := by
  have hc : directional (C c : AmbientPoly n) N = 0 := by
    simp [directional]
  unfold divergenceNumerator
  rw [divergence_mul, hc, zero_add, directional_mul]
  ring

theorem defect_C_mul {n : ℕ} (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (c : ℂ) :
    defect F (C c * A) D q (fun i => C c * N i) =
      C c * defect F A D q N := by
  unfold defect
  rw [directional_mul, divergenceNumerator_C_mul]
  ring

theorem Verify.C_mul {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (c : ℂ) :
    Verify F (C c * A) d q D (fun i => C c * N i) (C c * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.C_mul c
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i => (h.numerator_homogeneous i).C_mul c
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_C_mul, h.identity]
    ring

/-- Adding a legal homogeneous factor to the denominator preserves the
certificate, with the same factor in every numerator and its square in Q. -/
theorem Verify.scale_denominator {n : ℕ} {F A D Q : AmbientPoly n} {d q : ℕ}
    {N : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (H : AmbientPoly n)
    (hH : H ≠ 0) (hHhom : H.IsHomogeneous H.totalDegree)
    (hHlegal : IsRelPrime F H) :
    Verify F A d q (H * D) (fun i => H * N i) (H ^ 2 * Q) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous
  denominator_ne_zero := mul_ne_zero hH h.denominator_ne_zero
  denominator_homogeneous := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero]
    exact hHhom.mul h.denominator_homogeneous
  numerator_homogeneous := by
    intro i
    have hn := (Homogeneous.of_isHomogeneous hHhom).mul (h.numerator_homogeneous i)
    rw [MvPolynomial.totalDegree_mul_of_isDomain hH h.denominator_ne_zero,
      Nat.cast_add]
    convert hn using 1 <;> ring
  denominator_legal := hHlegal.mul_right h.denominator_legal
  identity := by
    rw [defect_scale_denominator, h.identity]
    ring

/-- Zero source with any already legal homogeneous denominator. -/
theorem Verify.zero_denominator {n : ℕ} (F D : AmbientPoly n) (d q : ℕ)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D) :
    Verify F 0 d q D (fun _ => 0) 0 where
  hypersurface_ne_zero := hF
  hypersurface_homogeneous := hFhom
  source_homogeneous := homogeneous_zero _
  denominator_ne_zero := hD
  denominator_homogeneous := hDhom
  numerator_homogeneous := fun _ => homogeneous_zero _
  denominator_legal := hDlegal
  identity := by simp [defect, directional, divergenceNumerator, divergence]

theorem Verify.add_same_denominator {n : ℕ}
    {F A B D Q R : AmbientPoly n} {d q : ℕ}
    {N M : Fin (n + 1) → AmbientPoly n}
    (h : Verify F A d q D N Q) (k : Verify F B d q D M R) :
    Verify F (A + B) d q D (fun i => N i + M i) (Q + R) where
  hypersurface_ne_zero := h.hypersurface_ne_zero
  hypersurface_homogeneous := h.hypersurface_homogeneous
  source_homogeneous := h.source_homogeneous.add k.source_homogeneous
  denominator_ne_zero := h.denominator_ne_zero
  denominator_homogeneous := h.denominator_homogeneous
  numerator_homogeneous := fun i =>
    (h.numerator_homogeneous i).add (k.numerator_homogeneous i)
  denominator_legal := h.denominator_legal
  identity := by
    rw [defect_add_same_denominator, h.identity, k.identity]
    ring

/-- Finite addition at one denominator does not raise its degree. -/
theorem Verify.sum_same_denominator {n : ℕ} {ι : Type*}
    (s : Finset ι) (F D : AmbientPoly n) (d q : ℕ)
    (A Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hDlegal : IsRelPrime F D)
    (h : ∀ j ∈ s, Verify F (A j) d q D (N j) (Q j)) :
    Verify F (∑ j ∈ s, A j) d q D
      (fun i => ∑ j ∈ s, N j i) (∑ j ∈ s, Q j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using Verify.zero_denominator F D d q hF hFhom hD hDhom hDlegal
  | @insert a s ha ih =>
      intro h
      have hs := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have hsum := (h a (Finset.mem_insert_self a s)).add_same_denominator hs
      simpa only [Finset.sum_insert ha] using hsum

/-- Finite products retain all three denominator side conditions. -/
theorem homogeneous_legal_product {n : ℕ} {ι : Type*}
    (s : Finset ι) (F : AmbientPoly n) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0 ∧ (D j).IsHomogeneous (D j).totalDegree ∧
      IsRelPrime F (D j)) :
    (∏ j ∈ s, D j) ≠ 0 ∧
      (∏ j ∈ s, D j).IsHomogeneous (∏ j ∈ s, D j).totalDegree ∧
      IsRelPrime F (∏ j ∈ s, D j) := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero, by simpa using isHomogeneous_one (Fin (n + 1)) ℂ,
        isRelPrime_one_right⟩
  | @insert a s ha ih =>
      intro h
      rcases ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) with
        ⟨hs, hshom, hslegal⟩
      rcases h a (Finset.mem_insert_self a s) with ⟨ha0, hahom, halegal⟩
      rw [Finset.prod_insert ha]
      refine ⟨mul_ne_zero ha0 hs, ?_, halegal.mul_right hslegal⟩
      rw [MvPolynomial.totalDegree_mul_of_isDomain ha0 hs]
      exact hahom.mul hshom

/-- The product denominator has exactly the sum of the input degrees. -/
theorem totalDegree_product_of_nonzero {n : ℕ} {ι : Type*}
    (s : Finset ι) (D : ι → AmbientPoly n)
    (h : ∀ j ∈ s, D j ≠ 0) :
    (∏ j ∈ s, D j).totalDegree = ∑ j ∈ s, (D j).totalDegree := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      intro h
      have hs : (∏ j ∈ s, D j) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun j hj => h j (Finset.mem_insert_of_mem hj))
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        MvPolynomial.totalDegree_mul_of_isDomain (h a (Finset.mem_insert_self a s)) hs,
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))]

/-- Explicit finite linear combination. Each complementary product clears
one summand; the product of all denominators is homogeneous and relatively
prime to F. The quotient is retained even when it is nonzero. -/
theorem Verify.linearCombination {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F : AmbientPoly n) (d q : ℕ)
    (A D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F (A j) d q (D j) (N j) (Q j)) :
    Verify F (∑ j ∈ s, C (c j) * A j) d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hden := homogeneous_legal_product s F D (fun j hj =>
    ⟨(h j hj).denominator_ne_zero, (h j hj).denominator_homogeneous,
      (h j hj).denominator_legal⟩)
  apply Verify.sum_same_denominator s F (∏ j ∈ s, D j) d q
    (fun j => C (c j) * A j)
    (fun j => (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j))
    (fun j i => (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
    hF hFhom hden.1 hden.2.1 hden.2.2
  intro j hj
  have hrest := homogeneous_legal_product (s.erase j) F D (fun k hk =>
    ⟨(h k (Finset.mem_of_mem_erase hk)).denominator_ne_zero,
      (h k (Finset.mem_of_mem_erase hk)).denominator_homogeneous,
      (h k (Finset.mem_of_mem_erase hk)).denominator_legal⟩)
  have hscaled := ((h j hj).C_mul (c j)).scale_denominator
    (∏ k ∈ s.erase j, D k) hrest.1 hrest.2.1 hrest.2.2
  have hprod : (∏ k ∈ s.erase j, D k) * D j = ∏ k ∈ s, D k := by
    calc
      (∏ k ∈ s.erase j, D k) * D j =
          D j * (∏ k ∈ s.erase j, D k) := mul_comm _ _
      _ = ∏ k ∈ insert j (s.erase j), D k :=
        (Finset.prod_insert (Finset.notMem_erase j s)).symm
      _ = ∏ k ∈ s, D k := by rw [Finset.insert_erase hj]
  simpa only [hprod] using hscaled

/-- Weighted averaging preserves a common source. This is the algebraic
certificate step needed after a finite family of conjugate witnesses has
been supplied; the resulting denominator is their product. -/
theorem Verify.average {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (c : ι → ℂ) (hc : ∑ j ∈ s, c j = 1)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s, (∏ k ∈ s.erase j, D k) * (C (c j) * N j i))
      (∑ j ∈ s, (∏ k ∈ s.erase j, D k) ^ 2 * (C (c j) * Q j)) := by
  have hsource : (∑ j ∈ s, C (c j) * A) = A := by
    calc
      (∑ j ∈ s, C (c j) * A) = (∑ j ∈ s, C (c j)) * A :=
        (Finset.sum_mul s (fun j => C (c j)) A).symm
      _ = C (∑ j ∈ s, c j) * A := by rw [map_sum]
      _ = A := by rw [hc]; simp
  simpa only [hsource] using
    Verify.linearCombination s F d q (fun _ => A) D Q N c hF hFhom h

/-- Equal-weight averaging over a nonempty finite family. -/
theorem Verify.uniformAverage {n : ℕ} {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty) (F A : AmbientPoly n) (d q : ℕ)
    (D Q : ι → AmbientPoly n) (N : ι → Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (h : ∀ j ∈ s, Verify F A d q (D j) (N j) (Q j)) :
    Verify F A d q (∏ j ∈ s, D j)
      (fun i => ∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) * (C ((s.card : ℂ)⁻¹) * N j i))
      (∑ j ∈ s,
        (∏ k ∈ s.erase j, D k) ^ 2 * (C ((s.card : ℂ)⁻¹) * Q j)) := by
  have hcard : (s.card : ℂ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hc : (∑ _j ∈ s, (s.card : ℂ)⁻¹) = 1 := by
    simp [nsmul_eq_mul, hcard]
  exact Verify.average s F A d q D Q N (fun _ => (s.card : ℂ)⁻¹) hc hF hFhom h

end HodgeComputer

#print axioms HodgeComputer.Verify.scale_denominator
#print axioms HodgeComputer.Verify.linearCombination
#print axioms HodgeComputer.Verify.average
#print axioms HodgeComputer.Verify.uniformAverage
end
end


/- Component: bridge/LocalizedCertificate.lean -/
section
/-!
# Rational differential equations and the protected certificate

This module supplies the algebraic end of the nonconstructive support argument.
It uses actual derivations on the fraction field of the ambient polynomial ring.
The quotient rule is proved by the existing fraction-derivation construction;
the divergence and the cleared defect are then identified without additional
differential hypotheses.

The key equivalence allows the residual term to have an arbitrary denominator
coprime to the hypersurface. Euclid's lemma removes that residual denominator,
so geometry need only prove regularity along the hypersurface. It need not
predict the polynomial quotient accepted by `Verify`.

The prescribed-power constructor proves nonvanishing, homogeneity, the exact
numerator degree, and coprimality for D = S^q. For a sextic at q = 2, its
denominator is S^2 and numerator degree is 2 * degree(S) + 7.

No support theorem or geometric existence assertion is assumed as an axiom.
The geometric input remains an explicit hypothesis of the final constructor.
The fraction derivations and vector-field calculus are reused with their
original attribution from the repository's accepted constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace CycleQ2Bridge

open MvPolynomial HodgeComputer HodgeTestbed HodgeTestbed.Conic
open scoped BigOperators

variable {n : ℕ}

/-- The actual rational-function field in the homogeneous coordinates. -/
abbrev RationalFunction (n : ℕ) := FractionRing (AmbientPoly n)

-- Choose the algebra-induced rational scalar action consistently. The
-- concrete localization also carries a transported module instance.
local instance rationalFunctionRatAlgebra (n : ℕ) : Algebra ℚ (RationalFunction n) :=
  DivisionRing.toRatAlgebra

local instance rationalFunctionRatModule (n : ℕ) : Module ℚ (RationalFunction n) :=
  Algebra.toModule

/-- The injective polynomial-to-rational-function map. -/
abbrev polynomialMap (n : ℕ) : AmbientPoly n →+* RationalFunction n :=
  algebraMap (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_injective : Function.Injective (polynomialMap n) :=
  IsFractionRing.injective (AmbientPoly n) (RationalFunction n)

theorem polynomialMap_ne_zero {P : AmbientPoly n} (hP : P ≠ 0) :
    polynomialMap n P ≠ 0 := by
  intro h
  apply hP
  apply polynomialMap_injective
  simpa only [map_zero] using h

/-- Coordinate partial derivatives extended by the proved quotient rule. -/
def rationalPartial (n : ℕ) (i : Fin (n + 1)) :
    Derivation ℚ (RationalFunction n) (RationalFunction n) :=
  QuadricContactFraction.extend (F := RationalFunction n)
    ((MvPolynomial.pderiv i : Derivation ℂ (AmbientPoly n) (AmbientPoly n)).restrictScalars ℚ)

@[simp] theorem rationalPartial_map (i : Fin (n + 1)) (P : AmbientPoly n) :
    rationalPartial n i (polynomialMap n P) = polynomialMap n (pderiv i P) := by
  unfold rationalPartial polynomialMap
  rw [QuadricContactFraction.extend_map]
  rfl

/-- The rational field represented by a common polynomial denominator. -/
def rationalField (D : AmbientPoly n) (N : Fin (n + 1) → AmbientPoly n) :
    Fin (n + 1) → RationalFunction n :=
  fun i => polynomialMap n (N i) / polynomialMap n D

/-- The actual first-order rational differential expression. -/
def rationalDefect (F A : AmbientPoly n) (q : ℕ)
    (v : Fin (n + 1) → RationalFunction n) : RationalFunction n :=
  polynomialMap n A - (q : RationalFunction n) *
      fieldAction (k := ℚ) (rationalPartial n) v (polynomialMap n F) +
    polynomialMap n F * fieldDivergence (k := ℚ) (rationalPartial n) v

theorem rationalField_action (F D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldAction (k := ℚ) (rationalPartial n) (rationalField D N) (polynomialMap n F) =
      polynomialMap n (directional F N) / polynomialMap n D := by
  simp only [fieldAction_apply, rationalField, rationalPartial_map,
    directional, map_sum, map_mul, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The quotient-rule numerator really is the divergence of N / D. -/
theorem rationalField_divergence (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) :
    fieldDivergence (k := ℚ) (rationalPartial n) (rationalField D N) =
      polynomialMap n (divergenceNumerator D N) / (polynomialMap n D)^2 := by
  have hdirection :
      (∑ i, polynomialMap n (N i) * polynomialMap n (pderiv i D)) =
        polynomialMap n (directional D N) := by
    simp only [directional, map_sum, map_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [fieldDivergence, rationalField, Derivation.leibniz_div,
    smul_eq_mul, rationalPartial_map]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum, hdirection]
  simp only [divergenceNumerator, divergence, map_sub, map_mul, map_sum,
    div_eq_mul_inv, inv_pow]
  ring

/-- Clearing the common denominator identifies the rational and polynomial defects. -/
theorem rationalDefect_eq (F A D : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalDefect F A q (rationalField D N) =
      polynomialMap n (defect F A D q N) / (polynomialMap n D)^2 := by
  have hD' := polynomialMap_ne_zero hD
  unfold rationalDefect
  rw [rationalField_action, rationalField_divergence]
  simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast]
  field_simp

/-- Exact polynomial equality is equivalent to its actual rational differential equation. -/
theorem identity_iff_rationalDefect (F A D Q : AmbientPoly n) (q : ℕ)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    defect F A D q N = F^(q+1) * Q ↔
      rationalDefect F A q (rationalField D N) =
        (polynomialMap n F)^(q+1) *
          (polynomialMap n Q / (polynomialMap n D)^2) := by
  rw [rationalDefect_eq F A D q N hD]
  constructor
  · intro h
    rw [h, map_mul, map_pow]
    ring
  · intro h
    apply polynomialMap_injective
    have hD' := polynomialMap_ne_zero hD
    have hh := congrArg (fun z : RationalFunction n => z * (polynomialMap n D)^2) h
    simpa only [map_mul, map_pow] using (by
      field_simp at hh
      linear_combination hh : polynomialMap n (defect F A D q N) =
        (polynomialMap n F)^(q+1) * polynomialMap n Q)

/-- Divisibility of the residual expression by F^(q+1) in the ring of
rational functions with denominators coprime to F.

This is the precise algebraic meaning needed from regularity of the rational
top form along the hypersurface. The residual denominator T is unrestricted.
-/
def LocalizedEquation (F A : AmbientPoly n) (q : ℕ) (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) : Prop :=
  ∃ P T : AmbientPoly n, T ≠ 0 ∧ IsRelPrime F T ∧
    rationalDefect F A q (rationalField D N) =
      (polynomialMap n F)^(q+1) * (polynomialMap n P / polynomialMap n T)

/-- An auxiliary residual denominator cancels by coprimality, not by an
unjustified assertion that the residual function was a polynomial. -/
theorem quotient_exists_of_localizedEquation
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (h : LocalizedEquation F A q D N) :
    ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  obtain ⟨P, T, hT, hlegal, heq⟩ := h
  have hD' := polynomialMap_ne_zero hD
  have hT' := polynomialMap_ne_zero hT
  rw [rationalDefect_eq F A D q N hD] at heq
  have hcleared : T * defect F A D q N = F^(q+1) * (P * D^2) := by
    apply polynomialMap_injective
    simp only [map_mul, map_pow]
    field_simp at heq
    linear_combination heq
  have hdiv : F^(q+1) ∣ T * defect F A D q N := ⟨P * D^2, hcleared⟩
  exact (hlegal.pow_left : IsRelPrime (F^(q+1)) T).dvd_of_dvd_mul_left hdiv

/-- The polynomial quotient gives a legal localized residual with
denominator D^2, yielding an equivalence for a legal field. -/
theorem localizedEquation_iff_quotient
    (F A D : AmbientPoly n) (q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hD : D ≠ 0) (hlegal : IsRelPrime F D) :
    LocalizedEquation F A q D N ↔
      ∃ Q : AmbientPoly n, defect F A D q N = F^(q+1) * Q := by
  constructor
  · exact quotient_exists_of_localizedEquation F A D q N hD
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, D^2, pow_ne_zero 2 hD, hlegal.pow_right, ?_⟩
    simpa only [map_pow] using
      (identity_iff_rationalDefect F A D Q q N hD).mp hQ

/-- The actual first-order equation supplies exactly the quotient required
by Verify, retaining the stated homogeneous and legal field. -/
theorem exists_verify_iff_localizedEquation
    (F A D : AmbientPoly n) (d q : ℕ) (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hD : D ≠ 0) (hDhom : D.IsHomogeneous D.totalDegree)
    (hN : ∀ i, Homogeneous (N i) ((D.totalDegree : ℤ) + d*q - n))
    (hlegal : IsRelPrime F D) :
    (∃ Q : AmbientPoly n, Verify F A d q D N Q) ↔
      LocalizedEquation F A q D N := by
  constructor
  · rintro ⟨Q, hQ⟩
    exact (localizedEquation_iff_quotient F A D q N hD hlegal).mpr ⟨Q, hQ.identity⟩
  · intro h
    obtain ⟨Q, hQ⟩ := quotient_exists_of_localizedEquation F A D q N hD h
    exact ⟨Q, {
      hypersurface_ne_zero := hF
      hypersurface_homogeneous := hFhom
      source_homogeneous := hA
      denominator_ne_zero := hD
      denominator_homogeneous := hDhom
      numerator_homogeneous := hN
      denominator_legal := hlegal
      identity := hQ }⟩

/-- A nonconstructively chosen support equation with a bounded primitive
finishes every algebraic clause of the protected certificate. -/
theorem hasCertificate_of_prescribed_power
    (F A S : AmbientPoly n) (d q e : ℕ)
    (N : Fin (n + 1) → AmbientPoly n)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous d)
    (hA : Homogeneous A ((d : ℤ) * (q + 1) - (n + 1)))
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) ((e : ℤ)*q + d*q - n))
    (hlocal : LocalizedEquation F A q (S^q) N) :
    HasCertificate F q A := by
  have hD : S^q ≠ 0 := pow_ne_zero q hS
  have hDhom : (S^q).IsHomogeneous (e*q) := hShom.pow q
  have hdegree : (S^q).totalDegree = e*q := hDhom.totalDegree hD
  obtain ⟨Q, hQ⟩ := (exists_verify_iff_localizedEquation F A (S^q) d q N
    hF hFhom hA hD (by simpa only [hdegree] using hDhom)
    (by
      intro i
      simpa only [hdegree, Nat.cast_mul] using hN i)
    hlegal.pow_right).mpr hlocal
  exact hQ.hasCertificate

/-- The degree bookkeeping from the filtered double-pole primitive for a
sextic fourfold, without an explicit support equation or degree bound. -/
theorem sextic_q2_hasCertificate_of_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : F ≠ 0) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12)
    (hS : S ≠ 0) (hShom : S.IsHomogeneous e)
    (hlegal : IsRelPrime F S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  apply hasCertificate_of_prescribed_power F A S 6 2 e N hF hFhom
  · simpa using hA
  · exact hS
  · exact hShom
  · exact hlegal
  · intro i
    convert hN i using 1
    ring
  · exact hlocal

/-- For an irreducible hypersurface, the geometric choice S outside (F)
already proves both denominator nonvanishing and coprimality. -/
theorem sextic_q2_hasCertificate_of_irreducible_square_primitive
    (F A S : AmbientPoly 5) (e : ℕ) (N : Fin 6 → AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) (hShom : S.IsHomogeneous e)
    (hS : ¬ F ∣ S)
    (hN : ∀ i, Homogeneous (N i) (2*(e : ℤ)+7))
    (hlocal : LocalizedEquation F A 2 (S^2) N) :
    HasCertificate F 2 A := by
  have hS0 : S ≠ 0 := by
    intro hs
    apply hS
    rw [hs]
    exact dvd_zero F
  exact sextic_q2_hasCertificate_of_square_primitive F A S e N
    hF.ne_zero hFhom hA hS0 hShom
    (hF.isRelPrime_iff_not_dvd.mpr hS) hN hlocal

/-- Any nonzero denominator can be squared without changing the actual field. -/
theorem rationalField_square (D : AmbientPoly n)
    (N : Fin (n + 1) → AmbientPoly n) (hD : D ≠ 0) :
    rationalField (D^2) (fun i => D * N i) = rationalField D N := by
  have hD' := polynomialMap_ne_zero hD
  funext i
  simp only [rationalField, map_mul, map_pow]
  field_simp

/-- The square-support formulation is exactly the original existential
problem. It is not an extra denominator ansatz, and this equivalence does
not assert that either side has been proved for a particular source. -/
theorem sextic_q2_hasCertificate_iff_square_primitive
    (F A : AmbientPoly 5)
    (hF : Irreducible F) (hFhom : F.IsHomogeneous 6)
    (hA : Homogeneous A 12) :
    HasCertificate F 2 A ↔
      ∃ (e : ℕ) (S : AmbientPoly 5) (N : Fin 6 → AmbientPoly 5),
        S.IsHomogeneous e ∧ ¬ F ∣ S ∧
        (∀ i, Homogeneous (N i) (2*(e : ℤ)+7)) ∧
        LocalizedEquation F A 2 (S^2) N := by
  constructor
  · rintro ⟨D, N, Q, h⟩
    have hdegree : F.totalDegree = 6 := hFhom.totalDegree hF.ne_zero
    rw [hdegree] at h
    refine ⟨D.totalDegree, D, (fun i => D * N i), h.denominator_homogeneous,
      hF.isRelPrime_iff_not_dvd.mp h.denominator_legal, ?_, ?_⟩
    · intro i
      have hn := (Homogeneous.of_isHomogeneous h.denominator_homogeneous).mul
        (h.numerator_homogeneous i)
      convert hn using 1
      ring
    · have hlocal := (localizedEquation_iff_quotient F A D 2 N
        h.denominator_ne_zero h.denominator_legal).mpr ⟨Q, h.identity⟩
      simpa only [LocalizedEquation, rationalField_square D N h.denominator_ne_zero]
        using hlocal
  · rintro ⟨e, S, N, hShom, hS, hN, hlocal⟩
    exact sextic_q2_hasCertificate_of_irreducible_square_primitive
      F A S e N hF hFhom hA hShom hS hN hlocal

end CycleQ2Bridge

#print axioms CycleQ2Bridge.rationalField_divergence
#print axioms CycleQ2Bridge.quotient_exists_of_localizedEquation
#print axioms CycleQ2Bridge.exists_verify_iff_localizedEquation
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_of_irreducible_square_primitive
#print axioms CycleQ2Bridge.sextic_q2_hasCertificate_iff_square_primitive
end
end


/- Component: support_choice/ProjectiveSupportEquation.lean -/
section
/-!
# Choosing an ambient equation for an actual proper projective support

This file proves the support-equation choice using mathlib's actual projective
spectrum, homogeneous vanishing ideals, and homogeneous components. No
cohomology or residue support is postulated or constructed here.

For every closed strict subset Z of the protected hypersurface, the theorem
chooses a positive-degree homogeneous S that vanishes on Z and is not divisible
by F. Its square is therefore a nonzero homogeneous legal denominator.

The remaining geometric assertion is that the specified residue vanishes off
some such Z. The theorem below does not assert that support exists.
-/

noncomputable section

namespace CycleQ2SupportEquation

open MvPolynomial HodgeComputer

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous ideal not contained in another ideal has a homogeneous
element outside the latter ideal. The proof selects an actual homogeneous
component of an actual ideal-membership witness. -/
theorem exists_homogeneous_mem_not_mem
    {σ R : Type*} [CommRing R]
    (I J : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hIJ : ¬ I ≤ J) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ S ∉ J := by
  classical
  obtain ⟨P, hPI, hPJ⟩ := SetLike.not_le_iff_exists.mp hIJ
  have hex : ∃ e : ℕ, homogeneousComponent e P ∉ J := by
    by_contra! h
    apply hPJ
    rw [← sum_homogeneousComponent P]
    exact J.sum_mem fun e _ => h e
  obtain ⟨e, he⟩ := hex
  exact ⟨e, homogeneousComponent e P,
    homogeneousComponent_mem_of_mem hI hPI e,
    homogeneousComponent_isHomogeneous e P, he⟩

/-- The special case used when the hypersurface ideal is properly contained
in the ideal of a support. -/
theorem homogeneous_equation_of_strict_ideal_inclusion
    {σ R : Type*} [CommRing R]
    (F : MvPolynomial σ R) (I : Ideal (MvPolynomial σ R))
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (hFI : Ideal.span ({F} : Set (MvPolynomial σ R)) < I) :
    ∃ (e : ℕ) (S : MvPolynomial σ R),
      S ∈ I ∧ S.IsHomogeneous e ∧ ¬ F ∣ S := by
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I (Ideal.span {F}) hI (not_le_of_gt hFI)
  exact ⟨e, S, hSI, hShom, by simpa only [Ideal.mem_span_singleton] using hSF⟩

abbrev ambientGrading (n : ℕ) := homogeneousSubmodule (Fin (n + 1)) ℂ

/-- The actual topological projective spectrum of the ambient polynomial ring. -/
abbrev AmbientProjectiveSpace (n : ℕ) := ProjectiveSpectrum (ambientGrading n)

/-- A proper closed subset of an actual projective hypersurface has a
homogeneous ambient equation that is not divisible by its defining equation.
No projective Nullstellensatz or saturation hypothesis is needed: otherwise
zero-locus antitonicity would force the entire hypersurface into the support. -/
theorem homogeneous_equation_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      S.IsHomogeneous e ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} := by
  classical
  let I := ProjectiveSpectrum.vanishingIdeal Z
  have hnot : ¬ I.toIdeal ≤ Ideal.span ({F} : Set (AmbientPoly n)) := by
    intro h
    have hreverse := ProjectiveSpectrum.zeroLocus_anti_mono_ideal
      (ambientGrading n) h
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) ⊆
      ProjectiveSpectrum.zeroLocus (ambientGrading n)
        (ProjectiveSpectrum.vanishingIdeal Z) at hreverse
    rw [ProjectiveSpectrum.zeroLocus_span,
      ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at hreverse
    exact hproper.2 hreverse
  obtain ⟨e, S, hSI, hShom, hSF⟩ :=
    exists_homogeneous_mem_not_mem I.toIdeal (Ideal.span {F}) I.isHomogeneous hnot
  refine ⟨e, S, hShom, ?_, ?_⟩
  · simpa only [Ideal.mem_span_singleton] using hSF
  · apply (ProjectiveSpectrum.subset_zeroLocus_iff_subset_vanishingIdeal
      (ambientGrading n) Z {S}).mpr
    exact Set.singleton_subset_iff.mpr hSI

theorem not_dvd_coordinate_of_degree_gt_one
    {n : ℕ} (F : AmbientPoly n) (hdegree : 1 < F.totalDegree)
    (i : Fin (n + 1)) : ¬ F ∣ X i := by
  intro h
  have hh := totalDegree_le_of_dvd_of_isDomain h (X_ne_zero i)
  rw [totalDegree_X] at hh
  exact (not_le_of_gt hdegree) hh

/-- A positive-degree support equation and its square denominator, with
legality derived from irreducibility. This is the exact equation-selection
step used before filtered de Rham theory is invoked. -/
theorem legal_square_of_closed_proper_subset
    {n : ℕ} (F : AmbientPoly n) (Z : Set (AmbientProjectiveSpace n))
    (hF : Irreducible F) (hdegree : 1 < F.totalDegree)
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) :
    ∃ (e : ℕ) (S : AmbientPoly n),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading n) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧ IsRelPrime F (S ^ 2) := by
  obtain ⟨e, S, hShom, hnot, hcover⟩ :=
    homogeneous_equation_of_closed_proper_subset F Z hZ hproper
  have hS : S ≠ 0 := by
    intro h
    apply hnot
    rw [h]
    exact dvd_zero F
  have hlegal : IsRelPrime F S := hF.isRelPrime_iff_not_dvd.mpr hnot
  have hXlegal : IsRelPrime F (X (0 : Fin (n + 1))) :=
    hF.isRelPrime_iff_not_dvd.mpr (not_dvd_coordinate_of_degree_gt_one F hdegree 0)
  have hprodlegal : IsRelPrime F (S * X (0 : Fin (n + 1))) :=
    hlegal.mul_right hXlegal
  have hprod : S * X (0 : Fin (n + 1)) ≠ 0 := mul_ne_zero hS (X_ne_zero 0)
  have hprodhom : (S * X (0 : Fin (n + 1))).IsHomogeneous (e + 1) :=
    hShom.mul (isHomogeneous_X ℂ 0)
  refine ⟨e + 1, S * X 0, Nat.succ_pos e, hprodhom, hprod,
    hF.isRelPrime_iff_not_dvd.mp hprodlegal, ?_, ?_, pow_ne_zero 2 hprod,
    hprodlegal.pow_right⟩
  · rw [ProjectiveSpectrum.zeroLocus_singleton_mul]
    exact hcover.trans Set.subset_union_left
  · simpa only [Nat.mul_comm] using hprodhom.pow 2

/-- Exact target specialization: every actual proper projective closed
support admits a legal homogeneous square denominator, existentially. -/
theorem protected_support_has_legal_square
    (Z : Set (AmbientProjectiveSpace 5))
    (hZ : IsClosed Z)
    (hproper : Z ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      Z ⊆ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S} ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  apply legal_square_of_closed_proper_subset HodgeSubmission.F Z
    CycleQ2ExactIrreducible.protected_F_irreducible
  · rw [CycleQ2Workspace.originalF_totalDegree]
    decide
  · exact hZ
  · exact hproper

/-- The actual protected hypersurface as a closed subspace of projective
spectrum, with its induced topology. -/
abbrev ProtectedHypersurface :=
  {x : AmbientProjectiveSpace 5 //
    x ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {HodgeSubmission.F}}

/-- The geometric support statement normally provides a proper closed subset
inside X. Closedness of the hypersurface promotes that relative support to an
ambient closed set, so the preceding theorem applies without an added
ambient-closedness assumption. -/
theorem protected_relative_support_has_legal_square
    (Z : Set ProtectedHypersurface) (hZ : IsClosed Z) (hproper : Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ x ∈ Z, x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  let Y : Set (AmbientProjectiveSpace 5) := Subtype.val '' Z
  have hY : IsClosed Y :=
    (ProjectiveSpectrum.isClosed_zeroLocus (ambientGrading 5)
      {HodgeSubmission.F}).isClosedMap_subtype_val Z hZ
  have hYproper : Y ⊂ ProjectiveSpectrum.zeroLocus (ambientGrading 5)
      {HodgeSubmission.F} := by
    refine ⟨?_, ?_⟩
    · rintro x ⟨y, hy, rfl⟩
      exact y.property
    · intro h
      apply hproper
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy, hxy⟩ := h x.property
      have he : y = x := Subtype.ext hxy
      simpa only [he] using hy
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_support_has_legal_square Y hY hYproper
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro x hx
  exact hcover ⟨x, hx, rfl⟩


/-- The homogeneous prime ideal `(F)` is an actual generic point of the
projective hypersurface. The degree assumption excludes the irrelevant ideal.
Its singleton closure gives irreducibility of the actual projective zero set. -/
theorem hypersurface_isIrreducible
    {n d : ℕ} (F : AmbientPoly n)
    (hF : Irreducible F) (hhom : F.IsHomogeneous d)
    (hdegree : 1 < F.totalDegree) :
    IsIrreducible (ProjectiveSpectrum.zeroLocus (ambientGrading n) {F}) := by
  let I : HomogeneousIdeal (ambientGrading n) :=
    ⟨Ideal.span {F}, Ideal.homogeneous_span (ambientGrading n) {F} (by
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact ⟨d, hhom⟩)⟩
  let η : AmbientProjectiveSpace n :=
    { asHomogeneousIdeal := I
      isPrime := (Ideal.span_singleton_prime hF.ne_zero).mpr hF.prime
      not_irrelevant_le := by
        intro h
        have hX : (X (0 : Fin (n + 1)) : AmbientPoly n) ∈
            HomogeneousIdeal.irrelevant (ambientGrading n) :=
          HomogeneousIdeal.mem_irrelevant_of_mem (ambientGrading n)
            (by decide : 0 < 1) (isHomogeneous_X ℂ 0)
        exact not_dvd_coordinate_of_degree_gt_one F hdegree 0
          (Ideal.mem_span_singleton.mp (h hX)) }
  have hclosure : closure ({η} : Set (AmbientProjectiveSpace n)) =
      ProjectiveSpectrum.zeroLocus (ambientGrading n) {F} := by
    rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      ProjectiveSpectrum.vanishingIdeal_singleton]
    change ProjectiveSpectrum.zeroLocus (ambientGrading n) (Ideal.span {F}) = _
    exact ProjectiveSpectrum.zeroLocus_span (ambientGrading n) {F}
  rw [← hclosure]
  exact isIrreducible_singleton.closure

/-- Irreducibility of the exact protected hypersurface as an actual space. -/
theorem protected_hypersurface_irreducible :
    IrreducibleSpace ProtectedHypersurface := by
  apply Subtype.irreducibleSpace
  apply hypersurface_isIrreducible HodgeSubmission.F
    CycleQ2ExactIrreducible.protected_F_irreducible
    CycleQ2Workspace.originalF_homogeneous
  rw [CycleQ2Workspace.originalF_totalDegree]
  decide

/-- A finite collection of genuine proper closed supports inside the
protected hypersurface still has proper union. -/
theorem protected_finite_union_proper
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ⋃₀ (T : Set (Set ProtectedHypersurface)) ≠ Set.univ := by
  letI := protected_hypersurface_irreducible
  intro h
  obtain ⟨Z, hZT, hcover⟩ := isIrreducible_iff_sUnion_isClosed.mp
    (IrreducibleSpace.isIrreducible_univ ProtectedHypersurface) T hclosed
    (by rw [h])
  exact hproper Z hZT (Set.eq_univ_of_univ_subset hcover)

/-- A finite family of proper closed supports has one positive-degree
homogeneous ambient equation whose square is a legal denominator. -/
theorem protected_finite_supports_have_legal_square
    (T : Finset (Set ProtectedHypersurface))
    (hclosed : ∀ Z ∈ T, IsClosed Z)
    (hproper : ∀ Z ∈ T, Z ≠ Set.univ) :
    ∃ (e : ℕ) (S : AmbientPoly 5),
      0 < e ∧ S.IsHomogeneous e ∧ S ≠ 0 ∧ ¬ HodgeSubmission.F ∣ S ∧
      (∀ Z ∈ T, ∀ x ∈ Z,
        x.val ∈ ProjectiveSpectrum.zeroLocus (ambientGrading 5) {S}) ∧
      (S ^ 2).IsHomogeneous (2 * e) ∧ S ^ 2 ≠ 0 ∧
      IsRelPrime HodgeSubmission.F (S ^ 2) := by
  have hc : IsClosed (⋃₀ (T : Set (Set ProtectedHypersurface))) := by
    rw [Set.sUnion_eq_biUnion]
    exact isClosed_biUnion_finset hclosed
  obtain ⟨e, S, he, hShom, hS, hnot, hcover, hDhom, hD, hlegal⟩ :=
    protected_relative_support_has_legal_square _ hc
      (protected_finite_union_proper T hclosed hproper)
  refine ⟨e, S, he, hShom, hS, hnot, ?_, hDhom, hD, hlegal⟩
  intro Z hZT x hx
  exact hcover x ⟨Z, hZT, hx⟩

end CycleQ2SupportEquation

#print axioms CycleQ2SupportEquation.homogeneous_equation_of_closed_proper_subset
#print axioms CycleQ2SupportEquation.protected_support_has_legal_square
#print axioms CycleQ2SupportEquation.protected_relative_support_has_legal_square

#print axioms CycleQ2SupportEquation.protected_hypersurface_irreducible
#print axioms CycleQ2SupportEquation.protected_finite_supports_have_legal_square
end
end


/- Component: jacobian/FermatJacobian.lean -/
section
/-!
# The actual weighted Fermat Jacobian algebra

The coefficient functionals and the socle pairing in this file descend from
the polynomial ring to its actual Jacobian quotient. They are not supplied
as abstract pairing hypotheses. The comparison with geometric Hodge theory
remains a different assertion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian

open MvPolynomial
open CycleQ2FermatHiggs

abbrev Poly := MvPolynomial (Fin 5) ℂ
abbrev Exp := Fin 5 →₀ ℕ

def exponent (a : Fin 5 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 5 → ℕ) (i : Fin 5) : exponent a i = a i := rfl

def cutoff (i : Fin 5) : ℕ := socle i + 1
def fermat : Poly := X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3
def generator (i : Fin 5) : Poly := X i ^ cutoff i
def derivativeScalar (i : Fin 5) : ℂ := if i = 4 then 3 else 6
def jacobianIdeal : Ideal Poly := Ideal.span (Set.range fun i => pderiv i fermat)
def powerIdeal : Ideal Poly := Ideal.span (Set.range generator)

theorem derivative_eq (i : Fin 5) :
    pderiv i fermat = C (derivativeScalar i) * generator i := by
  fin_cases i <;>
    norm_num [fermat, derivativeScalar, generator, cutoff, socle, Pi.single_apply,
      Fin.ext_iff, map_ofNat] <;> ring <;> rfl

theorem derivativeScalar_ne_zero (i : Fin 5) : derivativeScalar i ≠ 0 := by
  unfold derivativeScalar
  split <;> norm_num

theorem jacobianIdeal_eq_powerIdeal : jacobianIdeal = powerIdeal := by
  apply le_antisymm
  · rw [jacobianIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    change pderiv i fermat ∈ powerIdeal
    rw [derivative_eq]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [powerIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hi : pderiv i fermat ∈ jacobianIdeal := Ideal.subset_span ⟨i, rfl⟩
    have hs := Ideal.mul_mem_left jacobianIdeal (C ((derivativeScalar i)⁻¹)) hi
    rw [derivative_eq, ← mul_assoc, ← map_mul, inv_mul_cancel₀ (derivativeScalar_ne_zero i),
      map_one, one_mul] at hs
    exact hs

theorem powerIdeal_eq_monomialIdeal : powerIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 5 => Finsupp.single i (cutoff i))) := by
  unfold powerIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, generator, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

/-- An exact membership criterion in the ideal generated by the five actual
partial derivatives. -/
theorem mem_jacobianIdeal_iff (p : Poly) : p ∈ jacobianIdeal ↔
    ∀ d ∈ p.support, ∃ i : Fin 5, socle i < d i := by
  rw [jacobianIdeal_eq_powerIdeal, powerIdeal_eq_monomialIdeal,
    mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff, cutoff,
    Nat.succ_le_iff]

def bounded : Set Exp := {d | ∀ i, d i ≤ socle i}
abbrev BoundedExp := bounded

theorem bounded_coeff_zero_of_mem {p : Poly} (hp : p ∈ jacobianIdeal)
    {d : Exp} (hd : d ∈ bounded) : coeff d p = 0 := by
  by_contra hc
  obtain ⟨i, hi⟩ := (mem_jacobianIdeal_iff p).mp hp d (mem_support_iff.mpr hc)
  exact (not_lt_of_ge (hd i)) hi

theorem mem_jacobianIdeal_iff_bounded_coeff_zero (p : Poly) :
    p ∈ jacobianIdeal ↔ ∀ d ∈ bounded, coeff d p = 0 := by
  constructor
  · exact fun hp d hd => bounded_coeff_zero_of_mem hp hd
  · intro hp
    apply (mem_jacobianIdeal_iff p).mpr
    intro d hd
    by_contra h
    push Not at h
    have hz := hp d (by simpa only [bounded, Set.mem_ofPred_eq, not_lt] using h)
    exact (mem_support_iff.mp hd) hz

abbrev JacobianRing := Poly ⧸ jacobianIdeal

def quotientMap : Poly →ₐ[ℂ] JacobianRing := Ideal.Quotient.mkₐ ℂ jacobianIdeal

/-- Coefficients inside the exponent box descend to the true Jacobian ring. -/
def quotientCoeff (d : BoundedExp) : JacobianRing →ₗ[ℂ] ℂ :=
  (jacobianIdeal.restrictScalars ℂ).liftQ (lcoeff ℂ d.val) (by
    intro p hp
    exact bounded_coeff_zero_of_mem hp d.property)

@[simp] theorem quotientCoeff_mk (d : BoundedExp) (p : Poly) :
    quotientCoeff d (quotientMap p) = coeff d.val p := rfl

def socleTrace : JacobianRing →ₗ[ℂ] ℂ :=
  quotientCoeff ⟨exponent socle, fun _ => le_rfl⟩

@[simp] theorem socleTrace_mk (p : Poly) :
    socleTrace (quotientMap p) = coeff (exponent socle) p := rfl

def monomialClass (a : Fin 5 → ℕ) : JacobianRing :=
  quotientMap (monomial (exponent a) 1)

theorem exponent_add (a b : Fin 5 → ℕ) :
    exponent a + exponent b = exponent (fun i => a i + b i) := by
  ext i
  rfl

/-- The socle trace of a triple product in the actual quotient is precisely
the exponent-sum test used to construct the finite Higgs matrices. -/
theorem socleTrace_triple_monomial (a b c : Fin 5 → ℕ) :
    socleTrace (monomialClass a * monomialClass b * monomialClass c) =
      if (∀ i, a i + b i + c i = socle i) then 1 else 0 := by
  classical
  rw [monomialClass, monomialClass, monomialClass, ← map_mul, ← map_mul,
    socleTrace_mk, monomial_mul, monomial_mul, one_mul, one_mul, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h i
    exact congrArg (fun d : Exp => d i) h
  · intro h
    ext i
    exact h i

/-- This is a literal equality with the already checked finite matrix, not
an assumption naming an unspecified residue pairing. -/
theorem socleTrace_triple_eq_higgsMatrix (m : Fin 35) (i j : Fin 33) :
    socleTrace (monomialClass (basisMonomial i) * monomialClass (basisMonomial j) *
      monomialClass (tangentMonomial m)) = higgsMatrix ℂ m i j := by
  rw [socleTrace_triple_monomial, higgsMatrix_socle]

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.jacobianIdeal_eq_powerIdeal
#print axioms CycleQ2FermatJacobian.mem_jacobianIdeal_iff
#print axioms CycleQ2FermatJacobian.socleTrace_triple_eq_higgsMatrix
end
end


/- Component: jacobian/FermatJacobianBasis.lean -/
section
/-!
# Monomial basis of the actual Fermat Jacobian quotient

The normal form is constructed by retaining bounded coefficients. Its kernel
is proved to be the derivative ideal, so the basis below is a basis of the
actual quotient rather than a separately introduced finite algebra.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def normalForm : Poly →ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Finsupp.lsubtypeDomain bounded).comp
    (MvPolynomial.basisMonomials (Fin 5) ℂ).repr.toLinearMap

@[simp] theorem normalForm_apply (p : Poly) (d : BoundedExp) :
    normalForm p d = coeff d.val p := rfl

theorem normalForm_surjective : Function.Surjective normalForm := by
  classical
  intro f
  refine ⟨(MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain, ?_⟩
  change Finsupp.subtypeDomain (fun x => x ∈ bounded)
    ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr
      ((MvPolynomial.basisMonomials (Fin 5) ℂ).repr.symm f.extendDomain)) = f
  rw [LinearEquiv.apply_symm_apply, Finsupp.subtypeDomain_extendDomain]

theorem normalForm_ker :
    LinearMap.ker normalForm = jacobianIdeal.restrictScalars ℂ := by
  ext p
  rw [LinearMap.mem_ker, Finsupp.ext_iff]
  change (∀ d : BoundedExp, coeff d.val p = 0) ↔ p ∈ jacobianIdeal
  rw [mem_jacobianIdeal_iff_bounded_coeff_zero]
  exact Subtype.forall

/-- Unique bounded monomial coordinates in the actual Jacobian quotient. -/
def normalCoordinates : JacobianRing ≃ₗ[ℂ] (BoundedExp →₀ ℂ) :=
  (Submodule.quotEquivOfEq (jacobianIdeal.restrictScalars ℂ)
    (LinearMap.ker normalForm) normalForm_ker.symm).trans
      (normalForm.quotKerEquivOfSurjective normalForm_surjective)

@[simp] theorem normalCoordinates_mk (p : Poly) :
    normalCoordinates (quotientMap p) = normalForm p := rfl

/-- The classes of every monomial within the derivative exponent bounds form
a basis of the quotient over the complex numbers. -/
def quotientBasis : Module.Basis BoundedExp ℂ JacobianRing :=
  (Finsupp.basisSingleOne : Module.Basis BoundedExp ℂ (BoundedExp →₀ ℂ)).map
    normalCoordinates.symm

@[simp] theorem normalForm_monomial (d : BoundedExp) :
    normalForm (monomial d.val 1) = Finsupp.single d 1 := by
  classical
  ext e
  simp only [normalForm_apply, coeff_monomial, Finsupp.single_apply]
  congr 1
  exact propext Subtype.ext_iff.symm

theorem quotientBasis_eq_monomialClass (d : BoundedExp) :
    quotientBasis d = quotientMap (monomial d.val 1) := by
  apply normalCoordinates.injective
  simp [quotientBasis]

theorem boundedMonomials_linearIndependent :
    LinearIndependent ℂ (fun d : BoundedExp => quotientMap (monomial d.val 1)) := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.linearIndependent

theorem boundedMonomials_span :
    Submodule.span ℂ (Set.range fun d : BoundedExp =>
      quotientMap (monomial d.val 1)) = ⊤ := by
  simpa only [← quotientBasis_eq_monomialClass] using quotientBasis.span_eq

/-- The exponent box has four side lengths five and one side length two. -/
def boundedExponentEquiv : BoundedExp ≃ (∀ i : Fin 5, Fin (cutoff i)) where
  toFun d i := ⟨d.val i, Nat.lt_succ_of_le (d.property i)⟩
  invFun a := ⟨exponent (fun i => (a i).val), fun i => Nat.le_of_lt_succ (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

theorem boundedExponent_card : Nat.card BoundedExp = 1250 := by
  rw [Nat.card_congr boundedExponentEquiv, Nat.card_eq_fintype_card, Fintype.card_pi]
  norm_num [cutoff, socle, Fin.prod_univ_succ]

theorem jacobian_finrank : Module.finrank ℂ JacobianRing = 1250 := by
  rw [Module.finrank_eq_nat_card_basis quotientBasis, boundedExponent_card]

def basisIndex (i : Fin 33) : BoundedExp :=
  ⟨exponent (basisMonomial i), (basis_properties i).2.2⟩

def tangentIndex (m : Fin 35) : BoundedExp :=
  ⟨exponent (tangentMonomial m), (tangent_properties m).2.2⟩

theorem basisIndex_injective : Function.Injective basisIndex := by
  intro i j h
  apply basis_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem tangentIndex_injective : Function.Injective tangentIndex := by
  intro i j h
  apply tangent_injective
  funext k
  exact congrArg (fun d : BoundedExp => d.val k) h

theorem basisMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  boundedMonomials_linearIndependent.comp basisIndex basisIndex_injective

theorem tangentMonomialClass_linearIndependent :
    LinearIndependent ℂ (fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  boundedMonomials_linearIndependent.comp tangentIndex tangentIndex_injective

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.normalCoordinates
#print axioms CycleQ2FermatJacobian.quotientBasis_eq_monomialClass
#print axioms CycleQ2FermatJacobian.boundedMonomials_linearIndependent
#print axioms CycleQ2FermatJacobian.boundedMonomials_span
#print axioms CycleQ2FermatJacobian.jacobian_finrank
#print axioms CycleQ2FermatJacobian.basisMonomialClass_linearIndependent
#print axioms CycleQ2FermatJacobian.tangentMonomialClass_linearIndependent
end
end


/- Component: jacobian/FermatJacobianGraded.lean -/
section
/-!
# The actual degree-six character components

These components are images of polynomial support subspaces under the actual
Jacobian quotient map. The finite lists are proved to span those components;
their independence comes from the normal-form theorem for the quotient.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2FermatJacobian
open MvPolynomial
open CycleQ2FermatHiggs

def pieceSupport (n χ : ℕ) : Set Exp :=
  {d | weightedDegree d = n ∧ character d = χ}

def gradedPiece (n χ : ℕ) : Submodule ℂ JacobianRing :=
  Submodule.map quotientMap.toLinearMap (restrictSupport ℂ (pieceSupport n χ))

theorem unbounded_monomial_eq_zero (d : Exp) (hd : d ∉ bounded) :
    quotientMap (monomial d 1) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mem_jacobianIdeal_iff_bounded_coeff_zero _).mpr
  intro e he
  have hde : d ≠ e := by
    intro h
    exact hd (h ▸ he)
  simp [coeff_monomial, hde]

theorem bounded_exponent_tuple (d : Exp) (hd : d ∈ bounded) :
    ∃ a b c e : Fin 5, ∃ w : Fin 2,
      (d : Fin 5 → ℕ) = ![a.val, b.val, c.val, e.val, w.val] := by
  have h0 : d 0 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 0)
  have h1 : d 1 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 1)
  have h2 : d 2 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 2)
  have h3 : d 3 < 5 := by simpa [socle] using Nat.lt_succ_of_le (hd 3)
  have h4 : d 4 < 2 := by simpa [socle] using Nat.lt_succ_of_le (hd 4)
  refine ⟨⟨d 0, h0⟩, ⟨d 1, h1⟩, ⟨d 2, h2⟩, ⟨d 3, h3⟩, ⟨d 4, h4⟩, ?_⟩
  funext i
  fin_cases i <;> rfl

theorem basis_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 1) :
    ∃ i : Fin 33, exponent (basisMonomial i) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨i, hi⟩ := basis_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨i, ?_⟩
  ext k
  exact congrFun (hi.trans h.symm) k

theorem tangent_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 6) (hc : character d = 0) :
    ∃ m : Fin 35, exponent (tangentMonomial m) = d := by
  obtain ⟨a, b, c, e, w, h⟩ := bounded_exponent_tuple d hb
  obtain ⟨m, hm⟩ := tangent_complete a b c e w (h ▸ hn) (h ▸ hc)
  refine ⟨m, ?_⟩
  ext k
  exact congrFun (hm.trans h.symm) k

theorem gradedPiece_eq_span_of_enumeration {ι : Type} (a : ι → Fin 5 → ℕ)
    (n χ : ℕ) (hprop : ∀ i, weightedDegree (a i) = n ∧ character (a i) = χ)
    (hcomplete : ∀ d ∈ bounded, weightedDegree d = n → character d = χ →
      ∃ i, exponent (a i) = d) :
    gradedPiece n χ = Submodule.span ℂ (Set.range fun i => monomialClass (a i)) := by
  classical
  rw [gradedPiece, restrictSupport_eq_span, Submodule.map_span, Set.image_image]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro q ⟨d, hd, rfl⟩
    change quotientMap (monomial d 1) ∈ _
    by_cases hb : d ∈ bounded
    · obtain ⟨i, hi⟩ := hcomplete d hb hd.1 hd.2
      apply Submodule.subset_span
      refine ⟨i, ?_⟩
      change quotientMap (monomial (exponent (a i)) 1) = quotientMap (monomial d 1)
      rw [hi]
    · rw [unbounded_monomial_eq_zero d hb]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    apply Submodule.subset_span
    exact ⟨exponent (a i), hprop i, rfl⟩

theorem degreeSixCharacterOne_eq_span :
    gradedPiece 6 1 = Submodule.span ℂ
      (Set.range fun i : Fin 33 => monomialClass (basisMonomial i)) :=
  gradedPiece_eq_span_of_enumeration basisMonomial 6 1
    (fun i => ⟨(basis_properties i).1, (basis_properties i).2.1⟩)
    basis_complete_bounded

theorem degreeSixCharacterZero_eq_span :
    gradedPiece 6 0 = Submodule.span ℂ
      (Set.range fun m : Fin 35 => monomialClass (tangentMonomial m)) :=
  gradedPiece_eq_span_of_enumeration tangentMonomial 6 0
    (fun m => ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)
    tangent_complete_bounded

def degreeSixCharacterOneBasis : Module.Basis (Fin 33) ℂ (gradedPiece 6 1) :=
  (Module.Basis.span basisMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterOne_eq_span.symm)

def degreeSixCharacterZeroBasis : Module.Basis (Fin 35) ℂ (gradedPiece 6 0) :=
  (Module.Basis.span tangentMonomialClass_linearIndependent).map
    (LinearEquiv.ofEq _ _ degreeSixCharacterZero_eq_span.symm)

theorem degreeSixCharacterOne_finrank : Module.finrank ℂ (gradedPiece 6 1) = 33 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterOneBasis]
  rfl

theorem degreeSixCharacterZero_finrank : Module.finrank ℂ (gradedPiece 6 0) = 35 := by
  rw [Module.finrank_eq_card_basis degreeSixCharacterZeroBasis]
  rfl

theorem degreeSixCharacterOneBasis_coe (i : Fin 33) :
    (degreeSixCharacterOneBasis i : JacobianRing) = monomialClass (basisMonomial i) := by
  simp [degreeSixCharacterOneBasis]

theorem degreeSixCharacterZeroBasis_coe (m : Fin 35) :
    (degreeSixCharacterZeroBasis m : JacobianRing) = monomialClass (tangentMonomial m) := by
  simp [degreeSixCharacterZeroBasis]

/-- The checked finite matrices are the trace matrices on the actual
degree-six character components of the Fermat derivative quotient. -/
theorem actual_component_trace_matrix (m : Fin 35) (i j : Fin 33) :
    socleTrace ((degreeSixCharacterOneBasis i : JacobianRing) *
      (degreeSixCharacterOneBasis j : JacobianRing) *
      (degreeSixCharacterZeroBasis m : JacobianRing)) = higgsMatrix ℂ m i j := by
  rw [degreeSixCharacterOneBasis_coe, degreeSixCharacterOneBasis_coe,
    degreeSixCharacterZeroBasis_coe, socleTrace_triple_eq_higgsMatrix]

theorem socle_weightedDegree_character :
    weightedDegree socle = 18 ∧ character socle = 2 := by decide

theorem socleTrace_normalized : socleTrace (monomialClass socle) = 1 := by
  rw [monomialClass, socleTrace_mk, coeff_monomial]
  simp

/-- The distinguished degree-eighteen class is actually in the socle:
each variable class annihilates it in the derivative quotient. -/
theorem socle_annihilated_by_variables (i : Fin 5) :
    quotientMap (X i) * monomialClass socle = 0 := by
  change quotientMap (monomial (Finsupp.single i 1) 1) *
    quotientMap (monomial (exponent socle) 1) = 0
  rw [← map_mul, monomial_mul, one_mul]
  apply unbounded_monomial_eq_zero
  intro h
  have hi := h i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, exponent_apply] at hi
  omega

end CycleQ2FermatJacobian

#print axioms CycleQ2FermatJacobian.degreeSixCharacterOne_finrank
#print axioms CycleQ2FermatJacobian.degreeSixCharacterZero_finrank
#print axioms CycleQ2FermatJacobian.actual_component_trace_matrix
#print axioms CycleQ2FermatJacobian.socle_annihilated_by_variables
end
end


/- Component: seed_trace/SparseSeedTraceData.lean -/
section
/-!
# An actual quotient trace for the sparse seed

The finite trace is constructed as a coefficient of multiplication by an
explicit polynomial. Four polynomial annihilator identities prove that it
vanishes on the defining ideal, so it descends to the actual quotient.

This file concerns the sparse seed algebra. Its associated geometric surface
is singular; no smoothness or geometric trace comparison is asserted here.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

abbrev Poly := MvPolynomial (Fin 4) ℂ
abbrev Exp := Fin 4 →₀ ℕ

def exponent (a : Fin 4 → ℕ) : Exp := Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponent_apply (a : Fin 4 → ℕ) (i : Fin 4) : exponent a i = a i := rfl

def mon (a b c d : ℕ) : Poly := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

def topExponent : Exp := exponent ![3, 9, 3, 9]
def cutoff (i : Fin 4) : ℕ := topExponent i + 1
def truncationIdeal : Ideal Poly := Ideal.span (Set.range fun i : Fin 4 => X i ^ cutoff i)

def b : Poly := X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 + X 0 * X 1 ^ 2
def h : Poly := b - C Complex.I * (X 1 ^ 3 + X 3 ^ 3)
def k : Poly := b + C Complex.I * (X 1 ^ 3 + X 3 ^ 3)

def relation (r : ℂ) : Fin 4 → Poly := ![
  X 0 ^ 2 - C r * X 1 * X 3,
  X 1 ^ 2 * X 3 ^ 2,
  X 2 ^ 4,
  h]

def reducedIdeal (r : ℂ) : Ideal Poly := Ideal.span (Set.range (relation r))

def traceNumerator (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness00 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 1 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 1 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 1 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 1 4 0 8 +
    C ((4 : ℂ)) * mon 1 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 1 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 1 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 1 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 0 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 0 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 0 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 0 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 2 3 8 +
    C ((12 : ℂ)) * mon 0 1 3 9

def witness01 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * r) * mon 3 0 3 1 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 3 0 2 2 +
    C ((-1 : ℂ) * r * Complex.I + (1 : ℂ) * r) * mon 2 0 2 3 +
    C ((2 : ℂ) * Complex.I) * mon 2 0 1 4 +
    C ((2 : ℂ) * r * Complex.I) * mon 1 0 1 5 +
    C ((2 : ℂ) * r * Complex.I) * mon 0 0 3 4 +
    C ((-2 : ℂ) * r * Complex.I + (-2 : ℂ) * r) * mon 0 0 0 7

def witness02 (r : ℂ) : Poly :=
    0

def witness03 (r : ℂ) : Poly :=
    C ((-4 : ℂ) * r) * mon 3 4 0 0 +
    C ((-8 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 1 0 +
    C ((16 : ℂ) * r * Complex.I) * mon 3 1 3 0 +
    C ((-4 : ℂ) * r * Complex.I) * mon 2 5 0 0 +
    C ((4 : ℂ)) * mon 2 4 1 0 +
    C ((-12 : ℂ) * r) * mon 2 2 3 0 +
    C ((4 : ℂ) * r) * mon 1 6 0 0 +
    C ((-8 : ℂ) * r * Complex.I) * mon 1 3 3 0 +
    C ((4 : ℂ) * r * Complex.I) * mon 0 7 0 0 +
    C ((4 : ℂ) * r) * mon 0 4 3 0

theorem annihilator0 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 0 =
      X 0 ^ 4 * witness00 r +
      X 1 ^ 10 * witness01 r +
      X 2 ^ 4 * witness02 r +
      X 3 ^ 10 * witness03 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness00, witness01, witness02, witness03,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness10 (r : ℂ) : Poly :=
    0

def witness11 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 1 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 2 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 0 1 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 1 2 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 1 1 5 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 3 4 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 0 0 7 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 1 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 1 3 5 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 1 0 8

def witness12 (r : ℂ) : Poly :=
    0

def witness13 (r : ℂ) : Poly :=
    C ((-2 : ℂ) * r ^ 2) * mon 3 6 0 0 +
    C ((4 : ℂ)) * mon 3 5 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 1 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 3 3 0 +
    C ((-16 : ℂ) * Complex.I) * mon 3 2 3 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 7 0 0 +
    C ((4 : ℂ) * Complex.I) * mon 2 6 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 5 1 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 3 0 +
    C ((12 : ℂ)) * mon 2 3 3 1 +
    C ((-4 : ℂ)) * mon 1 7 0 1 +
    C ((8 : ℂ) * Complex.I) * mon 1 4 3 1 +
    C ((-4 : ℂ) * Complex.I) * mon 0 8 0 1 +
    C ((-4 : ℂ)) * mon 0 5 3 1

theorem annihilator1 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 1 =
      X 0 ^ 4 * witness10 r +
      X 1 ^ 10 * witness11 r +
      X 2 ^ 4 * witness12 r +
      X 3 ^ 10 * witness13 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness10, witness11, witness12, witness13,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness20 (r : ℂ) : Poly :=
    0

def witness21 (r : ℂ) : Poly :=
    0

def witness22 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 1 3 +
    C ((-2 : ℂ) * r ^ 2) * mon 3 4 0 8 +
    C ((4 : ℂ)) * mon 3 3 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 2 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 3 8 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 3 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 1 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 8 0 5 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 5 0 8 +
    C ((4 : ℂ) * Complex.I) * mon 2 4 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 3 1 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 3 8 +
    C ((12 : ℂ)) * mon 2 1 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 1 9 1 4 +
    C ((-4 : ℂ)) * mon 1 5 0 9 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 3 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 9 0 6 +
    C ((-4 : ℂ) * Complex.I) * mon 0 6 0 9 +
    C ((-4 : ℂ)) * mon 0 3 3 9

def witness23 (r : ℂ) : Poly :=
    0

theorem annihilator2 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 2 =
      X 0 ^ 4 * witness20 r +
      X 1 ^ 10 * witness21 r +
      X 2 ^ 4 * witness22 r +
      X 3 ^ 10 * witness23 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness20, witness21, witness22, witness23,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

def witness30 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 0 11 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 11 2 1 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 10 1 3 +
    C ((1 : ℂ)) * mon 0 9 4 1 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 0 9 3 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 0 8 2 4 +
    C ((-2 : ℂ) * r ^ 2) * mon 0 6 0 8 +
    C ((4 : ℂ)) * mon 0 5 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 0 4 1 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 3 3 8 +
    C ((4 : ℂ)) * mon 0 3 1 10 +
    C ((-16 : ℂ) * Complex.I) * mon 0 2 3 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 0 2 2 10 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 0 1 4 9 +
    C ((-16 : ℂ) * Complex.I) * mon 0 0 4 10

def witness31 (r : ℂ) : Poly :=
    C ((-1 : ℂ) * Complex.I) * mon 3 2 3 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 2 2 1 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 3 1 2 2 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 1 1 3 +
    C ((1 : ℂ)) * mon 3 0 4 1 +
    C ((-1 : ℂ) * r ^ 2) * mon 3 0 3 2 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 3 0 0 5 +
    C ((1 : ℂ) * Complex.I + (1 : ℂ)) * mon 2 2 2 2 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 2 1 3 +
    C ((-1 : ℂ) * r ^ 2) * mon 2 1 3 2 +
    C ((-2 : ℂ) * Complex.I) * mon 2 1 1 4 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I + (1 : ℂ) * r ^ 2) * mon 2 1 0 5 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 0 3 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 0 2 4 +
    C ((-2 : ℂ)) * mon 1 2 1 4 +
    C ((-2 : ℂ) * Complex.I) * mon 1 1 3 3 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 1 1 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 1 0 2 5 +
    C ((-2 : ℂ)) * mon 0 2 3 3 +
    C ((-2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 2 0 6 +
    C ((-2 : ℂ) * Complex.I) * mon 0 0 4 4 +
    C ((2 : ℂ) * Complex.I + (2 : ℂ)) * mon 0 0 1 7

def witness32 (r : ℂ) : Poly :=
    C ((1 : ℂ)) * mon 3 9 2 0 +
    C ((1 : ℂ) * r ^ 2 * Complex.I + (-1 : ℂ) * r ^ 2) * mon 3 9 1 1 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 3 8 0 3 +
    C ((8 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 2 0 9 +
    C ((4 : ℂ) * r ^ 2 * Complex.I) * mon 3 1 2 8 +
    C ((-16 : ℂ) * Complex.I + (12 : ℂ)) * mon 3 1 0 10 +
    C ((-16 : ℂ) * Complex.I) * mon 3 0 2 9 +
    C ((1 : ℂ) * Complex.I + (-1 : ℂ)) * mon 2 9 1 2 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I) * mon 2 9 0 3 +
    C ((-1 : ℂ) * r ^ 2 * Complex.I) * mon 2 8 2 2 +
    C ((-4 : ℂ) * r ^ 2) * mon 2 3 0 9 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 2 2 8 +
    C ((8 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 2 0 10 +
    C ((12 : ℂ)) * mon 2 1 2 9 +
    C ((-4 : ℂ) * Complex.I) * mon 1 9 0 4 +
    C ((8 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 3 0 10 +
    C ((8 : ℂ) * Complex.I) * mon 1 2 2 9 +
    C ((-2 : ℂ) * Complex.I) * mon 0 9 2 3 +
    C ((-4 : ℂ)) * mon 0 4 0 10 +
    C ((-4 : ℂ)) * mon 0 3 2 9

def witness33 (r : ℂ) : Poly :=
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 4 1 0 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 3 4 0 1 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (-4 : ℂ) * r ^ 2) * mon 3 3 2 0 +
    C ((-4 : ℂ) * Complex.I + (4 : ℂ)) * mon 3 3 0 2 +
    C ((6 : ℂ) * r ^ 2 * Complex.I + (2 : ℂ) * r ^ 2) * mon 3 2 1 2 +
    C ((4 : ℂ) * r ^ 2 * Complex.I + (4 : ℂ) * r ^ 2) * mon 3 1 3 1 +
    C ((-16 : ℂ) * Complex.I + (-16 : ℂ)) * mon 3 0 3 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 2 5 1 0 +
    C ((-2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 5 0 1 +
    C ((-2 : ℂ) * r ^ 2) * mon 2 4 2 0 +
    C ((4 : ℂ) * Complex.I + (4 : ℂ)) * mon 2 4 0 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 3 1 2 +
    C ((2 : ℂ) * r ^ 2 * Complex.I + (-2 : ℂ) * r ^ 2) * mon 2 2 3 1 +
    C ((-12 : ℂ) * Complex.I + (12 : ℂ)) * mon 2 1 3 2 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 6 1 0 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 1 5 0 2 +
    C ((8 : ℂ) * Complex.I + (8 : ℂ)) * mon 1 2 3 2 +
    C ((-4 : ℂ) * Complex.I) * mon 0 7 1 0 +
    C ((-4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 6 0 2 +
    C ((4 : ℂ) * Complex.I + (-4 : ℂ)) * mon 0 3 3 2

theorem annihilator3 (r : ℂ) (hr : r ^ 3 = 2) :
    traceNumerator r * relation r 3 =
      X 0 ^ 4 * witness30 r +
      X 1 ^ 10 * witness31 r +
      X 2 ^ 4 * witness32 r +
      X 3 ^ 10 * witness33 r := by
  have hr' : (C r : Poly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : Poly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  norm_num only [traceNumerator, relation, b, h, mon,
    witness30, witness31, witness32, witness33,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    map_add, map_sub, map_mul, map_pow, map_neg, map_ofNat, map_zero, map_one]
  ring_nf <;> (try simp only [hr', hi']) <;> ring

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.annihilator0
#print axioms CycleQ2SeedTrace.annihilator1
#print axioms CycleQ2SeedTrace.annihilator2
#print axioms CycleQ2SeedTrace.annihilator3
end
end


