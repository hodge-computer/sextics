import Proposal.GeometricCurveCoordinates
import Proposal.GeometricFormalInputs01Part03
import Proposal.GeometricSeedNormalIdeals

/-! Continuation of GeometricFormalInputs01.lean; complete source components and declarations. -/

set_option Elab.async false

/- Component: seed_trace/SparseSeedTrace.lean -/
section
/-!
# Descent of the constructed sparse trace to the actual ideal quotient

The polynomial annihilator certificates prove the trace vanishes on every
multiple of every defining relation, not just on selected finite products.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial

theorem truncationIdeal_eq_monomials : truncationIdeal =
    Ideal.span ((fun d : Exp => monomial d (1 : ℂ)) ''
      Set.range (fun i : Fin 4 => Finsupp.single i (cutoff i))) := by
  unfold truncationIdeal
  congr 1
  ext p
  simp only [Set.mem_range, Set.mem_image, X_pow_eq_monomial]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, ⟨i, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩

theorem top_coeff_zero_of_mem {p : Poly} (hp : p ∈ truncationIdeal) :
    coeff topExponent p = 0 := by
  rw [truncationIdeal_eq_monomials, mem_ideal_span_monomial_image] at hp
  by_contra hc
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hp topExponent (mem_support_iff.mpr hc)
  have h := Finsupp.single_le_iff.mp hi
  change topExponent i + 1 ≤ topExponent i at h
  omega

theorem fourTerm_mem_truncation (a b c d : Poly) :
    X 0 ^ 4 * a + X 1 ^ 10 * b + X 2 ^ 4 * c + X 3 ^ 10 * d ∈
      truncationIdeal := by
  have hg (i : Fin 4) : X i ^ cutoff i ∈ truncationIdeal :=
    Ideal.subset_span ⟨i, rfl⟩
  exact Ideal.add_mem _ (Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right a _ (hg 0)) (Ideal.mul_mem_right b _ (hg 1)))
    (Ideal.mul_mem_right c _ (hg 2))) (Ideal.mul_mem_right d _ (hg 3))

theorem annihilator_generators_mem (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    traceNumerator r * relation r i ∈ truncationIdeal := by
  fin_cases i
  · change traceNumerator r * relation r 0 ∈ truncationIdeal
    rw [annihilator0 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 1 ∈ truncationIdeal
    rw [annihilator1 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 2 ∈ truncationIdeal
    rw [annihilator2 r hr]
    exact fourTerm_mem_truncation _ _ _ _
  · change traceNumerator r * relation r 3 ∈ truncationIdeal
    rw [annihilator3 r hr]
    exact fourTerm_mem_truncation _ _ _ _

theorem traceNumerator_mul_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) :
    traceNumerator r * p ∈ truncationIdeal := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨i, rfl⟩ := hp
      exact annihilator_generators_mem r hr i
  | zero => simp
  | add p q _ _ hp hq =>
      simpa only [mul_add] using Ideal.add_mem truncationIdeal hp hq
  | smul a p _ hp =>
      simpa only [smul_eq_mul, mul_left_comm] using
        Ideal.mul_mem_left truncationIdeal a hp

def traceLinear (r : ℂ) : Poly →ₗ[ℂ] ℂ :=
  ((1 / 12 : ℂ) • lcoeff ℂ topExponent).comp
    (LinearMap.mul ℂ Poly (traceNumerator r))

@[simp] theorem traceLinear_apply (r : ℂ) (p : Poly) :
    traceLinear r p = (1 / 12 : ℂ) * coeff topExponent (traceNumerator r * p) := rfl

theorem traceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : Poly} (hp : p ∈ reducedIdeal r) : traceLinear r p = 0 := by
  rw [traceLinear_apply, top_coeff_zero_of_mem (traceNumerator_mul_mem r hr hp), mul_zero]

abbrev ReducedAlgebra (r : ℂ) := Poly ⧸ reducedIdeal r

def reducedQuotient (r : ℂ) : Poly →ₐ[ℂ] ReducedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (reducedIdeal r)

/-- The normalized coefficient functional genuinely descends to the quotient. -/
def reducedTrace (r : ℂ) (hr : r ^ 3 = 2) : ReducedAlgebra r →ₗ[ℂ] ℂ :=
  ((reducedIdeal r).restrictScalars ℂ).liftQ (traceLinear r) (by
    intro p hp
    exact traceLinear_zero_of_mem r hr hp)

@[simp] theorem reducedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : Poly) :
    reducedTrace r hr (reducedQuotient r p) = traceLinear r p := rfl

theorem mon_eq_monomial (a b c d : ℕ) :
    mon a b c d = monomial (exponent ![a, b, c, d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : Exp => monomial e (1 : ℂ))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem mon_mul (a b c d e f g h : ℕ) :
    mon a b c d * mon e f g h = mon (a+e) (b+f) (c+g) (d+h) := by
  simp only [mon, pow_add]
  ring

theorem coeff_top_mon (a b c d : ℕ) :
    coeff topExponent (mon a b c d) =
      if a = 3 ∧ b = 9 ∧ c = 3 ∧ d = 9 then 1 else 0 := by
  rw [mon_eq_monomial, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨congrArg (fun e : Exp => e 0) h, congrArg (fun e : Exp => e 1) h,
      congrArg (fun e : Exp => e 2) h, congrArg (fun e : Exp => e 3) h⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    rfl

theorem trace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    reducedTrace r hr (reducedQuotient r (mon 1 8 0 0)) = 1 := by
  rw [reducedTrace_mk, traceLinear_apply]
  simp only [traceNumerator, add_mul, mul_assoc, mon_mul, coeff_add, coeff_C_mul,
    coeff_top_mon]
  norm_num

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.traceLinear_zero_of_mem
#print axioms CycleQ2SeedTrace.reducedTrace
#print axioms CycleQ2SeedTrace.trace_normalized
end
end


/- Component: seed_trace/SparseSeedOriginal.lean -/
section
/-!
# The trace on the original five-variable seed algebra

This uses the actual five relations f1,g1,f2,g2,h from the sparse seed.
Substitution w=-x2^2 sends their ideal into the four-variable ideal on which
the coefficient functional has already been proved to vanish.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2SeedTrace
open MvPolynomial


def seedEquation : WeightedPoly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3 + originalB ^ 2

theorem seedEquation_decomposition (r : ℂ) (hr : r ^ 3 = 2) :
    seedEquation = originalF1 r * originalG1 r + originalF2 * originalG2 +
      originalH * originalK := by
  have hr' : (C r : WeightedPoly) ^ 3 = 2 := by rw [← map_pow, hr, map_ofNat]
  have hi' : (C Complex.I : WeightedPoly) ^ 2 = -1 := by
    rw [← map_pow, Complex.I_sq, map_neg, map_one]
  simp only [seedEquation, originalF1, originalG1, originalF2, originalG2,
    originalH, originalK, map_pow]
  ring_nf
  rw [hr', hi']
  ring

def originalRelations (r : ℂ) : Fin 5 → WeightedPoly :=
  ![originalF1 r, originalG1 r, originalF2, originalG2, originalH]

def originalIdeal (r : ℂ) : Ideal WeightedPoly := Ideal.span (Set.range (originalRelations r))


theorem substitute_relations (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) =
      ![relation r 0,
        relation r 0 * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
          C (3 * r ^ 2) * relation r 1,
        0,
        3 * relation r 2,
        relation r 3] i := by
  fin_cases i <;>
    norm_num [substitute, originalRelations, originalF1, originalG1, originalF2,
      originalG2, originalH, originalB, relation, b, h, map_pow, map_mul, map_ofNat,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons] <;> ring

theorem substitute_relations_mem (r : ℂ) (i : Fin 5) :
    substitute (originalRelations r i) ∈ reducedIdeal r := by
  have hg (j : Fin 4) : relation r j ∈ reducedIdeal r := Ideal.subset_span ⟨j, rfl⟩
  rw [substitute_relations]
  fin_cases i
  · exact hg 0
  · exact Ideal.add_mem _
      (Ideal.mul_mem_right _ _ (hg 0)) (Ideal.mul_mem_left _ _ (hg 1))
  · exact Ideal.zero_mem _
  · exact Ideal.mul_mem_left _ _ (hg 2)
  · exact hg 3

theorem substitute_mem_reduced (r : ℂ) {p : WeightedPoly} (hp : p ∈ originalIdeal r) :
    substitute p ∈ reducedIdeal r := by
  have hle : originalIdeal r ≤ Ideal.comap substitute.toRingHom (reducedIdeal r) := by
    rw [originalIdeal, Ideal.span_le]
    rintro p ⟨i, rfl⟩
    exact substitute_relations_mem r i
  exact hle hp

def originalTraceLinear (r : ℂ) : WeightedPoly →ₗ[ℂ] ℂ :=
  (traceLinear r).comp substitute.toLinearMap

theorem originalTraceLinear_zero_of_mem (r : ℂ) (hr : r ^ 3 = 2)
    {p : WeightedPoly} (hp : p ∈ originalIdeal r) : originalTraceLinear r p = 0 :=
  traceLinear_zero_of_mem r hr (substitute_mem_reduced r hp)

abbrev SeedAlgebra (r : ℂ) := WeightedPoly ⧸ originalIdeal r

def seedQuotient (r : ℂ) : WeightedPoly →ₐ[ℂ] SeedAlgebra r :=
  Ideal.Quotient.mkₐ ℂ (originalIdeal r)

/-- The constructed functional on the actual original seed ideal quotient. -/
def seedTrace (r : ℂ) (hr : r ^ 3 = 2) : SeedAlgebra r →ₗ[ℂ] ℂ :=
  ((originalIdeal r).restrictScalars ℂ).liftQ (originalTraceLinear r) (by
    intro p hp
    exact originalTraceLinear_zero_of_mem r hr hp)

@[simp] theorem seedTrace_mk (r : ℂ) (hr : r ^ 3 = 2) (p : WeightedPoly) :
    seedTrace r hr (seedQuotient r p) = traceLinear r (substitute p) := rfl

theorem seedTrace_normalized (r : ℂ) (hr : r ^ 3 = 2) :
    seedTrace r hr (seedQuotient r (X 0 * X 1 ^ 8)) = 1 := by
  rw [seedTrace_mk]
  have heq : substitute (X 0 * X 1 ^ 8) = mon 1 8 0 0 := by
    simp [substitute, mon]
  rw [heq]
  exact trace_normalized r hr

end CycleQ2SeedTrace

#print axioms CycleQ2SeedTrace.seedEquation_decomposition
#print axioms CycleQ2SeedTrace.seedTrace
#print axioms CycleQ2SeedTrace.seedTrace_normalized
end
end


