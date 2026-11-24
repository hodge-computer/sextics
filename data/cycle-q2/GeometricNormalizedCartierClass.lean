import Proposal.GeometricSurfaceBindings
import Proposal.GeometricCartierCoordinateDescent
import Proposal.GeometricCartierCharacter

/-! Actual normalized universal-surface coordinates, their canonical graded
projection, and the literal original Cartier class in the original
character-one top Cech quotient. Each component retains its source options
and anonymous section scope. -/

/- Component: DebugUniversalSurfaceBasis.lean -/
section
/-! Exact named declaration extraction for the normalized universal surface.
The original coefficient indices and original quotient/basis definitions are retained.
No old aggregate or independent chosen cohomology vector is imported. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2IncidenceNormalForm
open MvPolynomial
variable {σ R : Type*} [CommRing R]

theorem unit_scaled_representation_iff (u v : Rˣ) (h F p r : MvPolynomial σ R) :
    (∃ a b, p = a * h + b * F + r) ↔
      (∃ a b, p = a * (C (u : R) * h) + b * (C (v : R) * F) + r) := by
  constructor
  · rintro ⟨a, b, hp⟩
    refine ⟨a * C (↑u⁻¹ : R), b * C (↑v⁻¹ : R), ?_⟩
    have hcancel (z : Rˣ) (a q : MvPolynomial σ R) :
        (a * C (↑z⁻¹ : R)) * (C (z : R) * q) = a * q := by
      calc
        _ = a * (C (↑z⁻¹ : R) * C (z : R)) * q := by ring
        _ = a * q := by rw [← map_mul, Units.inv_mul, map_one, mul_one]
    simpa only [hcancel] using hp
  · rintro ⟨a, b, hp⟩
    exact ⟨a * C (u : R), b * C (v : R), by simpa only [mul_assoc] using hp⟩

abbrev FullCubicTailIndex := {e : FullInvariantIndex 3 // (e.val 0).val < 3}
abbrev FullSexticTailIndex := {e : FullInvariantIndex 6 // (e.val 4).val < 3}

def normalizedFullCubic (c : FullCubicTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 0 3) 1 + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def normalizedFullSextic (c : FullSexticTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 4 3) 1 + ∑ e, monomial (fullExponentOf e.val.val) (c e)

/-- The raw full families have all nine cubic and all forty-five sextic
coefficients, including their leading coefficients. -/
def rawFullCubic (a : R) (c : FullCubicTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 0 3) a + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def rawFullSextic (a : R) (c : FullSexticTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 4 3) a + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def fullCubicLeadingIndex : FullInvariantIndex 3 :=
  ⟨![3, 0, 0, 0, 0], by decide⟩

def fullSexticLeadingIndex : FullInvariantIndex 6 :=
  ⟨![0, 0, 0, 0, 3], by decide⟩

lemma fullCubic_tail_iff_ne (e : FullInvariantIndex 3) :
    (e.val 0).val < 3 ↔ e ≠ fullCubicLeadingIndex := by
  constructor
  · intro he h
    subst e
    change (3 : ℕ) < 3 at he
    omega
  · intro he
    by_contra h0
    apply he
    have hd := e.property.1
    have hb := (e.val 0).isLt
    simp only [fullDegree] at hd
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i <;> simp [fullCubicLeadingIndex] <;> omega

lemma fullSextic_tail_iff_ne (e : FullInvariantIndex 6) :
    (e.val 4).val < 3 ↔ e ≠ fullSexticLeadingIndex := by
  constructor
  · intro he h
    subst e
    change (3 : ℕ) < 3 at he
    omega
  · intro he
    by_contra h4
    apply he
    have hd := e.property.1
    simp only [fullDegree] at hd
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i <;> simp [fullSexticLeadingIndex] <;> omega

noncomputable def fullCubicTailEquiv :
    FullCubicTailIndex ≃ {e : FullInvariantIndex 3 // e ≠ fullCubicLeadingIndex} :=
  Equiv.subtypeEquivRight fullCubic_tail_iff_ne

noncomputable def fullSexticTailEquiv :
    FullSexticTailIndex ≃ {e : FullInvariantIndex 6 // e ≠ fullSexticLeadingIndex} :=
  Equiv.subtypeEquivRight fullSextic_tail_iff_ne

@[simp] lemma fullCubicLeadingIndex_exponent :
    fullExponentOf fullCubicLeadingIndex.val = Finsupp.single 0 3 := by
  ext i
  fin_cases i <;> simp [fullCubicLeadingIndex]

@[simp] lemma fullSexticLeadingIndex_exponent :
    fullExponentOf fullSexticLeadingIndex.val = Finsupp.single 4 3 := by
  ext i
  fin_cases i <;> simp [fullSexticLeadingIndex]

theorem fullInvariantPolynomial_cubic (c : FullInvariantIndex 3 → R) :
    fullInvariantPolynomial 3 c =
      rawFullCubic (c fullCubicLeadingIndex) (fun e ↦ c e.val) := by
  classical
  rw [fullInvariantPolynomial,
    Fintype.sum_eq_add_sum_subtype_ne _ fullCubicLeadingIndex]
  simp only [fullCubicLeadingIndex_exponent, rawFullCubic]
  exact congrArg (fun q : MvPolynomial (Fin 5) R ↦
    monomial (Finsupp.single 0 3) (c fullCubicLeadingIndex) + q)
    (fullCubicTailEquiv.sum_comp
      (fun e ↦ monomial (fullExponentOf e.val.val) (c e.val))).symm

theorem fullInvariantPolynomial_sextic (c : FullInvariantIndex 6 → R) :
    fullInvariantPolynomial 6 c =
      rawFullSextic (c fullSexticLeadingIndex) (fun e ↦ c e.val) := by
  classical
  rw [fullInvariantPolynomial,
    Fintype.sum_eq_add_sum_subtype_ne _ fullSexticLeadingIndex]
  simp only [fullSexticLeadingIndex_exponent, rawFullSextic]
  exact congrArg (fun q : MvPolynomial (Fin 5) R ↦
    monomial (Finsupp.single 4 3) (c fullSexticLeadingIndex) + q)
    (fullSexticTailEquiv.sum_comp
      (fun e ↦ monomial (fullExponentOf e.val.val) (c e.val))).symm

theorem rawFullCubic_eq_unit_mul (u : Rˣ) (c : FullCubicTailIndex → R) :
    rawFullCubic (u : R) c =
      C (u : R) * normalizedFullCubic (fun e ↦ (↑u⁻¹ : R) * c e) := by
  simp [rawFullCubic, normalizedFullCubic, mul_add, Finset.mul_sum,
    C_mul_monomial, ← mul_assoc]

theorem rawFullSextic_eq_unit_mul (u : Rˣ) (c : FullSexticTailIndex → R) :
    rawFullSextic (u : R) c =
      C (u : R) * normalizedFullSextic (fun e ↦ (↑u⁻¹ : R) * c e) := by
  simp [rawFullSextic, normalizedFullSextic, mul_add, Finset.mul_sum,
    C_mul_monomial, ← mul_assoc]

end CycleQ2IncidenceNormalForm

namespace CycleQ2IncidenceEquations
open MvPolynomial CycleQ2IncidenceNormalForm
variable {R : Type*} [CommRing R]

theorem smoothH_leading_coefficient (ι : R) :
    (smoothH ι).coeff (Finsupp.single 0 3) = 1 := by
  simp only [smoothH, smoothB, smoothA, coeff_sub, coeff_add, coeff_C_mul,
    X_pow_eq_monomial]
  simp only [X, monomial_mul, coeff_monomial]
  have h3 : (Finsupp.single (3 : Fin 5) 3 : FullExponent) ≠ Finsupp.single 0 3 := by
    intro he
    have h0 := congrArg (fun e : FullExponent ↦ e 0) he
    have h30 : (3 : Fin 5) ≠ 0 := by decide
    rw [Finsupp.single_eq_of_ne' h30, Finsupp.single_eq_same] at h0
    omega
  simp only [if_neg h3]
  norm_num [Finsupp.ext_iff, Fin.forall_fin_succ]

private def wOnly : Fin 5 → ℕ := fun i ↦ if i = 4 then 1 else 0

private theorem wOnly_X (i : Fin 5) (hi : i ≠ 4) :
    (X i : Poly R).IsWeightedHomogeneous wOnly 0 := by
  simpa only [wOnly, if_neg hi] using isWeightedHomogeneous_X R wOnly i

private theorem smoothB_no_w :
    (smoothB : Poly R).IsWeightedHomogeneous wOnly 0 := by
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  exact (((((h3.pow 3).add (h2.pow 3)).add ((h1.mul h2).mul h3)).add
    ((h0.mul h2).mul h3)).add (h0.mul (h1.pow 2))).add (h0.pow 3)

private theorem smoothA_no_w :
    (smoothA : Poly R).IsWeightedHomogeneous wOnly 0 :=
  ((wOnly_X 1 (by decide)).pow 3).add ((wOnly_X 3 (by decide)).pow 3)

private theorem wOnly_leading_ne :
    Finsupp.weight wOnly (Finsupp.single 4 3) ≠ 0 := by
  simp [Finsupp.weight_single, wOnly]

theorem smoothF_leading_coefficient (r ι : R) :
    (smoothF r ι).coeff (Finsupp.single 4 3) = 1 := by
  have hprod : (smoothH ι * smoothK ι).IsWeightedHomogeneous wOnly 0 :=
    (smoothB_no_w.sub (smoothA_no_w.C_mul ι)).mul
      (smoothB_no_w.add (smoothA_no_w.C_mul ι))
  have h0 := wOnly_X (R := R) 0 (by decide)
  have h1 := wOnly_X (R := R) 1 (by decide)
  have h2 := wOnly_X (R := R) 2 (by decide)
  have h3 := wOnly_X (R := R) 3 (by decide)
  have hpart : IsWeightedHomogeneous wOnly
      ((X 0 : Poly R)^6 - (C r)^3 * X 1^3 * X 3^3 + X 2^6) 0 :=
    ((h0.pow 6).sub ((((isWeightedHomogeneous_C wOnly r).pow 3).mul
      (h1.pow 3)).mul (h3.pow 3))).add (h2.pow 6)
  rw [smoothF, coeff_add, hprod.coeff_eq_zero _ wOnly_leading_ne, add_zero,
    seedG, CycleQ2SegreSeed.seedG_expanded, coeff_add,
    hpart.coeff_eq_zero _ wOnly_leading_ne, zero_add, coeff_X_pow, if_pos rfl]

theorem seedCubicCoefficients_unit (ι : R) :
    IsUnit (seedCubicCoefficients ι fullCubicLeadingIndex) := by
  have he := fullCubicLeadingIndex_exponent
  simpa only [seedCubicCoefficients, he, smoothH_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

theorem seedSexticCoefficients_unit (r ι : R) :
    IsUnit (seedSexticCoefficients r ι fullSexticLeadingIndex) := by
  have he := fullSexticLeadingIndex_exponent
  simpa only [seedSexticCoefficients, he, smoothF_leading_coefficient] using (isUnit_one : IsUnit (1 : R))

end CycleQ2IncidenceEquations

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurface

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

def selectedExponent (e : Fin 5 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (e 0) + Finsupp.single 1 (e 4)

def remainingExponent (e : Fin 5 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (e 1) + Finsupp.single 1 (e 2) + Finsupp.single 2 (e 3)

theorem regroup_monomial (e : Fin 5 →₀ ℕ) (c : R) :
    regroup R (monomial e c) =
      monomial (selectedExponent e) (monomial (remainingExponent e) c) := by
  simp only [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_succ, selectedExponent, remainingExponent, Fin.reduceSucc]
  ring

def nestedWeight : (Fin 2 →₀ ℕ) →+ ℕ where
  toFun e := 3 * e 0 + 7 * e 1
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def nestedOrder : MonomialOrder (Fin 2) :=
  weightedOrder MonomialOrder.lex nestedWeight

def nestedCubic (hcoeff : FullCubicTailIndex → R) : Nested R :=
  monomial (Finsupp.single 0 3) 1 +
    ∑ e, monomial (selectedExponent (fullExponentOf e.val.val))
      (monomial (remainingExponent (fullExponentOf e.val.val)) (hcoeff e))

def nestedSextic (Fcoeff : FullSexticTailIndex → R) : Nested R :=
  monomial (Finsupp.single 1 3) 1 +
    ∑ e, monomial (selectedExponent (fullExponentOf e.val.val))
      (monomial (remainingExponent (fullExponentOf e.val.val)) (Fcoeff e))

theorem regroup_cubic (hcoeff : FullCubicTailIndex → R) :
    regroup R (normalizedFullCubic hcoeff) = nestedCubic R hcoeff := by
  simp only [normalizedFullCubic, map_add, map_sum, regroup_monomial, nestedCubic]
  congr 1
  simp [selectedExponent, remainingExponent, Finsupp.single_apply]

theorem regroup_sextic (Fcoeff : FullSexticTailIndex → R) :
    regroup R (normalizedFullSextic Fcoeff) = nestedSextic R Fcoeff := by
  simp only [normalizedFullSextic, map_add, map_sum, regroup_monomial, nestedSextic]
  congr 1
  simp [selectedExponent, remainingExponent, Finsupp.single_apply]

theorem nestedCubic_leading [Nontrivial R] (hcoeff : FullCubicTailIndex → R) :
    nestedOrder.degree (nestedCubic R hcoeff) = Finsupp.single 0 3 ∧
      nestedOrder.Monic (nestedCubic R hcoeff) := by
  apply degree_monic_add_sum nestedOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [nestedWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have hc := e.val.property.2
    have h0 := e.property
    simp only [fullDegree, fullCharacter] at hd hc
    simp only [nestedWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      selectedExponent, Finsupp.add_apply, Finsupp.single_apply,
      fullExponentOf_apply]
    norm_num
    have h4 : (e.val.val 4).val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h4 with h4 | h4
    · omega
    · have hc_lt : 2 * (e.val.val 0).val + 2 * (e.val.val 1).val +
          (e.val.val 2).val < 3 := by omega
      rw [Nat.mod_eq_of_lt hc_lt] at hc
      omega

theorem nestedSextic_leading [Nontrivial R] (Fcoeff : FullSexticTailIndex → R) :
    nestedOrder.degree (nestedSextic R Fcoeff) = Finsupp.single 1 3 ∧
      nestedOrder.Monic (nestedSextic R Fcoeff) := by
  apply degree_monic_add_sum nestedOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [nestedWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have h4 := e.property
    simp only [fullDegree] at hd
    simp only [nestedWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      selectedExponent, Finsupp.add_apply, Finsupp.single_apply,
      fullExponentOf_apply]
    norm_num
    omega

def surfaceIdeal (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Ideal (Poly R) :=
  equationsIdeal (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff)

abbrev SurfaceRing (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) := Poly R ⧸ surfaceIdeal R hcoeff Fcoeff

instance surfaceModule (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Module (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  (inferInstance : Algebra (Base R) (SurfaceRing R hcoeff Fcoeff)).toModule

def nestedIdeal (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Ideal (Nested R) :=
  equationsIdeal (nestedCubic R hcoeff) (nestedSextic R Fcoeff)

theorem nestedIdeal_map (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    nestedIdeal R hcoeff Fcoeff =
      (surfaceIdeal R hcoeff Fcoeff).map (regroupOverBase R).toRingHom := by
  simp only [nestedIdeal, surfaceIdeal, equationsIdeal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {nestedCubic R hcoeff, nestedSextic R Fcoeff} =
    Ideal.span {regroup R (normalizedFullCubic hcoeff),
      regroup R (normalizedFullSextic Fcoeff)}
  rw [regroup_cubic, regroup_sextic]

def quotientRegroup (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    SurfaceRing R hcoeff Fcoeff ≃ₐ[Base R]
      (Nested R ⧸ nestedIdeal R hcoeff Fcoeff) :=
  Ideal.quotientEquivAlg _ _ (regroupOverBase R) (nestedIdeal_map R hcoeff Fcoeff)

theorem nested_coprime [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    ∀ j, nestedOrder.degree (nestedCubic R hcoeff) j = 0 ∨
      nestedOrder.degree (nestedSextic R Fcoeff) j = 0 := by
  intro j
  rw [(nestedCubic_leading R hcoeff).1, (nestedSextic_leading R Fcoeff).1]
  fin_cases j <;> simp

def nestedExponentEquiv [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    reducedExponents nestedOrder (nestedCubic R hcoeff) (nestedSextic R Fcoeff) ≃
      Fin 3 × Fin 3 where
  toFun d :=
    (⟨d.val 0, by
      have hd := d.property.1
      rw [(nestedCubic_leading R hcoeff).1, single_three_le_iff] at hd
      omega⟩,
     ⟨d.val 1, by
      have hd := d.property.2
      rw [(nestedSextic_leading R Fcoeff).1, single_three_le_iff] at hd
      omega⟩)
  invFun ij := ⟨Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val, by
    constructor
    · rw [(nestedCubic_leading R hcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.1.isLt
    · rw [(nestedSextic_leading R Fcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.2.isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp
  right_inv ij := by
    apply Prod.ext <;> apply Fin.ext <;> simp

def nestedBasis [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (Nested R ⧸ nestedIdeal R hcoeff Fcoeff) :=
  (quotientBasis nestedOrder (nestedCubic R hcoeff) (nestedSextic R Fcoeff)
    (nestedCubic_leading R hcoeff).2 (nestedSextic_leading R Fcoeff).2
    (nested_coprime R hcoeff Fcoeff)).reindex
      (nestedExponentEquiv R hcoeff Fcoeff)

theorem nestedBasis_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : Fin 3 × Fin 3) :
    nestedBasis R hcoeff Fcoeff ab = Ideal.Quotient.mk (nestedIdeal R hcoeff Fcoeff)
      (X 0 ^ ab.1.val * X 1 ^ ab.2.val) := by
  unfold nestedBasis
  erw [Module.Basis.reindex_apply, quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val) 1 = _
  rw [MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

def surfaceBasis [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  (nestedBasis R hcoeff Fcoeff).map (quotientRegroup R hcoeff Fcoeff).symm.toLinearEquiv

theorem surfaceBasis_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : Fin 3 × Fin 3) :
    surfaceBasis R hcoeff Fcoeff ab = Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff)
      ((X 0 : Poly R) ^ ab.1.val * X 4 ^ ab.2.val) := by
  apply (quotientRegroup R hcoeff Fcoeff).injective
  simp only [surfaceBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, nestedBasis_apply]
  change Ideal.Quotient.mk _ (X 0 ^ ab.1.val * X 1 ^ ab.2.val) =
    Ideal.Quotient.mk _ (regroup R ((X 0 : Poly R) ^ ab.1.val * X 4 ^ ab.2.val))
  simp

theorem surfaceQuotient_free [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Free (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  Module.Free.of_basis (surfaceBasis R hcoeff Fcoeff)

theorem surfaceQuotient_finite [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Finite (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  Module.Finite.of_basis (surfaceBasis R hcoeff Fcoeff)

theorem surfaceQuotient_rank_nine [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank (Base R) (SurfaceRing R hcoeff Fcoeff) = 9 := by
  rw [Module.finrank_eq_card_basis (surfaceBasis R hcoeff Fcoeff)]
  decide
end CycleQ2UniversalSurface
end
end
end

/- Component: DebugUniversalSurfaceNormalization.lean -/
section
/-! Exact leading-coefficient localization and normalization declarations.
The original parameter ring, original specialization, and original
`seed_normalized_ideal` are retained with their actual definitions. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2IncidenceUniversalChart
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations

def leadingProduct (R : Type*) [CommRing R] : ParameterPolynomial R :=
  X (Sum.inl fullCubicLeadingIndex) * X (Sum.inr (Sum.inl fullSexticLeadingIndex))

theorem leadingProduct_ne_zero (R : Type*) [CommRing R] [IsDomain R] :
    leadingProduct R ≠ 0 := mul_ne_zero (X_ne_zero _) (X_ne_zero _)

abbrev ParameterRing (R : Type*) [CommRing R] := Localization.Away (leadingProduct R)

instance parameterRingDomain (R : Type*) [CommRing R] [IsDomain R] :
    IsDomain (ParameterRing R) := Localization.Away.isDomain (leadingProduct_ne_zero R)

variable (R : Type*) [CommRing R] [IsDomain R]

def cubicCoefficient (e : FullInvariantIndex 3) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inl e))

def sexticCoefficient (e : FullInvariantIndex 6) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inl e)))

def matrixCoefficient (i j : Fin 3) (e : StandardIndex 14) : ParameterRing R :=
  algebraMap (ParameterPolynomial R) (ParameterRing R) (X (Sum.inr (Sum.inr ((i, j), e))))

theorem leading_coefficients_units :
    IsUnit (cubicCoefficient R fullCubicLeadingIndex) ∧
      IsUnit (sexticCoefficient R fullSexticLeadingIndex) := by
  have hu := IsLocalization.Away.algebraMap_isUnit (S := ParameterRing R) (leadingProduct R)
  have hp : IsUnit (cubicCoefficient R fullCubicLeadingIndex *
      sexticCoefficient R fullSexticLeadingIndex) := by
    simpa only [leadingProduct, map_mul, cubicCoefficient, sexticCoefficient] using hu
  exact ⟨isUnit_of_mul_isUnit_left hp, isUnit_of_mul_isUnit_right hp⟩

section Specialization
variable {R} {S : Type*} [CommRing S] [Algebra R S]

theorem polynomialSpecialization_leadingProduct
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) :
    polynomialSpecialization hcoeff Fcoeff δ (leadingProduct R) =
      hcoeff fullCubicLeadingIndex * Fcoeff fullSexticLeadingIndex := by
  simp [polynomialSpecialization, leadingProduct, coefficientPoint]

/-- Every actual coefficient point in the two-leading-coefficient open has
its canonical specialization from the universal localized coefficient ring. -/
def specialization (hcoeff : FullInvariantIndex 3 → S)
    (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : ParameterRing R →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (leadingProduct R)
    (f := polynomialSpecialization hcoeff Fcoeff δ)
    (by rw [polynomialSpecialization_leadingProduct]; exact hu.mul Fu)

@[simp] theorem specialization_polynomial
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (p : ParameterPolynomial R) :
    specialization hcoeff Fcoeff hu Fu δ
      (algebraMap (ParameterPolynomial R) (ParameterRing R) p) =
        polynomialSpecialization hcoeff Fcoeff δ p := by
  simp [specialization, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem specialization_cubicCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 3) :
    specialization hcoeff Fcoeff hu Fu δ (cubicCoefficient R e) = hcoeff e := by
  simp [specialization, cubicCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_sexticCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) (e : FullInvariantIndex 6) :
    specialization hcoeff Fcoeff hu Fu δ (sexticCoefficient R e) = Fcoeff e := by
  simp [specialization, sexticCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

@[simp] theorem specialization_matrixCoefficient
    (hcoeff : FullInvariantIndex 3 → S) (Fcoeff : FullInvariantIndex 6 → S)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S)
    (i j : Fin 3) (e : StandardIndex 14) :
    specialization hcoeff Fcoeff hu Fu δ (matrixCoefficient R i j e) = δ i j e := by
  simp [specialization, matrixCoefficient, IsLocalization.Away.liftAlgHom_apply,
    polynomialSpecialization, coefficientPoint]

end Specialization

/-- The literal raw smooth seed is an actual point of the universal chart. -/
def seedSpecialization (r ι : R) : ParameterRing R →ₐ[R] R :=
  specialization (seedCubicCoefficients ι) (seedSexticCoefficients r ι)
    (seedCubicCoefficients_unit ι) (seedSexticCoefficients_unit r ι)
    (fun _ _ _ => 0)

end CycleQ2IncidenceUniversalChart
end

namespace CycleQ2UniversalSurfaceCoefficientMap
open MvPolynomial CycleQ2IncidenceNormalForm
variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_cubic (f : R →+* S) (hcoeff : FullCubicTailIndex → R) :
    MvPolynomial.map f (normalizedFullCubic hcoeff) =
      normalizedFullCubic (fun i => f (hcoeff i)) := by
  simp [normalizedFullCubic]

theorem map_sextic (f : R →+* S) (Fcoeff : FullSexticTailIndex → R) :
    MvPolynomial.map f (normalizedFullSextic Fcoeff) =
      normalizedFullSextic (fun i => f (Fcoeff i)) := by
  simp [normalizedFullSextic]

end CycleQ2UniversalSurfaceCoefficientMap

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceNormalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2SeedQuotientFiniteFree
  CycleQ2UniversalSurface CycleQ2UniversalSurfaceCoefficientMap

variable {R : Type*} [CommRing R]

theorem equationsIdeal_unit_mul (u v : Rˣ) (h F : Poly R) :
    equationsIdeal (C (u : R) * h) (C (v : R) * F) = equationsIdeal h F := by
  ext p
  constructor
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    have hp' : ∃ a b, p = a * (C (u : R) * h) + b * (C (v : R) * F) + 0 :=
      ⟨a,b,by simpa using hab.symm⟩
    obtain ⟨a,b,hab⟩ := (unit_scaled_representation_iff u v h F p 0).mpr hp'
    exact Ideal.mem_span_pair.mpr ⟨a,b,by simpa using hab.symm⟩
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    have hp' : ∃ a b, p = a * h + b * F + 0 := ⟨a,b,by simpa using hab.symm⟩
    obtain ⟨a,b,hab⟩ := (unit_scaled_representation_iff u v h F p 0).mp hp'
    exact Ideal.mem_span_pair.mpr ⟨a,b,by simpa using hab.symm⟩

def normalizedCubicTail (hcoeff : FullInvariantIndex 3 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex)) : FullCubicTailIndex → R :=
  fun e => (↑hu.unit⁻¹ : R) * hcoeff e.val

def normalizedSexticTail (Fcoeff : FullInvariantIndex 6 → R)
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) : FullSexticTailIndex → R :=
  fun e => (↑Fu.unit⁻¹ : R) * Fcoeff e.val

theorem fullCubic_eq_unit_mul (hcoeff : FullInvariantIndex 3 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex)) :
    fullInvariantPolynomial 3 hcoeff =
      C (hu.unit : R) * normalizedFullCubic (normalizedCubicTail hcoeff hu) := by
  rw [fullInvariantPolynomial_cubic]
  exact (congrArg (fun z => rawFullCubic z (fun e => hcoeff e.val))
    hu.unit_spec.symm).trans (rawFullCubic_eq_unit_mul hu.unit _)

theorem fullSextic_eq_unit_mul (Fcoeff : FullInvariantIndex 6 → R)
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    fullInvariantPolynomial 6 Fcoeff =
      C (Fu.unit : R) * normalizedFullSextic (normalizedSexticTail Fcoeff Fu) := by
  rw [fullInvariantPolynomial_sextic]
  exact (congrArg (fun z => rawFullSextic z (fun e => Fcoeff e.val))
    Fu.unit_spec.symm).trans (rawFullSextic_eq_unit_mul Fu.unit _)

theorem fullIdeal_normalized (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) =
      surfaceIdeal R (normalizedCubicTail hcoeff hu) (normalizedSexticTail Fcoeff Fu) := by
  rw [fullCubic_eq_unit_mul hcoeff hu, fullSextic_eq_unit_mul Fcoeff Fu]
  exact equationsIdeal_unit_mul hu.unit Fu.unit _ _

/-- This equivalence is induced by the identity on the original five coordinates. -/
def fullSurfaceEquiv (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) :
    (Poly R ⧸ equationsIdeal (fullInvariantPolynomial 3 hcoeff)
      (fullInvariantPolynomial 6 Fcoeff)) ≃ₐ[Base R]
      SurfaceRing R (normalizedCubicTail hcoeff hu) (normalizedSexticTail Fcoeff Fu) :=
  Ideal.quotientEquivAlgOfEq (Base R) (fullIdeal_normalized hcoeff Fcoeff hu Fu)

@[simp] theorem fullSurfaceEquiv_mk (hcoeff : FullInvariantIndex 3 → R)
    (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : Poly R) :
    fullSurfaceEquiv hcoeff Fcoeff hu Fu (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ p := rfl

variable (R) [IsDomain R]

def universalCubicTail : FullCubicTailIndex → ParameterRing R :=
  normalizedCubicTail (cubicCoefficient R) (leading_coefficients_units R).1

def universalSexticTail : FullSexticTailIndex → ParameterRing R :=
  normalizedSexticTail (sexticCoefficient R) (leading_coefficients_units R).2

theorem universalIdeal_normalized :
    equationsIdeal (fullInvariantPolynomial 3 (cubicCoefficient R))
      (fullInvariantPolynomial 6 (sexticCoefficient R)) =
      surfaceIdeal (ParameterRing R) (universalCubicTail R) (universalSexticTail R) :=
  fullIdeal_normalized _ _ (leading_coefficients_units R).1
    (leading_coefficients_units R).2

/-- The equality of the actual surface ideals is compatible with every
coefficient-ring map, including maps to a pointed generic trace field. -/
theorem mapped_universalIdeal_normalized {S : Type*} [CommRing S]
    (f : ParameterRing R →+* S) :
    equationsIdeal (fullInvariantPolynomial 3 (fun i => f (cubicCoefficient R i)))
      (fullInvariantPolynomial 6 (fun i => f (sexticCoefficient R i))) =
      surfaceIdeal S (fun i => f (universalCubicTail R i))
        (fun i => f (universalSexticTail R i)) := by
  have h := congrArg (fun I : Ideal (Poly (ParameterRing R)) =>
    I.map (MvPolynomial.map f)) (universalIdeal_normalized R)
  simpa only [equationsIdeal, surfaceIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton, map_fullInvariantPolynomial, map_cubic, map_sextic,
    Function.comp_def] using h

theorem seed_normalized_ideal (r ι : R) :
    equationsIdeal (smoothH ι) (smoothF r ι) =
      surfaceIdeal R
        (fun i => seedSpecialization R r ι (universalCubicTail R i))
        (fun i => seedSpecialization R r ι (universalSexticTail R i)) := by
  have h := mapped_universalIdeal_normalized R (seedSpecialization R r ι).toRingHom
  simpa only [seedSpecialization, specialization_cubicCoefficient,
    specialization_sexticCoefficient, seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h
end CycleQ2UniversalSurfaceNormalization
end
end
end

/- Component: DebugUniversalSurfaceLocalization.lean -/
section
/-! Original normalized surface localizations, their actual monomial
coordinates and canonical restrictions. This extraction preserves the
original public definitions and theorem bodies. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceLocalizedBasis

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization

variable (R : Type*) [CommRing R]

abbrev SurfaceLocal (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :=
  Localization (Algebra.algebraMapSubmonoid (SurfaceRing R hcoeff Fcoeff)
    (Submonoid.powers (baseProduct R s)))

instance surfaceLocalBaseAlgebra (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Algebra (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s) :=
  localizationAlgebra (Rₘ := coordinateLocalization R s) (Sₘ := SurfaceLocal R hcoeff Fcoeff s)
    (Submonoid.powers (baseProduct R s)) (SurfaceRing R hcoeff Fcoeff)

instance surfaceLocalBaseTower (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    IsScalarTower (Base R) (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s) :=
  isScalarTower_localizationAlgebra (Rₘ := coordinateLocalization R s)
    (Sₘ := SurfaceLocal R hcoeff Fcoeff s) (Submonoid.powers (baseProduct R s)) (SurfaceRing R hcoeff Fcoeff)

def localizedBasis [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Module.Basis ShiftIndex (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s) :=
  (surfaceBasis R hcoeff Fcoeff).localizationLocalization (coordinateLocalization R s)
    (Submonoid.powers (baseProduct R s)) (SurfaceLocal R hcoeff Fcoeff s)

@[simp] theorem localizedBasis_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (ab : ShiftIndex) :
    localizedBasis R hcoeff Fcoeff s ab = algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
      (surfaceBasis R hcoeff Fcoeff ab) := by
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

@[simp] theorem localizedBasis_repr_algebraMap [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceRing R hcoeff Fcoeff) (ab : ShiftIndex) :
    (localizedBasis R hcoeff Fcoeff s).repr (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p) ab =
      algebraMap (Base R) (coordinateLocalization R s) ((surfaceBasis R hcoeff Fcoeff).repr p ab) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

def localizedCoordinates [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →+ (ShiftIndex → Laurent (R := R)) where
  toFun p ab := localizationToLaurent R s ((localizedBasis R hcoeff Fcoeff s).repr p ab)
  map_zero' := by ext ab; simp
  map_add' p q := by ext ab; simp

theorem localizedCoordinates_injective [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    Function.Injective (localizedCoordinates R hcoeff Fcoeff s) := by
  intro p q hpq
  apply (localizedBasis R hcoeff Fcoeff s).repr.injective
  ext ab
  exact localizationToLaurent_injective R s (congrFun hpq ab)

theorem localizedCoordinates_hasPoles [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    HasPoles s (localizedCoordinates R hcoeff Fcoeff s p ab) :=
  localizationToLaurent_hasPoles R s _

theorem mem_range_localizedCoordinates [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : ShiftIndex → Laurent (R := R)) :
    p ∈ Set.range (localizedCoordinates R hcoeff Fcoeff s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p, rfl⟩ ab
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s p ab
  · intro hp
    choose a ha using fun ab ↦ (mem_range_localizationToLaurent R s (p ab)).mpr (hp ab)
    refine ⟨(localizedBasis R hcoeff Fcoeff s).repr.symm (Finsupp.equivFunOnFinite.symm a), ?_⟩
    funext ab
    change localizationToLaurent R s
      ((localizedBasis R hcoeff Fcoeff s).repr ((localizedBasis R hcoeff Fcoeff s).repr.symm
        (Finsupp.equivFunOnFinite.symm a)) ab) = p ab
    simpa using ha ab

@[simp] theorem localizedCoordinates_algebraMap [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceRing R hcoeff Fcoeff) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff s (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p) ab =
      baseToLaurent R ((surfaceBasis R hcoeff Fcoeff).repr p ab) := by
  simp [localizedCoordinates]

@[simp] theorem localizedCoordinates_smul [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (a : coordinateLocalization R s) (p : SurfaceLocal R hcoeff Fcoeff s)
    (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff s (a • p) ab =
      localizationToLaurent R s a * localizedCoordinates R hcoeff Fcoeff s p ab := by
  simp [localizedCoordinates, Finsupp.smul_apply, smul_eq_mul]

end CycleQ2UniversalSurfaceLocalizedBasis

namespace CycleQ2UniversalSurfaceRestrictions

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis

variable (R : Type*) [CommRing R]

instance surfaceLocalAway (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    IsLocalization.Away (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
      (SurfaceLocal R hcoeff Fcoeff s) := by
  have hh : Algebra.algebraMapSubmonoid (SurfaceRing R hcoeff Fcoeff)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem surfaceProduct_isUnit (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    IsUnit (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := SurfaceLocal R hcoeff Fcoeff t)
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff)) (baseProduct_dvd R hst)

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SurfaceLocal R hcoeff Fcoeff s →+* SurfaceLocal R hcoeff Fcoeff t :=
  IsLocalization.Away.lift
    (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal R hcoeff Fcoeff t)
    (g := algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t))
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
    (surfaceProduct_isUnit R hcoeff Fcoeff hst)

@[simp] theorem restriction_algebraMap (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (p : SurfaceRing R hcoeff Fcoeff) :
    restriction R hcoeff Fcoeff hst (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff t) p :=
  IsLocalization.Away.lift_eq (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal R hcoeff Fcoeff t) _ (surfaceProduct_isUnit R hcoeff Fcoeff hst) p

theorem coordinates_mul_base [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : SurfaceLocal R hcoeff Fcoeff s) (c : Base R) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff s
      (p * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
        (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) c)) ab =
      baseToLaurent R c * localizedCoordinates R hcoeff Fcoeff s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst z) ab =
      localizedCoordinates R hcoeff Fcoeff s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) z
  have hp' : z * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s ^ n)) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R hcoeff Fcoeff hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R hcoeff Fcoeff t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

end CycleQ2UniversalSurfaceRestrictions

namespace CycleQ2UniversalSurfaceLinearCoordinates

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2UniversalSurface
  CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions

variable (R : Type*) [CommRing R]

theorem base_C_surface (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (c : R) :
    algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (C c) = algebraMap R (SurfaceRing R hcoeff Fcoeff) c := by
  change Ideal.Quotient.mk _ (remainingInclusion R (C c)) = Ideal.Quotient.mk _ (C c)
  simp [remainingInclusion]

theorem localized_scalar_eq (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) (c : R)
    (p : SurfaceLocal R hcoeff Fcoeff s) :
    algebraMap (Base R) (coordinateLocalization R s) (C c) • p = c • p := by
  simp only [Algebra.smul_def]
  rw [← IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SurfaceLocal R hcoeff Fcoeff s),
    IsScalarTower.algebraMap_apply (Base R) (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s), base_C_surface,
    ← IsScalarTower.algebraMap_apply R (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)]

theorem localizedCoordinates_R_smul [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (c : R) (p : SurfaceLocal R hcoeff Fcoeff s) :
    localizedCoordinates R hcoeff Fcoeff s (c • p) = c • localizedCoordinates R hcoeff Fcoeff s p := by
  funext ab
  rw [← localized_scalar_eq R hcoeff Fcoeff s c p, localizedCoordinates_smul,
    localizationToLaurent_algebraMap]
  change baseToLaurent R (algebraMap R (Base R) c) * _ = c • _
  rw [AlgHom.commutes, Algebra.smul_def]

def linearCoordinates [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →ₗ[R] (ShiftIndex → Laurent (R := R)) where
  __ := localizedCoordinates R hcoeff Fcoeff s
  map_smul' c p := localizedCoordinates_R_smul R hcoeff Fcoeff s c p

@[simp] theorem linearCoordinates_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3))
    (p : SurfaceLocal R hcoeff Fcoeff s) :
    linearCoordinates R hcoeff Fcoeff s p = localizedCoordinates R hcoeff Fcoeff s p := rfl

def restrictionLinear [Nontrivial R] (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SurfaceLocal R hcoeff Fcoeff s →ₗ[R] SurfaceLocal R hcoeff Fcoeff t where
  __ := (restriction R hcoeff Fcoeff hst).toAddMonoidHom
  map_smul' c p := by
    apply localizedCoordinates_injective R hcoeff Fcoeff t
    funext ab
    change localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst (c • p)) ab =
      localizedCoordinates R hcoeff Fcoeff t (c • restriction R hcoeff Fcoeff hst p) ab
    simp only [localizedCoordinates_R_smul, Pi.smul_apply, coordinates_restriction]

end CycleQ2UniversalSurfaceLinearCoordinates
end
end

/- Component: DebugUniversalSurfaceCoefficientMap.lean -/
section
/-! Original actual coefficient-specialization maps and their exact
localized-coordinate/restriction compatibility. The two polynomial
mapping lemmas are already retained by the normalization extraction. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurfaceCoefficientMap

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions

variable {R S : Type*} [CommRing R] [CommRing S]

theorem map_mem_surfaceIdeal (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {p : Poly R} (hp : p ∈ surfaceIdeal R hcoeff Fcoeff) :
    MvPolynomial.map f p ∈ surfaceIdeal S (fun i => f (hcoeff i))
      (fun i => f (Fcoeff i)) := by
  obtain ⟨a,b,hp⟩ := Ideal.mem_span_pair.mp hp
  apply Ideal.mem_span_pair.mpr
  refine ⟨MvPolynomial.map f a, MvPolynomial.map f b, ?_⟩
  rw [← hp]
  simp only [map_add, map_mul, map_cubic, map_sextic]

def surfaceMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    SurfaceRing R hcoeff Fcoeff →+*
      SurfaceRing S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (by
    intro p hp
    exact map_mem_surfaceIdeal f hcoeff Fcoeff hp)

@[simp] theorem surfaceMap_mk (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Poly R) :
    surfaceMap f hcoeff Fcoeff (Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff) p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

@[simp] theorem surfaceMap_base (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : Base R) :
    surfaceMap f hcoeff Fcoeff (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) p) =
      algebraMap (Base S) (SurfaceRing S (fun i => f (hcoeff i))
        (fun i => f (Fcoeff i))) (MvPolynomial.map f p) := by
  change Ideal.Quotient.mk _ (MvPolynomial.map f (remainingInclusion R p)) =
    Ideal.Quotient.mk _ (remainingInclusion S (MvPolynomial.map f p))
  rw [remainingInclusion, remainingInclusion, MvPolynomial.map_rename]

@[simp] theorem surfaceMap_basis [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (ab : ShiftIndex) :
    surfaceMap f hcoeff Fcoeff (surfaceBasis R hcoeff Fcoeff ab) =
      surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) ab := by
  simp only [surfaceBasis_apply, surfaceMap_mk, map_mul, map_pow,
    MvPolynomial.map_X]

theorem coordinates_surfaceMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (z : SurfaceRing R hcoeff Fcoeff) (ab : ShiftIndex) :
    (surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))).repr
        (surfaceMap f hcoeff Fcoeff z) ab =
      MvPolynomial.map f ((surfaceBasis R hcoeff Fcoeff).repr z ab) := by
  classical
  have hz := (surfaceBasis R hcoeff Fcoeff).sum_repr z
  have hm := congrArg (surfaceMap f hcoeff Fcoeff) hz
  simp only [map_sum, Algebra.smul_def, map_mul, surfaceMap_base,
    surfaceMap_basis] at hm
  rw [← hm]
  change (surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i))).repr
      (∑ i, MvPolynomial.map f ((surfaceBasis R hcoeff Fcoeff).repr z i) •
        surfaceBasis S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) i) ab = _
  simp [Finsupp.single_apply]

def laurentMap (f : R →+* S) : Laurent (R := R) →+* Laurent (R := S) :=
  AddMonoidAlgebra.mapRingHom LaurentExponent f

@[simp] theorem laurentMap_coeff (f : R →+* S) (z : Laurent (R := R))
    (e : LaurentExponent) : (laurentMap f z).coeff e = f (z.coeff e) := by
  exact AddMonoidAlgebra.coeff_mapRingHom f z e

@[simp] theorem laurentMap_T (f : R →+* S) (e : LaurentExponent) :
    laurentMap f (T R e) = T S e := by
  simp [laurentMap, T]

@[simp] theorem map_baseProduct (f : R →+* S) (s : Finset (Fin 3)) :
    MvPolynomial.map f (baseProduct R s) = baseProduct S s := by
  simp [baseProduct]

@[simp] theorem laurentMap_baseToLaurent (f : R →+* S) (p : Base R) :
    laurentMap f (baseToLaurent R p) = baseToLaurent S (MvPolynomial.map f p) := by
  have he : (laurentMap f).comp (baseToLaurent R).toRingHom =
      (baseToLaurent S).toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change laurentMap f (baseToLaurent R (monomial 0 c)) =
        baseToLaurent S (monomial 0 (f c))
      rw [baseToLaurent_monomial, baseToLaurent_monomial]
      simp [laurentMap]
    · intro i
      simp
  exact congrArg (fun g : Base R →+* Laurent (R := S) => g p) he

def localMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →+*
      SurfaceLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s :=
  IsLocalization.Away.lift
    (S := SurfaceLocal R hcoeff Fcoeff s)
    (P := SurfaceLocal S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s)
    (g := (algebraMap _ _).comp (surfaceMap f hcoeff Fcoeff))
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s))
    (by
      simp only [RingHom.comp_apply, surfaceMap_base, map_baseProduct]
      exact IsLocalization.Away.algebraMap_isUnit _)

@[simp] theorem localMap_algebraMap (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (z : SurfaceRing R hcoeff Fcoeff) :
    localMap f hcoeff Fcoeff s
        (algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) z) =
      algebraMap _ _ (surfaceMap f hcoeff Fcoeff z) := by
  exact IsLocalization.Away.lift_eq _ _ z

theorem coordinates_localMap [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (z : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    localizedCoordinates S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
        (localMap f hcoeff Fcoeff s z) ab =
      laurentMap f (localizedCoordinates R hcoeff Fcoeff s z ab) := by
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s)) z
  have hp' : z * algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s)
      (algebraMap (Base R) (SurfaceRing R hcoeff Fcoeff) (baseProduct R s ^ n)) =
      algebraMap (SurfaceRing R hcoeff Fcoeff) (SurfaceLocal R hcoeff Fcoeff s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z => localizedCoordinates R hcoeff Fcoeff s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have hs' := congrArg (laurentMap f) hs
  simp only [map_mul, laurentMap_baseToLaurent, map_pow, map_baseProduct] at hs'
  have ht := congrArg (localMap f hcoeff Fcoeff s) hp'
  simp only [map_mul, localMap_algebraMap, surfaceMap_base] at ht
  simp only [map_pow, map_baseProduct] at ht
  have ht0 : localMap f hcoeff Fcoeff s z *
      algebraMap _ _ (algebraMap (Base S)
        (SurfaceRing S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)))
        (baseProduct S s ^ n)) =
      algebraMap _ _ (surfaceMap f hcoeff Fcoeff p) := by
    simpa only [map_pow] using ht
  have ht' := congrArg (fun z => localizedCoordinates S (fun i => f (hcoeff i))
    (fun i => f (Fcoeff i)) s z ab) ht0
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap,
    coordinates_surfaceMap] at ht'
  have hu : IsUnit (baseToLaurent S (baseProduct S s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit S _).pow n
  apply hu.mul_right_injective
  simpa only [map_pow] using ht'.trans hs'.symm

theorem localMap_restriction [Nontrivial R] [Nontrivial S] (f : R →+* S)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SurfaceLocal R hcoeff Fcoeff s) :
    localMap f hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst z) =
      restriction S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) hst
        (localMap f hcoeff Fcoeff s z) := by
  apply localizedCoordinates_injective S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) t
  funext ab
  simp only [coordinates_localMap, coordinates_restriction]

end CycleQ2UniversalSurfaceCoefficientMap
end
end

/- Component: DebugSeedNormalizedCoordinates.lean -/
section
/-! The original normalized universal surface at the literal seed is
identified with the actual Cartier surface by the identity on all five
polynomial coordinates. The same maps preserve the fixed nine monomial
coordinates on every actual coordinate localization. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSeedNormalizedCoordinates

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2UniversalSurfaceNormalization
  CycleQ2SeedQuotientFiniteFree CycleQ2SegreTangentLocal
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricLaurentTop

def cubicCoefficients (r : ℂ) : FullCubicTailIndex → ℂ :=
  fun i => seedSpecialization ℂ r Complex.I (universalCubicTail ℂ i)

def sexticCoefficients (r : ℂ) : FullSexticTailIndex → ℂ :=
  fun i => seedSpecialization ℂ r Complex.I (universalSexticTail ℂ i)

abbrev NormalizedSurface (r : ℂ) :=
  CycleQ2UniversalSurface.SurfaceRing ℂ (cubicCoefficients r) (sexticCoefficients r)

abbrev NormalizedLocal (r : ℂ) (s : Finset (Fin 3)) :=
  CycleQ2UniversalSurfaceLocalizedBasis.SurfaceLocal ℂ
    (cubicCoefficients r) (sexticCoefficients r) s

/-- The canonical quotient equivalence is induced by the identity on
the original polynomial ring, using the actual leading-coefficient
specialization retained in the original universal construction. -/
def seedNormalizedRingEquiv (r : ℂ) :
    SeedRing r Complex.I ≃ₐ[Base ℂ] NormalizedSurface r :=
  Ideal.quotientEquivAlgOfEq (Base ℂ) (seed_normalized_ideal ℂ r Complex.I)

@[simp] theorem seedNormalizedRingEquiv_mk (r : ℂ) (p : Poly ℂ) :
    seedNormalizedRingEquiv r
      (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p) =
      Ideal.Quotient.mk
        (CycleQ2UniversalSurface.surfaceIdeal ℂ (cubicCoefficients r)
          (sexticCoefficients r)) p := rfl

def surfaceNormalizedRingEquiv (r : ℂ) :
    CycleQ2GeometricSeedNormalIdeals.SurfaceRing r 1 ≃ₐ[Base ℂ] NormalizedSurface r :=
  (seedRingEquivOverBase r).trans (seedNormalizedRingEquiv r)

@[simp] theorem surfaceNormalizedRingEquiv_mk (r : ℂ)
    (p : CycleQ2SeedTrace.WeightedPoly) :
    surfaceNormalizedRingEquiv r (quotientMap r 1 p) =
      Ideal.Quotient.mk
        (CycleQ2UniversalSurface.surfaceIdeal ℂ (cubicCoefficients r)
          (sexticCoefficients r)) p := rfl

@[simp] theorem seedNormalizedRingEquiv_basis (r : ℂ) (ab : ShiftIndex) :
    seedNormalizedRingEquiv r (seedBasis ℂ r Complex.I ab) =
      CycleQ2UniversalSurface.surfaceBasis ℂ (cubicCoefficients r)
        (sexticCoefficients r) ab := by
  rw [seedBasis_apply, CycleQ2UniversalSurface.surfaceBasis_apply]
  rfl

/-- This is a comparison of the actual fixed quotient bases, not an
independently chosen isomorphism between two nine-dimensional spaces. -/
theorem seedNormalizedRingEquiv_coordinates (r : ℂ)
    (p : SeedRing r Complex.I) (ab : ShiftIndex) :
    (CycleQ2UniversalSurface.surfaceBasis ℂ (cubicCoefficients r)
      (sexticCoefficients r)).repr (seedNormalizedRingEquiv r p) ab =
      (seedBasis ℂ r Complex.I).repr p ab := by
  classical
  have hp := (seedBasis ℂ r Complex.I).sum_repr p
  have hm := congrArg (seedNormalizedRingEquiv r).toLinearEquiv hp
  simp only [map_sum, map_smul, AlgEquiv.toLinearEquiv_apply,
    seedNormalizedRingEquiv_basis] at hm
  rw [← hm]
  simp [Finsupp.single_apply]

/-- The localization map is induced by the quotient-ring identity and
the same actual coordinate denominator on both sides. -/
def seedNormalizedLocalEquiv (r : ℂ) (s : Finset (Fin 3)) :
    CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s ≃+* NormalizedLocal r s :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s)))
    (T := Submonoid.powers
      (algebraMap (Base ℂ) (NormalizedSurface r) (baseProduct ℂ s)))
    (CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s)
    (NormalizedLocal r s) (seedNormalizedRingEquiv r).toRingEquiv
    (by rw [Submonoid.map_powers];
        exact congrArg Submonoid.powers ((seedNormalizedRingEquiv r).commutes _))

@[simp] theorem seedNormalizedLocalEquiv_base (r : ℂ) (s : Finset (Fin 3))
    (p : SeedRing r Complex.I) :
    seedNormalizedLocalEquiv r s
      (algebraMap (SeedRing r Complex.I)
        (CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s) p) =
      algebraMap (NormalizedSurface r) (NormalizedLocal r s)
        (seedNormalizedRingEquiv r p) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ p

/-- Every Laurent coordinate agrees exactly with the coordinate of the
same localized polynomial fraction in the original normalized quotient. -/
theorem seedNormalizedLocalEquiv_coordinates (r : ℂ) (s : Finset (Fin 3))
    (z : CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s) (ab : ShiftIndex) :
    CycleQ2UniversalSurfaceLocalizedBasis.localizedCoordinates ℂ
      (cubicCoefficients r) (sexticCoefficients r) s
      (seedNormalizedLocalEquiv r s z) ab =
      CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r Complex.I s z ab := by
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s)) z
  have hp' : z * algebraMap (SeedRing r Complex.I)
      (CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s ^ n)) =
      algebraMap (SeedRing r Complex.I)
        (CycleQ2SeedCechLocalizedBasis.SeedLocal ℂ r Complex.I s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z =>
    CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r Complex.I s z ab) hp'
  simp only [seed_coordinates_mul_base,
    CycleQ2SeedCechLocalizedBasis.localizedCoordinates_algebraMap] at hs
  have ht := congrArg (seedNormalizedLocalEquiv r s) hp'
  simp only [map_mul, seedNormalizedLocalEquiv_base, AlgEquiv.commutes] at ht
  have ht' := congrArg (fun z =>
    CycleQ2UniversalSurfaceLocalizedBasis.localizedCoordinates ℂ
      (cubicCoefficients r) (sexticCoefficients r) s z ab) ht
  simp only [CycleQ2UniversalSurfaceRestrictions.coordinates_mul_base,
    CycleQ2UniversalSurfaceLocalizedBasis.localizedCoordinates_algebraMap,
    seedNormalizedRingEquiv_coordinates] at ht'
  have hu : IsUnit (baseToLaurent ℂ (baseProduct ℂ s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit ℂ _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

def normalizedCoordinateEquiv (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s ≃+* NormalizedLocal r s :=
  (seedCoordinateEquiv r s).trans (seedNormalizedLocalEquiv r s)

@[simp] theorem normalizedCoordinateEquiv_polynomial (r : ℂ)
    (s : Finset (Fin 3)) (p : CycleQ2SeedTrace.WeightedPoly) :
    normalizedCoordinateEquiv r s
      (algebraMap (CycleQ2GeometricSeedNormalIdeals.SurfaceRing r 1)
        (CoordinateLocal r 1 s) (quotientMap r 1 p)) =
      algebraMap (NormalizedSurface r) (NormalizedLocal r s)
        (Ideal.Quotient.mk
          (CycleQ2UniversalSurface.surfaceIdeal ℂ (cubicCoefficients r)
            (sexticCoefficients r)) p) := by
  simp only [normalizedCoordinateEquiv, RingEquiv.trans_apply,
    seedCoordinateEquiv_polynomial, seedNormalizedLocalEquiv_base,
    seedNormalizedRingEquiv_mk]

theorem normalizedCoordinateEquiv_coordinates (r : ℂ) (s : Finset (Fin 3))
    (p : CoordinateLocal r 1 s) :
    CycleQ2UniversalSurfaceLocalizedBasis.localizedCoordinates ℂ
      (cubicCoefficients r) (sexticCoefficients r) s
      (normalizedCoordinateEquiv r s p) = coordinateLaurent r s p := by
  funext ab
  exact seedNormalizedLocalEquiv_coordinates r s (seedCoordinateEquiv r s p) ab

/-- The identity-on-polynomial quotient equivalence commutes with the
original actual restrictions on every pair of coordinate opens. -/
theorem normalizedCoordinateEquiv_restriction (r : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : CoordinateLocal r 1 s) :
    normalizedCoordinateEquiv r t (coordinateRestriction r 1 hst p) =
      CycleQ2UniversalSurfaceRestrictions.restriction ℂ
        (cubicCoefficients r) (sexticCoefficients r) hst
        (normalizedCoordinateEquiv r s p) := by
  apply CycleQ2UniversalSurfaceLocalizedBasis.localizedCoordinates_injective
    ℂ (cubicCoefficients r) (sexticCoefficients r) t
  funext ab
  rw [normalizedCoordinateEquiv_coordinates, coordinateLaurent_restriction,
    CycleQ2UniversalSurfaceRestrictions.coordinates_restriction,
    normalizedCoordinateEquiv_coordinates]

end CycleQ2GeometricSeedNormalizedCoordinates
end
end

/- Component: DebugSeedNormalizedCharacter.lean -/
section
/-! The original character-graded local modules and original actual
three-coordinate top Čech quotient, with a direct coefficient detector
on the very same localized section. No finite basis or replacement
cohomology vector is used to define the class. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2CharacterTopCech
open CycleQ2SeedCechThreeOpen
variable (R : Type*) [CommRing R] (χ : ZMod 3)
abbrev Family := ShiftIndex → Laurent (R := R)

def gradedFamilies : Submodule R (Family R) where
  carrier := {p | ∀ ab, HasGrade ab (0,χ) (p ab)}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab := hasGrade_add ab (0,χ) (hp ab) (hq ab)
  smul_mem' c p hp ab := by
    intro e he
    simp [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he]

end CycleQ2CharacterTopCech

namespace CycleQ2UniversalSurfaceCharacterCech
open CycleQ2IncidenceNormalForm CycleQ2UniversalSurface CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2UniversalSurfaceLocalizedBasis
  CycleQ2UniversalSurfaceRestrictions CycleQ2UniversalSurfaceLinearCoordinates CycleQ2CharacterTopCech

variable (R : Type*) [CommRing R] [Nontrivial R] (χ : ZMod 3)

/-- Degree-zero sections of the explicitly specified character inside the actual coordinate localization. -/
def gradedLocal (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) (s : Finset (Fin 3)) : Submodule R (SurfaceLocal R hcoeff Fcoeff s) :=
  (gradedFamilies R χ).comap (linearCoordinates R hcoeff Fcoeff s)

def gradedRestriction (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R χ hcoeff Fcoeff s →ₗ[R] gradedLocal R χ hcoeff Fcoeff t where
  toFun p := ⟨restrictionLinear R hcoeff Fcoeff hst p.val, by
    intro ab
    change HasGrade ab (0,χ) (localizedCoordinates R hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R hcoeff Fcoeff hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R hcoeff Fcoeff hst) c p.val

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) : Submodule R (gradedLocal R χ hcoeff Fcoeff Finset.univ) :=
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R χ hcoeff Fcoeff (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

abbrev ActualTopCechQuotient (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :=
  gradedLocal R χ hcoeff Fcoeff Finset.univ ⧸ actualBoundary R χ hcoeff Fcoeff

/-- Evaluation of one specified Laurent coordinate of an actual
character-graded triple-open section. -/
def actualCoefficient (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : ShiftIndex) (e : LaurentExponent) :
    gradedLocal R χ hcoeff Fcoeff Finset.univ →ₗ[R] R where
  toFun p := (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val ab).coeff e
  map_add' p q := by simp only [Submodule.coe_add, map_add, Pi.add_apply,
    AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c p := by simp only [Submodule.coe_smul, localizedCoordinates_R_smul,
    Pi.smul_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, RingHom.id_apply]

/-- A strictly negative coefficient vanishes on each of the three
actual pair-open restrictions, hence on their full boundary submodule. -/
theorem actualBoundary_le_coefficient_kernel (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) :
    actualBoundary R χ hcoeff Fcoeff ≤
      LinearMap.ker (actualCoefficient R χ hcoeff Fcoeff ab e) := by
  have hpair (s : Finset (Fin 3)) (hs : s ⊆ Finset.univ)
      (i : Fin 3) (hi : i ∉ s) :
      LinearMap.range (gradedRestriction R χ hcoeff Fcoeff hs) ≤
        LinearMap.ker (actualCoefficient R χ hcoeff Fcoeff ab e) := by
    rintro _ ⟨p,rfl⟩
    change (localizedCoordinates R hcoeff Fcoeff Finset.univ
      (restriction R hcoeff Fcoeff hs p.val) ab).coeff e = 0
    rw [coordinates_restriction]
    exact localizedCoordinates_hasPoles R hcoeff Fcoeff s p.val ab e i hi (he i)
  exact sup_le (sup_le (hpair {0,1} (by decide) 2 (by decide))
    (hpair {0,2} (by decide) 1 (by decide)))
    (hpair {1,2} (by decide) 0 (by decide))

theorem actualClass_ne_zero_of_negative_coefficient
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : gradedLocal R χ hcoeff Fcoeff Finset.univ)
    (ab : ShiftIndex) (e : LaurentExponent) (he : ∀ i, e i < 0)
    (hp : (localizedCoordinates R hcoeff Fcoeff Finset.univ p.val ab).coeff e ≠ 0) :
    (Submodule.Quotient.mk p : ActualTopCechQuotient R χ hcoeff Fcoeff) ≠ 0 := by
  intro hz
  have hm : p ∈ actualBoundary R χ hcoeff Fcoeff :=
    (Submodule.Quotient.mk_eq_zero _).mp hz
  exact hp (actualBoundary_le_coefficient_kernel R χ hcoeff Fcoeff ab e he hm)

end CycleQ2UniversalSurfaceCharacterCech

namespace CycleQ2GeometricSeedNormalizedCoordinates

open CycleQ2SeedCechThreeOpen CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop CycleQ2UniversalSurfaceCharacterCech
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceLinearCoordinates

/-- The same actual coordinate-localized section, now viewed in the
original normalized character-graded local module. -/
def normalizedGradedSection (r : ℂ) (χ : ZMod 3) (s : Finset (Fin 3))
    (p : CoordinateLocal r 1 s)
    (hp : ∀ ab, HasGrade ab (0,χ) (coordinateLaurent r s p ab)) :
    gradedLocal ℂ χ (cubicCoefficients r) (sexticCoefficients r) s :=
  ⟨normalizedCoordinateEquiv r s p, by
    change ∀ ab, HasGrade ab (0,χ)
      (localizedCoordinates ℂ (cubicCoefficients r) (sexticCoefficients r) s
        (normalizedCoordinateEquiv r s p) ab)
    rw [normalizedCoordinateEquiv_coordinates]
    exact hp⟩

@[simp] theorem normalizedGradedSection_val (r : ℂ) (χ : ZMod 3)
    (s : Finset (Fin 3)) (p : CoordinateLocal r 1 s)
    (hp : ∀ ab, HasGrade ab (0,χ) (coordinateLaurent r s p ab)) :
    (normalizedGradedSection r χ s p hp).val = normalizedCoordinateEquiv r s p := rfl

theorem normalizedGradedSection_restriction (r : ℂ) (χ : ZMod 3)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : CoordinateLocal r 1 s)
    (hp : ∀ ab, HasGrade ab (0,χ) (coordinateLaurent r s p ab)) :
    gradedRestriction ℂ χ (cubicCoefficients r) (sexticCoefficients r) hst
      (normalizedGradedSection r χ s p hp) =
      normalizedGradedSection r χ t (coordinateRestriction r 1 hst p)
        (by simpa only [coordinateLaurent_restriction] using hp) := by
  apply Subtype.ext
  exact (normalizedCoordinateEquiv_restriction r hst p).symm

/-- The original top Čech quotient applied to the actual section, with
its character certificate supplied by the actual coordinate projection. -/
def normalizedCharacterClass (r : ℂ) (χ : ZMod 3)
    (p : CoordinateLocal r 1 Finset.univ)
    (hp : ∀ ab, HasGrade ab (0,χ) (coordinateLaurent r Finset.univ p ab)) :
    ActualTopCechQuotient ℂ χ (cubicCoefficients r) (sexticCoefficients r) :=
  Submodule.Quotient.mk (normalizedGradedSection r χ Finset.univ p hp)

theorem normalizedCharacterClass_ne_zero (r : ℂ) (χ : ZMod 3)
    (p : CoordinateLocal r 1 Finset.univ)
    (hp : ∀ ab, HasGrade ab (0,χ) (coordinateLaurent r Finset.univ p ab))
    (ab : ShiftIndex) (e : LaurentExponent) (he : ∀ i, e i < 0)
    (hc : (coordinateLaurent r Finset.univ p ab).coeff e ≠ 0) :
    normalizedCharacterClass r χ p hp ≠ 0 := by
  apply actualClass_ne_zero_of_negative_coefficient ℂ χ
    (cubicCoefficients r) (sexticCoefficients r)
    (normalizedGradedSection r χ Finset.univ p hp) ab e he
  simpa only [normalizedGradedSection_val, normalizedCoordinateEquiv_coordinates] using hc

end CycleQ2GeometricSeedNormalizedCoordinates
end
end

/- Component: DebugUniversalSurfaceGradeProjection.lean -/
section
/-! Canonical weight-zero character projection on the actual universal
surface localizations.  It is defined by filtering the actual unique
Laurent coordinates, and commutes with both restriction and coefficient
specialization. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2UniversalSurfaceCanonicalProjection

open CycleQ2IncidenceNormalForm CycleQ2SeedCechThreeOpen
  CycleQ2UniversalSurfaceLocalizedBasis CycleQ2UniversalSurfaceRestrictions
  CycleQ2UniversalSurfaceLinearCoordinates CycleQ2UniversalSurfaceCharacterCech
  CycleQ2UniversalSurfaceCoefficientMap

variable (R : Type*) [CommRing R]

def gradePart (ab : ShiftIndex) (g : LaurentGrade) (p : Laurent (R := R)) :
    Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e => shiftedGrade ab e = g))

@[simp] theorem gradePart_coeff (ab : ShiftIndex) (g : LaurentGrade)
    (p : Laurent (R := R)) (e : LaurentExponent) :
    (gradePart R ab g p).coeff e = if shiftedGrade ab e = g then p.coeff e else 0 := rfl

theorem gradePart_hasGrade (ab : ShiftIndex) (g : LaurentGrade)
    (p : Laurent (R := R)) : HasGrade ab g (gradePart R ab g p) := by
  intro e he
  simp only [gradePart_coeff, if_neg he]

theorem gradePart_hasPoles (ab : ShiftIndex) (g : LaurentGrade)
    {s : Finset (Fin 3)} {p : Laurent (R := R)} (hp : HasPoles s p) :
    HasPoles s (gradePart R ab g p) := by
  intro e i hi he
  simp only [gradePart_coeff, hp e i hi he, ite_self]

variable [Nontrivial R]

private theorem project_exists (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceLocal R hcoeff Fcoeff s) :
    ∃ q : SurfaceLocal R hcoeff Fcoeff s,
      localizedCoordinates R hcoeff Fcoeff s q =
        fun ab => gradePart R ab (0,χ) (localizedCoordinates R hcoeff Fcoeff s p ab) := by
  apply (mem_range_localizedCoordinates R hcoeff Fcoeff s _).mpr
  intro ab
  exact gradePart_hasPoles R ab (0,χ)
    (localizedCoordinates_hasPoles R hcoeff Fcoeff s p ab)

/-- The projected element remains in the same actual localization. -/
def localProjection (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceLocal R hcoeff Fcoeff s) :
    SurfaceLocal R hcoeff Fcoeff s := (project_exists R χ hcoeff Fcoeff s p).choose

@[simp] theorem localProjection_coordinates (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceLocal R hcoeff Fcoeff s) (ab : ShiftIndex) :
    localizedCoordinates R hcoeff Fcoeff s (localProjection R χ hcoeff Fcoeff s p) ab =
      gradePart R ab (0,χ) (localizedCoordinates R hcoeff Fcoeff s p ab) :=
  congrFun (project_exists R χ hcoeff Fcoeff s p).choose_spec ab

/-- This is the canonical component of the same section in the original
character-graded local module, not a replacement cohomology vector. -/
def gradedProjection (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) :
    SurfaceLocal R hcoeff Fcoeff s →ₗ[R] gradedLocal R χ hcoeff Fcoeff s where
  toFun p := ⟨localProjection R χ hcoeff Fcoeff s p, by
    intro ab
    change HasGrade ab (0,χ) (localizedCoordinates R hcoeff Fcoeff s
      (localProjection R χ hcoeff Fcoeff s p) ab)
    rw [localProjection_coordinates]
    exact gradePart_hasGrade R ab (0,χ) _⟩
  map_add' p q := by
    apply Subtype.ext
    apply localizedCoordinates_injective R hcoeff Fcoeff s
    funext ab
    ext e
    simp only [localProjection_coordinates, map_add, Pi.add_apply,
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, gradePart_coeff]
    by_cases h : shiftedGrade ab e = (0,χ) <;> simp [h]
  map_smul' c p := by
    apply Subtype.ext
    apply localizedCoordinates_injective R hcoeff Fcoeff s
    funext ab
    ext e
    change (localizedCoordinates R hcoeff Fcoeff s
      (localProjection R χ hcoeff Fcoeff s (c • p)) ab).coeff e =
      (localizedCoordinates R hcoeff Fcoeff s
        (c • localProjection R χ hcoeff Fcoeff s p) ab).coeff e
    rw [localizedCoordinates_R_smul]
    simp only [localProjection_coordinates, localizedCoordinates_R_smul,
      Pi.smul_apply, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply,
      gradePart_coeff, RingHom.id_apply]
    by_cases h : shiftedGrade ab e = (0,χ) <;> simp [h]

theorem gradedProjection_eq_self (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : gradedLocal R χ hcoeff Fcoeff s) :
    gradedProjection R χ hcoeff Fcoeff s p.val = p := by
  apply Subtype.ext
  apply localizedCoordinates_injective R hcoeff Fcoeff s
  funext ab
  ext e
  change (localizedCoordinates R hcoeff Fcoeff s
    (localProjection R χ hcoeff Fcoeff s p.val) ab).coeff e = _
  rw [localProjection_coordinates, gradePart_coeff]
  split
  · rfl
  · exact (p.property ab e ‹_›).symm

theorem gradedProjection_restriction (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : SurfaceLocal R hcoeff Fcoeff s) :
    gradedRestriction R χ hcoeff Fcoeff hst (gradedProjection R χ hcoeff Fcoeff s p) =
      gradedProjection R χ hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p) := by
  apply Subtype.ext
  apply localizedCoordinates_injective R hcoeff Fcoeff t
  funext ab
  change localizedCoordinates R hcoeff Fcoeff t
    (restriction R hcoeff Fcoeff hst (localProjection R χ hcoeff Fcoeff s p)) ab =
      localizedCoordinates R hcoeff Fcoeff t
        (localProjection R χ hcoeff Fcoeff t (restriction R hcoeff Fcoeff hst p)) ab
  rw [coordinates_restriction, localProjection_coordinates,
    localProjection_coordinates, coordinates_restriction]

/-- Projection commutes with the actual coefficient-induced map of the
actual quotient localizations, including specialization to the seed. -/
theorem gradedProjection_specialization {S : Type*} [CommRing S] [Nontrivial S]
    (f : R →+* S) (χ : ZMod 3)
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (s : Finset (Fin 3)) (p : SurfaceLocal R hcoeff Fcoeff s) :
    localMap f hcoeff Fcoeff s (gradedProjection R χ hcoeff Fcoeff s p).val =
      (gradedProjection S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
        (localMap f hcoeff Fcoeff s p)).val := by
  apply localizedCoordinates_injective S (fun i => f (hcoeff i))
    (fun i => f (Fcoeff i)) s
  funext ab
  ext e
  change (localizedCoordinates S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
    (localMap f hcoeff Fcoeff s (localProjection R χ hcoeff Fcoeff s p)) ab).coeff e =
      (localizedCoordinates S (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
        (localProjection S χ (fun i => f (hcoeff i)) (fun i => f (Fcoeff i)) s
          (localMap f hcoeff Fcoeff s p)) ab).coeff e
  rw [coordinates_localMap, laurentMap_coeff, localProjection_coordinates,
    localProjection_coordinates, gradePart_coeff, gradePart_coeff, coordinates_localMap,
    laurentMap_coeff]
  split <;> simp

end CycleQ2UniversalSurfaceCanonicalProjection
end
end

/- Component: DebugLiteralNormalizedCharacter.lean -/
section
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2GeometricSeedNormalizedCoordinates

open CycleQ2GeometricCoordinateCharacter CycleQ2GeometricCartierCech
  CycleQ2GeometricFourOpenCech CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricLaurentTop CycleQ2SeedCechThreeOpen CycleQ2NormalConnecting

/-- The literal original Cartier class, after the actual homogeneous
coordinate descent and actual character projection, is nonzero in the
original normalized universal surface's character-one top Čech quotient.
The descent witnesses and original section remain part of the conclusion. -/
theorem literal_normalized_character_one_nonzero :
    ∃ (d : TwoCocycles (coordinateScalarSystem 57)) (q : HomogeneousCoordinateTop 57)
      (hp : ∀ ab, HasGrade ab (0,1)
        (coordinateLaurent 57 Finset.univ (coordinateProject 57 Finset.univ 1 q.val) ab)),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      q.val = coordinateTopRepresentative 57 d ∧
      normalizedCharacterClass 57 1 (coordinateProject 57 Finset.univ 1 q.val) hp ≠ 0 := by
  obtain ⟨d,q,hcd,hq,hp,ab,e,he,hc⟩ := literal_homogeneous_character_one_nonzero
  exact ⟨d,q,hp,hcd,hq,
    normalizedCharacterClass_ne_zero 57 1
      (coordinateProject 57 Finset.univ 1 q.val) hp ab e he hc⟩

end CycleQ2GeometricSeedNormalizedCoordinates
end
end

#print axioms CycleQ2IncidenceNormalForm.fullInvariantPolynomial_cubic
#print axioms CycleQ2IncidenceNormalForm.fullInvariantPolynomial_sextic
#print axioms CycleQ2IncidenceEquations.seedCubicCoefficients_unit
#print axioms CycleQ2IncidenceEquations.seedSexticCoefficients_unit
#print axioms CycleQ2UniversalSurface.surfaceBasis_apply
#print axioms CycleQ2UniversalSurface.surfaceQuotient_rank_nine
#print axioms CycleQ2IncidenceUniversalChart.leading_coefficients_units
#print axioms CycleQ2IncidenceUniversalChart.specialization_cubicCoefficient
#print axioms CycleQ2IncidenceUniversalChart.specialization_sexticCoefficient
#print axioms CycleQ2UniversalSurfaceNormalization.fullSurfaceEquiv_mk
#print axioms CycleQ2UniversalSurfaceNormalization.seed_normalized_ideal
#print axioms CycleQ2UniversalSurfaceLocalizedBasis.localizedBasis_apply
#print axioms CycleQ2UniversalSurfaceLocalizedBasis.mem_range_localizedCoordinates
#print axioms CycleQ2UniversalSurfaceRestrictions.coordinates_restriction
#print axioms CycleQ2UniversalSurfaceLinearCoordinates.linearCoordinates
#print axioms CycleQ2UniversalSurfaceLinearCoordinates.restrictionLinear
#print axioms CycleQ2UniversalSurfaceCoefficientMap.surfaceMap_basis
#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_surfaceMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.coordinates_localMap
#print axioms CycleQ2UniversalSurfaceCoefficientMap.localMap_restriction
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.surfaceNormalizedRingEquiv_mk
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.seedNormalizedRingEquiv_coordinates
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedCoordinateEquiv_polynomial
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedCoordinateEquiv_coordinates
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedCoordinateEquiv_restriction
#print axioms CycleQ2UniversalSurfaceCharacterCech.actualBoundary_le_coefficient_kernel
#print axioms CycleQ2UniversalSurfaceCharacterCech.actualClass_ne_zero_of_negative_coefficient
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedGradedSection_restriction
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.normalizedCharacterClass_ne_zero
#print axioms CycleQ2UniversalSurfaceCanonicalProjection.gradedProjection
#print axioms CycleQ2UniversalSurfaceCanonicalProjection.gradedProjection_eq_self
#print axioms CycleQ2UniversalSurfaceCanonicalProjection.gradedProjection_restriction
#print axioms CycleQ2UniversalSurfaceCanonicalProjection.gradedProjection_specialization
#print axioms CycleQ2GeometricSeedNormalizedCoordinates.literal_normalized_character_one_nonzero
