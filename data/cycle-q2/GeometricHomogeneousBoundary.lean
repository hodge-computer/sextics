import Proposal.GeometricKoszulKernel
import Proposal.GeometricGradedWitness
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Homogeneous polynomial relations give genuine chart boundaries

Let `R = K[x]/(f₁,h)`, with the two quartics `g₁,g₂` giving the principal
charts. A degree-nine relation modulo `(f₁,h,g₁,g₂)` has homogeneous quintic
coefficients on the two quartic generators. This module proves that its
literal fraction `p/(g₁*g₂)` is the sum of the restrictions of the two
single-chart fractions with those quintic numerators.

All quotient rings, localization rings, and restriction maps here are actual
Mathlib constructions. The homogeneity witnesses are retained, so the two
fractions have the degrees needed by the projective degree-one chart
modules. No regular-sequence hypothesis is needed for this forward boundary
identity. No projective cohomology or canonical-bundle identification is
assumed or asserted.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GeometricHomogeneousBoundary

open CycleQ2GeometricKoszulKernel

section Fractions

variable {R : Type*} [CommRing R]

def chartDenominator (f : R) : Submonoid.powers f := ⟨f, 1, pow_one _⟩

/-- A genuine single-chart section with a simple pole. -/
def chartFraction (f a : R) : Localization.Away f :=
  IsLocalization.mk' (Localization.Away f) a (chartDenominator f)

theorem chartFraction_eq_smul_invSelf (f a : R) :
    chartFraction f a = a • (IsLocalization.Away.invSelf f : Localization.Away f) := by
  change IsLocalization.mk' (Localization.Away f) a (chartDenominator f) =
    a • IsLocalization.mk' (Localization.Away f) 1 (chartDenominator f)
  exact (IsLocalization.smul_mk'_one a (chartDenominator f)).symm

/-- The basic Koszul numerator relation is an equality of actual overlap
sections under the two localization restriction maps. -/
theorem representative_relation (f g c d : R) :
    representative f g (c * f + d * g) =
      firstRestriction f g (chartFraction f d) +
        secondRestriction f g (chartFraction g c) := by
  change representative f g (c • f + d • g) = _
  rw [map_add, map_smul, map_smul, representative_first, representative_second,
    chartFraction_eq_smul_invSelf, chartFraction_eq_smul_invSelf,
    map_smul, map_smul]
  exact add_comm _ _

end Fractions

section Polynomials

variable {K σ : Type*} [CommRing K]

/-- The actual homogeneous curve coordinate ring before localization. -/
abbrev CurveRing (f₁ h : MvPolynomial σ K) :=
  MvPolynomial σ K ⧸ Ideal.span ({f₁, h} : Set (MvPolynomial σ K))

def curveMap (f₁ h : MvPolynomial σ K) : MvPolynomial σ K →+* CurveRing f₁ h :=
  Ideal.Quotient.mk (Ideal.span ({f₁, h} : Set (MvPolynomial σ K)))

@[simp] theorem curveMap_first (f₁ h : MvPolynomial σ K) : curveMap f₁ h f₁ = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

@[simp] theorem curveMap_second (f₁ h : MvPolynomial σ K) : curveMap f₁ h h = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

/-- Membership in the two quartic images is exactly membership in all four
equations before taking the actual curve quotient. -/
theorem curveMap_mem_span_pair_iff (f₁ h g₁ g₂ p : MvPolynomial σ K) :
    curveMap f₁ h p ∈ Ideal.span
        ({curveMap f₁ h g₁, curveMap f₁ h g₂} : Set (CurveRing f₁ h)) ↔
      p ∈ Ideal.span ({f₁, h, g₁, g₂} : Set (MvPolynomial σ K)) := by
  have hmap := Ideal.map_span (curveMap f₁ h)
    ({g₁, g₂} : Set (MvPolynomial σ K))
  simp only [Set.image_insert_eq, Set.image_singleton] at hmap
  rw [← hmap]
  change Ideal.Quotient.mk (Ideal.span ({f₁, h} : Set (MvPolynomial σ K))) p ∈
    (Ideal.span ({g₁, g₂} : Set (MvPolynomial σ K))).map
      (Ideal.Quotient.mk (Ideal.span ({f₁, h} : Set (MvPolynomial σ K)))) ↔ _
  rw [Ideal.mem_quotient_iff_mem_sup, sup_comm, ← Ideal.span_union]
  simp only [Set.insert_union, Set.singleton_union]

/-- The all-poles Koszul criterion on the actual curve quotient, expressed
in the four original polynomial equations. Regularity is used only for
the converse; no equality of kernels is assumed. -/
theorem quotient_boundary_eq_zero_iff (f₁ h g₁ g₂ p : MvPolynomial σ K)
    (hg₁ : IsSMulRegular (CurveRing f₁ h) (curveMap f₁ h g₁))
    (hg₂ : IsSMulRegular
      (CurveRing f₁ h ⧸ Ideal.span {curveMap f₁ h g₁}) (curveMap f₁ h g₂)) :
    boundary (curveMap f₁ h g₁) (curveMap f₁ h g₂) (curveMap f₁ h p) = 0 ↔
      p ∈ Ideal.span ({f₁, h, g₁, g₂} : Set (MvPolynomial σ K)) :=
  (boundary_eq_zero_iff _ _ hg₁ hg₂ _).trans
    (curveMap_mem_span_pair_iff f₁ h g₁ g₂ p)

/-- Homogeneous degree-nine ideal membership yields explicit quintic
single-chart numerators and an equality in the genuine overlap localization. -/
theorem degreeNine_quotient_boundary (f₁ h g₁ g₂ p : MvPolynomial σ K)
    (hf₁ : f₁.IsHomogeneous 2) (hh : h.IsHomogeneous 3)
    (hg₁ : g₁.IsHomogeneous 4) (hg₂ : g₂.IsHomogeneous 4)
    (hp : p.IsHomogeneous 9)
    (hmem : p ∈ Ideal.span ({f₁, h, g₁, g₂} : Set (MvPolynomial σ K))) :
    ∃ c d : MvPolynomial σ K,
      c.IsHomogeneous 5 ∧ d.IsHomogeneous 5 ∧
      representative (curveMap f₁ h g₁) (curveMap f₁ h g₂) (curveMap f₁ h p) =
        firstRestriction (curveMap f₁ h g₁) (curveMap f₁ h g₂)
          (chartFraction (curveMap f₁ h g₁) (curveMap f₁ h d)) +
        secondRestriction (curveMap f₁ h g₁) (curveMap f₁ h g₂)
          (chartFraction (curveMap f₁ h g₂) (curveMap f₁ h c)) := by
  obtain ⟨a, b, c, d, _, _, hc, hd, hrelation⟩ :=
    CycleQ2GeometricGradedWitness.degreeNine_witness f₁ h g₁ g₂ p
      hf₁ hh hg₁ hg₂ hp hmem
  refine ⟨c, d, hc, hd, ?_⟩
  have hquotient : curveMap f₁ h p =
      curveMap f₁ h c * curveMap f₁ h g₁ + curveMap f₁ h d * curveMap f₁ h g₂ := by
    rw [← hrelation]
    simp only [map_add, map_mul, curveMap_first, curveMap_second, mul_zero, zero_add]
  rw [hquotient]
  exact representative_relation _ _ _ _

/-- In particular, the degree-nine relation vanishes in the actual Cech
quotient; the stronger theorem above keeps the homogeneous chart witnesses. -/
theorem degreeNine_boundary_eq_zero (f₁ h g₁ g₂ p : MvPolynomial σ K)
    (hf₁ : f₁.IsHomogeneous 2) (hh : h.IsHomogeneous 3)
    (hg₁ : g₁.IsHomogeneous 4) (hg₂ : g₂.IsHomogeneous 4)
    (hp : p.IsHomogeneous 9)
    (hmem : p ∈ Ideal.span ({f₁, h, g₁, g₂} : Set (MvPolynomial σ K))) :
    boundary (curveMap f₁ h g₁) (curveMap f₁ h g₂) (curveMap f₁ h p) = 0 := by
  obtain ⟨c, d, _, _, heq⟩ :=
    degreeNine_quotient_boundary f₁ h g₁ g₂ p hf₁ hh hg₁ hg₂ hp hmem
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  rw [heq]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left ⟨chartFraction (curveMap f₁ h g₁) (curveMap f₁ h d), rfl⟩)
    (Submodule.mem_sup_right ⟨chartFraction (curveMap f₁ h g₂) (curveMap f₁ h c), rfl⟩)

end Polynomials

end CycleQ2GeometricHomogeneousBoundary

end
