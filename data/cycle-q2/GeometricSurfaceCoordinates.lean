import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Localization.Module
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Proposal.GeometricSeedNormalIdeals
import Proposal.GeometricSeedConormalBases
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Basic

/-!
# The actual surface and its three coordinate localizations

The original incidence equations and seed localization aliases are extracted
without changing their definitions. At theta = 1, the actual surface quotient
is identified with that literal seed ring by the identity on all five
coordinates. The induced localization equivalences preserve every fraction
and commute with the actual restriction maps. No finite trace vector is used
to define a surface cohomology class.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section
open scoped BigOperators MonomialOrder

namespace CycleQ2SegreSeed
variable {R : Type*} [CommRing R]

def linkageG (a b c d : R) : R := a ^ 3 - b ^ 3 + c ^ 3 + d ^ 3

def seedG (r x0 x1 x2 x3 w : R) : R := linkageG (x0^2) (r*x1*x3) w (x2^2)

theorem seedG_expanded (r x0 x1 x2 x3 w : R) :
    seedG r x0 x1 x2 x3 w = x0^6-r^3*x1^3*x3^3+x2^6+w^3 := by
  unfold seedG linkageG
  ring

end CycleQ2SegreSeed

namespace CycleQ2IncidenceNormalForm
open MvPolynomial
variable {σ R : Type*} [CommRing R]

def equationsIdeal (h F : MvPolynomial σ R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {h, F}

end CycleQ2IncidenceNormalForm

namespace CycleQ2IncidenceEquations
open MvPolynomial
variable {R : Type*} [CommRing R]

abbrev Poly (R : Type*) [CommRing R] := MvPolynomial (Fin 5) R

def smoothB : Poly R :=
  X 3 ^ 3 + X 2 ^ 3 + X 1 * X 2 * X 3 + X 0 * X 2 * X 3 +
    X 0 * X 1 ^ 2 + X 0 ^ 3

def smoothA : Poly R := X 1 ^ 3 + X 3 ^ 3
def smoothH (ι : R) : Poly R := smoothB - C ι * smoothA
def smoothK (ι : R) : Poly R := smoothB + C ι * smoothA

def seedG (r : R) : Poly R :=
  CycleQ2SegreSeed.seedG (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def smoothF (r ι : R) : Poly R := seedG r + smoothH ι * smoothK ι

end CycleQ2IncidenceEquations

namespace CycleQ2SegreTangentLocal
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
variable {R : Type*} [CommRing R]

abbrev SeedRing (r ι : R) := Poly R ⧸ equationsIdeal (smoothH ι) (smoothF r ι)

end CycleQ2SegreTangentLocal

namespace CycleQ2SeedQuotientFiniteFree
open MvPolynomial CycleQ2IncidenceEquations
variable (R : Type*) [CommRing R]

abbrev Base := MvPolynomial (Fin 3) R

def remainingIndex (i : Fin 3) : Fin 5 := ![1,2,3] i

def remainingInclusion : Base R →ₐ[R] Poly R := rename remainingIndex

instance remainingAlgebra : Algebra (Base R) (Poly R) :=
  (remainingInclusion R).toRingHom.toAlgebra

@[simp] theorem algebraMap_remaining (p : Base R) :
    algebraMap (Base R) (Poly R) p = remainingInclusion R p := rfl

end CycleQ2SeedQuotientFiniteFree

namespace CycleQ2SeedCechLocalization
open MvPolynomial CycleQ2SeedQuotientFiniteFree
variable (R : Type*) [CommRing R]

def baseProduct (s : Finset (Fin 3)) : Base R := ∏ i ∈ s, X i

end CycleQ2SeedCechLocalization

namespace CycleQ2SeedCechLocalizedBasis
open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
variable (R : Type*) [CommRing R]

abbrev SeedLocal (r ι : R) (s : Finset (Fin 3)) :=
  Localization (Algebra.algebraMapSubmonoid (SeedRing r ι)
    (Submonoid.powers (baseProduct R s)))

end CycleQ2SeedCechLocalizedBasis

namespace CycleQ2NormalConnecting
open MvPolynomial CycleQ2SeedTrace

theorem smoothH_eq_thetaH : CycleQ2IncidenceEquations.smoothH Complex.I = thetaH 1 := by
  simp [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, thetaH, originalH, originalB]
  ring

/-- The literal incidence polynomial `seedG` has this factorization for
all parameter values, without a Fermat specialization. -/
theorem seedG_eq_factorization (r : ℂ) :
    CycleQ2IncidenceEquations.seedG r =
      originalF1 r*originalG1 r+originalF2*originalG2 := by
  unfold CycleQ2IncidenceEquations.seedG
  rw [CycleQ2SegreSeed.seedG_expanded]
  unfold originalF1 originalG1 originalF2 originalG2
  simp only [map_pow]
  ring

/-- At the smooth cubic seed, this is the actual hypersurface equation of
the incidence system, including at `r = 57`. -/
theorem actualSeedEquation_eq_smoothF (r : ℂ) :
    actualSeedEquation r 1 = CycleQ2IncidenceEquations.smoothF r Complex.I := by
  unfold actualSeedEquation CycleQ2IncidenceEquations.smoothF
  rw [seedG_eq_factorization,smoothH_eq_thetaH]
  have hk : CycleQ2IncidenceEquations.smoothK Complex.I = thetaK 1 := by
    simp [CycleQ2IncidenceEquations.smoothK,CycleQ2IncidenceEquations.smoothB,
      CycleQ2IncidenceEquations.smoothA,thetaK,originalK,originalB]
    ring
  rw [hk]

end CycleQ2NormalConnecting

namespace CycleQ2GeometricSurfaceCoordinates

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
open CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2SegreTangentLocal
open CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechLocalization
open CycleQ2SeedCechLocalizedBasis

def quotientMap (r θ : ℂ) : WeightedPoly →+* SurfaceRing r θ :=
  Ideal.Quotient.mk (surfaceIdeal r θ)

/-- The original surface ideal is the literal incidence ideal, including
at the actual parameter 57. No cube-root specialization is used. -/
theorem surfaceIdeal_eq_seedIdeal (r : ℂ) :
    surfaceIdeal r 1 = equationsIdeal (smoothH Complex.I) (smoothF r Complex.I) := by
  rw [← actualSeedEquation_eq_smoothF, smoothH_eq_thetaH]
  unfold surfaceIdeal equationsIdeal
  congr 1
  ext x
  simp [surfaceEquations, or_comm]

def seedRingEquiv (r : ℂ) : SurfaceRing r 1 ≃ₐ[ℂ] SeedRing r Complex.I :=
  Ideal.quotientEquivAlgOfEq ℂ (surfaceIdeal_eq_seedIdeal r)

@[simp] theorem seedRingEquiv_quotient (r : ℂ) (p : WeightedPoly) :
    seedRingEquiv r (quotientMap r 1 p) =
      Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p :=
  Ideal.quotientEquivAlgOfEq_mk ℂ _ p

def coordinateElement (r θ : ℂ) (i : Fin 3) : SurfaceRing r θ :=
  quotientMap r θ (X (remainingIndex i))

def coordinateProduct (r θ : ℂ) (s : Finset (Fin 3)) : SurfaceRing r θ :=
  ∏ i ∈ s, coordinateElement r θ i

theorem coordinateProduct_eq (r θ : ℂ) (s : Finset (Fin 3)) :
    coordinateProduct r θ s =
      quotientMap r θ (remainingInclusion ℂ (baseProduct ℂ s)) := by
  simp [coordinateProduct, coordinateElement, baseProduct, remainingInclusion]

@[simp] theorem seedRingEquiv_coordinateProduct (r : ℂ) (s : Finset (Fin 3)) :
    seedRingEquiv r (coordinateProduct r 1 s) =
      algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s) := by
  rw [coordinateProduct_eq, seedRingEquiv_quotient]
  rfl

abbrev CoordinateLocal (r θ : ℂ) (s : Finset (Fin 3)) :=
  Localization.Away (coordinateProduct r θ s)

instance seedLocalIsAway (r : ℂ) (s : Finset (Fin 3)) :
    IsLocalization.Away
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s))
      (SeedLocal ℂ r Complex.I s) := by
  simpa only [Algebra.algebraMapSubmonoid_powers] using
    (inferInstance : IsLocalization
      (Algebra.algebraMapSubmonoid (SeedRing r Complex.I)
        (Submonoid.powers (baseProduct ℂ s))) (SeedLocal ℂ r Complex.I s))

/-- The actual coordinate localization is exactly the localization used by
the seed's three-coordinate Čech complex. -/
def seedCoordinateEquiv (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s ≃+* SeedLocal ℂ r Complex.I s :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (coordinateProduct r 1 s))
    (T := Submonoid.powers
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s)))
    (CoordinateLocal r 1 s) (SeedLocal ℂ r Complex.I s)
    (seedRingEquiv r).toRingEquiv
    (by rw [Submonoid.map_powers];
        exact congrArg Submonoid.powers (seedRingEquiv_coordinateProduct r s))

@[simp] theorem seedCoordinateEquiv_base (r : ℂ) (s : Finset (Fin 3))
    (p : SurfaceRing r 1) :
    seedCoordinateEquiv r s
      (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 s) p) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s) (seedRingEquiv r p) :=
  IsLocalization.ringEquivOfRingEquiv_eq _ p

@[simp] theorem seedCoordinateEquiv_polynomial (r : ℂ) (s : Finset (Fin 3))
    (p : WeightedPoly) :
    seedCoordinateEquiv r s
      (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 s) (quotientMap r 1 p)) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s)
        (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p) := by
  rw [seedCoordinateEquiv_base, seedRingEquiv_quotient]

def coordinateRestriction (r θ : ℂ) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    CoordinateLocal r θ s →ₐ[SurfaceRing r θ] CoordinateLocal r θ t where
  __ := IsLocalization.Away.lift (S := CoordinateLocal r θ s) (coordinateProduct r θ s)
    (IsLocalization.Away.isUnit_of_dvd (S := CoordinateLocal r θ t)
      (coordinateProduct r θ t)
      (Finset.prod_dvd_prod_of_subset s t (coordinateElement r θ) hst))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

@[simp] theorem coordinateRestriction_base (r θ : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : SurfaceRing r θ) :
    coordinateRestriction r θ hst
      (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) p) =
      algebraMap (SurfaceRing r θ) (CoordinateLocal r θ t) p :=
  (coordinateRestriction r θ hst).commutes p

def seedRestriction (r : ℂ) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SeedLocal ℂ r Complex.I s →ₐ[SeedRing r Complex.I] SeedLocal ℂ r Complex.I t where
  __ := IsLocalization.Away.lift (S := SeedLocal ℂ r Complex.I s)
    (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ s))
    (IsLocalization.Away.isUnit_of_dvd (S := SeedLocal ℂ r Complex.I t)
      (algebraMap (Base ℂ) (SeedRing r Complex.I) (baseProduct ℂ t))
      (map_dvd _ (Finset.prod_dvd_prod_of_subset s t (fun i : Fin 3 => (X i : Base ℂ)) hst)))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

@[simp] theorem seedRestriction_base (r : ℂ) {s t : Finset (Fin 3)}
    (hst : s ⊆ t) (p : SeedRing r Complex.I) :
    seedRestriction r hst
      (algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I s) p) =
      algebraMap (SeedRing r Complex.I) (SeedLocal ℂ r Complex.I t) p :=
  (seedRestriction r hst).commutes p

/-- The localization comparison respects the actual restriction maps on
every fraction, so it is a comparison of Čech coefficient diagrams. -/
theorem seedCoordinateEquiv_restriction (r : ℂ) {s t : Finset (Fin 3)}
    (hst : s ⊆ t) (p : CoordinateLocal r 1 s) :
    seedCoordinateEquiv r t (coordinateRestriction r 1 hst p) =
      seedRestriction r hst (seedCoordinateEquiv r s p) := by
  have hh : (seedCoordinateEquiv r t).toRingHom.comp
        (coordinateRestriction r 1 hst).toRingHom =
      (seedRestriction r hst).toRingHom.comp (seedCoordinateEquiv r s).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinateProduct r 1 s))
    apply RingHom.ext
    intro x
    change seedCoordinateEquiv r t
        (coordinateRestriction r 1 hst
          (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 s) x)) =
      seedRestriction r hst
        (seedCoordinateEquiv r s
          (algebraMap (SurfaceRing r 1) (CoordinateLocal r 1 s) x))
    rw [coordinateRestriction_base, seedCoordinateEquiv_base,
      seedCoordinateEquiv_base, seedRestriction_base]
  exact congrArg (fun f : CoordinateLocal r 1 s →+* SeedLocal ℂ r Complex.I t => f p) hh

/-- The explicit literal incidence parameter is retained by the complete
coordinate restriction comparison. -/
theorem literal_coordinate_restriction {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (p : CoordinateLocal 57 1 s) :
    seedCoordinateEquiv 57 t (coordinateRestriction 57 1 hst p) =
      seedRestriction 57 hst (seedCoordinateEquiv 57 s p) :=
  seedCoordinateEquiv_restriction 57 hst p

end CycleQ2GeometricSurfaceCoordinates

namespace CycleQ2IncidenceNormalForm
open MvPolynomial
variable {σ R : Type*} [CommRing R]

lemma reduced_sub (m : MonomialOrder σ) {h F p q : MvPolynomial σ R}
    (hp : Reduced m h F p) (hq : Reduced m h F q) :
    Reduced m h F (p - q) := by
  intro d hd
  by_cases hpd : p.coeff d = 0
  · have hqd : q.coeff d ≠ 0 := by
      intro hqd
      have := mem_support_iff.mp hd
      simp [coeff_sub, hpd, hqd] at this
    exact hq d (mem_support_iff.mpr hqd)
  · exact hp d (mem_support_iff.mpr hpd)

/-- The two-monic-polynomial product criterion, proved by dividing the first
coefficient by the second equation.  Disjoint supports of the leading exponents
prevent cancellation of the two remaining leading terms. -/
theorem reduced_eq_zero_of_representation
    (m : MonomialOrder σ) {h F p a b : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (heq : p = a * h + b * F) : p = 0 := by
  obtain ⟨q, r, ha, _, hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff F) by rw [hF.leadingCoeff_eq_one]; exact isUnit_one) a
  let s := b + q * h
  have hp' : p = r * h + s * F := by
    rw [heq, ha]
    dsimp [s]
    ring
  by_contra hp0
  have hpn := hp (m.degree p) (m.degree_mem_support hp0)
  by_cases hr0 : r = 0
  · have hs0 : s ≠ 0 := by
      intro hs0
      simp [hr0, hs0] at hp'
      exact hp0 hp'
    have hpd : m.degree p = m.degree s + m.degree F := by
      rw [hp', hr0, zero_mul, zero_add, degree_mul_monic m hs0 hF]
    apply hpn.2
    rw [hpd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hrd : m.degree (r * h) = m.degree r + m.degree h :=
    degree_mul_monic m hr0 hh
  have hrn : ¬ m.degree F ≤ m.degree (r * h) := by
    intro hd
    apply hr (m.degree r) (m.degree_mem_support hr0)
    rw [hrd] at hd
    intro i
    rcases hcop i with hi | hi
    · simpa only [Finsupp.add_apply, hi, add_zero] using hd i
    · simp [hi]
  have hhd : m.degree h ≤ m.degree (r * h) := by
    rw [hrd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  by_cases hs0 : s = 0
  · have hpd : m.degree p = m.degree (r * h) := by
      rw [hp', hs0, zero_mul, add_zero]
    apply hpn.1
    rw [hpd]
    exact hhd
  have hsd : m.degree (s * F) = m.degree s + m.degree F :=
    degree_mul_monic m hs0 hF
  have hFd : m.degree F ≤ m.degree (s * F) := by
    rw [hsd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hne : m.toSyn (m.degree (r * h)) ≠ m.toSyn (m.degree (s * F)) := by
    intro hd
    apply hrn
    rwa [m.toSyn.injective hd]
  rcases lt_or_gt_of_ne hne with hd | hd
  · have hpd : m.degree p = m.degree (s * F) := by
      rw [hp', m.degree_add_eq_right_of_lt hd]
    apply hpn.2
    rw [hpd]
    exact hFd
  · have hpd : m.degree p = m.degree (r * h) := by
      rw [hp', m.degree_add_of_lt hd]
    apply hpn.1
    rw [hpd]
    exact hhd

/-- Uniqueness is an actual consequence of the two polynomial equations and the
coprimality of their leading monomials, over an arbitrary coefficient ring. -/
theorem reduced_unique
    (m : MonomialOrder σ) {h F p r₁ r₂ a₁ a₂ b₁ b₂ : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hr₁ : Reduced m h F r₁) (hr₂ : Reduced m h F r₂)
    (hp₁ : p = a₁ * h + b₁ * F + r₁)
    (hp₂ : p = a₂ * h + b₂ * F + r₂) : r₁ = r₂ := by
  apply sub_eq_zero.mp
  apply reduced_eq_zero_of_representation m hh hF hcop (reduced_sub m hr₁ hr₂)
    (a := a₂ - a₁) (b := b₂ - b₁)
  linear_combination hp₂ - hp₁

theorem existsUnique_reduced_representative
    (m : MonomialOrder σ) (h F p : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    ∃! r, Reduced m h F r ∧ ∃ a b, p = a * h + b * F + r := by
  obtain ⟨a, b, r, hp, hr⟩ := exists_reduced_representation m h F p hh hF
  refine ⟨r, ⟨hr, a, b, hp⟩, ?_⟩
  rintro r' ⟨hr', a', b', hp'⟩
  exact reduced_unique m hh hF hcop hr' hr hp' hp

def reducedExponents (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    Set (σ →₀ ℕ) :=
  {d | ¬ m.degree h ≤ d ∧ ¬ m.degree F ≤ d}

def reducedSubmodule (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R (reducedExponents m h F)

lemma mem_reducedSubmodule (m : MonomialOrder σ) (h F p : MvPolynomial σ R) :
    p ∈ reducedSubmodule m h F ↔ Reduced m h F p := Iff.rfl

def reducedQuotientMap (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    reducedSubmodule m h F →ₗ[R] MvPolynomial σ R ⧸ equationsIdeal h F :=
  (Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap.comp
    (reducedSubmodule m h F).subtype

theorem reducedQuotientMap_bijective
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    Function.Bijective (reducedQuotientMap m h F) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk (equationsIdeal h F) p.val =
      Ideal.Quotient.mk (equationsIdeal h F) q.val at hpq
    have hpq' := Ideal.Quotient.eq.mp hpq
    obtain ⟨a, b, heq⟩ := Ideal.mem_span_pair.mp hpq'
    exact reduced_eq_zero_of_representation m hh hF hcop
      (reduced_sub m p.property q.property) heq.symm
  · intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, r, hp, hr⟩ := exists_reduced_representation m h F p hh hF
    refine ⟨⟨r, hr⟩, ?_⟩
    change Ideal.Quotient.mk (equationsIdeal h F) r =
      Ideal.Quotient.mk (equationsIdeal h F) p
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨-a, -b, ?_⟩
    rw [hp]
    ring

/-- The standard-monomial submodule is the whole quotient, with no unproved
injectivity or flatness assumption. -/
noncomputable def reducedQuotientEquiv
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    reducedSubmodule m h F ≃ₗ[R] MvPolynomial σ R ⧸ equationsIdeal h F :=
  LinearEquiv.ofBijective (reducedQuotientMap m h F)
    (reducedQuotientMap_bijective m h F hh hF hcop)

/-- The classes of standard monomials form a basis over the coefficient ring. -/
noncomputable def quotientBasis
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    Module.Basis (reducedExponents m h F) R (MvPolynomial σ R ⧸ equationsIdeal h F) :=
  (MvPolynomial.basisRestrictSupport R (reducedExponents m h F)).map
    (reducedQuotientEquiv m h F hh hF hcop)

theorem quotientBasis_apply
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (d : reducedExponents m h F) :
    quotientBasis m h F hh hF hcop d =
      Ideal.Quotient.mk (equationsIdeal h F) (monomial d.val 1) := by
  change Ideal.Quotient.mk (equationsIdeal h F)
    (AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := R) (reducedExponents m h F)).symm
        (Finsupp.single d 1) : Finsupp.supported R R (reducedExponents m h F)) :
        (σ →₀ ℕ) →₀ R)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

abbrev Exponent := Fin 2 →₀ ℕ

def auxiliaryWeight : Exponent →+ ℕ where
  toFun d := 3 * d 0 + 7 * d 1
  map_zero' := by simp
  map_add' a b := by
    simp only [Finsupp.add_apply]
    omega

/-- A separate type keeps the auxiliary order distinct from the divisibility
order on exponent vectors. -/
def AuxiliaryExponent := Exponent

def toAuxiliary : Exponent ≃ AuxiliaryExponent := Equiv.refl _
def ofAuxiliary : AuxiliaryExponent ≃ Exponent := Equiv.refl _

noncomputable instance : AddCommMonoid AuxiliaryExponent := ofAuxiliary.addCommMonoid

lemma ofAuxiliary_add (a b : AuxiliaryExponent) :
    ofAuxiliary (a + b) = ofAuxiliary a + ofAuxiliary b := rfl

def auxiliaryKey (a : AuxiliaryExponent) : Lex (ℕ × Lex Exponent) :=
  toLex (auxiliaryWeight (ofAuxiliary a), toLex (ofAuxiliary a))

lemma auxiliaryKey_injective : Function.Injective auxiliaryKey := by
  intro a b hab
  exact ofAuxiliary.injective (toLex.injective (Prod.mk.inj (toLex.injective hab)).2)

noncomputable instance : LinearOrder AuxiliaryExponent :=
  LinearOrder.lift' auxiliaryKey auxiliaryKey_injective

lemma auxiliaryKey_add (a b : AuxiliaryExponent) :
    auxiliaryKey (a + b) = auxiliaryKey a + auxiliaryKey b := by
  change toLex (auxiliaryWeight (ofAuxiliary a + ofAuxiliary b),
    toLex (ofAuxiliary a + ofAuxiliary b)) =
    toLex (auxiliaryWeight (ofAuxiliary a) + auxiliaryWeight (ofAuxiliary b),
      toLex (ofAuxiliary a) + toLex (ofAuxiliary b))
  rw [map_add, toLex_add]

noncomputable instance : IsOrderedCancelAddMonoid AuxiliaryExponent where
  le_of_add_le_add_left a b c h := by
    change auxiliaryKey b ≤ auxiliaryKey c
    change auxiliaryKey (a + b) ≤ auxiliaryKey (a + c) at h
    simpa only [auxiliaryKey, ofAuxiliary_add, map_add, toLex_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_left, add_right_inj,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    change auxiliaryKey a ≤ auxiliaryKey b at h
    change auxiliaryKey (a + c) ≤ auxiliaryKey (b + c)
    simpa only [auxiliaryKey, ofAuxiliary_add, map_add, toLex_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

noncomputable instance : WellFoundedLT AuxiliaryExponent :=
  ⟨InvImage.wf auxiliaryKey wellFounded_lt⟩

noncomputable def auxiliaryOrder : MonomialOrder (Fin 2) where
  syn := AuxiliaryExponent
  toSyn := { toEquiv := toAuxiliary, map_add' _ _ := rfl }
  toSyn_monotone a b hab := by
    change toLex (auxiliaryWeight a, toLex a) ≤ toLex (auxiliaryWeight b, toLex b)
    rw [Prod.Lex.toLex_le_toLex]
    have hw : auxiliaryWeight a ≤ auxiliaryWeight b := by
      have h0 := hab 0
      have h1 := hab 1
      dsimp [auxiliaryWeight]
      omega
    rcases lt_or_eq_of_le hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, Finsupp.toLex_monotone hab⟩

lemma auxiliaryOrder_lt_of_weight_lt {a b : Exponent}
    (h : auxiliaryWeight a < auxiliaryWeight b) : a ≺[auxiliaryOrder] b := by
  change toLex (auxiliaryWeight a, toLex a) < toLex (auxiliaryWeight b, toLex b)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

lemma single_three_le_iff (i : σ) (d : σ →₀ ℕ) :
    Finsupp.single i 3 ≤ d ↔ 3 ≤ d i := by
  classical
  constructor
  · intro h
    simpa using h i
  · intro h j
    by_cases hji : j = i
    · subst j
      simpa using h
    · simp [Ne.symm hji]

end CycleQ2IncidenceNormalForm

namespace CycleQ2IncidenceFirstOrder
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
variable {R : Type*} [CommRing R]

theorem smoothSeed_mem_iff_linkage {p : Poly R} (r ι : R) :
    p ∈ equationsIdeal (smoothH ι) (smoothF r ι) ↔
      ∃ a b : Poly R, a * smoothH ι + b * seedG r = p := by
  rw [equationsIdeal, Ideal.mem_span_pair]
  constructor
  · rintro ⟨a, b, hab⟩
    refine ⟨a + b * smoothK ι, b, ?_⟩
    rw [← hab]
    unfold smoothF
    ring
  · rintro ⟨a, b, hab⟩
    refine ⟨a - b * smoothK ι, b, ?_⟩
    rw [← hab]
    unfold smoothF
    ring

end CycleQ2IncidenceFirstOrder

section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
namespace CycleQ2SeedQuotientFiniteFree
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
variable (R : Type*) [CommRing R]

abbrev Nested := MvPolynomial (Fin 2) (Base R)

def splitIndex : Fin 5 ≃ Fin 2 ⊕ Fin 3 where
  toFun := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 1]
  invFun := Sum.elim ![0,4] ![1,2,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by
    cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl


def regroup : Poly R ≃ₐ[R] Nested R :=
  (renameEquiv R splitIndex).trans (sumAlgEquiv R (Fin 2) (Fin 3))

@[simp] theorem regroup_C (c : R) : regroup R (C c) = C (C c) := by simp [regroup]
@[simp] theorem regroup_X_zero : regroup R (X 0) = X 0 := by simp [regroup, splitIndex]
@[simp] theorem regroup_X_one : regroup R (X 1) = C (X 0) := by simp [regroup, splitIndex]
@[simp] theorem regroup_X_two : regroup R (X 2) = C (X 1) := by simp [regroup, splitIndex]
@[simp] theorem regroup_X_three : regroup R (X 3) = C (X 2) := by simp [regroup, splitIndex]
@[simp] theorem regroup_X_four : regroup R (X 4) = X 1 := by simp [regroup, splitIndex]

theorem regroup_remaining (p : Base R) : regroup R (remainingInclusion R p) = C p := by
  have hh : (regroup R).toAlgHom.comp (remainingInclusion R) =
      IsScalarTower.toAlgHom R (Base R) (Nested R) := by
    ext i
    fin_cases i <;> simp [remainingInclusion, remainingIndex]
  exact congrArg (fun f : Base R →ₐ[R] Nested R ↦ f p) hh

def regroupOverBase : Poly R ≃ₐ[Base R] Nested R where
  toRingEquiv := (regroup R).toRingEquiv
  commutes' p := regroup_remaining R p

def cubicConstant (ι : R) : Base R :=
  X 2^3 + X 1^3 + X 0*X 1*X 2 - C ι*(X 0^3+X 2^3)

def cubicLinear : Base R := X 0^2 + X 1*X 2

def sexticConstant (r : R) : Base R := X 1^6 - C (r^3)*X 0^3*X 2^3

def nestedH (ι : R) : Nested R := X 0^3 + C (cubicConstant R ι) + C (cubicLinear R)*X 0
def nestedG (r : R) : Nested R := X 1^3 + X 0^6 + C (sexticConstant R r)

theorem regroup_smoothH (ι : R) : regroup R (smoothH ι) = nestedH R ι := by
  simp only [smoothH, smoothB, smoothA, map_sub, map_add, map_mul, map_pow,
    regroup_C, regroup_X_zero, regroup_X_one, regroup_X_two, regroup_X_three]
  simp only [nestedH, cubicConstant, cubicLinear, map_sub, map_add, map_mul, map_pow]
  ring

theorem regroup_seedG (r : R) : regroup R (seedG r) = nestedG R r := by
  rw [seedG, CycleQ2SegreSeed.seedG_expanded]
  simp only [map_sub, map_add, map_mul, map_pow, regroup_C, regroup_X_zero,
    regroup_X_one, regroup_X_two, regroup_X_three, regroup_X_four]
  simp only [nestedG, sexticConstant, map_sub, map_mul, map_pow]
  ring

theorem nestedH_shape (ι : R) : nestedH R ι =
    monomial (Finsupp.single 0 3) 1 +
      ∑ j : Fin 2, monomial (![0, Finsupp.single 0 1] j)
        (![cubicConstant R ι, cubicLinear R] j) := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    nestedH, ← X_pow_eq_monomial, ← C_mul_X_eq_monomial, monomial_zero']
  ring

theorem nestedG_shape (r : R) : nestedG R r =
    monomial (Finsupp.single 1 3) 1 +
      ∑ j : Fin 2, monomial (![Finsupp.single 0 6, 0] j)
        (![1, sexticConstant R r] j) := by
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    nestedG, ← X_pow_eq_monomial, monomial_zero']
  ring

theorem nestedH_leading [Nontrivial R] (ι : R) :
    auxiliaryOrder.degree (nestedH R ι) = Finsupp.single 0 3 ∧
      auxiliaryOrder.Monic (nestedH R ι) := by
  rw [nestedH_shape]
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro j
    apply auxiliaryOrder_lt_of_weight_lt
    fin_cases j <;> norm_num [auxiliaryWeight]

theorem nestedG_leading [Nontrivial R] (r : R) :
    auxiliaryOrder.degree (nestedG R r) = Finsupp.single 1 3 ∧
      auxiliaryOrder.Monic (nestedG R r) := by
  rw [nestedG_shape]
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro j
    apply auxiliaryOrder_lt_of_weight_lt
    fin_cases j <;> norm_num [auxiliaryWeight]

theorem nested_coprime [Nontrivial R] (r ι : R) :
    ∀ j, auxiliaryOrder.degree (nestedH R ι) j = 0 ∨
      auxiliaryOrder.degree (nestedG R r) j = 0 := by
  intro j
  rw [(nestedH_leading R ι).1, (nestedG_leading R r).1]
  fin_cases j <;> simp

def nestedIdeal (r ι : R) : Ideal (Nested R) := equationsIdeal (nestedH R ι) (nestedG R r)

theorem seed_ideal_eq_linkage (r ι : R) :
    equationsIdeal (smoothH ι) (smoothF r ι) = equationsIdeal (smoothH ι) (seedG r) := by
  ext p
  rw [smoothSeed_mem_iff_linkage, equationsIdeal, Ideal.mem_span_pair]

theorem nestedIdeal_map (r ι : R) : nestedIdeal R r ι =
    (equationsIdeal (smoothH ι) (smoothF r ι)).map (regroupOverBase R).toRingHom := by
  rw [seed_ideal_eq_linkage]
  simp only [nestedIdeal, equationsIdeal, Ideal.map_span, Set.image_insert_eq,
    Set.image_singleton]
  change Ideal.span {nestedH R ι, nestedG R r} =
    Ideal.span {regroup R (smoothH ι), regroup R (seedG r)}
  rw [regroup_smoothH, regroup_seedG]

instance seedModule (r ι : R) : Module (Base R) (SeedRing r ι) :=
  (inferInstance : Algebra (Base R) (SeedRing r ι)).toModule

def quotientRegroup (r ι : R) :
    SeedRing r ι ≃ₐ[Base R] (Nested R ⧸ nestedIdeal R r ι) :=
  Ideal.quotientEquivAlg _ _ (regroupOverBase R) (nestedIdeal_map R r ι)

def nestedExponentEquiv [Nontrivial R] (r ι : R) :
    reducedExponents auxiliaryOrder (nestedH R ι) (nestedG R r) ≃ Fin 3 × Fin 3 where
  toFun d :=
    (⟨d.val 0, by
      have hd := d.property.1
      rw [(nestedH_leading R ι).1, single_three_le_iff] at hd
      omega⟩,
     ⟨d.val 1, by
      have hd := d.property.2
      rw [(nestedG_leading R r).1, single_three_le_iff] at hd
      omega⟩)
  invFun ij := ⟨Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val, by
    constructor
    · rw [(nestedH_leading R ι).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.1.isLt
    · rw [(nestedG_leading R r).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.2.isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp
  right_inv ij := by
    apply Prod.ext <;> apply Fin.ext <;> simp

def nestedBasis [Nontrivial R] (r ι : R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (Nested R ⧸ nestedIdeal R r ι) :=
  (quotientBasis auxiliaryOrder (nestedH R ι) (nestedG R r)
    (nestedH_leading R ι).2 (nestedG_leading R r).2 (nested_coprime R r ι)).reindex
      (nestedExponentEquiv R r ι)

theorem nestedBasis_apply [Nontrivial R] (r ι : R) (ij : Fin 3 × Fin 3) :
    nestedBasis R r ι ij = Ideal.Quotient.mk (nestedIdeal R r ι)
      (X 0 ^ ij.1.val * X 1 ^ ij.2.val) := by
  unfold nestedBasis
  erw [Module.Basis.reindex_apply, quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val) 1 = _
  rw [MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

/-- A rank-nine basis of the existing, unchanged seed quotient. -/
def seedBasis [Nontrivial R] (r ι : R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (SeedRing r ι) :=
  (nestedBasis R r ι).map (quotientRegroup R r ι).symm.toLinearEquiv

theorem seedBasis_apply [Nontrivial R] (r ι : R) (ij : Fin 3 × Fin 3) :
    seedBasis R r ι ij = Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      ((X 0 : Poly R) ^ ij.1.val * X 4 ^ ij.2.val) := by
  apply (quotientRegroup R r ι).injective
  simp only [seedBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, nestedBasis_apply]
  change Ideal.Quotient.mk _ (X 0 ^ ij.1.val * X 1 ^ ij.2.val) =
    Ideal.Quotient.mk _ (regroup R ((X 0 : Poly R) ^ ij.1.val * X 4 ^ ij.2.val))
  simp

theorem seedQuotient_free [Nontrivial R] (r ι : R) : Module.Free (Base R) (SeedRing r ι) :=
  Module.Free.of_basis (seedBasis R r ι)

theorem seedQuotient_finite [Nontrivial R] (r ι : R) : Module.Finite (Base R) (SeedRing r ι) :=
  Module.Finite.of_basis (seedBasis R r ι)

theorem seedQuotient_rank_nine [Nontrivial R] (r ι : R) :
    Module.finrank (Base R) (SeedRing r ι) = 9 := by
  rw [Module.finrank_eq_card_basis (seedBasis R r ι)]
  decide

end CycleQ2SeedQuotientFiniteFree
end

namespace CycleQ2GeometricSurfaceCoordinates

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2SeedQuotientFiniteFree
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2SegreTangentLocal

/-- The identity-coordinate comparison also respects the actual polynomial
base in x1,x2,x3. -/
def seedRingEquivOverBase (r : ℂ) : SurfaceRing r 1 ≃ₐ[Base ℂ] SeedRing r Complex.I :=
  Ideal.quotientEquivAlgOfEq (Base ℂ) (surfaceIdeal_eq_seedIdeal r)

@[simp] theorem seedRingEquivOverBase_quotient (r : ℂ) (p : WeightedPoly) :
    seedRingEquivOverBase r (quotientMap r 1 p) =
      Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF r Complex.I)) p :=
  Ideal.quotientEquivAlgOfEq_mk (Base ℂ) _ p

/-- The nine literal monomials are a basis of the actual surface ring over
the original three-coordinate polynomial base. -/
def surfaceBasis (r : ℂ) : Module.Basis (Fin 3 × Fin 3) (Base ℂ) (SurfaceRing r 1) :=
  (seedBasis ℂ r Complex.I).map (seedRingEquivOverBase r).symm.toLinearEquiv

@[simp] theorem surfaceBasis_apply (r : ℂ) (ij : Fin 3 × Fin 3) :
    surfaceBasis r ij = quotientMap r 1 ((X 0 : WeightedPoly)^ij.1.val * X 4^ij.2.val) := by
  apply (seedRingEquivOverBase r).injective
  simp only [surfaceBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, seedBasis_apply, seedRingEquivOverBase_quotient]

theorem literal_surface_rank_nine : Module.finrank (Base ℂ) (SurfaceRing 57 1) = 9 := by
  rw [Module.finrank_eq_card_basis (surfaceBasis 57)]
  decide

end CycleQ2GeometricSurfaceCoordinates

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedCechThreeOpen

open MvPolynomial CycleQ2SeedQuotientFiniteFree
open scoped BigOperators

variable {R : Type*} [CommRing R]

abbrev LaurentExponent := Fin 3 → ℤ
abbrev Laurent := AddMonoidAlgebra R LaurentExponent
abbrev ShiftIndex := Fin 3 × Fin 3
abbrev LaurentGrade := ℤ × ZMod 3

/-- Only coordinates in `s` may have poles. -/
def HasPoles (s : Finset (Fin 3)) (p : Laurent (R := R)) : Prop :=
  ∀ e i, i ∉ s → e i < 0 → p.coeff e = 0

/-- The degree and character of `x₀^a*w^b` times a base Laurent monomial. -/
def shiftedGrade (ab : ShiftIndex) (e : LaurentExponent) : LaurentGrade :=
  ((ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i,
    (2 * ab.1.val : ℕ) + (2 * e 0 + e 1 : ℤ))

def HasGrade (ab : ShiftIndex) (g : LaurentGrade) (p : Laurent (R := R)) : Prop :=
  ∀ e, shiftedGrade ab e ≠ g → p.coeff e = 0

/-- Projection onto nonnegative exponent of the first base coordinate. -/
def nonnegativePart (p : Laurent (R := R)) : Laurent (R := R) :=
  AddMonoidAlgebra.ofCoeff (p.coeff.filter (fun e ↦ 0 ≤ e 0))

@[simp] theorem nonnegativePart_apply (p : Laurent (R := R)) (e : LaurentExponent) :
    (nonnegativePart p).coeff e = if 0 ≤ e 0 then p.coeff e else 0 := rfl

theorem hasGrade_nonnegativePart (ab : ShiftIndex) (g : LaurentGrade)
    {p : Laurent (R := R)} (hp : HasGrade ab g p) : HasGrade ab g (nonnegativePart p) := by
  intro e he
  simp only [nonnegativePart_apply]
  split <;> simp [hp e he]

theorem hasGrade_add (ab : ShiftIndex) (g : LaurentGrade)
    {p q : Laurent (R := R)} (hp : HasGrade ab g p) (hq : HasGrade ab g q) :
    HasGrade ab g (p + q) := by
  intro e he
  simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp e he, hq e he]

theorem hasGrade_sub (ab : ShiftIndex) (g : LaurentGrade)
    {p q : Laurent (R := R)} (hp : HasGrade ab g p) (hq : HasGrade ab g q) :
    HasGrade ab g (p - q) := by
  intro e he
  simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hp e he, hq e he]

/-- A concrete contraction, before imposing any degree. -/
theorem threeOpen_kernel (p01 p02 p12 : Laurent (R := R))
    (h01 : HasPoles {0, 1} p01) (h02 : HasPoles {0, 2} p02)
    (h12 : HasPoles {1, 2} p12) (hc : p01 - p02 + p12 = 0) :
    HasPoles {0} (nonnegativePart p01 - p01) ∧
    HasPoles {1} (nonnegativePart p01) ∧
    HasPoles {2} (p12 + nonnegativePart p01) ∧
    p01 = nonnegativePart p01 - (nonnegativePart p01 - p01) ∧
    p02 = (p12 + nonnegativePart p01) - (nonnegativePart p01 - p01) ∧
    p12 = (p12 + nonnegativePart p01) - nonnegativePart p01 := by
  have heq (e : LaurentExponent) : p01.coeff e - p02.coeff e + p12.coeff e = 0 := by
    have hh := congrArg (fun p : Laurent (R := R) ↦ p.coeff e) hc
    simpa only [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub, AddMonoidAlgebra.coeff_zero, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.zero_apply] using hh
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e i hi hneg
    fin_cases i
    · simp at hi
    · by_cases h0 : 0 ≤ e 0
      · simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h0]
      · have hz02 := h02 e 1 (by decide) hneg
        have hz12 := h12 e 0 (by decide) (lt_of_not_ge h0)
        have hz01 : p01.coeff e = 0 := by
          have hh := heq e
          simpa [hz02, hz12] using hh
        simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, h0, hz01]
    · have hz := h01 e 2 (by decide) hneg
      simp [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, hz]
  · intro e i hi hneg
    fin_cases i
    · change e 0 < 0 at hneg
      simp [not_le.mpr hneg]
    · simp at hi
    · simp [h01 e 2 (by decide) hneg]
  · intro e i hi hneg
    fin_cases i
    · change e 0 < 0 at hneg
      simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
        not_le.mpr hneg, h12 e 0 (by decide) hneg]
    · by_cases h0 : 0 ≤ e 0
      · have hz02 := h02 e 1 (by decide) hneg
        have hh := heq e
        simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
          nonnegativePart_apply, if_pos h0]
        linear_combination hh + hz02
      · simp [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, h0,
          h12 e 0 (by decide) (lt_of_not_ge h0)]
    · simp at hi
  · abel
  · linear_combination -hc
  · abel

/-- Every graded one-cocycle is a coboundary with the same degree and character. -/
theorem exists_graded_primitives (ab : ShiftIndex) (g : LaurentGrade)
    (p01 p02 p12 : Laurent (R := R))
    (h01 : HasPoles {0, 1} p01) (h02 : HasPoles {0, 2} p02)
    (h12 : HasPoles {1, 2} p12)
    (hg01 : HasGrade ab g p01) (_hg02 : HasGrade ab g p02)
    (hg12 : HasGrade ab g p12) (hc : p01 - p02 + p12 = 0) :
    ∃ q0 q1 q2 : Laurent (R := R),
      HasPoles {0} q0 ∧ HasPoles {1} q1 ∧ HasPoles {2} q2 ∧
      HasGrade ab g q0 ∧ HasGrade ab g q1 ∧ HasGrade ab g q2 ∧
      p01 = q1 - q0 ∧ p02 = q2 - q0 ∧ p12 = q2 - q1 := by
  have hh := threeOpen_kernel p01 p02 p12 h01 h02 h12 hc
  have hn := hasGrade_nonnegativePart ab g hg01
  exact ⟨nonnegativePart p01 - p01, nonnegativePart p01,
    p12 + nonnegativePart p01, hh.1, hh.2.1, hh.2.2.1,
    hasGrade_sub ab g hn hg01, hn, hasGrade_add ab g hg12 hn,
    hh.2.2.2⟩

/-- The same exactness for the actual nine degree-shifted summands. -/
theorem nineSummand_kernel (g : LaurentGrade)
    (p01 p02 p12 : ShiftIndex → Laurent (R := R))
    (h01 : ∀ ab, HasPoles {0, 1} (p01 ab))
    (h02 : ∀ ab, HasPoles {0, 2} (p02 ab))
    (h12 : ∀ ab, HasPoles {1, 2} (p12 ab))
    (hg01 : ∀ ab, HasGrade ab g (p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (p12 ab))
    (hc : ∀ ab, p01 ab - p02 ab + p12 ab = 0) :
    ∃ q0 q1 q2 : ShiftIndex → Laurent (R := R),
      (∀ ab, HasPoles {0} (q0 ab)) ∧ (∀ ab, HasPoles {1} (q1 ab)) ∧
      (∀ ab, HasPoles {2} (q2 ab)) ∧
      (∀ ab, HasGrade ab g (q0 ab)) ∧ (∀ ab, HasGrade ab g (q1 ab)) ∧
      (∀ ab, HasGrade ab g (q2 ab)) ∧
      (∀ ab, p01 ab = q1 ab - q0 ab) ∧
      (∀ ab, p02 ab = q2 ab - q0 ab) ∧
      (∀ ab, p12 ab = q2 ab - q1 ab) := by
  choose q0 q1 q2 h0 h1 h2 hg0 hg1 hg2 he01 he02 he12 using
    fun ab ↦ exists_graded_primitives ab g (p01 ab) (p02 ab) (p12 ab)
      (h01 ab) (h02 ab) (h12 ab) (hg01 ab) (hg02 ab) (hg12 ab) (hc ab)
  exact ⟨q0, q1, q2, h0, h1, h2, hg0, hg1, hg2, he01, he02, he12⟩

end CycleQ2SeedCechThreeOpen

end

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedCechLocalization

open MvPolynomial CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
open scoped BigOperators

variable (R : Type*) [CommRing R]

abbrev NatExponent := Fin 3 →₀ ℕ

def castExponent : NatExponent →+ LaurentExponent where
  toFun e i := e i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

@[simp] theorem castExponent_apply (e : NatExponent) (i : Fin 3) :
    castExponent e i = (e i : ℤ) := rfl

theorem castExponent_injective : Function.Injective castExponent := by
  intro a b hab
  ext i
  exact Nat.cast_injective (congrFun hab i)

theorem mem_range_castExponent (e : LaurentExponent) :
    e ∈ Set.range castExponent ↔ ∀ i, 0 ≤ e i := by
  constructor
  · rintro ⟨a, rfl⟩ i
    exact Nat.cast_nonneg _
  · intro he
    refine ⟨Finsupp.equivFunOnFinite.symm (fun i ↦ (e i).toNat), ?_⟩
    ext i
    exact Int.toNat_of_nonneg (he i)

def baseToLaurent : Base R →ₐ[R] Laurent (R := R) :=
  AddMonoidAlgebra.mapDomainAlgHom R R castExponent

theorem baseToLaurent_injective : Function.Injective (baseToLaurent R) :=
  AddMonoidAlgebra.mapDomain_injective castExponent_injective

@[simp] theorem baseToLaurent_monomial (e : NatExponent) (c : R) :
    baseToLaurent R (monomial e c) = AddMonoidAlgebra.single (castExponent e) c :=
  AddMonoidAlgebra.mapDomain_single

theorem baseToLaurent_hasPoles (p : Base R) : HasPoles ∅ (baseToLaurent R p) := by
  intro e i _ hi
  change Finsupp.mapDomain castExponent (AddMonoidAlgebra.coeff p) e = 0
  apply Finsupp.mapDomain_of_notMem_range
  intro he
  exact (not_le.mpr hi) ((mem_range_castExponent e).mp he i)

theorem mem_range_baseToLaurent (p : Laurent (R := R)) :
    p ∈ Set.range (baseToLaurent R) ↔ HasPoles ∅ p := by
  constructor
  · rintro ⟨p, rfl⟩
    exact baseToLaurent_hasPoles R p
  · intro hp
    have hs : ↑p.coeff.support ⊆ Set.range castExponent := by
      intro e he
      apply (mem_range_castExponent e).mpr
      intro i
      by_contra hi
      exact (Finsupp.mem_support_iff.mp he) (hp e i (by simp) (lt_of_not_ge hi))
    exact ⟨AddMonoidAlgebra.comapDomain castExponent castExponent_injective p,
      AddMonoidAlgebra.mapDomain_comapDomain hs castExponent_injective⟩

def T (e : LaurentExponent) : Laurent (R := R) := AddMonoidAlgebra.single e 1

@[simp] theorem T_zero : T R 0 = 1 := rfl
@[simp] theorem T_mul (a b : LaurentExponent) : T R a * T R b = T R (a + b) := by
  simp [T, AddMonoidAlgebra.single_mul_single]
@[simp] theorem T_pow (e : LaurentExponent) (n : ℕ) : (T R e)^n = T R (n • e) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, ih, T_mul, succ_nsmul]

theorem T_isUnit (e : LaurentExponent) : IsUnit (T R e) := by
  refine ⟨⟨T R e, T R (-e), ?_, ?_⟩, rfl⟩ <;> simp

@[simp] theorem coeff_mul_T (p : Laurent (R := R)) (a e : LaurentExponent) :
    (p * T R a).coeff e = p.coeff (e - a) := by
  simp [T, AddMonoidAlgebra.coeff_mul_single_apply, sub_eq_add_neg]

def openExponent (s : Finset (Fin 3)) : LaurentExponent := fun i ↦ if i ∈ s then 1 else 0

@[simp] theorem openExponent_empty : openExponent ∅ = 0 := by
  ext i
  simp [openExponent]


@[simp] theorem castExponent_single (i : Fin 3) :
    castExponent (Finsupp.single i 1) = openExponent {i} := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_X (i : Fin 3) :
    baseToLaurent R (X i) = T R (openExponent {i}) := by
  change baseToLaurent R (monomial (Finsupp.single i 1) 1) = _
  simp [T]

theorem openExponent_insert (i : Fin 3) (s : Finset (Fin 3)) (hi : i ∉ s) :
    openExponent (insert i s) = openExponent {i} + openExponent s := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent, hi]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_baseProduct (s : Finset (Fin 3)) :
    baseToLaurent R (baseProduct R s) = T R (openExponent s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseProduct]
  | @insert i s hi ih =>
      rw [baseProduct, Finset.prod_insert hi, map_mul]
      change baseToLaurent R (X i) * baseToLaurent R (baseProduct R s) = _
      rw [baseToLaurent_X, ih, T_mul, openExponent_insert i s hi]

def coordinateLocalization (s : Finset (Fin 3)) := Localization.Away (baseProduct R s)

instance (s : Finset (Fin 3)) : CommRing (coordinateLocalization R s) :=
  inferInstanceAs (CommRing (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 3)) : Algebra (Base R) (coordinateLocalization R s) :=
  inferInstanceAs (Algebra (Base R) (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 3)) : IsLocalization.Away (baseProduct R s) (coordinateLocalization R s) :=
  inferInstanceAs (IsLocalization.Away (baseProduct R s) (Localization.Away (baseProduct R s)))

def localizationToLaurent (s : Finset (Fin 3)) :
    coordinateLocalization R s →+* Laurent (R := R) :=
  IsLocalization.Away.lift (baseProduct R s)
    (show IsUnit ((baseToLaurent R).toRingHom (baseProduct R s)) by
      change IsUnit (baseToLaurent R (baseProduct R s))
      rw [baseToLaurent_baseProduct]
      exact T_isUnit R _)

@[simp] theorem localizationToLaurent_algebraMap (s : Finset (Fin 3)) (p : Base R) :
    localizationToLaurent R s (algebraMap (Base R) (coordinateLocalization R s) p) =
      baseToLaurent R p := IsLocalization.Away.lift_eq _ _ _

theorem localizationToLaurent_injective (s : Finset (Fin 3)) :
    Function.Injective (localizationToLaurent R s) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq
    (Submonoid.powers (baseProduct R s)) (localizationToLaurent R s)).mpr
  intro p q
  constructor
  · intro h
    exact congrArg (localizationToLaurent R s) h
  · intro h
    simp only [localizationToLaurent_algebraMap] at h
    exact congrArg (algebraMap (Base R) (coordinateLocalization R s))
      (baseToLaurent_injective R h)

theorem localizationToLaurent_hasPoles (s : Finset (Fin 3))
    (z : coordinateLocalization R s) : HasPoles s (localizationToLaurent R s z) := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj (baseProduct R s) z
  have hh := congrArg (localizationToLaurent R s) hp
  simp only [map_mul, map_pow, localizationToLaurent_algebraMap,
    baseToLaurent_baseProduct, T_pow] at hh
  have hrep : localizationToLaurent R s z =
      baseToLaurent R p * T R (-(n • openExponent s)) := by
    have hm := congrArg (fun t ↦ t * T R (-(n • openExponent s))) hh
    simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm
  rw [hrep]
  intro e i hi hneg
  rw [coeff_mul_T]
  apply baseToLaurent_hasPoles R p _ i (by simp)
  simpa [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, openExponent, hi] using hneg

/-- A single common monomial denominator clears the poles of any finite
Laurent sum; its existence is proved from the finite coefficient support. -/
theorem exists_clear_poles (s : Finset (Fin 3)) (p : Laurent (R := R))
    (hp : HasPoles s p) :
    ∃ n : ℕ, HasPoles ∅ (p * T R (n • openExponent s)) := by
  classical
  let n := p.coeff.support.sup (fun e ↦ Finset.univ.sup (fun i : Fin 3 ↦ (-e i).toNat))
  refine ⟨n, ?_⟩
  intro e i _ hneg
  rw [coeff_mul_T]
  by_contra hne
  have hs : e - n • openExponent s ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hne
  by_cases hi : i ∈ s
  · have hbound : (-((e - n • openExponent s) i)).toNat ≤ n :=
      (Finset.le_sup (f := fun i : Fin 3 ↦ (-((e - n • openExponent s) i)).toNat)
        (Finset.mem_univ i)).trans
          (Finset.le_sup (f := fun e : LaurentExponent ↦
            Finset.univ.sup (fun i : Fin 3 ↦ (-e i).toNat)) hs)
    have hcast : ((-((e - n • openExponent s) i)).toNat : ℤ) ≤ (n : ℤ) := by
      exact_mod_cast hbound
    have hle := (Int.self_le_toNat (-((e - n • openExponent s) i))).trans hcast
    have hexp : (n • openExponent s) i = (n : ℤ) := by
      change n • (openExponent s i) = (n : ℤ)
      simp [openExponent, hi]
    change -(e i - (n • openExponent s) i) ≤ (n : ℤ) at hle
    rw [hexp] at hle
    omega
  · apply hne
    apply hp _ i hi
    simpa [Pi.sub_apply, Pi.smul_apply, openExponent, hi] using hneg

theorem mem_range_localizationToLaurent (s : Finset (Fin 3)) (p : Laurent (R := R)) :
    p ∈ Set.range (localizationToLaurent R s) ↔ HasPoles s p := by
  constructor
  · rintro ⟨z, rfl⟩
    exact localizationToLaurent_hasPoles R s z
  · intro hp
    obtain ⟨n, hn⟩ := exists_clear_poles R s p hp
    obtain ⟨a, ha⟩ := (mem_range_baseToLaurent R _).mpr hn
    let den : Submonoid.powers (baseProduct R s) := ⟨baseProduct R s ^ n, n, rfl⟩
    let z := IsLocalization.mk' (coordinateLocalization R s) a den
    refine ⟨z, ?_⟩
    have hz : z * algebraMap (Base R) (coordinateLocalization R s) (baseProduct R s ^ n) =
        algebraMap (Base R) (coordinateLocalization R s) a :=
      IsLocalization.mk'_spec (coordinateLocalization R s) a den
    have hh := congrArg (localizationToLaurent R s) hz
    simp only [map_mul, localizationToLaurent_algebraMap, map_pow,
      baseToLaurent_baseProduct, T_pow] at hh
    rw [ha] at hh
    have hm := congrArg (fun t ↦ t * T R (-(n • openExponent s))) hh
    simpa only [mul_assoc, T_mul, add_neg_cancel, T_zero, mul_one] using hm

end CycleQ2SeedCechLocalization

end

section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedCechLocalizedBasis

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization

variable (R : Type*) [CommRing R]

instance seedLocalBaseAlgebra (r ι : R) (s : Finset (Fin 3)) :
    Algebra (coordinateLocalization R s) (SeedLocal R r ι s) :=
  localizationAlgebra (Rₘ := coordinateLocalization R s) (Sₘ := SeedLocal R r ι s)
    (Submonoid.powers (baseProduct R s)) (SeedRing r ι)

instance seedLocalBaseTower (r ι : R) (s : Finset (Fin 3)) :
    IsScalarTower (Base R) (coordinateLocalization R s) (SeedLocal R r ι s) :=
  isScalarTower_localizationAlgebra (Rₘ := coordinateLocalization R s)
    (Sₘ := SeedLocal R r ι s) (Submonoid.powers (baseProduct R s)) (SeedRing r ι)

def localizedBasis [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    Module.Basis ShiftIndex (coordinateLocalization R s) (SeedLocal R r ι s) :=
  (seedBasis R r ι).localizationLocalization (coordinateLocalization R s)
    (Submonoid.powers (baseProduct R s)) (SeedLocal R r ι s)

@[simp] theorem localizedBasis_apply [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (ab : ShiftIndex) :
    localizedBasis R r ι s ab = algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (seedBasis R r ι ab) := by
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

@[simp] theorem localizedBasis_repr_algebraMap [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : SeedRing r ι) (ab : ShiftIndex) :
    (localizedBasis R r ι s).repr (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) ab =
      algebraMap (Base R) (coordinateLocalization R s) ((seedBasis R r ι).repr p ab) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

def localizedCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →+ (ShiftIndex → Laurent (R := R)) where
  toFun p ab := localizationToLaurent R s ((localizedBasis R r ι s).repr p ab)
  map_zero' := by ext ab; simp
  map_add' p q := by ext ab; simp

theorem localizedCoordinates_injective [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    Function.Injective (localizedCoordinates R r ι s) := by
  intro p q hpq
  apply (localizedBasis R r ι s).repr.injective
  ext ab
  exact localizationToLaurent_injective R s (congrFun hpq ab)

theorem localizedCoordinates_hasPoles [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) (ab : ShiftIndex) :
    HasPoles s (localizedCoordinates R r ι s p ab) :=
  localizationToLaurent_hasPoles R s _

theorem mem_range_localizedCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : ShiftIndex → Laurent (R := R)) :
    p ∈ Set.range (localizedCoordinates R r ι s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p, rfl⟩ ab
    exact localizedCoordinates_hasPoles R r ι s p ab
  · intro hp
    choose a ha using fun ab ↦ (mem_range_localizationToLaurent R s (p ab)).mpr (hp ab)
    refine ⟨(localizedBasis R r ι s).repr.symm (Finsupp.equivFunOnFinite.symm a), ?_⟩
    funext ab
    change localizationToLaurent R s
      ((localizedBasis R r ι s).repr ((localizedBasis R r ι s).repr.symm
        (Finsupp.equivFunOnFinite.symm a)) ab) = p ab
    simpa using ha ab

@[simp] theorem localizedCoordinates_algebraMap [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (p : SeedRing r ι) (ab : ShiftIndex) :
    localizedCoordinates R r ι s (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) ab =
      baseToLaurent R ((seedBasis R r ι).repr p ab) := by
  simp [localizedCoordinates]

@[simp] theorem localizedCoordinates_smul [Nontrivial R] (r ι : R)
    (s : Finset (Fin 3)) (a : coordinateLocalization R s) (p : SeedLocal R r ι s)
    (ab : ShiftIndex) :
    localizedCoordinates R r ι s (a • p) ab =
      localizationToLaurent R s a * localizedCoordinates R r ι s p ab := by
  simp [localizedCoordinates, Finsupp.smul_apply, smul_eq_mul]

/-- Exactness of the three-open complex on actual localized seed rings,
expressed through their injective common Laurent coordinates. -/
theorem localized_nineSummand_kernel [Nontrivial R] (r ι : R) (g : LaurentGrade)
    (p01 : SeedLocal R r ι {0, 1}) (p02 : SeedLocal R r ι {0, 2})
    (p12 : SeedLocal R r ι {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {1, 2} p12 ab))
    (hc : ∀ ab, localizedCoordinates R r ι {0, 1} p01 ab -
      localizedCoordinates R r ι {0, 2} p02 ab +
      localizedCoordinates R r ι {1, 2} p12 ab = 0) :
    ∃ (q0 : SeedLocal R r ι {0}) (q1 : SeedLocal R r ι {1})
      (q2 : SeedLocal R r ι {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {2} q2 ab)) ∧
      (∀ ab, localizedCoordinates R r ι {0, 1} p01 ab =
        localizedCoordinates R r ι {1} q1 ab - localizedCoordinates R r ι {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R r ι {0, 2} p02 ab =
        localizedCoordinates R r ι {2} q2 ab - localizedCoordinates R r ι {0} q0 ab) ∧
      (∀ ab, localizedCoordinates R r ι {1, 2} p12 ab =
        localizedCoordinates R r ι {2} q2 ab - localizedCoordinates R r ι {1} q1 ab) := by
  obtain ⟨q0, q1, q2, h0, h1, h2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    nineSummand_kernel g
      (localizedCoordinates R r ι {0, 1} p01)
      (localizedCoordinates R r ι {0, 2} p02)
      (localizedCoordinates R r ι {1, 2} p12)
      (localizedCoordinates_hasPoles R r ι {0, 1} p01)
      (localizedCoordinates_hasPoles R r ι {0, 2} p02)
      (localizedCoordinates_hasPoles R r ι {1, 2} p12)
      hg01 hg02 hg12 hc
  obtain ⟨q0', hq0⟩ := (mem_range_localizedCoordinates R r ι {0} q0).mpr h0
  obtain ⟨q1', hq1⟩ := (mem_range_localizedCoordinates R r ι {1} q1).mpr h1
  obtain ⟨q2', hq2⟩ := (mem_range_localizedCoordinates R r ι {2} q2).mpr h2
  refine ⟨q0', q1', q2', ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hq0, hq1, hq2] <;> assumption

end CycleQ2SeedCechLocalizedBasis

end

namespace CycleQ2GeometricFreeCoordinateCech

open MvPolynomial CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization
open scoped TensorProduct

variable (R : Type*) [CommRing R]
variable (M : Type*) [AddCommGroup M] [Module (Base R) M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev LocalModule (s : Finset (Fin 3)) := coordinateLocalization R s ⊗[Base R] M

def baseRestriction {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateLocalization R s →ₐ[Base R] coordinateLocalization R t where
  __ := IsLocalization.Away.lift (S := coordinateLocalization R s) (baseProduct R s)
    (IsLocalization.Away.isUnit_of_dvd (S := coordinateLocalization R t) (baseProduct R t)
      (Finset.prod_dvd_prod_of_subset s t (fun i : Fin 3 => (X i : Base R)) hst))
  commutes' x := IsLocalization.Away.lift_eq _ _ x

@[simp] theorem baseRestriction_base {s t : Finset (Fin 3)} (hst : s ⊆ t) (a : Base R) :
    baseRestriction R hst (algebraMap (Base R) (coordinateLocalization R s) a) =
      algebraMap (Base R) (coordinateLocalization R t) a :=
  (baseRestriction R hst).commutes a

@[simp] theorem laurent_baseRestriction {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (a : coordinateLocalization R s) :
    localizationToLaurent R t (baseRestriction R hst a) = localizationToLaurent R s a := by
  have hh : (localizationToLaurent R t).comp (baseRestriction R hst).toRingHom =
      localizationToLaurent R s := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (baseProduct R s))
    apply RingHom.ext
    intro p
    change localizationToLaurent R t
      (baseRestriction R hst (algebraMap (Base R) (coordinateLocalization R s) p)) =
      localizationToLaurent R s (algebraMap (Base R) (coordinateLocalization R s) p)
    rw [baseRestriction_base, localizationToLaurent_algebraMap,
      localizationToLaurent_algebraMap]
  exact RingHom.congr_fun hh a

def restriction {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    LocalModule R M s →ₗ[Base R] LocalModule R M t :=
  TensorProduct.map (baseRestriction R hst).toLinearMap LinearMap.id

variable {R M}

def coordinates (b : Module.Basis ι (Base R) M) (s : Finset (Fin 3)) :
    LocalModule R M s →+ (ι → Laurent (R := R)) where
  toFun p i := localizationToLaurent R s (TensorProduct.equivFinsuppOfBasisRight b p i)
  map_zero' := by ext i; simp
  map_add' p q := by ext i; simp

omit [Fintype ι] in
theorem coordinates_injective (b : Module.Basis ι (Base R) M) (s : Finset (Fin 3)) :
    Function.Injective (coordinates b s) := by
  intro p q hpq
  apply (TensorProduct.equivFinsuppOfBasisRight b).injective
  ext i
  exact localizationToLaurent_injective R s (congrFun hpq i)

omit [Fintype ι] in
theorem coordinates_hasPoles (b : Module.Basis ι (Base R) M) (s : Finset (Fin 3))
    (p : LocalModule R M s) (i : ι) : HasPoles s (coordinates b s p i) :=
  localizationToLaurent_hasPoles R s _

theorem coordinates_range (b : Module.Basis ι (Base R) M) (s : Finset (Fin 3))
    (p : ι → Laurent (R := R)) :
    p ∈ Set.range (coordinates b s) ↔ ∀ i, HasPoles s (p i) := by
  constructor
  · rintro ⟨p, rfl⟩ i
    exact coordinates_hasPoles b s p i
  · intro hp
    choose z hz using fun i => (mem_range_localizationToLaurent R s (p i)).mpr (hp i)
    refine ⟨(TensorProduct.equivFinsuppOfBasisRight b).symm
      (Finsupp.equivFunOnFinite.symm z), ?_⟩
    funext i
    change localizationToLaurent R s
      (TensorProduct.equivFinsuppOfBasisRight b
        ((TensorProduct.equivFinsuppOfBasisRight b).symm
          (Finsupp.equivFunOnFinite.symm z)) i) = p i
    rw [LinearEquiv.apply_symm_apply]
    exact hz i

@[simp] theorem coordinates_restriction (b : Module.Basis ι (Base R) M)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : LocalModule R M s) :
    coordinates b t (restriction R M hst p) = coordinates b s p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
      funext i
      change localizationToLaurent R t
        (TensorProduct.equivFinsuppOfBasisRight b
          (TensorProduct.map (baseRestriction R hst).toLinearMap LinearMap.id (a ⊗ₜ m)) i) =
        localizationToLaurent R s (TensorProduct.equivFinsuppOfBasisRight b (a ⊗ₜ m) i)
      rw [TensorProduct.map_tmul]
      simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
        LinearMap.id_apply, AlgHom.toLinearMap_apply, Algebra.smul_def,
        map_mul, localizationToLaurent_algebraMap, laurent_baseRestriction]
  | add p q hp hq => simp only [map_add, hp, hq]

/-- The coordinate Čech complex of any actual finite free base module is
exact in degree one. The proof supplies actual localized primitives. -/
theorem firstCech_exact (b : Module.Basis ι (Base R) M)
    (p01 : LocalModule R M {0,1}) (p02 : LocalModule R M {0,2})
    (p12 : LocalModule R M {1,2})
    (hc : restriction R M (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by simp) p01 -
      restriction R M (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p02 +
      restriction R M (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by simp) p12 = 0) :
    ∃ (q0 : LocalModule R M {0}) (q1 : LocalModule R M {1}) (q2 : LocalModule R M {2}),
      p01 = restriction R M (show ({1} : Finset (Fin 3)) ⊆ {0,1} by decide) q1 -
        restriction R M (show ({0} : Finset (Fin 3)) ⊆ {0,1} by decide) q0 ∧
      p02 = restriction R M (show ({2} : Finset (Fin 3)) ⊆ {0,2} by decide) q2 -
        restriction R M (show ({0} : Finset (Fin 3)) ⊆ {0,2} by decide) q0 ∧
      p12 = restriction R M (show ({2} : Finset (Fin 3)) ⊆ {1,2} by decide) q2 -
        restriction R M (show ({1} : Finset (Fin 3)) ⊆ {1,2} by decide) q1 := by
  have heq (i : ι) : coordinates b {0,1} p01 i - coordinates b {0,2} p02 i +
      coordinates b {1,2} p12 i = 0 := by
    have hh := congrArg (fun p => coordinates b Finset.univ p i) hc
    simpa only [map_add, map_sub, map_zero, coordinates_restriction,
      Pi.add_apply, Pi.sub_apply, Pi.zero_apply] using hh
  let v0 : ι → Laurent (R := R) := fun i =>
    nonnegativePart (coordinates b {0,1} p01 i) - coordinates b {0,1} p01 i
  let v1 : ι → Laurent (R := R) := fun i => nonnegativePart (coordinates b {0,1} p01 i)
  let v2 : ι → Laurent (R := R) := fun i =>
    coordinates b {1,2} p12 i + nonnegativePart (coordinates b {0,1} p01 i)
  have hlocal (i : ι) := threeOpen_kernel
    (coordinates b {0,1} p01 i) (coordinates b {0,2} p02 i) (coordinates b {1,2} p12 i)
    (coordinates_hasPoles b _ p01 i) (coordinates_hasPoles b _ p02 i)
    (coordinates_hasPoles b _ p12 i) (heq i)
  obtain ⟨q0,h0⟩ := (coordinates_range b {0} v0).mpr (fun i => (hlocal i).1)
  obtain ⟨q1,h1⟩ := (coordinates_range b {1} v1).mpr (fun i => (hlocal i).2.1)
  obtain ⟨q2,h2⟩ := (coordinates_range b {2} v2).mpr (fun i => (hlocal i).2.2.1)
  refine ⟨q0,q1,q2,?_,?_,?_⟩
  · apply coordinates_injective b {0,1}
    simp only [map_sub, coordinates_restriction, h0, h1]
    funext i
    exact (hlocal i).2.2.2.1
  · apply coordinates_injective b {0,2}
    simp only [map_sub, coordinates_restriction, h0, h2]
    funext i
    exact (hlocal i).2.2.2.2.1
  · apply coordinates_injective b {1,2}
    simp only [map_sub, coordinates_restriction, h1, h2]
    funext i
    exact (hlocal i).2.2.2.2.2

end CycleQ2GeometricFreeCoordinateCech
