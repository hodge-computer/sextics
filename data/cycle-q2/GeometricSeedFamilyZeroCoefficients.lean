import Proposal.GeometricSeedProjectiveSpecialization

/-!
# Actual coefficient primes and zero specialization in the cubic family

The original parameter morphism is computed on its actual projective
points. Every point over the zero-coefficient parameter contains the
kernel of the original coefficient evaluation. For a polynomial ideal
with this coefficient-kernel property, specialization followed by the
original complex coefficient inclusion is the identity modulo that ideal.
Consequently its contracted complex prime contains the exact specialized
equation and derivatives used in the subsequent Jacobian-cover argument.

No identification of the global scheme fiber is assumed. These are
coefficient and prime-transport statements for the original family.
Source-only draft: no Lean elaboration, compilation, or kernel replay
has been run. Prepared for `fqlx` with OpenAI ChatGPT assistance, following
Ben Diamond's geometric route and the earlier incidence-prime arguments.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFamilyZeroCoefficients

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2GeometricSeedSmooth CycleQ2SeedCubicFamily
  CycleQ2SeedProjectiveFamily CycleQ2SeedProjectiveSpecialization

private theorem basicOpenToSpec_toLRSHom (r : ℂ) (f : FamilyRing r) :
    (Proj.basicOpenToSpec (familyGrade r) f).toLRSHom =
      ProjectiveSpectrum.Proj.toSpec (familyGrade r) f := by
  refine Eq.trans ?_
    (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
  dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
  simp only [Category.assoc, ← Spec.map_comp]
  rfl

/-- Coefficient membership for the original projective parameter map. -/
theorem coefficient_mem_iff (r : ℂ) (x : family r) (a : ParameterRing) :
    a ∈ (familyToParameters r x).asIdeal ↔
      algebraMap ParameterRing (FamilyRing r) a ∈ x.asHomogeneousIdeal.toIdeal := by
  let x₁ : (Proj.basicOpen (familyGrade r) (1 : FamilyRing r)).toScheme :=
    ((Scheme.topIso (family r)).inv ≫
      (Scheme.isoOfEq (family r) (Proj.basicOpen_one (familyGrade r))).inv) x
  have hx₁ : x₁.1 = x := by
    change ((Scheme.topIso (family r)).inv ≫
      (Scheme.isoOfEq (family r) (Proj.basicOpen_one (familyGrade r))).inv ≫
        (Proj.basicOpen (familyGrade r) (1 : FamilyRing r)).ι) x = x
    simp only [Scheme.isoOfEq_inv_ι, Scheme.toIso_inv_ι]
  change fromZeroRingHom (familyGrade r) (Submonoid.powers (1 : FamilyRing r))
      (parameterCoefficient r a) ∈
        ((Proj.basicOpenToSpec (familyGrade r) (1 : FamilyRing r)).toLRSHom.base
          x₁).asIdeal ↔ _
  rw [basicOpenToSpec_toLRSHom]
  change HomogeneousLocalization.mk
      (⟨0, parameterCoefficient r a, 1, one_mem _⟩ :
        NumDenSameDeg (familyGrade r) (Submonoid.powers (1 : FamilyRing r))) ∈
        ((ProjectiveSpectrum.Proj.toSpec (familyGrade r) (1 : FamilyRing r)).base
          x₁).asIdeal ↔ _
  rw [ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply]
  simpa only [parameterCoefficient_coe, hx₁]

/-- Every actual point over zero contains every zero-evaluation coefficient. -/
theorem zero_kernel_mem_of_over_zero (r : ℂ) (x : family r)
    (s : Spec (CommRingCat.of ℂ))
    (hx : familyToParameters r x = zeroParameterMorphism s)
    (a : ParameterRing) (ha : zeroCoefficientMap a = 0) :
    algebraMap ParameterRing (FamilyRing r) a ∈ x.asHomogeneousIdeal.toIdeal := by
  apply (coefficient_mem_iff r x a).mp
  rw [hx]
  change zeroCoefficientMap a ∈ s.asIdeal
  rw [ha]
  exact Ideal.zero_mem _

/-- Contract through the original complex coefficient inclusion. -/
def specializedPrime (P : Ideal FamilyPolynomial) : Ideal SeedPolynomial :=
  P.comap coefficientLift

instance specializedPrime_isPrime (P : Ideal FamilyPolynomial) [P.IsPrime] :
    (specializedPrime P).IsPrime :=
  Ideal.IsPrime.comap coefficientLift

@[simp] theorem coordinate_mem_specializedPrime_iff
    (P : Ideal FamilyPolynomial) (j : Fin 5) :
    (X j : SeedPolynomial) ∈ specializedPrime P ↔ (X j : FamilyPolynomial) ∈ P := by
  change MvPolynomial.map (algebraMap ℂ ParameterRing) (X j) ∈ P ↔ _
  rw [MvPolynomial.map_X]

/-- Zero specialization is the identity modulo any ideal containing
the actual zero-coefficient kernel; no kernel presentation is needed. -/
theorem quotient_specialization (P : Ideal FamilyPolynomial)
    (hcoeff : ∀ a : ParameterRing, zeroCoefficientMap a = 0 → C a ∈ P)
    (p : FamilyPolynomial) :
    Ideal.Quotient.mk P (coefficientLift (zeroPolynomialSpecialization p)) =
      Ideal.Quotient.mk P p := by
  have h : (Ideal.Quotient.mk P).comp
      (coefficientLift.comp zeroPolynomialSpecialization) = Ideal.Quotient.mk P := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, coefficientLift, zeroPolynomialSpecialization,
        MvPolynomial.map_C]
      apply Ideal.Quotient.eq.mpr
      have hz : zeroCoefficientMap
          (algebraMap ℂ ParameterRing (zeroCoefficientMap a) - a) = 0 := by
        rw [map_sub, zeroCoefficientMap_complex, sub_self]
      simpa only [map_sub] using
        hcoeff (algebraMap ℂ ParameterRing (zeroCoefficientMap a) - a) hz
    · intro j
      simp only [RingHom.comp_apply, coefficientLift, zeroPolynomialSpecialization,
        MvPolynomial.map_X]
  exact RingHom.congr_fun h p

theorem specialization_mem (P : Ideal FamilyPolynomial)
    (hcoeff : ∀ a : ParameterRing, zeroCoefficientMap a = 0 → C a ∈ P)
    (p : FamilyPolynomial) (hp : p ∈ P) :
    zeroPolynomialSpecialization p ∈ specializedPrime P := by
  change coefficientLift (zeroPolynomialSpecialization p) ∈ P
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [quotient_specialization P hcoeff]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hp

/-- Differentiation in a geometric variable commutes with the actual
zero-coefficient specialization. -/
theorem zeroSpecialization_pderiv_equation (r : ℂ) (j : Fin 5) :
    zeroPolynomialSpecialization (pderiv j (familyEquation r)) =
      pderiv j (seedFamily r 0) := by
  change MvPolynomial.map zeroCoefficientMap (pderiv j (familyEquation r)) = _
  rw [← MvPolynomial.pderiv_map]
  change pderiv j (zeroPolynomialSpecialization (familyEquation r)) = _
  rw [zeroPolynomialSpecialization_equation]

end CycleQ2SeedFamilyZeroCoefficients

end

#print axioms CycleQ2SeedFamilyZeroCoefficients.coefficient_mem_iff
#print axioms CycleQ2SeedFamilyZeroCoefficients.zero_kernel_mem_of_over_zero
#print axioms CycleQ2SeedFamilyZeroCoefficients.quotient_specialization
#print axioms CycleQ2SeedFamilyZeroCoefficients.zeroSpecialization_pderiv_equation
