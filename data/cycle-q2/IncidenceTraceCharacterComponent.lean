import Proposal.SeedNormalConnectingClass
import Proposal.UniversalSurfaceCechBaseChange

/-!
# Persistence and orbit pairing on the incidence trace component
-/

set_option Elab.async false

/- Component: continuation_20261112/IncidenceTraceCechPersistence.lean -/
section
/-!
# Actual top-Cech persistence on the finite pointed incidence trace family

The pointedness already proved for the literal trace point is a kernel
containment on the polynomial parameter ring.  We extend it across the two
inverted leading coefficients and then apply the proved seven-coordinate
description of actual top Cech cohomology.

This theorem transports a supplied universal class with its identified seed
specialization.  It does not identify an Abel--Jacobi map, and it does not
assert that the fixed-sextic family's normal obstruction is nonzero.  The
relevant prospective input is an ambient-test class, which must be constructed
and compared with the seed normal/residue calculation separately.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceCechPersistence

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceTraceDerivative
  CycleQ2IncidenceTraceGenericPoint CycleQ2IncidenceTraceGeometry
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceImageLine
  CycleQ2SeedQuotientFiniteFree CycleQ2UniversalSurface
  CycleQ2UniversalSurfaceNormalization CycleQ2UniversalSurfaceTopCech
  CycleQ2UniversalSurfaceCechPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

/-- Kernel containment of the two coefficient maps survives localization.
No specialization of the generic field itself is asserted or needed. -/
theorem kernel_containment_away
    {R A S T : Type*} [CommRing R] [CommRing A] [CommRing S] [CommRing T]
    [Algebra R A] (r : R) [IsLocalization.Away r A]
    (generic : A →+* S) (specialization : A →+* T)
    (hpointed : ∀ p : R, generic (algebraMap R A p) = 0 →
      specialization (algebraMap R A p) = 0) :
    ∀ a : A, generic a = 0 → specialization a = 0 := by
  intro a ha
  obtain ⟨n,p,hp⟩ := IsLocalization.Away.surj r a
  have hpg : generic (algebraMap R A p) = 0 := by
    rw [← hp, map_mul, ha, zero_mul]
  have hps := hpointed p hpg
  have hmul : specialization a * specialization (algebraMap R A r) ^ n = 0 := by
    simpa only [map_mul, map_pow] using (congrArg specialization hp).trans hps
  have hu : IsUnit (specialization (algebraMap R A r) ^ n) :=
    ((IsLocalization.Away.algebraMap_isUnit (S := A) r).map specialization).pow n
  exact hu.mul_left_eq_zero.mp hmul

variable {S : Type} [CommRing S] [Algebra ℂ S]

def pointSpecialization (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) : ParameterRing ℂ →ₐ[ℂ] S :=
  specialization (pointCubic y) (pointSextic y)
    (point_leading_units y hy).1 (point_leading_units y hy).2 (pointMatrix y)

@[simp] theorem pointSpecialization_polynomial (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (p : ParameterPolynomial ℂ) :
    pointSpecialization y hy (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) p) =
      aeval y p := by
  rw [pointSpecialization, specialization_polynomial, polynomialSpecialization,
    coefficientPoint_components]

@[simp] theorem pointSpecialization_cubic (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (e : FullInvariantIndex 3) :
    pointSpecialization y hy (cubicCoefficient ℂ e) = pointCubic y e := by
  exact specialization_cubicCoefficient _ _ _ _ _ e

@[simp] theorem pointSpecialization_sextic (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (e : FullInvariantIndex 6) :
    pointSpecialization y hy (sexticCoefficient ℂ e) = pointSextic y e := by
  exact specialization_sexticCoefficient _ _ _ _ _ e

@[simp] theorem seedSpecialization_polynomial (p : ParameterPolynomial ℂ) :
    seedSpecialization ℂ (57 : ℂ) Complex.I
      (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) p) =
      eval (seedPoint (57 : ℂ) Complex.I) p := by
  rw [seedSpecialization, specialization_polynomial]
  rfl

theorem pointSurface_ideal_normalized (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) :
    equationsIdeal
      (MvPolynomial.map (pointMap y) CycleQ2IncidenceBasepointOpen.familyH)
      (MvPolynomial.map (pointMap y) CycleQ2IncidenceBasepointOpen.familyF) =
      surfaceIdeal S
        (fun i => pointSpecialization y hy (universalCubicTail ℂ i))
        (fun i => pointSpecialization y hy (universalSexticTail ℂ i)) := by
  rw [pointMap_familyH, pointMap_familyF]
  simpa only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    pointSpecialization_cubic, pointSpecialization_sextic] using
    mapped_universalIdeal_normalized ℂ (pointSpecialization y hy).toRingHom

/-- The literal surface supporting the already-constructed image line is
the normalized surface used in the actual Cech calculation. -/
def pointSurfaceEquiv (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) :
    PointSurface y ≃ₐ[Base S]
      SurfaceRing S
        (fun i => pointSpecialization y hy (universalCubicTail ℂ i))
        (fun i => pointSpecialization y hy (universalSexticTail ℂ i)) :=
  Ideal.quotientEquivAlgOfEq (Base S) (pointSurface_ideal_normalized y hy)

@[simp] theorem pointSurfaceEquiv_mk (y : ParameterIndex → S)
    (hy : IsUnit (aeval y (leadingProduct ℂ))) (p : Poly S) :
    pointSurfaceEquiv y hy (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := rfl

variable [Algebra TraceRing S] [IsScalarTower ℂ TraceRing S]

theorem pointedTrace_polynomial_kernel
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)
    (p : ParameterPolynomial ℂ) (hp : aeval (tracePointValue B z) p = 0) :
    eval (seedPoint (57 : ℂ) Complex.I) p = 0 := by
  have hp' : aeval (tracePointValue B z)
      (MvPolynomial.map (C : ℂ →+* TraceRing) p) = 0 := by
    rwa [eval_coefficient_map]
  have hs := hz.2 (MvPolynomial.map (C : ℂ →+* TraceRing) p) hp'
  simpa only [eval_coefficientMap] using hs

theorem pointedTrace_localized_kernel
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z) :
    ∀ a : ParameterRing ℂ,
      pointSpecialization (tracePointValue B z) (tracePoint_leading_unit P B c z hz.1) a = 0 →
        seedSpecialization ℂ (57 : ℂ) Complex.I a = 0 := by
  apply kernel_containment_away (leadingProduct ℂ)
    (pointSpecialization (tracePointValue B z) (tracePoint_leading_unit P B c z hz.1)).toRingHom
    (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
  intro p hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, pointSpecialization_polynomial] at hp
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, seedSpecialization_polynomial]
  exact pointedTrace_polynomial_kernel P B c z hz p hp

abbrev UniversalTopCech :=
  ActualTopCechQuotient (ParameterRing ℂ) (universalCubicTail ℂ) (universalSexticTail ℂ)

/-- Actual cohomology persistence for the proved finite pointed trace family.
The class must be one universal class with a nonzero identified seed image;
coefficient motion alone is not used as a substitute for that identification. -/
theorem tracePoint_top_nonzero [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)
    (ξ : UniversalTopCech)
    (hξ : actualTopMap (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
      (universalCubicTail ℂ) (universalSexticTail ℂ) ξ ≠ 0) :
    actualTopMap
      (pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1)).toRingHom
      (universalCubicTail ℂ) (universalSexticTail ℂ) ξ ≠ 0 := by
  apply nonzero_generic_of_nonzero_specialization
    (pointSpecialization (tracePointValue B z)
      (tracePoint_leading_unit P B c z hz.1)).toRingHom
    (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom
    (pointedTrace_localized_kernel P B c z hz)
    (universalCubicTail ℂ) (universalSexticTail ℂ) ξ hξ

end CycleQ2IncidenceTraceCechPersistence

#print axioms CycleQ2IncidenceTraceCechPersistence.pointSurfaceEquiv_mk
#print axioms CycleQ2IncidenceTraceCechPersistence.pointedTrace_localized_kernel
#print axioms CycleQ2IncidenceTraceCechPersistence.tracePoint_top_nonzero
end
end

/- Component: continuation_20261112/IncidenceSurfaceGradientOpen.lean -/
section
/-! The actual pointed trace surface is covered by its genuine Jacobian
minor opens. The seed cover is propagated by a proved coefficient open,
using pointedness rather than assuming smoothness of a moving surface. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceSurfaceGradientOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousPrimeCoverOpen
open CycleQ2IncidenceBasepointOpen (Coeff familyF familyH seedEvaluation)

theorem seed_prime_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hP : generatorIdeal (fun i => map seedEvaluation (generators i)) ≤ P) :
    ∀ j : Fin 5, X j ∈ P := by
  have hmem (i : Index) : map seedEvaluation (generators i) ∈ P :=
    hP (Ideal.subset_span ⟨i,rfl⟩)
  have hF : smoothF (57:ℂ) Complex.I ∈ P := by
    simpa only [generators,Matrix.cons_val_zero,familyF_seed] using hmem (Sum.inl 0)
  have hh : smoothH Complex.I ∈ P := by
    simpa only [generators,Matrix.cons_val_one,Matrix.cons_val_zero,familyH_seed]
      using hmem (Sum.inl 1)
  intro j
  by_contra hj
  obtain ⟨a,b,hab⟩ := CycleQ2SeedSurfaceGradient.prime_minor_cover P hF hh ⟨j,hj⟩
  apply hab
  have hm := hmem (Sum.inr (a,b))
  rw [generators,map_pow,minor_map,familyF_seed,familyH_seed] at hm
  exact (inferInstance : P.IsPrime).mem_of_pow_mem 3 hm

/-- This open is proved nonempty by the literal r=57,theta=1 seed. -/
theorem exists_surface_minor_open : ∃ s : Coeff, seedEvaluation s=1 ∧
    ∀ (S : Type*) [CommRing S] (φ : Coeff →+* S), IsUnit (φ s) →
      ∀ (P : Ideal (Poly S)) [P.IsPrime],
        map φ familyF ∈ P → map φ familyH ∈ P →
        (∃ j : Fin 5, X j ∉ P) →
        ∃ j k : Fin 5, minor (map φ familyF) (map φ familyH) j k ∉ P := by
  obtain ⟨s,hs,hopen⟩ := exists_prime_cover_open seedEvaluation C
    CycleQ2IncidenceBasepointOpen.seedEvaluation_constant generators degree
    generators_homogeneous seed_prime_cover
  refine ⟨s,hs,?_⟩
  intro S _ φ hφ P _ hF hh hx
  by_contra hn
  push_neg at hn
  have hP : generatorIdeal (fun i => map φ (generators i)) ≤ P := by
    rw [generatorIdeal,Ideal.span_le]
    rintro _ ⟨i,rfl⟩
    cases i with
    | inl j =>
      fin_cases j
      · simpa [generators] using hF
      · simpa [generators] using hh
    | inr jk =>
      rcases jk with ⟨j,k⟩
      change map φ (minor familyF familyH j k ^ 3) ∈ P
      rw [map_pow,minor_map]
      exact Ideal.pow_mem_of_mem P (hn j k) 3 (by decide)
  obtain ⟨j,hj⟩ := hx
  exact hj (hopen S φ hφ P hP j)

theorem pointed_surface_prime_cover {L : Type*} [Field L]
    (φ : Coeff →+* L) (hpointed : ∀ a, φ a=0 → seedEvaluation a=0)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hF : map φ familyF ∈ P) (hh : map φ familyH ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, minor (map φ familyF) (map φ familyH) j k ∉ P := by
  obtain ⟨s,hs,hopen⟩ := exists_surface_minor_open
  have hu : IsUnit (φ s) := isUnit_iff_ne_zero.mpr (fun hz =>
    one_ne_zero (hs.symm.trans (hpointed s hz)))
  exact hopen L φ hu P hF hh hx

section Trace
open CycleQ2IncidenceTraceCechPersistence CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceGeometry CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceLocalDerivations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidenceTraceFieldDerivation
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {L : Type} [Field L] [Algebra TraceField L]
  [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
  [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]

/-- The actual Jacobian localizations used by actualLocalTime cover every
relevant prime of the actual finite pointed trace surface. -/
theorem actual_trace_prime_minor_cover
    (Q : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → L) (hz : IsPointedTracePoint Q B c z)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hF : actualF B z ∈ P) (hh : actualH B z ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, minor (actualF B z) (actualH B z) j k ∉ P := by
  rw [actualF_eq_specialized] at hF ⊢
  rw [actualH_eq_specialized] at hh ⊢
  apply pointed_surface_prime_cover (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
    (fun a ha => ?_) P hF hh hx
  exact pointedTrace_polynomial_kernel Q B c z hz a ha

end Trace
end CycleQ2IncidenceSurfaceGradientOpen

#print axioms CycleQ2IncidenceSurfaceGradientOpen.exists_surface_minor_open
#print axioms CycleQ2IncidenceSurfaceGradientOpen.actual_trace_prime_minor_cover
end
end

/- Component: continuation_20261112/IncidenceTraceComponent.lean -/
section
/-!
# Cohomology on the actual pointed component of the incidence trace family

We first retain the chosen extra open (in particular the actual basepoint
open), then quotient by the kernel of the constructed trace-point map.
This coefficient ring maps injectively to the generic coefficient field
and has the literal r=57,i seed specialization.  Its incidence equations
vanish, and the retained open is a unit.  An ambient test class can therefore
be defined on this component itself; no lift to the unconstrained parameter
space is required by the persistence theorem.

The geometric class and the equality of its seed image with the computed
normal/residue class remain separate construction and comparison tasks.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceComponent

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceDirection
  CycleQ2IncidenceTraceGenericPoint CycleQ2IncidenceTraceGeometry
  CycleQ2UniversalSurfaceNormalization CycleQ2UniversalSurfaceTopCech
  CycleQ2UniversalSurfaceCechPersistence CycleQ2IncidenceTraceCechPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

def extraOpenElement (c : ParameterPolynomial ℂ) : ParameterRing ℂ :=
  algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ) c

abbrev TraceOpen (c : ParameterPolynomial ℂ) := Localization.Away (extraOpenElement c)

def openSeed (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) : TraceOpen c →+* ℂ :=
  IsLocalization.Away.lift (extraOpenElement c)
    (g := (seedSpecialization ℂ (57 : ℂ) Complex.I).toRingHom) (by
      change IsUnit (seedSpecialization ℂ (57 : ℂ) Complex.I (extraOpenElement c))
      rw [extraOpenElement, seedSpecialization_polynomial, hc]
      exact isUnit_one)

@[simp] theorem openSeed_algebraMap (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) (a : ParameterRing ℂ) :
    openSeed c hc (algebraMap (ParameterRing ℂ) (TraceOpen c) a) =
      seedSpecialization ℂ (57 : ℂ) Complex.I a := by
  exact IsLocalization.Away.lift_eq _ _ _

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra TraceRing S]
  [IsScalarTower ℂ TraceRing S]

variable (P : Matrix SquareIndex ColumnIndex ℂ)
  (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
  (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z)

def openGeneric : TraceOpen c →+* S :=
  IsLocalization.Away.lift (extraOpenElement c)
    (g := (pointSpecialization (tracePointValue B z)
      (tracePoint_leading_unit P B c z hz.1)).toRingHom) (by
      change IsUnit (pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) (extraOpenElement c))
      rw [extraOpenElement, pointSpecialization_polynomial]
      exact tracePoint_extra_unit P B c z hz.1)

@[simp] theorem openGeneric_algebraMap (a : ParameterRing ℂ) :
    openGeneric P B c z hz (algebraMap (ParameterRing ℂ) (TraceOpen c) a) =
      pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) a := by
  exact IsLocalization.Away.lift_eq _ _ _

theorem pointed_open_kernel
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) :
    ∀ a : TraceOpen c, openGeneric P B c z hz a = 0 → openSeed c hc a = 0 := by
  apply kernel_containment_away (extraOpenElement c)
    (openGeneric P B c z hz) (openSeed c hc)
  intro a ha
  rw [openGeneric_algebraMap] at ha
  rw [openSeed_algebraMap]
  exact pointedTrace_localized_kernel P B c z hz a ha

abbrev ComponentRing := TraceOpen c ⧸ RingHom.ker (openGeneric P B c z hz)

def componentGeneric : ComponentRing P B c z hz →+* S :=
  (openGeneric P B c z hz).kerLift

theorem componentGeneric_injective : Function.Injective (componentGeneric P B c z hz) :=
  RingHom.kerLift_injective _

instance componentNontrivial [Nontrivial S] : Nontrivial (ComponentRing P B c z hz) :=
  (componentGeneric P B c z hz).domain_nontrivial

def componentSeed (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) :
    ComponentRing P B c z hz →+* ℂ :=
  Ideal.Quotient.lift _ (openSeed c hc) (by
    intro a ha
    exact pointed_open_kernel P B c z hz hc a (RingHom.mem_ker.mp ha))

def componentCoefficients : ParameterRing ℂ →+* ComponentRing P B c z hz :=
  (Ideal.Quotient.mk _).comp (algebraMap (ParameterRing ℂ) (TraceOpen c))

@[simp] theorem componentGeneric_coefficients (a : ParameterRing ℂ) :
    componentGeneric P B c z hz (componentCoefficients P B c z hz a) =
      pointSpecialization (tracePointValue B z)
        (tracePoint_leading_unit P B c z hz.1) a := by
  simp only [componentGeneric, componentCoefficients, RingHom.comp_apply,
    RingHom.kerLift_mk, openGeneric_algebraMap]

@[simp] theorem componentSeed_coefficients
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1) (a : ParameterRing ℂ) :
    componentSeed P B c z hz hc (componentCoefficients P B c z hz a) =
      seedSpecialization ℂ (57 : ℂ) Complex.I a := by
  simp only [componentSeed, componentCoefficients, RingHom.comp_apply,
    Ideal.Quotient.lift_mk, openSeed_algebraMap]

/-- The retained geometric open is a unit on the whole component ring,
not just at its generic coefficient-field point. -/
theorem component_extraOpen_isUnit :
    IsUnit (componentCoefficients P B c z hz (extraOpenElement c)) :=
  (IsLocalization.Away.algebraMap_isUnit (S := TraceOpen c) (extraOpenElement c)).map
    (Ideal.Quotient.mk (RingHom.ker (openGeneric P B c z hz)))

/-- The actual cleared incidence equations vanish on this component. -/
theorem component_incidence_equations (q : ColumnIndex) :
    componentCoefficients P B c z hz
      (algebraMap (ParameterPolynomial ℂ) (ParameterRing ℂ)
        ((presentation ℂ 57).equation q)) = 0 := by
  apply componentGeneric_injective P B c z hz
  rw [componentGeneric_coefficients, map_zero, pointSpecialization_polynomial]
  exact tracePoint_original_equations P B c z hz.1 q

def componentCubic : FullCubicTailIndex → ComponentRing P B c z hz :=
  fun i => componentCoefficients P B c z hz (universalCubicTail ℂ i)

def componentSextic : FullSexticTailIndex → ComponentRing P B c z hz :=
  fun i => componentCoefficients P B c z hz (universalSexticTail ℂ i)

abbrev ComponentTopCech [Nontrivial S] :=
  ActualTopCechQuotient (ComponentRing P B c z hz)
    (componentCubic P B c z hz) (componentSextic P B c z hz)

/-- The actual top-Cech coefficient map to the generic point is injective. -/
theorem componentTop_generic_injective [Nontrivial S] :
    Function.Injective (actualTopMap (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz)) :=
  actualTopMap_injective _ (componentGeneric_injective P B c z hz) _ _

/-- Persistence for a class constructed on the actual pointed component.
This requires no lift of that class to the unconstrained parameter space. -/
theorem componentTop_nonzero [Nontrivial S]
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : ComponentTopCech P B c z hz)
    (hξ : actualTopMap (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 := by
  intro hzero
  have hξzero : ξ = 0 := (componentTop_generic_injective P B c z hz)
    (hzero.trans (map_zero _).symm)
  exact hξ (by rw [hξzero, map_zero])

end CycleQ2IncidenceTraceComponent

#print axioms CycleQ2IncidenceTraceComponent.component_extraOpen_isUnit
#print axioms CycleQ2IncidenceTraceComponent.component_incidence_equations
#print axioms CycleQ2IncidenceTraceComponent.componentTop_generic_injective
#print axioms CycleQ2IncidenceTraceComponent.componentTop_nonzero
end
end

/- Component: continuation_20261112/IncidenceTraceCharacterComponent.lean -/
section
/-!
# Character-one cohomology on the actual pointed incidence component

The actual coefficient ring, preserved geometric open, generic embedding,
and seed specialization are the previously checked constructions.  Only
the specified character of the actual Cech complex changes.  Character one
has rank eight and is the piece paired with the character-two canonical
residue of an invariant cubic.

Persistence below is conditional on an actual class and its nonzero seed
image.  It does not construct the geometric ambient-test class or identify
that class with the seed normal/residue calculation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceCharacterComponent

open MvPolynomial Matrix CycleQ2IncidenceNormalForm
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceTraceComponent CycleQ2UniversalSurfaceCharacterCech
  CycleQ2UniversalSurfaceCharacterPersistence
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {S : Type} [CommRing S] [Nontrivial S] [Algebra ℂ S]
  [Algebra TraceRing S] [IsScalarTower ℂ TraceRing S]

variable (P : Matrix SquareIndex ColumnIndex ℂ)
  (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
  (z : SquareIndex → S) (hz : IsPointedTracePoint P B c z) (χ : ZMod 3)

abbrev CharacterComponentTopCech :=
  ActualTopCechQuotient (ComponentRing P B c z hz) χ
    (componentCubic P B c z hz) (componentSextic P B c z hz)

theorem componentTop_generic_injective :
    Function.Injective (actualTopMap χ (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz)) :=
  actualTopMap_injective χ _ (componentGeneric_injective P B c z hz) _ _

theorem componentTop_nonzero
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : CharacterComponentTopCech P B c z hz χ)
    (hξ : actualTopMap χ (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap χ (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 := by
  intro hzero
  have hξzero : ξ = 0 := (componentTop_generic_injective P B c z hz χ)
    (hzero.trans (map_zero _).symm)
  exact hξ (by rw [hξzero, map_zero])

theorem characterOne_rank_eight :
    Module.finrank (ComponentRing P B c z hz)
      (CharacterComponentTopCech P B c z hz (1 : ZMod 3)) = 8 :=
  actualTop_rank_characterOne (ComponentRing P B c z hz)
    (componentCubic P B c z hz) (componentSextic P B c z hz)

theorem characterOne_nonzero
    (hc : eval (seedPoint (57 : ℂ) Complex.I) c = 1)
    (ξ : CharacterComponentTopCech P B c z hz (1 : ZMod 3))
    (hξ : actualTopMap (1 : ZMod 3) (componentSeed P B c z hz hc)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0) :
    actualTopMap (1 : ZMod 3) (componentGeneric P B c z hz)
      (componentCubic P B c z hz) (componentSextic P B c z hz) ξ ≠ 0 :=
  componentTop_nonzero P B c z hz (1 : ZMod 3) hc ξ hξ

end CycleQ2IncidenceTraceCharacterComponent

#print axioms CycleQ2IncidenceTraceCharacterComponent.characterOne_rank_eight
#print axioms CycleQ2IncidenceTraceCharacterComponent.characterOne_nonzero
end
end

/- Uncompiled continuation: OrbitTraceBridge.lean (2026-11-12). -/
section Q2UncompiledOrbitTrace

/-!
# The actual cyclic action and the character-one orbit trace

Development continuation; compilation status is recorded in solution.md.
Written against the source snapshot at commit 8d88f06, this component is
integrated before the nonconstructive endpoint in `Solution.lean`.

The localization statements below concern the existing, literal diagonal
action on the seed quotient and its actual coordinate localizations. In
particular, the character is proved from the homogeneous-fraction theorem;
it is not imposed by defining the action to be scalar multiplication.

The final trace statements are algebraic. They do not construct the missing
semiregularity map from `CycleQ2ActualNormalCech.NormalCech` to the surface
character-one top Cech quotient. They also do not identify an arbitrary
linear functional with Serre duality or Abel--Jacobi. That geometric map,
its covariance for the fixed ambient test, and its pairing comparison are
still needed before applying these lemmas to the computed normal class.

No theorem below uses `Submission.missing_geometric_existence`.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2OrbitTraceBridge


section DualCharacter

variable {R V W : Type*} [CommRing R]
variable [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

/-- An invariant bilinear pairing against a character-two test vector has
the dual character required by `pairing_twistedOrbit`. This is an algebraic
identity; no geometric Serre pairing is introduced or assumed to exist. -/
theorem dualCharacter_of_invariantPairing (ζ : R) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[R] V) (h : W →ₗ[R] W) (P : V →ₗ[R] W →ₗ[R] R)
    (hP : ∀ v w, P (g v) (h w) = P v w)
    (w : W) (hw : h w = ζ ^ 2 • w) :
    ∀ v, P (g v) w = ζ * P v w := by
  intro v
  have he := hP v w
  rw [hw, map_smul, smul_eq_mul] at he
  have hc : ζ * ζ ^ 2 = 1 := by
    linear_combination hζ
  calc
    P (g v) w = (ζ * ζ ^ 2) * P (g v) w := by rw [hc, one_mul]
    _ = ζ * (ζ ^ 2 * P (g v) w) := by ring
    _ = ζ * P v w := by rw [he]

end DualCharacter

section NonzeroPairing

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem pairing_twistedOrbit_ne_zero (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[ℂ] V) (φ : V →ₗ[ℂ] ℂ)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) (hv : φ v ≠ 0) :
    φ (twistedOrbit ζ g v) ≠ 0 := by
  rw [pairing_twistedOrbit ζ hζ g φ hφ]
  exact mul_ne_zero (by norm_num) hv

theorem twistedOrbit_ne_zero_of_pairing (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (g : V →ₗ[ℂ] V) (φ : V →ₗ[ℂ] ℂ)
    (hφ : ∀ v, φ (g v) = ζ * φ v) (v : V) (hv : φ v ≠ 0) :
    twistedOrbit ζ g v ≠ 0 := by
  intro hz
  have h := pairing_twistedOrbit_ne_zero ζ hζ g φ hφ v hv
  apply h
  rw [hz, map_zero]

end NonzeroPairing

section ActualLocalization

open MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization
open CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
open CycleQ2SeedQuotientGrading CycleQ2SeedCyclicAction
open CycleQ2SeedCyclicLocalization

variable {R : Type*} [CommRing R]

/-- Arbitrary powers of that denominator add no character to a fraction. -/
theorem tripleDenominator_character (n : ℕ) :
    (baseGrade (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = 0 := by
  have hb : (baseGrade (openExponent (Finset.univ : Finset (Fin 3)))).2 = 0 := by
    norm_num [baseGrade, openExponent] <;> decide
  rw [map_nsmul]
  change n • (baseGrade (openExponent (Finset.univ : Finset (Fin 3)))).2 = 0
  rw [hb, nsmul_zero]

/-- Every genuinely homogeneous section on the actual triple localization
has its declared eigenvalue under the existing diagonal action. -/
theorem localAction_triple_homogeneous [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g
      (localizedCoordinates R r ι Finset.univ q ab)) :
    localAction ζ hζ r ι Finset.univ q = ζ ^ g.2.val • q := by
  obtain ⟨n, p, hp, hfrac⟩ :=
    (localized_homogeneous_iff_fraction R r ι Finset.univ q g).mp hq
  let φ := algebraMap (SeedRing r ι) (SeedLocal R r ι Finset.univ)
  let π := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let den := φ (algebraMap (Base R) (SeedRing r ι)
    (baseProduct R (Finset.univ : Finset (Fin 3)) ^ n))
  have hden : IsUnit den := by
    dsimp [den, φ]
    simpa only [map_pow] using
      (seedProduct_isUnit R r ι (Finset.Subset.refl Finset.univ)).pow n
  have hden_fixed : localAction ζ hζ r ι Finset.univ den = den := by
    dsimp [den, φ]
    simp only [map_pow, localAction_algebraMap, seedAction_baseProduct,
      baseFactor_univ ζ hζ, map_one, one_mul]
  have hchar : (g + baseGrade
      (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = g.2 := by
    change g.2 + (baseGrade
      (n • openExponent (Finset.univ : Finset (Fin 3)))).2 = g.2
    rw [tripleDenominator_character, add_zero]
  change q * den = φ (π p) at hfrac
  have he := congrArg (localAction ζ hζ r ι Finset.univ) hfrac
  rw [map_mul, hden_fixed, localAction_mk,
    polynomialAction_signedHomogeneous ζ hζ p _ hp, hchar, map_mul, map_mul] at he
  change localAction ζ hζ r ι Finset.univ q * den =
    φ (π (C (ζ ^ g.2.val))) * φ (π p) at he
  rw [← hfrac] at he
  obtain ⟨u, hu⟩ := hden
  have he' := congrArg
    (fun z : SeedLocal R r ι Finset.univ => z * (↑(u⁻¹) : SeedLocal R r ι Finset.univ)) he
  rw [← hu] at he'
  have hcancel : localAction ζ hζ r ι Finset.univ q =
      φ (π (C (ζ ^ g.2.val))) * q := by
    simpa only [mul_assoc, u.mul_inv, mul_one] using he'
  rw [Algebra.smul_def,
    IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι Finset.univ)]
  exact hcancel

/-- In particular the actual character-one triple sections have eigenvalue
`zeta`; this is the character required by the ambient test. -/
theorem localLinearAction_characterOne [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates R r ι Finset.univ q ab)) :
    localLinearAction ζ hζ r ι Finset.univ q = ζ • q := by
  have hv : (1 : ZMod 3).val = 1 := by decide
  simpa only [localLinearAction_apply, hv, pow_one] using localAction_triple_homogeneous ζ hζ r ι q
    (0, (1 : ZMod 3)) hq

theorem actual_triple_twistedOrbit_eq_three_smul [Nontrivial R]
    (ζ : R) (hζ : ζ ^ 3 = 1) (r ι : R)
    (q : SeedLocal R r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates R r ι Finset.univ q ab)) :
    twistedOrbit ζ (localLinearAction ζ hζ r ι Finset.univ) q = (3 : R) • q :=
  twistedOrbit_eq_three_smul ζ hζ _ q
    (localLinearAction_characterOne ζ hζ r ι q hq)

end ActualLocalization

section ActualAmbientTest

open MvPolynomial CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization
open CycleQ2IncidenceEquations CycleQ2SegreTangentLocal
open CycleQ2SeedCechLocalizedBasis

/-- The external test used by the normal connecting class has character
one under the literal polynomial action. -/
theorem polynomialAction_ambientTest (ζ : ℂ) :
    polynomialAction ζ CycleQ2NormalConnecting.derivativeA =
      C ζ * CycleQ2NormalConnecting.derivativeA := by
  simp only [CycleQ2NormalConnecting.derivativeA, map_mul, map_pow,
    polynomialAction_X]
  change (C ζ * X 2) * (X 3) ^ 3 * X 4 =
    C ζ * (X 2 * X 3 ^ 3 * X 4)
  ring

/-- The same equality holds on every actual seed coordinate localization. -/
theorem localAction_ambientTest (ζ : ℂ) (hζ : ζ ^ 3 = 1) (r ι : ℂ)
    (s : Finset (Fin 3)) :
    localAction ζ hζ r ι s
      (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s)
        (Ideal.Quotient.mk (CycleQ2IncidenceNormalForm.equationsIdeal
          (smoothH ι) (smoothF r ι)) CycleQ2NormalConnecting.derivativeA)) =
      ζ • algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s)
        (Ideal.Quotient.mk (CycleQ2IncidenceNormalForm.equationsIdeal
          (smoothH ι) (smoothF r ι)) CycleQ2NormalConnecting.derivativeA) := by
  rw [localAction_mk, polynomialAction_ambientTest, map_mul, map_mul,
    Algebra.smul_def,
    IsScalarTower.algebraMap_apply ℂ (SeedRing r ι) (SeedLocal ℂ r ι s)]
  rfl

end ActualAmbientTest

section ActualNonzeroPairing

open CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis

/-- This is an application to the actual localization action. The remaining
geometric task is to supply the ambient-test class and its genuine trace
functional, rather than to assume their comparison with these objects. -/
theorem actual_triple_pairing_ne_zero
    (ζ : ℂ) (hζ : ζ ^ 3 = 1) (r ι : ℂ)
    (q : SeedLocal ℂ r ι Finset.univ)
    (hq : ∀ ab, HasGrade ab (0, (1 : ZMod 3))
      (localizedCoordinates ℂ r ι Finset.univ q ab))
    (φ : SeedLocal ℂ r ι Finset.univ →ₗ[ℂ] ℂ) (hφ : φ q ≠ 0) :
    φ (twistedOrbit ζ (localLinearAction ζ hζ r ι Finset.univ) q) ≠ 0 := by
  rw [actual_triple_twistedOrbit_eq_three_smul ζ hζ r ι q hq,
    map_smul, smul_eq_mul]
  exact mul_ne_zero (by norm_num) hφ

end ActualNonzeroPairing

end CycleQ2OrbitTraceBridge

end

end Q2UncompiledOrbitTrace
