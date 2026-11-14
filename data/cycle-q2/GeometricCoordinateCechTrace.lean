import Proposal.GeometricCartierCharacter
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# A fixed coefficient trace on the actual surface coordinate Čech quotient

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.

The functional is fixed before any class is considered: it extracts the
coefficient of x₀²w²/(x₁x₂x₃) in the original rank-nine Laurent coordinates.
Every actual Čech boundary has zero such coefficient. Among homogeneous
weight-three classes this coefficient detects zero, because this is the
unique strictly negative monomial of weight three in the actual basis.
The nonzero value below is for the original detector-cubic multiple of an
actual descendant of the unchanged Cartier cocycle.

This is a coordinate Čech trace. Identifying it with a trace on the actual
canonical sheaf requires a separate, restriction-compatible comparison of
that sheaf with the homogeneous weight-three localized modules. Nothing
in this file assumes or supplies that geometric comparison.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CoordinateCechTrace

open MvPolynomial
open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricCartierCech
  CycleQ2GeometricFourOpenCech CycleQ2GeometricLaurentTop
  CycleQ2GeometricHomogeneousWeight CycleQ2NormalConnecting

/-- The existing identity-coordinate localization equivalence also preserves
the original complex constants. -/
def seedCoordinateAlgEquiv (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s ≃ₐ[ℂ] SeedLocal ℂ r Complex.I s where
  __ := seedCoordinateEquiv r s
  commutes' c := by
    rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing r 1) (CoordinateLocal r 1 s),
      seedCoordinateEquiv_base, (seedRingEquiv r).commutes,
      ← IsScalarTower.algebraMap_apply ℂ (SeedRing r Complex.I)
        (SeedLocal ℂ r Complex.I s)]

private theorem base_C_seed (r c : ℂ) :
    algebraMap (Base ℂ) (SeedRing r Complex.I) (C c) =
      algebraMap ℂ (SeedRing r Complex.I) c := by
  change Ideal.Quotient.mk _ (remainingInclusion ℂ (C c)) =
    Ideal.Quotient.mk _ (C c)
  simp [remainingInclusion]

private theorem localizedCoordinates_complex_smul (r : ℂ) (s : Finset (Fin 3))
    (c : ℂ) (p : SeedLocal ℂ r Complex.I s) :
    localizedCoordinates ℂ r Complex.I s (c • p) =
      c • localizedCoordinates ℂ r Complex.I s p := by
  have hscalar : algebraMap (Base ℂ) (coordinateLocalization ℂ s) (C c) • p =
      c • p := by
    simp only [Algebra.smul_def]
    rw [← IsScalarTower.algebraMap_apply (Base ℂ) (coordinateLocalization ℂ s)
        (SeedLocal ℂ r Complex.I s),
      IsScalarTower.algebraMap_apply (Base ℂ) (SeedRing r Complex.I)
        (SeedLocal ℂ r Complex.I s), base_C_seed,
      ← IsScalarTower.algebraMap_apply ℂ (SeedRing r Complex.I)
        (SeedLocal ℂ r Complex.I s)]
  funext ab
  rw [← hscalar, localizedCoordinates_smul, localizationToLaurent_algebraMap]
  change baseToLaurent ℂ (algebraMap ℂ (Base ℂ) c) * _ = c • _
  rw [AlgHom.commutes, Algebra.smul_def]

theorem coordinateLaurent_complex_smul (r : ℂ) (s : Finset (Fin 3))
    (c : ℂ) (p : CoordinateLocal r 1 s) :
    coordinateLaurent r s (c • p) = c • coordinateLaurent r s p := by
  change localizedCoordinates ℂ r Complex.I s
    (seedCoordinateAlgEquiv r s (c • p)) =
      c • localizedCoordinates ℂ r Complex.I s (seedCoordinateAlgEquiv r s p)
  rw [map_smul, localizedCoordinates_complex_smul]

/-- The original Laurent-coordinate map, now retaining its complex linearity. -/
def coordinateLaurentLinear (r : ℂ) (s : Finset (Fin 3)) :
    CoordinateLocal r 1 s →ₗ[ℂ] (ShiftIndex → Laurent (R := ℂ)) where
  __ := coordinateLaurent r s
  map_smul' c p := coordinateLaurent_complex_smul r s c p

/-- Homogeneous weight in the actual localized surface ring. This is not a
replacement for the surface ring and does not choose representatives. -/
def coordinateLocalWeight (r : ℂ) (k : ℤ) (s : Finset (Fin 3)) :
    Submodule ℂ (CoordinateLocal r 1 s) where
  carrier := {p | ∀ ab e, (shiftedGrade ab e).1 ≠ k →
    (coordinateLaurent r s p ab).coeff e = 0}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab e he := by
    simp only [map_add, Pi.add_apply, AddMonoidAlgebra.coeff_add,
      Finsupp.add_apply, hp ab e he, hq ab e he, add_zero]
  smul_mem' c p hp ab e he := by
    simp only [coordinateLaurent_complex_smul, Pi.smul_apply,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he, smul_zero]

theorem mem_coordinateLocalWeight_iff (r : ℂ) (k : ℤ) (s : Finset (Fin 3))
    (p : CoordinateLocal r 1 s) :
    p ∈ coordinateLocalWeight r k s ↔
      ∀ ab e, (coordinateLaurent r s p ab).coeff e ≠ 0 →
        (shiftedGrade ab e).1 = k := by
  constructor
  · intro hp ab e he
    by_contra hw
    exact he (hp ab e hw)
  · intro hp ab e hw
    by_contra he
    exact hw (hp ab e he)

/-- The original ring restriction preserves this homogeneous local module. -/
def coordinateWeightRestriction (r : ℂ) (k : ℤ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateLocalWeight r k s →ₗ[ℂ] coordinateLocalWeight r k t where
  toFun p := ⟨coordinateRestriction r 1 hst p.val, by
    intro ab e he
    rw [coordinateLaurent_restriction]
    exact p.property ab e he⟩
  map_add' p q := by
    apply Subtype.ext
    exact map_add (coordinateRestriction r 1 hst) p.val q.val
  map_smul' c p := by
    apply Subtype.ext
    exact ((coordinateRestriction r 1 hst).toLinearMap.restrictScalars ℂ).map_smul c p.val

@[simp] theorem coordinateWeightRestriction_val (r : ℂ) (k : ℤ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (p : coordinateLocalWeight r k s) :
    (coordinateWeightRestriction r k hst p).val =
      coordinateRestriction r 1 hst p.val := rfl

/-- Evaluation of a specified coefficient in the unchanged Laurent coordinates. -/
def localCoefficient (r : ℂ) (s : Finset (Fin 3))
    (ab : ShiftIndex) (e : LaurentExponent) : CoordinateLocal r 1 s →ₗ[ℂ] ℂ where
  toFun p := (coordinateLaurent r s p ab).coeff e
  map_add' p q := by
    simp only [map_add, Pi.add_apply, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c p := by
    simp only [coordinateLaurent_complex_smul, Pi.smul_apply,
      AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, RingHom.id_apply]

/-- The first triple component of the original four-open cycle. The fourth
coordinate open is empty, as in the existing coordinate Čech complex. -/
def cycleTop (r : ℂ) :
    TwoCocycles (coordinateScalarSystem r) →ₗ[ℂ] CoordinateLocal r 1 Finset.univ where
  toFun := coordinateTopRepresentative r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fixed coefficient of x₀²w²/(x₁x₂x₃), on actual cocycles. -/
def cycleCoefficient (r : ℂ) : TwoCocycles (coordinateScalarSystem r) →ₗ[ℂ] ℂ :=
  (localCoefficient r Finset.univ (2,2) (fun _ => -1)).comp (cycleTop r)

@[simp] theorem cycleCoefficient_apply (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    cycleCoefficient r d =
      (coordinateLaurent r Finset.univ (coordinateTopRepresentative r d) (2,2)).coeff
        (fun _ => -1) := rfl

theorem cycleCoefficient_zero_of_class_zero (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r))
    (hd : classOf (coordinateScalarSystem r) d = 0) : cycleCoefficient r d = 0 :=
  (coordinate_class_zero_iff_all_negative r d).mp hd (2,2) (fun _ => -1)
    (by intro i; norm_num)

theorem boundaries_le_cycleCoefficient_kernel (r : ℂ) :
    (LinearMap.range (boundaryMap (coordinateScalarSystem r))).toAddSubgroup ≤
      (cycleCoefficient r).toAddMonoidHom.ker := by
  rintro d ⟨b, rfl⟩
  change cycleCoefficient r (boundaryMap (coordinateScalarSystem r) b) = 0
  apply cycleCoefficient_zero_of_class_zero
  exact (classOf_eq_zero_iff (coordinateScalarSystem r) _).mpr ⟨b, rfl⟩

/-- The original coefficient descends to the original coordinate Čech quotient.
Its definition does not refer to the literal Cartier class. -/
def coordinateTrace (r : ℂ) : ActualCoordinateSecondCech r →ₗ[ℂ] ℂ :=
  { QuotientAddGroup.lift
      (LinearMap.range (boundaryMap (coordinateScalarSystem r))).toAddSubgroup
      (cycleCoefficient r).toAddMonoidHom (boundaries_le_cycleCoefficient_kernel r) with
    map_smul' := by
      intro c x
      obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (cycleCoefficient r).map_smul c d }

@[simp] theorem coordinateTrace_classOf (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    coordinateTrace r (classOf (coordinateScalarSystem r) d) = cycleCoefficient r d := rfl

/-- Homogeneous cycles are a submodule of the actual cycle module. -/
def coordinateCycleWeight (r : ℂ) (k : ℤ) :
    Submodule ℂ (TwoCocycles (coordinateScalarSystem r)) :=
  (coordinateLocalWeight r k Finset.univ).comap (cycleTop r)

/-- The fixed coordinate trace detects every homogeneous weight-three class.
The proof uses all actual negative coefficients and the unique possible
weight-three monomial, not an assumed one-dimensional cohomology theorem. -/
theorem coordinateTrace_class_eq_zero_iff (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r))
    (hd : d ∈ coordinateCycleWeight r 3) :
    coordinateTrace r (classOf (coordinateScalarSystem r) d) = 0 ↔
      classOf (coordinateScalarSystem r) d = 0 := by
  constructor
  · intro ht
    apply (coordinate_class_zero_iff_all_negative r d).mpr
    intro ab e he
    by_contra hne
    have hw : (shiftedGrade ab e).1 = 3 := by
      by_contra hw
      exact hne (hd ab e hw)
    obtain ⟨rfl, rfl⟩ := strictlyNegative_weight_three_unique ab e he hw
    exact hne ht
  · intro hd
    rw [hd, map_zero]

theorem coordinateTrace_class_eq_iff (r : ℂ)
    (d e : TwoCocycles (coordinateScalarSystem r))
    (hd : d ∈ coordinateCycleWeight r 3) (he : e ∈ coordinateCycleWeight r 3) :
    coordinateTrace r (classOf (coordinateScalarSystem r) d) =
        coordinateTrace r (classOf (coordinateScalarSystem r) e) ↔
      classOf (coordinateScalarSystem r) d = classOf (coordinateScalarSystem r) e := by
  constructor
  · intro h
    have hz : coordinateTrace r (classOf (coordinateScalarSystem r) (d - e)) = 0 := by
      rw [map_sub, map_sub, h, sub_self]
    have hc := (coordinateTrace_class_eq_zero_iff r (d - e)
      ((coordinateCycleWeight r 3).sub_mem hd he)).mp hz
    exact sub_eq_zero.mp (by simpa only [map_sub] using hc)
  · intro h
    rw [h]

/-- The fixed detector-cubic multiplication of the original homogeneous
coordinate descendant has weight three in those same coordinates. -/
theorem literal_cubic_cycle_weight
    (d : TwoCocycles (coordinateScalarSystem 57))
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    surfaceQuotient 57 1 detectorCubic • d ∈ coordinateCycleWeight 57 3 := by
  intro ab e he
  change (coordinateLaurent 57 Finset.univ
    (coordinateTopRepresentative 57 (surfaceQuotient 57 1 detectorCubic • d)) ab).coeff e = 0
  rw [coordinateTopRepresentative_smul, ← hq]
  by_contra hn
  exact he (homogeneous_coordinate_cubic_weight 57 q ab e hn)

/-- This nonvanishing is evaluated by the already fixed coefficient functional
on the actual descended Cartier class, retaining its original cubic multiple. -/
theorem literal_cubic_coordinateTrace_nonzero
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    coordinateTrace 57 (surfaceQuotient 57 1 detectorCubic •
      classOf (coordinateScalarSystem 57) d) ≠ 0 := by
  rw [← map_smul (classOf (coordinateScalarSystem 57)), coordinateTrace_classOf,
    cycleCoefficient_apply, coordinateTopRepresentative_smul, ← hq]
  exact literal_homogeneous_cubic_coefficient d hcd q hq

/-- A closed result for the original literal Cartier cocycle: its genuine
homogeneous descendant has a cubic multiple detected by this fixed trace. -/
theorem literal_weightThree_coordinateTrace_nonzero :
    ∃ (d : TwoCocycles (coordinateScalarSystem 57)) (q : HomogeneousCoordinateTop 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      q.val = coordinateTopRepresentative 57 d ∧
      surfaceQuotient 57 1 detectorCubic • d ∈ coordinateCycleWeight 57 3 ∧
      coordinateTrace 57 (surfaceQuotient 57 1 detectorCubic •
        classOf (coordinateScalarSystem 57) d) ≠ 0 := by
  obtain ⟨d, q, hcd, hq, _, _⟩ := literal_homogeneous_coordinate_cubic_nonzero
  exact ⟨d, q, hcd, hq, literal_cubic_cycle_weight d q hq,
    literal_cubic_coordinateTrace_nonzero d hcd q hq⟩

theorem literal_coordinateTrace_ne_zero : coordinateTrace 57 ≠ 0 := by
  obtain ⟨d, q, hcd, hq, hw, ht⟩ := literal_weightThree_coordinateTrace_nonzero
  intro hz
  apply ht
  rw [hz, LinearMap.zero_apply]

#print axioms coordinateWeightRestriction
#print axioms coordinateTrace
#print axioms coordinateTrace_class_eq_zero_iff
#print axioms coordinateTrace_class_eq_iff
#print axioms literal_weightThree_coordinateTrace_nonzero
#print axioms literal_coordinateTrace_ne_zero

end CycleQ2CoordinateCechTrace

end
