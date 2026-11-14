import Proposal.GeometricDegreeOneCech
import Proposal.GeometricIncidenceTraceData
import Proposal.GeometricFormalInputs02Part03
import Proposal.GeometricCurveCoordinates
import Proposal.GeometricKoszulTrace
import Mathlib.Data.Finsupp.Weight
import Proposal.GeometricCurveRegularPair
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-!
# The actual incidence Cech line and its derivative coordinate

This module keeps the original degree-one homogeneous Cech quotient on
the literal curve r=57, theta=1. It proves natural complex linearity,
arbitrary-pole reduction, one-dimensionality, and the exact coefficient
of each original paired normal class. All polynomial, regular-pair and
nonmembership inputs are proved; no geometric trace normalization is
assumed. The Cech-to-derived and moving-cycle comparisons are separate.
-/

/-!
# Natural complex scalars on the existing Cech quotient

The homogeneous chart modules already carry their affine-coordinate
module structures. Restricting the ambient localization scalars gives
the same underlying sections complex-vector-space structures. Both
existing chart restrictions respect these scalars, so the original
additive Cech quotient is a complex vector space as well.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricCechComplex

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve

/-- The original section predicate, now as a complex submodule. -/
def complexDegreeOne (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) : Submodule ℂ (Localization.Away f) where
  carrier := degreeOneModule r θ f d hf
  zero_mem' := (degreeOneModule r θ f d hf).zero_mem
  add_mem' := (degreeOneModule r θ f d hf).add_mem
  smul_mem' := by
    rintro c _ ⟨n, a, ha, rfl⟩
    refine ⟨n, c • a, (curveGrade r θ _).smul_mem c ha, ?_⟩
    exact (Localization.smul_mk c a _).symm

instance degreeOneComplexModule (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) : Module ℂ (degreeOneModule r θ f d hf) :=
  inferInstanceAs (Module ℂ (complexDegreeOne r θ f d hf))

@[simp] theorem degreeOne_smul_coe (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (c : ℂ) (z : degreeOneModule r θ f d hf) :
    ((c • z : degreeOneModule r θ f d hf) : Localization.Away f) = c • (z : Localization.Away f) := rfl

@[simp] theorem awayRestriction_smul (r θ : ℂ) (f g x : CurveRing r θ)
    (hx : x = f * g) (c : ℂ) (z : Localization.Away f) :
    awayRestriction r θ f g x hx (c • z) = c • awayRestriction r θ f g x hx z := by
  have hcoeff : awayRestriction r θ f g x hx (algebraMap ℂ (Localization.Away f) c) =
      algebraMap ℂ (Localization.Away x) c := by
    change awayRestriction r θ f g x hx
        (algebraMap (CurveRing r θ) (Localization.Away f) (algebraMap ℂ (CurveRing r θ) c)) =
      algebraMap (CurveRing r θ) (Localization.Away x) (algebraMap ℂ (CurveRing r θ) c)
    exact awayRestriction_base r θ f g x hx _
  simp only [Algebra.smul_def, map_mul, hcoeff]

@[simp] theorem firstDegreeOneRestriction_smul (r θ c : ℂ) (z : FirstDegreeOne r θ) :
    firstDegreeOneRestriction r θ (c • z) = c • firstDegreeOneRestriction r θ z := by
  apply Subtype.ext
  change awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
      (curveG1 r θ * curveG2 r θ) rfl (c • (z : FirstOpen r θ)) =
    c • awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
      (curveG1 r θ * curveG2 r θ) rfl (z : FirstOpen r θ)
  exact awayRestriction_smul r θ _ _ _ _ c _

@[simp] theorem secondDegreeOneRestriction_smul (r θ c : ℂ) (z : SecondDegreeOne r θ) :
    secondDegreeOneRestriction r θ (c • z) = c • secondDegreeOneRestriction r θ z := by
  apply Subtype.ext
  change awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
      (curveG1 r θ * curveG2 r θ) (mul_comm _ _) (c • (z : SecondOpen r θ)) =
    c • awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
      (curveG1 r θ * curveG2 r θ) (mul_comm _ _) (z : SecondOpen r θ)
  exact awayRestriction_smul r θ _ _ _ _ c _

def complexBoundaries (r θ : ℂ) : Submodule ℂ (OverlapDegreeOne r θ) where
  carrier := degreeOneBoundaries r θ
  zero_mem' := (degreeOneBoundaries r θ).zero_mem
  add_mem' := (degreeOneBoundaries r θ).add_mem
  smul_mem' := by
    rintro c _ ⟨⟨a, b⟩, rfl⟩
    refine ⟨(c • a, c • b), ?_⟩
    simp [degreeOneCoboundary, smul_sub]

instance degreeOneCechComplexModule (r θ : ℂ) : Module ℂ (DegreeOneCech r θ) :=
  inferInstanceAs (Module ℂ ((OverlapDegreeOne r θ) ⧸ complexBoundaries r θ))

@[simp] theorem cech_mk_smul (r θ c : ℂ) (z : OverlapDegreeOne r θ) :
    (QuotientAddGroup.mk (c • z) : DegreeOneCech r θ) =
      c • (QuotientAddGroup.mk z : DegreeOneCech r θ) := rfl

theorem degreeNineRepresentative_C_mul (r θ c : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) :
    degreeNineRepresentative r θ (C c * p) (hp.C_mul c) =
      c • degreeNineRepresentative r θ p hp := by
  have hmap : curveMap r θ (C c * p) = c • curveMap r θ p := by
    rw [← smul_eq_C_mul]
    exact (Ideal.Quotient.mkₐ ℂ (CycleQ2SeedCechTheta.curveIdeal r θ)).toLinearMap.map_smul c p
  apply Subtype.ext
  change awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ (C c * p)) =
    c • awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ p)
  rw [hmap]
  exact (Localization.smul_mk c (curveMap r θ p) _).symm

/-- Complex multiplication acts on the original numerator classes in the
expected way; this is proved in the actual localizations. -/
theorem degreeNineCechClass_C_mul (r θ c : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) :
    degreeNineCechClass r θ (C c * p) (hp.C_mul c) =
      c • degreeNineCechClass r θ p hp := by
  unfold degreeNineCechClass
  rw [degreeNineRepresentative_C_mul, cech_mk_smul]

end CycleQ2GeometricCechComplex
end

/-!
# Small abstract-algebra reductions for the incidence numerator

The exact integer identities are first applied in an abstract complex
algebra. This prevents repeated elaboration through the concrete ideal
quotient. The next module instantiates these proved identities at the
actual incidence quotient.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2GeometricIncidenceTraceLinear
open CycleQ2SeedTrace

variable {R : Type*} [CommRing R] [Algebra ℂ R]

def value (v : Fin 4 → R) (a b c d : ℕ) : R := v 0 ^ a * v 1 ^ b * v 2 ^ c * v 3 ^ d
def line (v : Fin 4 → R) : Submodule ℂ R := Submodule.span ℂ {v 3 ^ 9}

private theorem mem_line_of_scaled (v : Fin 4 → R) (scale z : ℂ) (p : R)
    (hs : scale ≠ 0)
    (h : algebraMap ℂ R scale * p = algebraMap ℂ R z * v 3 ^ 9) : p ∈ line v := by
  have heq : scale • p = z • v 3 ^ 9 := by
    rw [Algebra.smul_def, Algebra.smul_def]
    exact h
  apply ((line v).smul_mem_iff hs).mp
  rw [heq]
  exact (line v).smul_mem z (Submodule.subset_span (Set.mem_singleton _))

private theorem i_sq : (algebraMap ℂ R Complex.I) ^ 2 + 1 = 0 := by
  rw [← map_pow, Complex.I_sq, map_neg, map_one]
  ring

variable (v : Fin 4 → R)
variable (hq : v 0 ^ 2 - 57 * v 1 * v 3 = 0)
variable (hb : v 1 ^ 2 * v 3 ^ 2 = 0) (hc : v 2 ^ 4 = 0)
variable (hh : v 2 ^ 3 + (v 0 + v 1) * v 3 * v 2 + v 0 * v 1 ^ 2 +
  (1 - algebraMap ℂ R Complex.I) * v 3 ^ 3 - algebraMap ℂ R Complex.I * v 1 ^ 3 + v 0 ^ 3 = 0)

private theorem normal0 : value v 0 0 0 9 ∈ line v := by
  simpa only [value, pow_zero, one_mul] using
    (show v 3 ^ 9 ∈ line v from Submodule.subset_span (Set.mem_singleton _))

include hq hb hc hh

private theorem normal1 : value v 0 0 1 8 ∈ line v := by
  apply mem_line_of_scaled v (1140 : ℂ) (24 + (8 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation1 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal2 : value v 0 0 2 7 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation2 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal3 : value v 0 0 3 6 ∈ line v := by
  apply mem_line_of_scaled v (10 : ℂ) ((-8) + (4 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation3 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal4 : value v 0 1 0 8 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation4 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal5 : value v 0 1 1 7 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation5 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal6 : value v 0 1 2 6 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) ((-4) + (2 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation6 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal7 : value v 0 1 3 5 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation7 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal8 : value v 0 5 3 1 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) (4 + (8 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation8 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal9 : value v 0 6 2 1 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation9 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal10 : value v 0 6 3 0 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation10 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal11 : value v 0 7 1 1 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation11 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal12 : value v 0 7 2 0 ∈ line v := by
  apply mem_line_of_scaled v (57 : ℂ) 4 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation12 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal13 : value v 0 8 0 1 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) (16 + ((-8) * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation13 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal14 : value v 0 8 1 0 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation14 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal15 : value v 0 9 0 0 ∈ line v := by
  apply mem_line_of_scaled v (5 : ℂ) ((-16) + (8 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation15 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal16 : value v 1 0 0 8 ∈ line v := by
  apply mem_line_of_scaled v (4 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation16 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal17 : value v 1 0 1 7 ∈ line v := by
  apply mem_line_of_scaled v (10 : ℂ) (6 + (2 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation17 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal18 : value v 1 0 2 6 ∈ line v := by
  apply mem_line_of_scaled v (570 : ℂ) ((-8) + (4 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation18 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal19 : value v 1 0 3 5 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation19 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal20 : value v 1 1 0 7 ∈ line v := by
  apply mem_line_of_scaled v (570 : ℂ) ((-8) + (4 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation20 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal21 : value v 1 1 1 6 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation21 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal22 : value v 1 1 2 5 ∈ line v := by
  apply mem_line_of_scaled v (2 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation22 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal23 : value v 1 1 3 4 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) (2 + ((-6) * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation23 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal24 : value v 1 4 3 1 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) ((-8) + (4 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation24 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal25 : value v 1 5 2 1 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation25 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal26 : value v 1 5 3 0 ∈ line v := by
  apply mem_line_of_scaled v (5 : ℂ) (8 + ((-4) * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation26 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal27 : value v 1 6 1 1 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation27 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal28 : value v 1 6 2 0 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) (4 + (8 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation28 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal29 : value v 1 7 0 1 ∈ line v := by
  apply mem_line_of_scaled v (285 : ℂ) (4 + (8 * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation29 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal30 : value v 1 7 1 0 ∈ line v := by
  apply mem_line_of_scaled v (1 : ℂ) 0 _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation30 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

private theorem normal31 : value v 1 8 0 0 ∈ line v := by
  apply mem_line_of_scaled v (5 : ℂ) ((-12) + ((-24) * Complex.I)) _ (by norm_num)
  have h := CycleQ2IncidenceTraceData.relation31 (algebraMap ℂ R Complex.I)
    (v 0) (v 1) (v 2) (v 3) i_sq hq hb hc hh
  simpa only [value, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat,
    map_one, map_zero, pow_zero, pow_one, one_mul, mul_one, zero_mul] using h

theorem normal_monomial_mem_line (k : Fin 32) :
    value v (degreeNineExponent k 0) (degreeNineExponent k 1)
      (degreeNineExponent k 2) (degreeNineExponent k 3) ∈ line v := by
  fin_cases k
  · exact normal0 v
  · exact normal1 v hq hb hc hh
  · exact normal2 v hq hb hc hh
  · exact normal3 v hq hb hc hh
  · exact normal4 v hq hb hc hh
  · exact normal5 v hq hb hc hh
  · exact normal6 v hq hb hc hh
  · exact normal7 v hq hb hc hh
  · exact normal8 v hq hb hc hh
  · exact normal9 v hq hb hc hh
  · exact normal10 v hq hb hc hh
  · exact normal11 v hq hb hc hh
  · exact normal12 v hq hb hc hh
  · exact normal13 v hq hb hc hh
  · exact normal14 v hq hb hc hh
  · exact normal15 v hq hb hc hh
  · exact normal16 v hq hb hc hh
  · exact normal17 v hq hb hc hh
  · exact normal18 v hq hb hc hh
  · exact normal19 v hq hb hc hh
  · exact normal20 v hq hb hc hh
  · exact normal21 v hq hb hc hh
  · exact normal22 v hq hb hc hh
  · exact normal23 v hq hb hc hh
  · exact normal24 v hq hb hc hh
  · exact normal25 v hq hb hc hh
  · exact normal26 v hq hb hc hh
  · exact normal27 v hq hb hc hh
  · exact normal28 v hq hb hc hh
  · exact normal29 v hq hb hc hh
  · exact normal30 v hq hb hc hh
  · exact normal31 v hq hb hc hh

end CycleQ2GeometricIncidenceTraceLinear
end

/-!
# The actual incidence numerator quotient

The complete degree-nine component of the four-generator ideal at
r = 57, θ = 1 is spanned by x3^9. The curve and parameters are those
of the original literal incidence construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section
namespace CycleQ2GeometricIncidenceTraceAlgebra
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta

private theorem reorder_h {R : Type*} [CommRing R] (i a b c d : R)
    (h : d ^ 3 + c ^ 3 + b * c * d + a * c * d + a * b ^ 2 -
      i * (b ^ 3 + d ^ 3) + 1 * a ^ 3 = 0) :
    c ^ 3 + (a + b) * d * c + a * b ^ 2 +
      (1 - i) * d ^ 3 - i * b ^ 3 + a ^ 3 = 0 := by
  linear_combination h

def generators : Fin 4 → Poly := ![relation 57 0, relation 57 1, relation 57 2, curveH 1]
def incidenceIdeal : Ideal Poly := Ideal.span (Set.range generators)
def IncidenceAlgebra : Type := Poly ⧸ incidenceIdeal
instance incidenceCommRing : CommRing IncidenceAlgebra :=
  inferInstanceAs (CommRing (Poly ⧸ incidenceIdeal))
instance incidenceComplexAlgebra : Algebra ℂ IncidenceAlgebra :=
  inferInstanceAs (Algebra ℂ (Poly ⧸ incidenceIdeal))

def quotient : Poly →ₐ[ℂ] IncidenceAlgebra := Ideal.Quotient.mkₐ ℂ incidenceIdeal

def normalization : IncidenceAlgebra := quotient (mon 0 0 0 9)
def degreeNineLine : Submodule ℂ IncidenceAlgebra := Submodule.span ℂ {normalization}

def degreeNinePiece : Submodule ℂ IncidenceAlgebra :=
  (homogeneousSubmodule (Fin 4) ℂ 9).map quotient.toLinearMap

theorem generator_mem (k : Fin 4) : generators k ∈ incidenceIdeal :=
  Ideal.subset_span ⟨k, rfl⟩

theorem quotient_generator (k : Fin 4) : quotient (generators k) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (generator_mem k)

private def i : IncidenceAlgebra := quotient (C Complex.I)
private def x (k : Fin 4) : IncidenceAlgebra := quotient (X k)

private theorem i_sq : i ^ 2 + 1 = 0 := by
  unfold i
  rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_one, map_neg, map_one]
  exact neg_add_cancel 1


private theorem q_relation : x 0 ^ 2 - 57 * x 1 * x 3 = 0 := by
  have h := quotient_generator 0
  simpa [generators, relation, x, map_sub, map_mul, map_pow, map_ofNat] using h

private theorem b_relation : x 1 ^ 2 * x 3 ^ 2 = 0 := by
  have h := quotient_generator 1
  simpa [generators, relation, x, map_sub, map_mul, map_pow, map_ofNat] using h

private theorem c_relation : x 2 ^ 4 = 0 := by
  have h := quotient_generator 2
  simpa [generators, relation, x, map_sub, map_mul, map_pow, map_ofNat] using h

private theorem h_relation : x 2 ^ 3 + (x 0 + x 1) * x 3 * x 2 +
    x 0 * x 1 ^ 2 + (1 - i) * x 3 ^ 3 - i * x 1 ^ 3 + x 0 ^ 3 = 0 := by
  have h := quotient_generator 3
  simp only [generators, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    curveH, CycleQ2SeedTrace.h, b, map_add, map_sub, map_mul, map_pow, map_one] at h
  change quotient (X 3) ^ 3 + quotient (X 2) ^ 3 +
      quotient (X 1) * quotient (X 2) * quotient (X 3) +
      quotient (X 0) * quotient (X 2) * quotient (X 3) +
      quotient (X 0) * quotient (X 1) ^ 2 -
      quotient (C Complex.I) * (quotient (X 1) ^ 3 + quotient (X 3) ^ 3) +
      1 * quotient (X 0) ^ 3 = 0 at h
  exact reorder_h (quotient (C Complex.I)) (quotient (X 0))
    (quotient (X 1)) (quotient (X 2)) (quotient (X 3)) h


theorem normalization_mem_line : normalization ∈ degreeNineLine :=
  Submodule.subset_span (Set.mem_singleton _)

theorem class_mem_line_of_scaled (scale z : ℂ) (p : Poly) (hs : scale ≠ 0)
    (heq : scale • quotient p = z • normalization) : quotient p ∈ degreeNineLine := by
  apply (degreeNineLine.smul_mem_iff hs).mp
  rw [heq]
  exact degreeNineLine.smul_mem z normalization_mem_line

@[simp] theorem quotient_C (c : ℂ) : quotient (C c) = algebraMap ℂ IncidenceAlgebra c :=
  quotient.commutes c

theorem quotient_scalar_mul (c : ℂ) (p : Poly) :
    c • quotient p = quotient (C c) * quotient p := by
  rw [← map_smul, smul_eq_C_mul, map_mul]

theorem degreeNineMonomial_mem_line (k : Fin 32) :
    quotient (degreeNineMonomial k) ∈ degreeNineLine := by
  have hh : (fun k : Fin 4 => quotient (X k)) 2 ^ 3 +
      ((fun k : Fin 4 => quotient (X k)) 0 + (fun k : Fin 4 => quotient (X k)) 1) *
        (fun k : Fin 4 => quotient (X k)) 3 * (fun k : Fin 4 => quotient (X k)) 2 +
      (fun k : Fin 4 => quotient (X k)) 0 * (fun k : Fin 4 => quotient (X k)) 1 ^ 2 +
      (1 - algebraMap ℂ IncidenceAlgebra Complex.I) * (fun k : Fin 4 => quotient (X k)) 3 ^ 3 -
      algebraMap ℂ IncidenceAlgebra Complex.I * (fun k : Fin 4 => quotient (X k)) 1 ^ 3 +
      (fun k : Fin 4 => quotient (X k)) 0 ^ 3 = 0 := by
    simpa only [x, i, quotient_C] using h_relation
  have h := CycleQ2GeometricIncidenceTraceLinear.normal_monomial_mem_line
    (fun k => quotient (X k)) q_relation b_relation c_relation hh k
  simpa only [degreeNineMonomial, degreeNineLine, normalization,
    CycleQ2GeometricIncidenceTraceLinear.value, CycleQ2GeometricIncidenceTraceLinear.line,
    mon, map_mul, map_pow, pow_zero, pow_one, one_mul, mul_one] using h


theorem quotient_eq_smul_of_relation (z : ℂ) (p q : Poly)
    (hp : p - C z * q ∈ incidenceIdeal) :
    quotient p = z • quotient q := by
  have hz : quotient (p - C z * q) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero] at hz
  exact hz

theorem quotient_mon_add_two (a b c d : ℕ) :
    quotient (mon (a + 2) b c d) =
      (57 : ℂ) • quotient (mon a (b + 1) c (d + 1)) := by
  apply quotient_eq_smul_of_relation
  have hpoly : mon (a + 2) b c d - C (57 : ℂ) * mon a (b + 1) c (d + 1) =
      generators 0 * mon a b c d := by
    simp only [mon, generators, relation, Matrix.cons_val_zero, pow_add, pow_one]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨0, rfl⟩)

theorem quotient_mon_c_add_four_zero (a b c d : ℕ) :
    quotient (mon a b (c + 4) d) = 0 := by
  change Ideal.Quotient.mk incidenceIdeal (mon a b (c + 4) d) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a b (c + 4) d = generators 2 * mon a b c d := by
    norm_num [mon, generators, relation, pow_add, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨2, rfl⟩)

theorem quotient_mon_bd_add_two_zero (a b c d : ℕ) :
    quotient (mon a (b + 2) c (d + 2)) = 0 := by
  change Ideal.Quotient.mk incidenceIdeal (mon a (b + 2) c (d + 2)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hpoly : mon a (b + 2) c (d + 2) = generators 1 * mon a b c d := by
    norm_num [mon, generators, relation, pow_add]
    ring
  rw [hpoly]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨1, rfl⟩)


theorem degreeNine_mon_class_mem_line     (a b c d : ℕ) (hdegree : a + b + c + d = 9) :
    quotient (mon a b c d) ∈ degreeNineLine := by
  induction a using Nat.strong_induction_on generalizing b c d with
  | h a ih =>
      by_cases ha : a < 2
      · by_cases hc : c < 4
        · by_cases hbd : b < 2 ∨ d < 2
          · obtain ⟨i, hi⟩ := degreeNine_normal_complete a b c d ha hc hbd hdegree
            rw [← hi]
            exact degreeNineMonomial_mem_line i
          · have hb : b = (b - 2) + 2 := by omega
            have hd : d = (d - 2) + 2 := by omega
            rw [hb, hd, quotient_mon_bd_add_two_zero]
            exact Submodule.zero_mem _
        · have hc' : c = (c - 4) + 4 := by omega
          rw [hc', quotient_mon_c_add_four_zero]
          exact Submodule.zero_mem _
      · have ha' : a = (a - 2) + 2 := by omega
        rw [ha', quotient_mon_add_two]
        apply Submodule.smul_mem
        exact ih (a - 2) (by omega) (b + 1) c (d + 1) (by omega)

theorem homogeneous_degreeNine_class_mem_line     {p : Poly} (hp : p.IsHomogeneous 9) :
    quotient p ∈ degreeNineLine := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (degreeNineLine).zero_mem
  | add p q _ _ hp hq =>
      simpa only [map_add] using (degreeNineLine).add_mem hp hq
  | monomial d z hd =>
      rw [monomial_eq_C_mul_mon, ← smul_eq_C_mul, map_smul]
      apply Submodule.smul_mem
      apply degreeNine_mon_class_mem_line
      have hdegree : d.degree = 9 := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      rw [Finsupp.degree_eq_sum] at hdegree
      norm_num [Fin.sum_univ_succ] at hdegree
      rw [show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl] at hdegree
      omega


theorem degreeNine_class_eq_smul {p : Poly} (hp : p.IsHomogeneous 9) :
    ∃ c : ℂ, quotient p = c • normalization := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (homogeneous_degreeNine_class_mem_line hp)
  exact ⟨c, hc.symm⟩


theorem x0_normal_zero : quotient (mon 1 0 0 8) = 0 := by
  have h : (4 : ℂ) • quotient (mon 1 0 0 8) = 0 := by
    have h := CycleQ2IncidenceTraceData.relation16 i (x 0) (x 1) (x 2) (x 3)
      i_sq q_relation b_relation c_relation h_relation
    rw [quotient_scalar_mul]
    simpa only [mon, map_mul, map_pow,
      map_add, map_sub, map_neg, map_ofNat, map_one, map_zero, quotient_C,
      pow_zero, pow_one, one_mul, mul_one, zero_mul, i, x] using h
  have hh := congrArg (fun a : IncidenceAlgebra => (4 : ℂ)⁻¹ • a) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (4 : ℂ) ≠ 0),
    one_smul, smul_zero] using hh

theorem x1_normal_zero : quotient (mon 0 1 0 8) = 0 := by
  have h : (2 : ℂ) • quotient (mon 0 1 0 8) = 0 := by
    have h := CycleQ2IncidenceTraceData.relation4 i (x 0) (x 1) (x 2) (x 3)
      i_sq q_relation b_relation c_relation h_relation
    rw [quotient_scalar_mul]
    simpa only [mon, map_mul, map_pow,
      map_add, map_sub, map_neg, map_ofNat, map_one, map_zero, quotient_C,
      pow_zero, pow_one, one_mul, mul_one, zero_mul, i, x] using h
  have hh := congrArg (fun a : IncidenceAlgebra => (2 : ℂ)⁻¹ • a) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul, smul_zero] using hh

theorem x2_squared_normal_zero : quotient (mon 0 0 2 7) = 0 := by
  have h : (2 : ℂ) • quotient (mon 0 0 2 7) = 0 := by
    have h := CycleQ2IncidenceTraceData.relation2 i (x 0) (x 1) (x 2) (x 3)
      i_sq q_relation b_relation c_relation h_relation
    rw [quotient_scalar_mul]
    simpa only [mon, map_mul, map_pow,
      map_add, map_sub, map_neg, map_ofNat, map_one, map_zero, quotient_C,
      pow_zero, pow_one, one_mul, mul_one, zero_mul, i, x] using h
  have hh := congrArg (fun a : IncidenceAlgebra => (2 : ℂ)⁻¹ • a) h
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : ℂ) ≠ 0),
    one_smul, smul_zero] using hh

theorem x2_normal_relation :
    (1140 : ℂ) • quotient (mon 0 0 1 8) = (24 + 8 * Complex.I) • normalization := by
  have h := CycleQ2IncidenceTraceData.relation1 i (x 0) (x 1) (x 2) (x 3)
    i_sq q_relation b_relation c_relation h_relation
  unfold normalization
  rw [quotient_scalar_mul, quotient_scalar_mul]
  simpa only [mon, map_mul, map_pow,
    map_add, map_sub, map_neg, map_ofNat, map_one, map_zero, quotient_C,
    pow_zero, pow_one, one_mul, mul_one, zero_mul, i, x] using h



/-- The only first nonzero cubic-column coefficient, certified in the
literal numerator quotient. -/
theorem paired_first_column_coefficient :
    quotient (mon 0 0 3 6) = ((-4 + 2 * Complex.I) / 5 : ℂ) • normalization := by
  have h := CycleQ2IncidenceTraceData.relation3 i (x 0) (x 1) (x 2) (x 3)
    i_sq q_relation b_relation c_relation h_relation
  have heq : (10 : ℂ) • quotient (mon 0 0 3 6) =
      (-8 + 4 * Complex.I : ℂ) • normalization := by
    unfold normalization
    rw [quotient_scalar_mul, quotient_scalar_mul]
    simpa only [mon, normalization, x, i, map_mul, map_pow, map_add,
      map_neg, map_ofNat, pow_zero, one_mul, mul_one] using h
  have hh := congrArg (fun z : IncidenceAlgebra => (10 : ℂ)⁻¹ • z) heq
  have hs : (10 : ℂ)⁻¹ * (-8 + 4 * Complex.I) = (-4 + 2 * Complex.I) / 5 := by ring
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (10 : ℂ) ≠ 0),
    one_smul, hs] using hh

/-- The second nonzero cubic-column coefficient before its single
quadratic reduction by x0 squared equals 57*x1*x3. -/
theorem paired_last_column_reduced_coefficient :
    quotient (mon 1 1 3 4) = ((2 - 6 * Complex.I) / 285 : ℂ) • normalization := by
  have h := CycleQ2IncidenceTraceData.relation23 i (x 0) (x 1) (x 2) (x 3)
    i_sq q_relation b_relation c_relation h_relation
  have heq : (285 : ℂ) • quotient (mon 1 1 3 4) =
      (2 - 6 * Complex.I : ℂ) • normalization := by
    unfold normalization
    rw [quotient_scalar_mul, quotient_scalar_mul]
    simpa only [mon, normalization, x, i, map_mul, map_pow, map_sub, map_add,
      map_neg, map_ofNat, pow_one, pow_zero, one_mul, sub_eq_add_neg, neg_mul] using h
  have hh := congrArg (fun z : IncidenceAlgebra => (285 : ℂ)⁻¹ • z) heq
  simpa only [smul_smul, inv_mul_cancel₀ (by norm_num : (285 : ℂ) ≠ 0),
    one_smul, div_eq_mul_inv, mul_comm] using hh

end CycleQ2GeometricIncidenceTraceAlgebra
end

/-!
# Arbitrary poles on the literal incidence curve

The exact degree-nine reduction at r = 57 and θ = 1 also shows that
all four coordinates annihilate the spanning numerator. Consequently
every homogeneous polynomial of degree greater than nine belongs to
the actual four-generator ideal used by its Cech boundary theorem.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricIncidenceTraceAlgebra
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2GeometricKoszulTrace

private theorem tuple_span_le {R : Type*} [CommRing R] (I : Ideal R)
    (a b c d : R) (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) (hd : d ∈ I) :
    Ideal.span (Set.range (![a, b, c, d] : Fin 4 → R)) ≤ I := by
  apply Ideal.span_le.mpr
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact ha
  · exact hb
  · exact hc
  · exact hd

private theorem incidenceIdeal_le_of_mem (I : Ideal Poly)
    (hq : relation 57 0 ∈ I) (hh : curveH 1 ∈ I)
    (hg1 : firstQuartic 57 ∈ I) (hg2 : secondQuartic ∈ I) :
    incidenceIdeal ≤ I := by
  change Ideal.span (Set.range
    (![relation 57 0, relation 57 1, relation 57 2, curveH 1] : Fin 4 → Poly)) ≤ I
  apply tuple_span_le
  · exact hq
  · have hm : C ((3 * (57 : ℂ) ^ 2)⁻¹) * firstQuartic 57 ∈ I :=
      I.mul_mem_left _ hg1
    have heq : C ((3 * (57 : ℂ) ^ 2)⁻¹) * firstQuartic 57 = relation 57 1 := by
      unfold firstQuartic
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one, one_mul]
      simp [relation, CycleQ2SeedCech.curveA, mul_pow]
    exact heq ▸ hm
  · have hm : C ((3 : ℂ)⁻¹) * secondQuartic ∈ I := I.mul_mem_left _ hg2
    have heq : C ((3 : ℂ)⁻¹) * secondQuartic = relation 57 2 := by
      unfold secondQuartic
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one, one_mul]
      rfl
    exact heq ▸ hm
  · exact hh

theorem incidenceIdeal_le_fourGenerator : incidenceIdeal ≤ fourGeneratorIdeal 57 1 := by
  apply incidenceIdeal_le_of_mem
  ·
    change relation 57 0 ∈ Ideal.span ({relation 57 0, curveH 1, firstQuartic 57, secondQuartic} : Set Poly)
    exact Ideal.subset_span (Or.inl rfl)
  ·
    change curveH 1 ∈ Ideal.span ({relation 57 0, curveH 1, firstQuartic 57, secondQuartic} : Set Poly)
    exact Ideal.subset_span (Or.inr (Or.inl rfl))
  ·
    change firstQuartic 57 ∈ Ideal.span ({relation 57 0, curveH 1, firstQuartic 57, secondQuartic} : Set Poly)
    exact Ideal.subset_span (Or.inr (Or.inr (Or.inl rfl)))
  ·
    change secondQuartic ∈ Ideal.span ({relation 57 0, curveH 1, firstQuartic 57, secondQuartic} : Set Poly)
    exact Ideal.subset_span (Or.inr (Or.inr (Or.inr rfl)))

end CycleQ2GeometricIncidenceTraceAlgebra

namespace CycleQ2GeometricIncidencePoleReduction

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricKoszulTrace
  CycleQ2GeometricIncidenceTraceAlgebra

theorem coordinate_mul_normalization (k : Fin 4) :
    quotient (X k) * normalization = 0 := by
  have hx0 : quotient (X 0) * normalization = 0 := by
    calc
      quotient (X 0) * normalization = quotient (X 3) * quotient (mon 1 0 0 8) := by
        unfold normalization
        rw [← map_mul, ← map_mul]
        apply congrArg quotient
        simp only [mon, pow_zero, pow_one, one_mul, mul_one]
        ring
      _ = 0 := by rw [x0_normal_zero, mul_zero]
  have hx1 : quotient (X 1) * normalization = 0 := by
    calc
      quotient (X 1) * normalization = quotient (X 3) * quotient (mon 0 1 0 8) := by
        unfold normalization
        rw [← map_mul, ← map_mul]
        apply congrArg quotient
        simp only [mon, pow_zero, pow_one, one_mul, mul_one]
        ring
      _ = 0 := by rw [x1_normal_zero, mul_zero]
  have hc : (24 + 8 * Complex.I : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
  have hquad : quotient (X 2) * quotient (mon 0 0 1 8) = 0 := by
    calc
      quotient (X 2) * quotient (mon 0 0 1 8) =
          quotient (X 3) * quotient (mon 0 0 2 7) := by
        rw [← map_mul, ← map_mul]
        apply congrArg quotient
        simp only [mon, pow_zero, pow_one, one_mul, mul_one]
        ring
      _ = 0 := by rw [x2_squared_normal_zero, mul_zero]
  have hx2 : quotient (X 2) * normalization = 0 := by
    have hz := congrArg (fun a => quotient (X 2) * a) x2_normal_relation
    rw [mul_smul_comm, mul_smul_comm, hquad, smul_zero] at hz
    have hh := congrArg (fun a : IncidenceAlgebra => (24 + 8 * Complex.I : ℂ)⁻¹ • a) hz.symm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] using hh
  have hx3 : quotient (X 3) * normalization = 0 := by
    have heq : quotient (X 3) * quotient (mon 0 0 1 8) =
        quotient (X 2) * normalization := by
      unfold normalization
      rw [← map_mul, ← map_mul]
      apply congrArg quotient
      simp only [mon, pow_zero, pow_one, one_mul, mul_one]
      ring
    have hz := congrArg (fun a => quotient (X 3) * a) x2_normal_relation
    rw [mul_smul_comm, mul_smul_comm, heq, hx2, smul_zero] at hz
    have hh := congrArg (fun a : IncidenceAlgebra => (24 + 8 * Complex.I : ℂ)⁻¹ • a) hz.symm
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul, smul_zero] using hh
  fin_cases k
  · exact hx0
  · exact hx1
  · exact hx2
  · exact hx3

private theorem positive_monomial_mul_normalization
    (d : Fin 4 →₀ ℕ) (hd : 0 < d.degree) (z : ℂ) :
    quotient (monomial d z) * normalization = 0 := by
  classical
  have hd0 : d ≠ 0 := by intro h; simp [h] at hd
  obtain ⟨k, hk⟩ := Finsupp.support_nonempty_iff.mpr hd0
  have hle : Finsupp.single k 1 ≤ d :=
    Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk))
  have heq : d = Finsupp.single k 1 + (d - Finsupp.single k 1) :=
    (add_tsub_cancel_of_le hle).symm
  have hmon : monomial d z = (X k : Poly) * monomial (d - Finsupp.single k 1) z := by
    rw [X, monomial_mul, one_mul, ← heq]
  rw [hmon, map_mul, mul_right_comm, coordinate_mul_normalization k, zero_mul]

/-- All higher degrees vanish in the actual incidence numerator quotient,
with no bound on the degree or initial pole orders. -/
theorem homogeneous_mem_incidenceIdeal_of_degree_gt_nine
    {n : ℕ} (hn : 9 < n) {p : Poly} (hp : p.IsHomogeneous n) : p ∈ incidenceIdeal := by
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change quotient p = 0
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => exact map_zero _
  | add p q _ _ hp hq => rw [map_add, hp, hq, add_zero]
  | monomial d z hd =>
      have hdegree : d.degree = n := by
        simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hd
      obtain ⟨e, hed, he⟩ := Finsupp.exists_le_degree_eq d 9 (by omega)
      have hsplit : d = (d - e) + e := (tsub_add_cancel_of_le hed).symm
      have hpositive : 0 < (d - e).degree := by
        have hs : d.degree = (d - e).degree + e.degree := by
          simpa only [map_add] using congrArg Finsupp.degree hsplit
        omega
      have hehom : (monomial e (1 : ℂ)).IsHomogeneous 9 := isHomogeneous_monomial _ he
      obtain ⟨c, hclass⟩ := degreeNine_class_eq_smul hehom
      have hmon : monomial d z = monomial (d - e) z * monomial e (1 : ℂ) := by
        rw [monomial_mul, mul_one, ← hsplit]
      rw [hmon, map_mul, hclass, mul_smul_comm,
        positive_monomial_mul_normalization (d - e) hpositive z, smul_zero]

theorem homogeneous_mem_fourGeneratorIdeal_of_degree_gt_nine
    {n : ℕ} (hn : 9 < n) {p : Poly} (hp : p.IsHomogeneous n) :
    p ∈ fourGeneratorIdeal 57 1 :=
  incidenceIdeal_le_fourGenerator (homogeneous_mem_incidenceIdeal_of_degree_gt_nine hn hp)

end CycleQ2GeometricIncidencePoleReduction
end

/-!
# Surjectivity of the actual homogeneous simple-pole presentation

Arbitrary degree-one overlap sections are reduced by their two pole orders.
Above degree nine, the actual numerator lies in the four-generator ideal.
Homogeneous coefficient extraction lowers one pole order in each summand;
sections with only one denominator are actual chart boundaries.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricIncidenceCechSurjectivity

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricKoszulTrace
  CycleQ2GeometricIncidencePoleReduction CycleQ2GeometricIncidenceTraceAlgebra
  CycleQ2GeometricCechComplex

theorem high_degree_curve_relation
    {n : ℕ} (hn : 9 < n) (p : Poly) (hp : p.IsHomogeneous n) :
    ∃ c d : Poly, c.IsHomogeneous (n - 4) ∧ d.IsHomogeneous (n - 4) ∧
      curveMap 57 1 p = curveMap 57 1 c * curveG1 57 1 + curveMap 57 1 d * curveG2 57 1 := by
  let v : Fin 4 → Poly := ![relation 57 0, curveH 1, firstQuartic 57, secondQuartic]
  let deg : Fin 4 → ℕ := ![2, 3, 4, 4]
  have hv : ∀ i, (v i).IsHomogeneous (deg i) := by
    intro i
    fin_cases i
    · exact relation_zero_homogeneous 57
    · exact sparse_curveH_homogeneous 1
    · exact firstQuartic_homogeneous 57
    · exact secondQuartic_homogeneous
  have hmem : p ∈ Ideal.span (Set.range v) := by
    have hmem := homogeneous_mem_fourGeneratorIdeal_of_degree_gt_nine hn hp
    simpa only [fourGeneratorIdeal, v, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using hmem
  obtain ⟨q, hq, _, heq⟩ :=
    CycleQ2GeometricGradedWitness.exists_homogeneous_coefficients deg v hv n p hp hmem
  refine ⟨q 2, q 3, hq 2, hq 3, ?_⟩
  rw [← heq]
  simp only [map_add, map_mul, Fin.sum_univ_succ, v, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, curveMap_f1, curveMap_h,
    mul_zero, zero_add, curveMap_firstQuartic, curveMap_secondQuartic]
  rfl

/-- An actual overlap fraction with independent pole orders at the two
quartics. The balanced denominator only presents the same localization. -/
def mixedFraction  (n m : ℕ) (a : CurveRing 57 1) : Overlap 57 1 :=
  awayFraction 57 1 (curveG1 57 1 * curveG2 57 1) (n + m)
    (a * curveG1 57 1 ^ m * curveG2 57 1 ^ n)

theorem mixedFraction_add  (n m : ℕ) (a b : CurveRing 57 1) :
    mixedFraction n m (a + b) = mixedFraction n m a + mixedFraction n m b := by
  simp only [mixedFraction, awayFraction, add_mul, Localization.add_mk_self]

theorem mixedFraction_mul_first  (n m : ℕ) (a : CurveRing 57 1) :
    mixedFraction (n + 1) m (a * curveG1 57 1) = mixedFraction n m a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 57 1 * curveG2 57 1) ^ (n + 1 + m) *
      (a * curveG1 57 1 ^ m * curveG2 57 1 ^ n) =
    (curveG1 57 1 * curveG2 57 1) ^ (n + m) *
      (a * curveG1 57 1 * curveG1 57 1 ^ m * curveG2 57 1 ^ (n + 1))
  rw [show n + 1 + m = (n + m) + 1 by omega, pow_succ, pow_succ]
  ring

theorem mixedFraction_mul_second  (n m : ℕ) (a : CurveRing 57 1) :
    mixedFraction n (m + 1) (a * curveG2 57 1) = mixedFraction n m a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 57 1 * curveG2 57 1) ^ (n + (m + 1)) *
      (a * curveG1 57 1 ^ m * curveG2 57 1 ^ n) =
    (curveG1 57 1 * curveG2 57 1) ^ (n + m) *
      (a * curveG2 57 1 * curveG1 57 1 ^ (m + 1) * curveG2 57 1 ^ n)
  rw [show n + (m + 1) = (n + m) + 1 by omega, pow_succ, pow_succ]
  ring

theorem mixedFraction_balanced  (n : ℕ) (a : CurveRing 57 1) :
    mixedFraction n n a = awayFraction 57 1 (curveG1 57 1 * curveG2 57 1) n a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 57 1 * curveG2 57 1) ^ (n + n) * a =
    (curveG1 57 1 * curveG2 57 1) ^ n *
      (a * curveG1 57 1 ^ n * curveG2 57 1 ^ n)
  rw [pow_add, mul_pow]
  ring

def mixedRepresentative  (n m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m))) : OverlapDegreeOne 57 1 :=
  ⟨mixedFraction n m (curveMap 57 1 p), by
    apply awayFraction_mem_degreeOne 57 1 _ 8 (curveG12_mem_grade 57 1) (n + m)
    have hgrade := SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (curveMap_mem_grade 57 1 hp)
        (SetLike.pow_mem_graded m (curveG1_mem_grade 57 1)))
      (SetLike.pow_mem_graded n (curveG2_mem_grade 57 1))
    have hdegree : 1 + 4 * (n + m) + m * 4 + n * 4 = 1 + (n + m) * 8 := by omega
    simpa only [nsmul_eq_mul, Nat.cast_id, hdegree] using hgrade⟩

def mixedCechClass  (n m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m))) : DegreeOneCech 57 1 :=
  QuotientAddGroup.mk (mixedRepresentative n m p hp)

theorem mixedCechClass_add  (n m : ℕ) (p q : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m)))
    (hq : q.IsHomogeneous (1 + 4 * (n + m))) :
    mixedCechClass n m (p + q) (hp.add hq) =
      mixedCechClass n m p hp + mixedCechClass n m q hq := by
  have hrep : mixedRepresentative n m (p + q) (hp.add hq) =
      mixedRepresentative n m p hp + mixedRepresentative n m q hq := by
    apply Subtype.ext
    exact (congrArg (mixedFraction n m) (map_add (curveMap 57 1) p q)).trans
      (mixedFraction_add n m _ _)
  change (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _ =
    (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _ +
      (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _
  rw [hrep, map_add]

def firstPoleSection  (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * n)) : FirstDegreeOne 57 1 :=
  ⟨awayFraction 57 1 (curveG1 57 1) n (curveMap 57 1 p),
    awayFraction_mem_degreeOne 57 1 _ 4 (curveG1_mem_grade 57 1) n _
      (by simpa only [Nat.mul_comm] using curveMap_mem_grade 57 1 hp)⟩

def secondPoleSection  (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * m)) : SecondDegreeOne 57 1 :=
  ⟨awayFraction 57 1 (curveG2 57 1) m (curveMap 57 1 p),
    awayFraction_mem_degreeOne 57 1 _ 4 (curveG2_mem_grade 57 1) m _
      (by simpa only [Nat.mul_comm] using curveMap_mem_grade 57 1 hp)⟩

theorem mixedRepresentative_first  (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + 0))) :
    mixedRepresentative n 0 p hp =
      firstDegreeOneRestriction 57 1 (firstPoleSection n p (by simpa using hp)) := by
  apply Subtype.ext
  change mixedFraction n 0 (curveMap 57 1 p) =
    awayRestriction 57 1 (curveG1 57 1) (curveG2 57 1) (curveG1 57 1 * curveG2 57 1) rfl
      (awayFraction 57 1 (curveG1 57 1) n (curveMap 57 1 p))
  rw [awayRestriction_fraction]
  simp only [mixedFraction, Nat.add_zero, pow_zero, mul_one]

theorem mixedRepresentative_second  (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (0 + m))) :
    mixedRepresentative 0 m p hp =
      secondDegreeOneRestriction 57 1 (secondPoleSection m p (by simpa using hp)) := by
  apply Subtype.ext
  change mixedFraction 0 m (curveMap 57 1 p) =
    awayRestriction 57 1 (curveG2 57 1) (curveG1 57 1) (curveG1 57 1 * curveG2 57 1)
      (mul_comm _ _) (awayFraction 57 1 (curveG2 57 1) m (curveMap 57 1 p))
  rw [awayRestriction_fraction]
  simp only [mixedFraction, Nat.zero_add, pow_zero, mul_one]

theorem mixedCechClass_first_zero  (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + 0))) : mixedCechClass n 0 p hp = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(firstPoleSection n p (by simpa using hp), 0), ?_⟩
  rw [mixedRepresentative_first]
  simp [degreeOneCoboundary]

theorem mixedCechClass_second_zero  (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (0 + m))) : mixedCechClass 0 m p hp = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(0, -(secondPoleSection m p (by simpa using hp))), ?_⟩
  rw [mixedRepresentative_second]
  simp [degreeOneCoboundary]

theorem mixedCechClass_one_one  (p : Poly) (hp : p.IsHomogeneous 9) :
    mixedCechClass 1 1 p hp = degreeNineCechClass 57 1 p hp := by
  apply congrArg QuotientAddGroup.mk
  apply Subtype.ext
  exact mixedFraction_balanced 1 (curveMap 57 1 p)

theorem degreeNineCechClass_zero  :
    degreeNineCechClass 57 1 0 (isHomogeneous_zero (Fin 4) ℂ 9) = 0 := by
  have hz : degreeNineRepresentative 57 1 0 (isHomogeneous_zero (Fin 4) ℂ 9) = 0 := by
    apply Subtype.ext
    change awayFraction 57 1 (curveG1 57 1 * curveG2 57 1) 1 (curveMap 57 1 0) = 0
    rw [map_zero]
    exact Localization.mk_zero _
  change (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _ = 0
  rw [hz, map_zero]

theorem degreeNineCechClass_add  (p q : Poly)
    (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9) :
    degreeNineCechClass 57 1 (p + q) (hp.add hq) =
      degreeNineCechClass 57 1 p hp + degreeNineCechClass 57 1 q hq := by
  rw [← mixedCechClass_one_one, ← mixedCechClass_one_one, ← mixedCechClass_one_one]
  exact mixedCechClass_add 1 1 p q hp hq

theorem mixedCechClass_relation  (n m : ℕ) (p c d : Poly)
    (hp : p.IsHomogeneous (1 + 4 * ((n + 1) + (m + 1))))
    (hc : c.IsHomogeneous (1 + 4 * (n + (m + 1))))
    (hd : d.IsHomogeneous (1 + 4 * ((n + 1) + m)))
    (hrelation : curveMap 57 1 p =
      curveMap 57 1 c * curveG1 57 1 + curveMap 57 1 d * curveG2 57 1) :
    mixedCechClass (n + 1) (m + 1) p hp =
      mixedCechClass n (m + 1) c hc + mixedCechClass (n + 1) m d hd := by
  have hrep : mixedRepresentative (n + 1) (m + 1) p hp =
      mixedRepresentative n (m + 1) c hc + mixedRepresentative (n + 1) m d hd := by
    apply Subtype.ext
    change mixedFraction (n + 1) (m + 1) (curveMap 57 1 p) =
      mixedFraction n (m + 1) (curveMap 57 1 c) +
        mixedFraction (n + 1) m (curveMap 57 1 d)
    rw [hrelation, mixedFraction_add, mixedFraction_mul_first, mixedFraction_mul_second]
  change (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _ =
    (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _ +
      (QuotientAddGroup.mk' (degreeOneBoundaries 57 1)) _
  rw [hrep, map_add]

/-- Every pair of homogeneous pole orders reduces to an actual
degree-nine numerator with simple poles at both quartics. -/
theorem mixedCechClass_exists_degreeNine
    (n m : ℕ) (p : Poly) (hp : p.IsHomogeneous (1 + 4 * (n + m))) :
    ∃ (q : Poly) (hq : q.IsHomogeneous 9),
      mixedCechClass n m p hp = degreeNineCechClass 57 1 q hq := by
  have aux : ∀ s n m, n + m = s →
      ∀ (p : Poly) (hp : p.IsHomogeneous (1 + 4 * (n + m))),
        ∃ (q : Poly) (hq : q.IsHomogeneous 9),
          mixedCechClass n m p hp = degreeNineCechClass 57 1 q hq := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro n m hsum p hp
        cases n with
        | zero =>
            refine ⟨0, isHomogeneous_zero (Fin 4) ℂ 9, ?_⟩
            rw [mixedCechClass_second_zero, degreeNineCechClass_zero]
        | succ n =>
            cases m with
            | zero =>
                refine ⟨0, isHomogeneous_zero (Fin 4) ℂ 9, ?_⟩
                rw [mixedCechClass_first_zero, degreeNineCechClass_zero]
            | succ m =>
                by_cases hbase : n = 0 ∧ m = 0
                · obtain ⟨rfl, rfl⟩ := hbase
                  exact ⟨p, hp, mixedCechClass_one_one p hp⟩
                · have hhigh : 9 < 1 + 4 * ((n + 1) + (m + 1)) := by omega
                  obtain ⟨c, d, hc, hd, hrelation⟩ :=
                    high_degree_curve_relation hhigh p hp
                  have hc' : c.IsHomogeneous (1 + 4 * (n + (m + 1))) := by
                    convert hc using 1; omega
                  have hd' : d.IsHomogeneous (1 + 4 * ((n + 1) + m)) := by
                    convert hd using 1; omega
                  obtain ⟨qc, hqc, heqc⟩ :=
                    ih (n + (m + 1)) (by omega) n (m + 1) rfl c hc'
                  obtain ⟨qd, hqd, heqd⟩ :=
                    ih ((n + 1) + m) (by omega) (n + 1) m rfl d hd'
                  refine ⟨qc + qd, hqc.add hqd, ?_⟩
                  rw [mixedCechClass_relation n m p c d hp hc' hd' hrelation,
                    heqc, heqd, degreeNineCechClass_add]
  exact aux (n + m) n m rfl p hp

/-- The degree-nine simple-pole construction is surjective onto the
entire actual degree-one Cech quotient, including arbitrary pole orders.
No geometric Serre-duality or comparison assumption is supplied. -/
theorem degreeNineCechClass_surjective
    (z : DegreeOneCech 57 1) :
    ∃ (p : Poly) (hp : p.IsHomogeneous 9), degreeNineCechClass 57 1 p hp = z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨n, a, ha, hax⟩ := x.property
  obtain ⟨p, hp, hpa⟩ := ha
  change p.IsHomogeneous (1 + n * 8) at hp
  change curveMap 57 1 p = a at hpa
  have hp' : p.IsHomogeneous (1 + 4 * (n + n)) := by
    convert hp using 1 <;> omega
  have hx : mixedRepresentative n n p hp' = x := by
    apply Subtype.ext
    change mixedFraction n n (curveMap 57 1 p) = (x : Overlap 57 1)
    rw [mixedFraction_balanced, hpa]
    exact hax
  obtain ⟨q, hq, heq⟩ := mixedCechClass_exists_degreeNine n n p hp'
  refine ⟨q, hq, ?_⟩
  rw [← heq]
  change QuotientAddGroup.mk (mixedRepresentative n n p hp') = QuotientAddGroup.mk x
  exact congrArg QuotientAddGroup.mk hx

/-- The actual degree-one incidence class of the fixed top numerator. -/
def incidenceCechNormalization : DegreeOneCech 57 1 :=
  degreeNineCechClass 57 1 (mon 0 0 0 9) (mon_homogeneous 0 0 0 9)

/-- A specified coefficient in the actual numerator quotient is the same
coefficient of the actual homogeneous Cech class. -/
theorem degreeNineCechClass_eq_smul_of_quotient_eq
    (p : Poly) (hp : p.IsHomogeneous 9) (c : ℂ)
    (hc : quotient p = c • normalization) :
    degreeNineCechClass 57 1 p hp = c • incidenceCechNormalization := by
  have hmem : p - C c * mon 0 0 0 9 ∈ fourGeneratorIdeal 57 1 := by
    apply incidenceIdeal_le_fourGenerator
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    change quotient (p - C c * mon 0 0 0 9) = 0
    rw [map_sub, ← smul_eq_C_mul, map_smul, sub_eq_zero]
    exact hc
  have hz := degreeNineCechClass_zero_of_mem 57 1
    (p - C c * mon 0 0 0 9) (hp.sub ((mon_homogeneous 0 0 0 9).C_mul c)) hmem
  rw [degreeNineCechClass_sub 57 1 p (C c * mon 0 0 0 9)
    hp ((mon_homogeneous 0 0 0 9).C_mul c), sub_eq_zero] at hz
  refine hz.trans ?_
  exact degreeNineCechClass_C_mul 57 1 c (mon 0 0 0 9) (mon_homogeneous 0 0 0 9)

theorem degreeNineCechClass_eq_smul (p : Poly) (hp : p.IsHomogeneous 9) :
    ∃ c : ℂ, degreeNineCechClass 57 1 p hp = c • incidenceCechNormalization := by
  obtain ⟨c, hc⟩ := degreeNine_class_eq_smul hp
  exact ⟨c, degreeNineCechClass_eq_smul_of_quotient_eq p hp c hc⟩

/-- Every class in the existing incidence Cech quotient, with arbitrary
initial pole orders, is a complex multiple of its fixed normalization.
This theorem has no regularity, trace-comparison or rank hypothesis. -/
theorem every_class_eq_smul (z : DegreeOneCech 57 1) :
    ∃ c : ℂ, z = c • incidenceCechNormalization := by
  obtain ⟨p, hp, hpz⟩ := degreeNineCechClass_surjective z
  obtain ⟨c, hc⟩ := degreeNineCechClass_eq_smul p hp
  exact ⟨c, hpz.symm.trans hc⟩

end CycleQ2GeometricIncidenceCechSurjectivity
end

/-! ## The original cubic columns and their derivative row

The definitions are relocated unchanged from the earlier aggregate
modules. Their literal ordering and polynomial numerators are preserved;
the elementary homogeneity proofs use the checked polynomial core.
-/
noncomputable section
namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace

/-- Ordering is exactly that of segre_trace_tangent.py's h_monomials after
w=-x₂²: w*x₃, x₃³, x₂³, x₁x₂x₃, x₁³, x₀x₂x₃, x₀x₁², x₀²x₁, x₀³. -/
def cubicColumn : Fin 9 → Poly := ![
  -mon 0 0 2 1, mon 0 0 0 3, mon 0 0 3 0, mon 0 1 1 1, mon 0 3 0 0,
  mon 1 0 1 1, mon 1 2 0 0, mon 2 1 0 0, mon 3 0 0 0]

def derivativeNumerator (p : Poly) : Poly := -X 2^3 * X 3^3 * p

def cubicDeformation (v : Fin 9 → ℂ) : Poly := ∑ j : Fin 9, C (v j) * cubicColumn j

/-- The ordering is exactly the nine h-monomials of the Segre incidence
Jacobian.  The x₃³ entry varies with θ; the sparse and smooth rows differ. -/
def derivativeTraceCoefficients (θ : ℂ) : Fin 9 → ℂ :=
  ![0, θ*Complex.I/6, 0, 0, 0, 0, 0, 0, -(1+Complex.I)/6]

def derivativeTrace (θ : ℂ) (v : Fin 9 → ℂ) : ℂ :=
  ∑ j : Fin 9, derivativeTraceCoefficients θ j * v j

theorem derivativeTrace_explicit (θ : ℂ) (v : Fin 9 → ℂ) :
    derivativeTrace θ v = (θ*Complex.I*v 1-(1+Complex.I)*v 8)/6 := by
  norm_num [derivativeTrace, derivativeTraceCoefficients, Fin.sum_univ_succ,
    Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.head_cons, Matrix.tail_cons,
    Fin.reduceSucc]
  rw [show ((Fin.succ (2 : Fin 3)).succ.succ.succ.succ.succ : Fin 9) = 8 from rfl]
  ring

/-- Exact characteristic-zero version of the two-entry functional used in
segre_trace_tangent.py.  No sparse-matrix invariance is assumed. -/
theorem smooth_derivativeTrace_explicit (v : Fin 9 → ℂ) :
    derivativeTrace 1 v = (Complex.I*v 1-(1+Complex.I)*v 8)/6 := by
  simpa using derivativeTrace_explicit 1 v

end CycleQ2SeedCechTheta
namespace CycleQ2SeedBoundaryProjection
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta

theorem cubicColumn_homogeneous (j : Fin 9) : (cubicColumn j).IsHomogeneous 3 := by
  have hm (a b c d : ℕ) (hd : a + b + c + d = 3) : (mon a b c d).IsHomogeneous 3 := by
    simpa only [hd] using CycleQ2SeedTrace.mon_homogeneous a b c d
  fin_cases j
  · simpa [cubicColumn] using (hm 0 0 2 1 (by omega)).neg
  · simpa [cubicColumn] using hm 0 0 0 3 (by omega)
  · simpa [cubicColumn] using hm 0 0 3 0 (by omega)
  · simpa [cubicColumn] using hm 0 1 1 1 (by omega)
  · simpa [cubicColumn] using hm 0 3 0 0 (by omega)
  · simpa [cubicColumn] using hm 1 0 1 1 (by omega)
  · simpa [cubicColumn] using hm 1 2 0 0 (by omega)
  · simpa [cubicColumn] using hm 2 1 0 0 (by omega)
  · simpa [cubicColumn] using hm 3 0 0 0 (by omega)

theorem cubicDeformation_homogeneous (v : Fin 9 → ℂ) :
    (cubicDeformation v).IsHomogeneous 3 := by
  show (∑ j : Fin 9, C (v j) * cubicColumn j) ∈ homogeneousSubmodule (Fin 4) ℂ 3
  apply Submodule.sum_mem
  intro j hj
  exact (cubicColumn_homogeneous j).C_mul (v j)

theorem derivativeNumerator_homogeneous (v : Fin 9 → ℂ) :
    (derivativeNumerator (cubicDeformation v)).IsHomogeneous 9 := by
  exact (((isHomogeneous_X_pow (2 : Fin 4) 3).neg).mul
    (isHomogeneous_X_pow (3 : Fin 4) 3)).mul (cubicDeformation_homogeneous v)

end CycleQ2SeedBoundaryProjection
namespace CycleQ2GeometricProjectiveCurve
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection

/-- The paired normal class is represented in the degree-one chart
modules, rather than only in the ungraded cone localization. -/
def pairedDegreeOneClass (r θ : ℂ) (v : Fin 9 → ℂ) : DegreeOneCech r θ :=
  degreeNineCechClass r θ (-derivativeNumerator (cubicDeformation v))
    (derivativeNumerator_homogeneous v).neg

end CycleQ2GeometricProjectiveCurve
end

/-! ## The full actual Cech space and the exact paired-class coefficient

All pole orders are included. The literal regular pair and exact dual
certificate prove that the original Cech space is one-dimensional.
Every paired normal class has its exact computed derivative coefficient.
No source-only incidence statement or geometric Serre-trace claim is used.
-/
noncomputable section
namespace CycleQ2GeometricIncidenceCechTrace
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricCechComplex
  CycleQ2GeometricIncidenceCechSurjectivity CycleQ2GeometricIncidenceTraceAlgebra

def incidenceCechSpanning : ℂ →ₗ[ℂ] DegreeOneCech 57 1 :=
  LinearMap.toSpanSingleton ℂ (DegreeOneCech 57 1) incidenceCechNormalization

theorem incidenceCechSpanning_surjective : Function.Surjective incidenceCechSpanning := by
  intro z
  obtain ⟨c, hc⟩ := every_class_eq_smul z
  exact ⟨c, hc.symm⟩

instance incidenceCech_finite : Module.Finite ℂ (DegreeOneCech 57 1) :=
  Module.Finite.of_surjective incidenceCechSpanning incidenceCechSpanning_surjective

/-- The entire existing Cech quotient has dimension at most one, without
any geometric comparison or nonvanishing hypothesis. -/
theorem incidenceCech_finrank_le_one : Module.finrank ℂ (DegreeOneCech 57 1) ≤ 1 := by
  simpa only [Module.finrank_self] using
    LinearMap.finrank_le_finrank_of_surjective incidenceCechSpanning_surjective

/-- The fixed top numerator survives every actual chart boundary. The
proof combines the literal regular pair with the exact dual certificate. -/
theorem incidenceCechNormalization_ne_zero : incidenceCechNormalization ≠ 0 := by
  intro hz
  apply CycleQ2GeometricIncidenceDual.normalization_not_mem_fourGeneratorIdeal
  exact (CycleQ2GeometricCurveRegularPairTheta.degreeNineCechClass_zero_iff_fourGeneratorIdeal
    57 1 (by norm_num) (mon 0 0 0 9) (mon_homogeneous 0 0 0 9)).mp hz

/-- A complex-linear coordinate on the complete original Cech quotient. -/
def incidenceCechEquiv : ℂ ≃ₗ[ℂ] DegreeOneCech 57 1 :=
  LinearEquiv.ofBijective incidenceCechSpanning
    ⟨smul_left_injective ℂ incidenceCechNormalization_ne_zero,
      incidenceCechSpanning_surjective⟩

theorem incidenceCech_finrank : Module.finrank ℂ (DegreeOneCech 57 1) = 1 := by
  rw [← incidenceCechEquiv.finrank_eq]
  exact Module.finrank_self ℂ

def incidenceCechCoordinate : DegreeOneCech 57 1 →ₗ[ℂ] ℂ :=
  incidenceCechEquiv.symm.toLinearMap

@[simp] theorem incidenceCechCoordinate_normalization :
    incidenceCechCoordinate incidenceCechNormalization = 1 := by
  change incidenceCechEquiv.symm incidenceCechNormalization = 1
  apply incidenceCechEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  change incidenceCechNormalization = (1 : ℂ) • incidenceCechNormalization
  rw [one_smul]

/-- Every complex-linear trace on the actual Cech line is uniformly
scaled by its value on the fixed normalization. -/
theorem trace_eq_smul_coordinate (τ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ) :
    τ = τ incidenceCechNormalization • incidenceCechCoordinate := by
  ext z
  obtain ⟨c, rfl⟩ := every_class_eq_smul z
  simp only [map_smul, LinearMap.smul_apply, incidenceCechCoordinate_normalization,
    smul_eq_mul, mul_one]

theorem trace_normalization_ne_zero (τ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ)
    (hτ : τ ≠ 0) : τ incidenceCechNormalization ≠ 0 := by
  intro hz
  apply hτ
  ext z
  obtain ⟨c, rfl⟩ := every_class_eq_smul z
  simp only [map_smul, hz, smul_zero, LinearMap.zero_apply]

/-- Nonzero traces on the complete incidence Cech space are injective. -/
theorem nonzero_trace_injective (τ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ)
    (hτ : τ ≠ 0) : Function.Injective τ := by
  intro a b hab
  have hz : τ (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := every_class_eq_smul (a - b)
  rw [hc, map_smul, smul_eq_mul] at hz
  have hc0 : c = 0 := (mul_eq_zero.mp hz).resolve_right (trace_normalization_ne_zero τ hτ)
  apply sub_eq_zero.mp
  rw [hc, hc0, zero_smul]

/-- Two nonzero traces differ by one common nonzero scalar, so all
matrix entries obtained by applying them to this curve scale together. -/
theorem nonzero_traces_proportional
    (τ σ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ τ = a • σ := by
  have hτn := trace_normalization_ne_zero τ hτ
  have hσn := trace_normalization_ne_zero σ hσ
  refine ⟨τ incidenceCechNormalization / σ incidenceCechNormalization,
    div_ne_zero hτn hσn, ?_⟩
  ext z
  obtain ⟨c, rfl⟩ := every_class_eq_smul z
  simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
  field_simp

/-- On maps into the actual Cech line, trace normalization cannot affect
the kernel. This removes the exact-scalar identification requirement from
any subsequently established geometric trace comparison. -/
theorem trace_kernel_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] DegreeOneCech 57 1)
    (τ σ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    LinearMap.ker (τ.comp f) = LinearMap.ker (σ.comp f) := by
  ext v
  change τ (f v) = 0 ↔ σ (f v) = 0
  constructor
  · intro hv
    have hfv : f v = 0 := nonzero_trace_injective τ hτ (hv.trans (map_zero τ).symm)
    rw [hfv, map_zero]
  · intro hv
    have hfv : f v = 0 := nonzero_trace_injective σ hσ (hv.trans (map_zero σ).symm)
    rw [hfv, map_zero]


/-- The already computed two-entry derivative row as a linear functional. -/
def derivativeTraceLinear : (Fin 9 → ℂ) →ₗ[ℂ] ℂ where
  toFun := derivativeTrace 1
  map_add' v w := by
    simp only [derivativeTrace, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    change derivativeTrace 1 (c • v) = c * derivativeTrace 1 v
    simp only [derivativeTrace, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring


private theorem pairedColumn_polynomial (j : Fin 9) :
    -derivativeNumerator (cubicColumn j) =
      (![-mon 0 0 5 4, mon 0 0 3 6, mon 0 0 6 3, mon 0 1 4 4,
        mon 0 3 3 3, mon 1 0 4 4, mon 1 2 3 3, mon 2 1 3 3,
        mon 3 0 3 3] : Fin 9 → Poly) j := by
  fin_cases j <;> simp [derivativeNumerator, cubicColumn, mon] <;> ring

private def pairedColumnCoefficient : Fin 9 → ℂ :=
  ![0, (-4 + 2 * Complex.I) / 5, 0, 0, 0, 0, 0, 0, (2 - 6 * Complex.I) / 5]

private theorem quotient_pairedColumn (j : Fin 9) :
    quotient (-derivativeNumerator (cubicColumn j)) =
      pairedColumnCoefficient j • normalization := by
  rw [pairedColumn_polynomial]
  fin_cases j <;>
    simp only [pairedColumnCoefficient, Matrix.cons_val_zero', Matrix.cons_val_succ']
  · rw [map_neg]
    simpa only [neg_zero, zero_smul] using congrArg (fun z : IncidenceAlgebra => -z)
      (CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_c_add_four_zero 0 0 1 4)
  · exact paired_first_column_coefficient
  · simpa only [zero_smul] using
      CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_c_add_four_zero 0 0 2 3
  · simpa only [zero_smul] using
      CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_c_add_four_zero 0 1 0 4
  · simpa only [zero_smul] using
      CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_bd_add_two_zero 0 1 3 1
  · simpa only [zero_smul] using
      CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_c_add_four_zero 1 0 0 4
  · simpa only [zero_smul] using
      CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_bd_add_two_zero 1 0 3 1
  · have hq := CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_add_two 0 1 3 3
    rw [CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_bd_add_two_zero 0 0 3 2,
      smul_zero] at hq
    simpa only [zero_smul] using hq
  · have hq := CycleQ2GeometricIncidenceTraceAlgebra.quotient_mon_add_two 1 0 3 3
    rw [paired_last_column_reduced_coefficient, smul_smul] at hq
    calc
      quotient (mon 3 0 3 3) =
          ((57 : ℂ) * ((2 - 6 * Complex.I) / 285)) • normalization := hq
      _ = ((2 - 6 * Complex.I) / 5 : ℂ) • normalization := by congr 1; ring

private theorem pairedNumerator_sum (v : Fin 9 → ℂ) :
    -derivativeNumerator (cubicDeformation v) =
      ∑ j : Fin 9, C (v j) * -derivativeNumerator (cubicColumn j) := by
  simp only [derivativeNumerator, cubicDeformation, neg_mul, neg_neg, Finset.mul_sum, Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The coefficient of the original paired numerator in the literal
r=57, theta=1 quotient. Only the saved integer identities are used. -/
theorem quotient_pairedNumerator (v : Fin 9 → ℂ) :
    quotient (-derivativeNumerator (cubicDeformation v)) =
      (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • normalization := by
  rw [pairedNumerator_sum, map_sum]
  simp_rw [map_mul, ← quotient_scalar_mul, quotient_pairedColumn, smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  rw [smooth_derivativeTrace_explicit]
  simp only [pairedColumnCoefficient, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, mul_zero, zero_add]
  rw [show (Fin.succ (0 : Fin 8) : Fin 9) = 1 from rfl,
    show ((Fin.succ (0 : Fin 1)).succ.succ.succ.succ.succ.succ.succ : Fin 9) = 8 from rfl]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Exact factorization of the original paired normal class through the
computed derivative row on the same literal curve. No trace functional
or kernel assumption enters this equality. -/
theorem pairedClass_eq_derivativeTrace_smul_normalization (v : Fin 9 → ℂ) :
    pairedDegreeOneClass 57 1 v =
      (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • incidenceCechNormalization := by
  exact degreeNineCechClass_eq_smul_of_quotient_eq _
    (CycleQ2SeedBoundaryProjection.derivativeNumerator_homogeneous v).neg _
    (quotient_pairedNumerator v)

theorem paired_coefficient_scale_ne_zero : ((12 + 24 * Complex.I) / 5 : ℂ) ≠ 0 := by
  apply div_ne_zero _ (by norm_num)
  intro hz
  have hre := congrArg Complex.re hz
  norm_num at hre

/-- The finite derivative row detects exactly the vanishing of the
original paired normal class on this same literal curve. -/
theorem pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero (v : Fin 9 → ℂ) :
    pairedDegreeOneClass 57 1 v = 0 ↔ derivativeTrace 1 v = 0 := by
  rw [pairedClass_eq_derivativeTrace_smul_normalization, smul_eq_zero]
  simp only [incidenceCechNormalization_ne_zero, or_false, mul_eq_zero,
    paired_coefficient_scale_ne_zero, false_or]

theorem incidenceCechCoordinate_paired (v : Fin 9 → ℂ) :
    incidenceCechCoordinate (pairedDegreeOneClass 57 1 v) =
      ((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v := by
  rw [pairedClass_eq_derivativeTrace_smul_normalization, map_smul,
    incidenceCechCoordinate_normalization, smul_eq_mul, mul_one]

/-- The original paired classes are linear, as follows from their exact
factorization through the already computed derivative row. -/
def pairedClassLinear : (Fin 9 → ℂ) →ₗ[ℂ] DegreeOneCech 57 1 where
  toFun := pairedDegreeOneClass 57 1
  map_add' v w := by
    have hadd := derivativeTraceLinear.map_add v w
    change derivativeTrace 1 (v + w) = derivativeTrace 1 v + derivativeTrace 1 w at hadd
    rw [pairedClass_eq_derivativeTrace_smul_normalization,
      pairedClass_eq_derivativeTrace_smul_normalization,
      pairedClass_eq_derivativeTrace_smul_normalization, hadd, mul_add, add_smul]
  map_smul' c v := by
    change pairedDegreeOneClass 57 1 (c • v) = c • pairedDegreeOneClass 57 1 v
    have hsmul := derivativeTraceLinear.map_smul c v
    change derivativeTrace 1 (c • v) = c * derivativeTrace 1 v at hsmul
    rw [pairedClass_eq_derivativeTrace_smul_normalization,
      pairedClass_eq_derivativeTrace_smul_normalization, hsmul, smul_smul]
    congr 1
    ring

/-- Every cubic direction of trace one normalizes every paired class by the original
computed derivative. This concerns the actual Cech classes themselves. -/
theorem pairedClass_eq_derivativeTrace_smul_traceOne
    (w : Fin 9 → ℂ) (hw : derivativeTrace 1 w = 1) (v : Fin 9 → ℂ) :
    pairedDegreeOneClass 57 1 v = derivativeTrace 1 v • pairedDegreeOneClass 57 1 w := by
  rw [pairedClass_eq_derivativeTrace_smul_normalization,
    pairedClass_eq_derivativeTrace_smul_normalization, hw, mul_one, smul_smul]
  rw [mul_comm (derivativeTrace 1 v)]

/-- Every actual linear functional gives the computed two-entry row,
scaled uniformly by its value on the fixed normalization. -/
theorem paired_trace_formula_explicit (τ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ) (v : Fin 9 → ℂ) :
    τ (pairedDegreeOneClass 57 1 v) =
      (((12 + 24 * Complex.I) / 5) * τ incidenceCechNormalization) *
        ((Complex.I * v 1 - (1 + Complex.I) * v 8) / 6) := by
  rw [pairedClass_eq_derivativeTrace_smul_normalization, map_smul, smul_eq_mul,
    smooth_derivativeTrace_explicit]
  ring

theorem paired_trace_scale_ne_zero (τ : DegreeOneCech 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) :
    (((12 + 24 * Complex.I) / 5) * τ incidenceCechNormalization) ≠ 0 := by
  apply mul_ne_zero _ (trace_normalization_ne_zero τ hτ)
  apply div_ne_zero _ (by norm_num)
  intro hz
  have hre := congrArg Complex.re hz
  norm_num at hre

end CycleQ2GeometricIncidenceCechTrace
#print axioms CycleQ2GeometricIncidenceCechTrace.incidenceCech_finrank
#print axioms CycleQ2GeometricIncidenceCechTrace.pairedClass_eq_derivativeTrace_smul_normalization
#print axioms CycleQ2GeometricIncidenceCechTrace.trace_kernel_independent
#print axioms CycleQ2GeometricIncidenceCechTrace.pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero
end
