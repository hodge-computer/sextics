import Proposal.SeedChartRelationsAndRankTransfer
import Proposal.SegreActionNormalForms

/-!
# Laurent coordinates and Čech residues on the curve and seed surface
-/

set_option Elab.async false

/- Component: continuation_3/CurveCechLocalization.lean -/
section
/-!
# Identifying the coordinate localizations with bounded Laurent sections

The map from the two-coordinate polynomial ring to Laurent polynomials is
injective. Its localization at any product of coordinate variables has image
exactly the Laurent polynomials whose poles occur only in those coordinates.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechLocalization

open MvPolynomial CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen
open scoped BigOperators

variable (R : Type*) [CommRing R]

abbrev NatExponent := Fin 2 →₀ ℕ

def castExponent : NatExponent →+ LaurentExponent where
  toFun e i := e i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

@[simp] theorem castExponent_apply (e : NatExponent) (i : Fin 2) :
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

def openExponent (s : Finset (Fin 2)) : LaurentExponent := fun i ↦ if i ∈ s then 1 else 0

@[simp] theorem openExponent_empty : openExponent ∅ = 0 := by
  ext i
  simp [openExponent]

def baseProduct (s : Finset (Fin 2)) : Base R := ∏ i ∈ s, X i

@[simp] theorem castExponent_single (i : Fin 2) :
    castExponent (Finsupp.single i 1) = openExponent {i} := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_X (i : Fin 2) :
    baseToLaurent R (X i) = T R (openExponent {i}) := by
  change baseToLaurent R (monomial (Finsupp.single i 1) 1) = _
  simp [T]

theorem openExponent_insert (i : Fin 2) (s : Finset (Fin 2)) (hi : i ∉ s) :
    openExponent (insert i s) = openExponent {i} + openExponent s := by
  ext j
  by_cases h : j = i
  · subst j; simp [openExponent, hi]
  · simp [openExponent, h]

@[simp] theorem baseToLaurent_baseProduct (s : Finset (Fin 2)) :
    baseToLaurent R (baseProduct R s) = T R (openExponent s) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [baseProduct]
  | @insert i s hi ih =>
      rw [baseProduct, Finset.prod_insert hi, map_mul]
      change baseToLaurent R (X i) * baseToLaurent R (baseProduct R s) = _
      rw [baseToLaurent_X, ih, T_mul, openExponent_insert i s hi]

def coordinateLocalization (s : Finset (Fin 2)) := Localization.Away (baseProduct R s)

instance (s : Finset (Fin 2)) : CommRing (coordinateLocalization R s) :=
  inferInstanceAs (CommRing (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 2)) : Algebra (Base R) (coordinateLocalization R s) :=
  inferInstanceAs (Algebra (Base R) (Localization.Away (baseProduct R s)))
instance (s : Finset (Fin 2)) : IsLocalization.Away (baseProduct R s) (coordinateLocalization R s) :=
  inferInstanceAs (IsLocalization.Away (baseProduct R s) (Localization.Away (baseProduct R s)))

def localizationToLaurent (s : Finset (Fin 2)) :
    coordinateLocalization R s →+* Laurent (R := R) :=
  IsLocalization.Away.lift (baseProduct R s)
    (show IsUnit ((baseToLaurent R).toRingHom (baseProduct R s)) by
      change IsUnit (baseToLaurent R (baseProduct R s))
      rw [baseToLaurent_baseProduct]
      exact T_isUnit R _)

@[simp] theorem localizationToLaurent_algebraMap (s : Finset (Fin 2)) (p : Base R) :
    localizationToLaurent R s (algebraMap (Base R) (coordinateLocalization R s) p) =
      baseToLaurent R p := IsLocalization.Away.lift_eq _ _ _

theorem localizationToLaurent_injective (s : Finset (Fin 2)) :
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

theorem localizationToLaurent_hasPoles (s : Finset (Fin 2))
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
theorem exists_clear_poles (s : Finset (Fin 2)) (p : Laurent (R := R))
    (hp : HasPoles s p) :
    ∃ n : ℕ, HasPoles ∅ (p * T R (n • openExponent s)) := by
  classical
  let n := p.coeff.support.sup (fun e ↦ Finset.univ.sup (fun i : Fin 2 ↦ (-e i).toNat))
  refine ⟨n, ?_⟩
  intro e i _ hneg
  rw [coeff_mul_T]
  by_contra hne
  have hs : e - n • openExponent s ∈ p.coeff.support := Finsupp.mem_support_iff.mpr hne
  by_cases hi : i ∈ s
  · have hbound : (-((e - n • openExponent s) i)).toNat ≤ n :=
      (Finset.le_sup (f := fun i : Fin 2 ↦ (-((e - n • openExponent s) i)).toNat)
        (Finset.mem_univ i)).trans
          (Finset.le_sup (f := fun e : LaurentExponent ↦
            Finset.univ.sup (fun i : Fin 2 ↦ (-e i).toNat)) hs)
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

theorem mem_range_localizationToLaurent (s : Finset (Fin 2)) (p : Laurent (R := R)) :
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

end CycleQ2CurveCechLocalization

#print axioms CycleQ2CurveCechLocalization.mem_range_localizationToLaurent
end
end

/- Component: continuation_3/SeedCechLocalizedBasis.lean -/
section
/-! # The actual localized seed quotient in the nine Laurent coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false


#print axioms CycleQ2SeedCechLocalizedBasis.mem_range_localizedCoordinates

#print axioms CycleQ2SeedCechLocalizedBasis.localized_nineSummand_kernel
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechThetaResidue.lean -/
section
/-! The smooth incidence trace row is an actual all-poles Čech functional.
The nine coefficients are computed from quotient-ring Laurent charts, not
assumed from the saved numerical array. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open MvPolynomial CycleQ2SeedTrace CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS firstJet seriesMap)

theorem false_derivative_residue (r θ : ℂ) (p : Poly) :
    fractionResidue r θ false (derivativeNumerator p) 2 4 = 0 := by
  rw [derivative_fractionResidue]
  have hh : firstJet (powerCoefficient r θ false (derivativeIntegral r θ false p)) = 0 := by
    rw [firstJet_powerCoefficient, false_jet_derivativeIntegral, map_zero]
  exact congrArg TrivSqZeroExt.snd hh

theorem true_derivative_column_residue (r θ : ℂ) (j : Fin 9) :
    fractionResidue r θ true (derivativeNumerator (cubicColumn j)) 2 4 =
      (trueJetVector r θ j).snd := by
  rw [derivative_fractionResidue]
  have hh := firstJet_powerCoefficient r θ true (derivativeIntegral r θ true (cubicColumn j))
  rw [true_jet_derivative_columns] at hh
  exact congrArg TrivSqZeroExt.snd hh


theorem negative_trueJetVector_snd (r θ : ℂ) (j : Fin 9) :
    -(trueJetVector r θ j).snd = (3*r) * derivativeTraceCoefficients θ j := by
  fin_cases j <;>
    norm_num [trueJetVector, derivativeTraceCoefficients, firstJet, kappa,
      Matrix.cons_val_zero', Matrix.cons_val_succ', smul_eq_mul, op_smul_eq_smul] <;>
    ring_nf <;> norm_num [Complex.I_sq]

/-- Direct actual Laurent-residue computation for all nine cubic columns
and every θ, including θ=1 from the smooth incidence seed. -/
theorem derivative_column_residue (r θ : ℂ) (j : Fin 9) :
    cechResidue r θ (derivativeNumerator (cubicColumn j)) 2 4 =
      (3*r) * derivativeTraceCoefficients θ j := by
  rw [cechResidue, false_derivative_residue, true_derivative_column_residue,
    zero_sub, negative_trueJetVector_snd]

theorem endpointResidue_scalar (r θ : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r θ e) :
    endpointResidue r θ e (laurentBase r θ e (seriesMap (PowerSeries.C c)) * z) =
      c * endpointResidue r θ e z := by
  change (laurentCoefficient r θ e
    (laurentBase r θ e (seriesMap (PowerSeries.C c)) * z)).coeff (-1) = _
  unfold laurentCoefficient laurentBase
  rw [coefficient_base_mul]
  change (seriesMap (PowerSeries.C c) * laurentCoefficient r θ e z).coeff (-1) = _
  rw [show seriesMap (PowerSeries.C c) = HahnSeries.single (0 : ℤ) c from
    HahnSeries.ofPowerSeries_C c, HahnSeries.coeff_single_zero_mul]
  rfl

theorem cechResidue_C_mul (r θ : ℂ) (c : ℂ) (p : Poly) (n m : ℕ) :
    cechResidue r θ (C c * p) n m = c * cechResidue r θ p n m := by
  have he (e : Bool) : fraction r θ e (C c * p) n m =
      laurentBase r θ e (seriesMap (PowerSeries.C c)) * fraction r θ e p n m := by
    simp [fraction, laurentEval, powerEval, chartEmbedding, laurentBase, powerBase, mul_assoc]
  simp only [cechResidue, fractionResidue_eq_endpointResidue, he, endpointResidue_scalar]
  ring



theorem deformation_residue (r θ : ℂ) (v : Fin 9 → ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation v)) 2 4 =
      (3*r) * derivativeTrace θ v := by
  have he : derivativeNumerator (cubicDeformation v) =
      ∑ j : Fin 9, C (v j) * derivativeNumerator (cubicColumn j) := by
    unfold derivativeNumerator cubicDeformation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he, cechResidue_sum]
  simp only [cechResidue_C_mul, derivative_column_residue, derivativeTrace, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring



theorem normalized_deformation_residue (r θ : ℂ) (hr : r ≠ 0) (v : Fin 9 → ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation v)) 2 4 / (3*r) =
      derivativeTrace θ v := by
  rw [deformation_residue]
  exact mul_div_cancel_left₀ _ (mul_ne_zero (by norm_num) hr)

/-- A nonzero smooth incidence trace is now an actual non-coboundary, even
when arbitrary larger denominator powers are permitted. -/
theorem nonboundary_of_derivativeTrace_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    ¬ CechBoundary r θ (derivativeNumerator (cubicDeformation v)) 2 4 := by
  intro hb
  have hz := cechResidue_zero_of_boundary r θ _ 2 4 hb
  rw [deformation_residue] at hz
  exact (mul_ne_zero (mul_ne_zero (by norm_num) hr) hv) hz

def selectedTangent : Fin 9 → ℂ := ![0,0,0,0,0,0,0,Complex.I,Complex.I-1]

theorem selectedTangent_trace (θ : ℂ) : derivativeTrace θ selectedTangent = 1/3 := by
  rw [derivativeTrace_explicit]
  change (θ*Complex.I*0-(1+Complex.I)*(Complex.I-1))/6 = 1/3
  simp only [mul_zero, zero_sub]
  ring_nf
  norm_num [Complex.I_sq]

theorem selectedTangent_residue (r θ : ℂ) :
    cechResidue r θ (derivativeNumerator (cubicDeformation selectedTangent)) 2 4 = r := by
  rw [deformation_residue, selectedTangent_trace]
  ring

theorem selectedTangent_not_boundary (r θ : ℂ) (hr : r ≠ 0) :
    ¬ CechBoundary r θ (derivativeNumerator (cubicDeformation selectedTangent)) 2 4 := by
  apply nonboundary_of_derivativeTrace_ne_zero r θ hr
  rw [selectedTangent_trace]
  norm_num

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.derivative_column_residue
#print axioms CycleQ2SeedCechTheta.deformation_residue
#print axioms CycleQ2SeedCechTheta.nonboundary_of_derivativeTrace_ne_zero
end
end

/- Component: continuation_3/CurveCechLocalizedBasis.lean -/
section
/-! # The actual localized curve quotients in six Laurent coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechLocalizedBasis

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization

variable (R : Type*) [CommRing R]

abbrev CurveLocal (side : Side) (r ι : R) (s : Finset (Fin 2)) :=
  Localization (Algebra.algebraMapSubmonoid (CurveRing side r ι)
    (Submonoid.powers (baseProduct R s)))

instance curveLocalBaseAlgebra (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Algebra (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  localizationAlgebra (Rₘ := coordinateLocalization R s) (Sₘ := CurveLocal R side r ι s)
    (Submonoid.powers (baseProduct R s)) (CurveRing side r ι)

instance curveLocalBaseTower (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    IsScalarTower (Base R) (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  isScalarTower_localizationAlgebra (Rₘ := coordinateLocalization R s)
    (Sₘ := CurveLocal R side r ι s) (Submonoid.powers (baseProduct R s)) (CurveRing side r ι)

def localizedBasis [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Module.Basis (ShiftIndex side) (coordinateLocalization R s) (CurveLocal R side r ι s) :=
  (curveBasis R side r ι).localizationLocalization (coordinateLocalization R s)
    (Submonoid.powers (baseProduct R s)) (CurveLocal R side r ι s)

@[simp] theorem localizedBasis_apply [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (ab : (ShiftIndex side)) :
    localizedBasis R side r ι s ab = algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (curveBasis R side r ι ab) := by
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

@[simp] theorem localizedBasis_repr_algebraMap [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (p : CurveRing side r ι) (ab : (ShiftIndex side)) :
    (localizedBasis R side r ι s).repr (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) ab =
      algebraMap (Base R) (coordinateLocalization R s) ((curveBasis R side r ι).repr p ab) := by
  exact Module.Basis.localizationLocalization_repr_algebraMap _ _ _ _ _ _

def localizedCoordinates [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    CurveLocal R side r ι s →+ ((ShiftIndex side) → Laurent (R := R)) where
  toFun p ab := localizationToLaurent R s ((localizedBasis R side r ι s).repr p ab)
  map_zero' := by ext ab; simp
  map_add' p q := by ext ab; simp

theorem localizedCoordinates_injective [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Function.Injective (localizedCoordinates R side r ι s) := by
  intro p q hpq
  apply (localizedBasis R side r ι s).repr.injective
  ext ab
  exact localizationToLaurent_injective R s (congrFun hpq ab)

theorem localizedCoordinates_hasPoles [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : CurveLocal R side r ι s) (ab : (ShiftIndex side)) :
    HasPoles s (localizedCoordinates R side r ι s p ab) :=
  localizationToLaurent_hasPoles R s _

theorem mem_range_localizedCoordinates [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : (ShiftIndex side) → Laurent (R := R)) :
    p ∈ Set.range (localizedCoordinates R side r ι s) ↔ ∀ ab, HasPoles s (p ab) := by
  constructor
  · rintro ⟨p, rfl⟩ ab
    exact localizedCoordinates_hasPoles R side r ι s p ab
  · intro hp
    choose a ha using fun ab ↦ (mem_range_localizationToLaurent R s (p ab)).mpr (hp ab)
    refine ⟨(localizedBasis R side r ι s).repr.symm (Finsupp.equivFunOnFinite.symm a), ?_⟩
    funext ab
    change localizationToLaurent R s
      ((localizedBasis R side r ι s).repr ((localizedBasis R side r ι s).repr.symm
        (Finsupp.equivFunOnFinite.symm a)) ab) = p ab
    simpa using ha ab

@[simp] theorem localizedCoordinates_algebraMap [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (p : CurveRing side r ι) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) ab =
      baseToLaurent R ((curveBasis R side r ι).repr p ab) := by
  simp [localizedCoordinates]

@[simp] theorem localizedCoordinates_smul [Nontrivial R] (side : Side) (r ι : R)
    (s : Finset (Fin 2)) (a : coordinateLocalization R s) (p : CurveLocal R side r ι s)
    (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s (a • p) ab =
      localizationToLaurent R s a * localizedCoordinates R side r ι s p ab := by
  simp [localizedCoordinates, Finsupp.smul_apply, smul_eq_mul]

/-- All positive-degree overlap classes are actual coboundaries. -/
theorem localized_sixSummand_exact [Nontrivial R] (side : Side) (r ι : R)
    (d : ℤ) (hd : 2≤d) (p : CurveLocal R side r ι {0,1})
    (hg : ∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0,1} p ab)) :
    ∃ (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}),
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0} q0 ab)) ∧
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {1} q1 ab)) ∧
      localizedCoordinates R side r ι {0,1} p=
        localizedCoordinates R side r ι {1} q1-localizedCoordinates R side r ι {0} q0 := by
  obtain ⟨q0,q1,h0,h1,hg0,hg1,he⟩ :=
    sixSummand_exact side d hd (localizedCoordinates R side r ι {0,1} p) hg
  obtain ⟨q0',hq0⟩ := (mem_range_localizedCoordinates R side r ι {0} q0).mpr h0
  obtain ⟨q1',hq1⟩ := (mem_range_localizedCoordinates R side r ι {1} q1).mpr h1
  exact ⟨q0',q1',by simpa only [hq0] using hg0,by simpa only [hq1] using hg1,
    by simpa only [hq0,hq1] using he⟩

end CycleQ2CurveCechLocalizedBasis

#print axioms CycleQ2CurveCechLocalizedBasis.localized_sixSummand_exact
end
end

/- Component: continuation_3/SeedCechRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechRestrictions

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis

variable (R : Type*) [CommRing R]

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SeedLocal R r ι s →+* SeedLocal R r ι t :=
  IsLocalization.Away.lift
    (S := SeedLocal R r ι s)
    (P := SeedLocal R r ι t)
    (g := algebraMap (SeedRing r ι) (SeedLocal R r ι t))
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s))
    (seedProduct_isUnit R r ι hst)

@[simp] theorem restriction_algebraMap (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (p : SeedRing r ι) :
    restriction R r ι hst (algebraMap (SeedRing r ι) (SeedLocal R r ι s) p) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι t) p :=
  IsLocalization.Away.lift_eq (S := SeedLocal R r ι s)
    (P := SeedLocal R r ι t) _ (seedProduct_isUnit R r ι hst) p

theorem coordinates_mul_base [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) (c : Base R) (ab : ShiftIndex) :
    localizedCoordinates R r ι s
      (p * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) c)) ab =
      baseToLaurent R c * localizedCoordinates R r ι s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (SeedRing r ι) (SeedLocal R r ι s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SeedLocal R r ι s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (r ι : R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : SeedLocal R r ι s) (ab : ShiftIndex) :
    localizedCoordinates R r ι t (restriction R r ι hst z) ab =
      localizedCoordinates R r ι s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) z
  have hp' : z * algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n)) =
      algebraMap (SeedRing r ι) (SeedLocal R r ι s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R r ι s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R r ι hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R r ι t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- Every graded one-cocycle for the canonical three-coordinate localization
complex of the actual seed quotient is an actual coboundary. -/
theorem coordinateCech_exact [Nontrivial R] (r ι : R) (g : LaurentGrade)
    (p01 : SeedLocal R r ι {0, 1}) (p02 : SeedLocal R r ι {0, 2})
    (p12 : SeedLocal R r ι {1, 2})
    (hg01 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 1} p01 ab))
    (hg02 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {0, 2} p02 ab))
    (hg12 : ∀ ab, HasGrade ab g (localizedCoordinates R r ι {1, 2} p12 ab))
    (hc : restriction R r ι (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide) p01 -
      restriction R r ι (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p02 +
      restriction R r ι (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide) p12 = 0) :
    ∃ (q0 : SeedLocal R r ι {0}) (q1 : SeedLocal R r ι {1})
      (q2 : SeedLocal R r ι {2}),
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {0} q0 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {1} q1 ab)) ∧
      (∀ ab, HasGrade ab g (localizedCoordinates R r ι {2} q2 ab)) ∧
      p01 = restriction R r ι (show ({1} : Finset (Fin 3)) ⊆ {0, 1} by decide) q1 -
        restriction R r ι (show ({0} : Finset (Fin 3)) ⊆ {0, 1} by decide) q0 ∧
      p02 = restriction R r ι (show ({2} : Finset (Fin 3)) ⊆ {0, 2} by decide) q2 -
        restriction R r ι (show ({0} : Finset (Fin 3)) ⊆ {0, 2} by decide) q0 ∧
      p12 = restriction R r ι (show ({2} : Finset (Fin 3)) ⊆ {1, 2} by decide) q2 -
        restriction R r ι (show ({1} : Finset (Fin 3)) ⊆ {1, 2} by decide) q1 := by
  have hc' (ab : ShiftIndex) : localizedCoordinates R r ι {0, 1} p01 ab -
      localizedCoordinates R r ι {0, 2} p02 ab +
      localizedCoordinates R r ι {1, 2} p12 ab = 0 := by
    have hh := congrArg (fun z ↦ localizedCoordinates R r ι Finset.univ z ab) hc
    simpa only [map_add, map_sub, map_zero, Pi.add_apply, Pi.sub_apply, Pi.zero_apply,
      coordinates_restriction] using hh
  obtain ⟨q0, q1, q2, hg0, hg1, hg2, he01, he02, he12⟩ :=
    localized_nineSummand_kernel R r ι g p01 p02 p12 hg01 hg02 hg12 hc'
  refine ⟨q0, q1, q2, hg0, hg1, hg2, ?_, ?_, ?_⟩
  · apply localizedCoordinates_injective R r ι {0, 1}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he01 ab
  · apply localizedCoordinates_injective R r ι {0, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he02 ab
  · apply localizedCoordinates_injective R r ι {1, 2}
    funext ab
    simpa only [map_sub, Pi.sub_apply, coordinates_restriction] using he12 ab

end CycleQ2SeedCechRestrictions

#print axioms CycleQ2SeedCechRestrictions.coordinateCech_exact
end
end

/- Component: continuation_3/SeedCechTopCohomology.lean -/
section
/-!
# The seven-dimensional top coordinate Čech quotient

The quotient by the three pair-open images keeps exactly the monomials whose
three base exponents are all negative. In total degree zero and invariant
character, the actual nine shifts leave precisely seven such monomials.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechTopCohomology

open CycleQ2SeedCechThreeOpen
open scoped BigOperators

abbrev SmallExponents := Fin 4 × Fin 4 × Fin 4

def topExponent (e : SmallExponents) : LaurentExponent :=
  ![-((e.1.val : ℤ) + 1), -((e.2.1.val : ℤ) + 1), -((e.2.2.val : ℤ) + 1)]

abbrev TopIndex := {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = 0}

theorem topIndex_count : Fintype.card TopIndex = 7 := by decide

theorem topExponent_negative (e : SmallExponents) (i : Fin 3) : topExponent e i < 0 := by
  fin_cases i
  · change -((e.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.1.val : ℤ) + 1) < 0; omega
  · change -((e.2.2.val : ℤ) + 1) < 0; omega

theorem topExponent_injective : Function.Injective topExponent := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  change -((a.1.val : ℤ) + 1) = -((b.1.val : ℤ) + 1) at h0
  change -((a.2.1.val : ℤ) + 1) = -((b.2.1.val : ℤ) + 1) at h1
  change -((a.2.2.val : ℤ) + 1) = -((b.2.2.val : ℤ) + 1) at h2
  apply Prod.ext
  · apply Fin.ext; omega
  · apply Prod.ext <;> apply Fin.ext <;> omega

def topCoordinate (q : TopIndex) : ShiftIndex × LaurentExponent := (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective topCoordinate := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent ↦ q.2) hab)

/-- Completeness of the finite index, derived from actual degree zero. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = 0) :
    ∃ q : TopIndex, topCoordinate q = (ab, e) := by
  have hd := congrArg Prod.fst hg
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i = 0 at hd
  rw [Fin.sum_univ_three] at hd
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have bounds (i : Fin 3) : (-e i - 1).toNat < 4 := by
    fin_cases i
    · change (-e 0 - 1).toNat < 4; omega
    · change (-e 1 - 1).toNat < 4; omega
    · change (-e 2 - 1).toNat < 4; omega
  let v : SmallExponents :=
    (⟨(-e 0 - 1).toNat, bounds 0⟩,
     ⟨(-e 1 - 1).toNat, bounds 1⟩,
     ⟨(-e 2 - 1).toNat, bounds 2⟩)
  have hv : topExponent v = e := by
    ext i
    fin_cases i
    · change -(((-e 0 - 1).toNat : ℤ) + 1) = e 0; omega
    · change -(((-e 1 - 1).toNat : ℤ) + 1) = e 1; omega
    · change -(((-e 2 - 1).toNat : ℤ) + 1) = e 2; omega
  refine ⟨⟨(ab, v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

variable (R : Type*) [CommRing R]

abbrev Family := ShiftIndex → Laurent (R := R)

def gradedFamilies : Submodule R (Family R) where
  carrier := {p | ∀ ab, HasGrade ab 0 (p ab)}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab := hasGrade_add ab 0 (hp ab) (hq ab)
  smul_mem' c p hp ab := by
    intro e he
    simp [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he]

def topProjection : gradedFamilies R →ₗ[R] (TopIndex →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R) (q : TopIndex) :
    topProjection R p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : TopIndex) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : TopIndex) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R q ab).coeff e = if topCoordinate q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : TopIndex) : gradedFamilies R := ⟨basisFamily R q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : TopIndex) :
    topProjection R (basisSection R q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate q = topCoordinate j then 1 else 0) = _
  simp only [topCoordinate_injective.eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R) := by
  intro p
  refine ⟨∑ q : TopIndex, p q • basisSection R q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R) :=
  poleSubmodule R {0, 1} ⊔ poleSubmodule R {0, 2} ⊔ poleSubmodule R {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R) :
    topProjection R p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = 0
    · obtain ⟨q, hq⟩ := exists_topIndex ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : TopIndex →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R s ≤ LinearMap.ker (topProjection R) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R ≤ LinearMap.ker (topProjection R) :=
  sup_le (sup_le (poleSubmodule_le_ker R {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) : gradedFamilies R :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R) :
    filterSection R P p ∈ poleSubmodule R s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R = LinearMap.ker (topProjection R) := by
  apply le_antisymm (topBoundary_le_ker R)
  intro p hp
  have hz := (topProjection_zero_iff R p).mp hp
  let p01 := filterSection R (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R {1, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · exact he.2.2
    · simp at hi
    · simp at hi
  have heq : p = p01 + p02 + p12 := by
    apply Subtype.ext
    funext ab
    apply AddMonoidAlgebra.ext
    ext e
    change (p.val ab).coeff e =
      ((p01.val ab + p02.val ab + p12.val ab).coeff e)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      p01, p02, p12, filterSection_coeff]
    by_cases h2 : 0 ≤ e 2
    · simp [h2, not_lt.mpr h2]
    · by_cases h1 : 0 ≤ e 1
      · simp [lt_of_not_ge h2, h1, not_lt.mpr h1]
      · by_cases h0 : 0 ≤ e 0
        · simp [h2, h1, lt_of_not_ge h2, lt_of_not_ge h1, h0]
        · have hn : ∀ i, e i < 0 := by
            intro i
            fin_cases i
            · exact lt_of_not_ge h0
            · exact lt_of_not_ge h1
            · exact lt_of_not_ge h2
          simp [lt_of_not_ge h2, lt_of_not_ge h1, h0, hz ab e hn]
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact (show poleSubmodule R {0, 1} ≤ topBoundary R from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R {0, 2} ≤ topBoundary R from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R {1, 2} ≤ topBoundary R from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R ⧸ topBoundary R

def topCechEquiv : TopCechQuotient R ≃ₗ[R] (TopIndex →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R)).trans
    ((topProjection R).quotKerEquivOfSurjective (topProjection_surjective R))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R) :
    topCechEquiv R (Submodule.Quotient.mk p) = topProjection R p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis TopIndex R (TopCechQuotient R) :=
  Finsupp.basisSingleOne.map (topCechEquiv R).symm

@[simp] theorem topCechBasis_apply (q : TopIndex) :
    topCechBasis R q = Submodule.Quotient.mk (basisSection R q) := by
  apply (topCechEquiv R).injective
  simp [topCechBasis]

theorem topCech_rank_seven [Nontrivial R] : Module.finrank R (TopCechQuotient R) = 7 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R), topIndex_count]

end CycleQ2SeedCechTopCohomology

#print axioms CycleQ2SeedCechTopCohomology.topIndex_count
#print axioms CycleQ2SeedCechTopCohomology.topProjection_surjective

#print axioms CycleQ2SeedCechTopCohomology.topCechBasis_apply
#print axioms CycleQ2SeedCechTopCohomology.topCech_rank_seven
end
end

/- Component: continuation_3/cylinder_bridge/SeedNormalConnecting.lean -/
section
/-! # The actual equation-normal connecting cocycle

The equation map is the dual of the displayed conormal relation for
`F=f₁g₁+f₂g₂+hk`.  Its two explicit local splittings have difference
`(kL-A)/(g₁g₂)` times `(g₂,-g₁,0)`.  The coefficients are then bound to the
literal smooth seed and its already constructed Laurent quotient charts.

The sign convention is fixed: normal fields follow `F+εA,h+εL`, hence their
images are `(-A,-L)`, and the overlap difference is first chart minus second
chart.  For fixed h the paired numerator is `-Aσ`, the negative of the
previously checked derivative numerator after substituting `w=-x₂²`.
No identification with a sheaf connecting morphism or an Abel--Jacobi map is
asserted here.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalConnecting



section Seed

open MvPolynomial CycleQ2SeedTrace
open CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def thetaEquation (θ : ℂ) : WeightedPoly :=
  X 0^6+X 1^6+X 2^6+X 3^6+X 4^3+(originalB+C θ*X 0^3)^2

theorem thetaEquation_decomposition (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ = originalF1 r*originalG1 r+originalF2*originalG2+
      thetaH θ*thetaK θ := by
  have hh := seedEquation_decomposition r hr
  unfold thetaEquation thetaH thetaK seedEquation originalH originalK at *
  linear_combination hh

theorem smoothF_eq_thetaEquation (r : ℂ) (hr : r^3=2) :
    CycleQ2IncidenceEquations.smoothF r Complex.I = thetaEquation 1 := by
  rw [thetaEquation_decomposition r 1 hr]
  unfold CycleQ2IncidenceEquations.smoothF
  rw [smoothH_eq_thetaH]
  have hk : CycleQ2IncidenceEquations.smoothK Complex.I = thetaK 1 := by
    simp [CycleQ2IncidenceEquations.smoothK, CycleQ2IncidenceEquations.smoothB,
      CycleQ2IncidenceEquations.smoothA, thetaK, originalK, originalB]
    ring
  rw [hk]
  apply congrArg (fun q : WeightedPoly => q+thetaH 1*thetaK 1)
  unfold CycleQ2IncidenceEquations.seedG
  rw [CycleQ2SegreSeed.seedG_expanded]
  unfold originalF1 originalG1 originalF2 originalG2
  simp only [map_pow]
  ring

@[simp] theorem ambientCurveMap_F (r θ : ℂ) (hr : r^3=2) :
    ambientCurveMap r θ (thetaEquation θ)=0 := by
  rw [thetaEquation_decomposition r θ hr]
  simp


/-- This is the actual equation-normal map on the curve quotient. -/
def seedEquationMap (r θ : ℂ) :
    (Fin 3 → CurveRing r θ) →ₗ[CurveRing r θ] (Fin 2 → CurveRing r θ) :=
  equationMap (ambientCurveMap r θ (originalG1 r))
    (ambientCurveMap r θ originalG2) (ambientCurveMap r θ (thetaK θ))

theorem substitute_derivativeA (p : Poly) :
    substitute derivativeA*p=derivativeNumerator p := by
  simp only [derivativeA, substitute, derivativeNumerator, map_mul, map_pow,
    aeval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The fixed-h normal cocycle has the opposite sign to the previously
defined derivative numerator.  The source `A=x₂x₃³w` is unchanged. -/
theorem fixed_h_paired_numerator (p : Poly) :
    -(substitute derivativeA)*p= -derivativeNumerator p := by
  rw [neg_mul, substitute_derivativeA]

theorem thetaEquation_mem (r θ : ℂ) (hr : r^3=2) :
    thetaEquation θ ∈ ambientCurveIdeal r θ := by
  rw [thetaEquation_decomposition r θ hr]
  exact Ideal.add_mem _ (Ideal.add_mem _
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 0))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 1)))
    (Ideal.mul_mem_right _ _ (curveEquation_mem r θ 2))

/-- The equation map uses the literal class of F in the actual ideal modulo
its square.  No abstract normal-bundle presentation is supplied as a premise. -/
theorem conormal_relation (r θ : ℂ) (hr : r^3=2) :
    (ambientCurveIdeal r θ).toCotangent ⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ =
      originalG1 r • conormalGenerator r θ 0+
      originalG2 • conormalGenerator r θ 1+thetaK θ • conormalGenerator r θ 2 := by
  have hh : (⟨thetaEquation θ,thetaEquation_mem r θ hr⟩ : ambientCurveIdeal r θ) =
      originalG1 r • ⟨curveEquations r θ 0,curveEquation_mem r θ 0⟩+
      originalG2 • ⟨curveEquations r θ 1,curveEquation_mem r θ 1⟩+
      thetaK θ • ⟨curveEquations r θ 2,curveEquation_mem r θ 2⟩ := by
    apply Subtype.ext
    change thetaEquation θ = originalG1 r*originalF1 r+originalG2*originalF2+
      thetaK θ*thetaH θ
    rw [thetaEquation_decomposition r θ hr]
    ring
  rw [hh, map_add, map_add, map_smul, map_smul, map_smul]
  rfl


end Seed

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.local_lift_difference
#print axioms CycleQ2NormalConnecting.smoothF_eq_thetaEquation
#print axioms CycleQ2NormalConnecting.ambientCurveMap_g1
#print axioms CycleQ2NormalConnecting.conormal_relation
#print axioms CycleQ2NormalConnecting.restricted_local_lifts_difference
end
end

/- Component: continuation_3/CurveCechRestrictions.lean -/
section
/-! # Canonical restriction maps and the actual coordinate Čech kernel -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCechRestrictions

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalization CycleQ2CurveCechLocalizedBasis

variable (R : Type*) [CommRing R]

instance curveLocalAway (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    IsLocalization.Away (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))
      (CurveLocal R side r ι s) := by
  have hh : Algebra.algebraMapSubmonoid (CurveRing side r ι)
      (Submonoid.powers (baseProduct R s)) =
      Submonoid.powers (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) := by
    exact Submonoid.map_powers _ _
  rw [IsLocalization.Away, ← hh]
  infer_instance

theorem baseProduct_dvd {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    baseProduct R s ∣ baseProduct R t :=
  Finset.prod_dvd_prod_of_subset s t (fun i ↦ X i) hst

theorem curveProduct_isUnit (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    IsUnit (algebraMap (CurveRing side r ι) (CurveLocal R side r ι t)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))) := by
  apply IsLocalization.Away.isUnit_of_dvd (S := CurveLocal R side r ι t)
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R t))
  exact map_dvd (algebraMap (Base R) (CurveRing side r ι)) (baseProduct_dvd R hst)

/-- The universal localization map, with no chosen Laurent inverse. -/
def restriction (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t) :
    CurveLocal R side r ι s →+* CurveLocal R side r ι t :=
  IsLocalization.Away.lift
    (S := CurveLocal R side r ι s)
    (P := CurveLocal R side r ι t)
    (g := algebraMap (CurveRing side r ι) (CurveLocal R side r ι t))
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s))
    (curveProduct_isUnit R side r ι hst)

@[simp] theorem restriction_algebraMap (side : Side) (r ι : R) {s t : Finset (Fin 2)} (hst : s ⊆ t)
    (p : CurveRing side r ι) :
    restriction R side r ι hst (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι t) p :=
  IsLocalization.Away.lift_eq (S := CurveLocal R side r ι s)
    (P := CurveLocal R side r ι t) _ (curveProduct_isUnit R side r ι hst) p

theorem coordinates_mul_base [Nontrivial R] (side : Side) (r ι : R) (s : Finset (Fin 2))
    (p : CurveLocal R side r ι s) (c : Base R) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι s
      (p * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
        (algebraMap (Base R) (CurveRing side r ι) c)) ab =
      baseToLaurent R c * localizedCoordinates R side r ι s p ab := by
  rw [← IsScalarTower.algebraMap_apply (Base R) (CurveRing side r ι) (CurveLocal R side r ι s) c,
    IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (CurveLocal R side r ι s) c,
    mul_comm p, ← Algebra.smul_def]
  rw [localizedCoordinates_smul, localizationToLaurent_algebraMap]

/-- Canonical restriction becomes literal inclusion in common Laurent coordinates. -/
theorem coordinates_restriction [Nontrivial R] (side : Side) (r ι : R)
    {s t : Finset (Fin 2)} (hst : s ⊆ t) (z : CurveLocal R side r ι s) (ab : (ShiftIndex side)) :
    localizedCoordinates R side r ι t (restriction R side r ι hst z) ab =
      localizedCoordinates R side r ι s z ab := by
  obtain ⟨n, p, hp⟩ := IsLocalization.Away.surj
    (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s)) z
  have hp' : z * algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)
      (algebraMap (Base R) (CurveRing side r ι) (baseProduct R s ^ n)) =
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι s) p := by
    simpa only [map_pow] using hp
  have hs := congrArg (fun z ↦ localizedCoordinates R side r ι s z ab) hp'
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at hs
  have ht := congrArg (restriction R side r ι hst) hp'
  simp only [map_mul, restriction_algebraMap] at ht
  have ht' := congrArg (fun z ↦ localizedCoordinates R side r ι t z ab) ht
  simp only [coordinates_mul_base, localizedCoordinates_algebraMap] at ht'
  have hu : IsUnit (baseToLaurent R (baseProduct R s ^ n)) := by
    rw [map_pow, baseToLaurent_baseProduct]
    exact (T_isUnit R _).pow n
  exact hu.mul_right_injective (ht'.trans hs.symm)

/-- The actual two-coordinate curve Čech differential is surjective
in every total degree at least two. -/
theorem coordinateCech_exact [Nontrivial R] (side : Side) (r ι : R)
    (d : ℤ) (hd : 2≤d) (p : CurveLocal R side r ι {0,1})
    (hg : ∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0,1} p ab)) :
    ∃ (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}),
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {0} q0 ab)) ∧
      (∀ ab,HasDegree ab d (localizedCoordinates R side r ι {1} q1 ab)) ∧
      p=restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1-
        restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0 := by
  obtain ⟨q0,q1,hg0,hg1,he⟩ := localized_sixSummand_exact R side r ι d hd p hg
  refine ⟨q0,q1,hg0,hg1,?_⟩
  apply localizedCoordinates_injective R side r ι {0,1}
  funext ab
  simpa only [map_sub,Pi.sub_apply,coordinates_restriction] using congrFun he ab

end CycleQ2CurveCechRestrictions

#print axioms CycleQ2CurveCechRestrictions.coordinateCech_exact
end
end

/- Component: continuation_3/cylinder_bridge/IncidenceCubicIndices.lean -/
section
/-! The literal nine detector cubic columns enumerate every invariant cubic
coefficient.  The enumeration is checked independently of any tangent data. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceCubicCechTrace
open CycleQ2IncidenceNormalForm CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2SegreModularDetectorData

theorem cubicIndex_injective : Function.Injective cubicIndex := by decide

theorem cubicIndex_bijective : Function.Bijective cubicIndex :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨cubicIndex_injective,by rw [Fintype.card_fin,CycleQ2IncidenceFullIndexCounts.cubic_count]⟩

def cubicEquiv : Fin 9 ≃ FullInvariantIndex 3 := Equiv.ofBijective cubicIndex cubicIndex_bijective

theorem cubicIndex8_eq_leading : cubicIndex 8=fullCubicLeadingIndex := by
  apply Subtype.ext
  funext i
  apply Fin.ext
  change CycleQ2SparseGaussianPolynomial.tupleFun (cubicExponents 8) i=
    (fullCubicLeadingIndex.val i).val
  fin_cases i <;> rfl

end CycleQ2IncidenceCubicCechTrace

#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex_injective
#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex_bijective
#print axioms CycleQ2IncidenceCubicCechTrace.cubicIndex8_eq_leading
end
end

/- Component: continuation_3/SeedCechLinearCoordinates.lean -/
section
/-! # Scalar compatibility of the actual localized seed coordinates -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechLinearCoordinates

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R]

theorem base_C_seed (r ι c : R) :
    algebraMap (Base R) (SeedRing r ι) (C c) = algebraMap R (SeedRing r ι) c := by
  change Ideal.Quotient.mk _ (remainingInclusion R (C c)) = Ideal.Quotient.mk _ (C c)
  simp [remainingInclusion]

theorem localized_scalar_eq (r ι : R) (s : Finset (Fin 3)) (c : R)
    (p : SeedLocal R r ι s) :
    algebraMap (Base R) (coordinateLocalization R s) (C c) • p = c • p := by
  simp only [Algebra.smul_def]
  rw [← IsScalarTower.algebraMap_apply (Base R) (coordinateLocalization R s) (SeedLocal R r ι s),
    IsScalarTower.algebraMap_apply (Base R) (SeedRing r ι) (SeedLocal R r ι s), base_C_seed,
    ← IsScalarTower.algebraMap_apply R (SeedRing r ι) (SeedLocal R r ι s)]

theorem localizedCoordinates_R_smul [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (c : R) (p : SeedLocal R r ι s) :
    localizedCoordinates R r ι s (c • p) = c • localizedCoordinates R r ι s p := by
  funext ab
  rw [← localized_scalar_eq R r ι s c p, localizedCoordinates_smul,
    localizationToLaurent_algebraMap]
  change baseToLaurent R (algebraMap R (Base R) c) * _ = c • _
  rw [AlgHom.commutes, Algebra.smul_def]

def linearCoordinates [Nontrivial R] (r ι : R) (s : Finset (Fin 3)) :
    SeedLocal R r ι s →ₗ[R] (ShiftIndex → Laurent (R := R)) where
  __ := localizedCoordinates R r ι s
  map_smul' c p := localizedCoordinates_R_smul R r ι s c p

@[simp] theorem linearCoordinates_apply [Nontrivial R] (r ι : R) (s : Finset (Fin 3))
    (p : SeedLocal R r ι s) :
    linearCoordinates R r ι s p = localizedCoordinates R r ι s p := rfl

def restrictionLinear [Nontrivial R] (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    SeedLocal R r ι s →ₗ[R] SeedLocal R r ι t where
  __ := (restriction R r ι hst).toAddMonoidHom
  map_smul' c p := by
    apply localizedCoordinates_injective R r ι t
    funext ab
    change localizedCoordinates R r ι t (restriction R r ι hst (c • p)) ab =
      localizedCoordinates R r ι t (c • restriction R r ι hst p) ab
    simp only [localizedCoordinates_R_smul, Pi.smul_apply, coordinates_restriction]

end CycleQ2SeedCechLinearCoordinates

#print axioms CycleQ2SeedCechLinearCoordinates.linearCoordinates
#print axioms CycleQ2SeedCechLinearCoordinates.restrictionLinear
end
end

/- Component: continuation_3/cylinder_bridge/SeedNormalGeneralParameter.lean -/
section
/-! # The actual seed conormal equation for every parameter

The Segre incidence family uses `smoothF r I`, whose definition is the
polynomial factorization for every `r`. The restriction `r^3 = 2` is needed
only to identify this polynomial with the fixed Fermat equation. This file
binds the actual incidence hypersurface to the actual curve ideal and its
conormal module without imposing that restriction.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2NormalConnecting

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta

/-- The older fixed-Fermat equation is recovered only at the specified
cube-root parameter. -/
theorem actualSeedEquation_eq_thetaEquation (r θ : ℂ) (hr : r^3=2) :
    actualSeedEquation r θ=thetaEquation θ := by
  exact (thetaEquation_decomposition r θ hr).symm

@[simp] theorem ambientCurveMap_actualSeedEquation (r θ : ℂ) :
    ambientCurveMap r θ (actualSeedEquation r θ)=0 := by
  simp [actualSeedEquation]

@[simp] theorem ambientCurveMap_smoothF (r : ℂ) :
    ambientCurveMap r 1 (CycleQ2IncidenceEquations.smoothF r Complex.I)=0 := by
  rw [← actualSeedEquation_eq_smoothF]
  exact ambientCurveMap_actualSeedEquation r 1

theorem smoothF_mem_curveIdeal (r : ℂ) :
    CycleQ2IncidenceEquations.smoothF r Complex.I ∈ ambientCurveIdeal r 1 := by
  rw [← actualSeedEquation_eq_smoothF]
  exact actualSeedEquation_mem r 1

/-- Direct binding of the incidence `smoothF` to the checked equation-normal
map, with no hypothesis on the cube of `r`. -/
theorem smoothF_conormal_relation (r : ℂ) :
    (ambientCurveIdeal r 1).toCotangent
        ⟨CycleQ2IncidenceEquations.smoothF r Complex.I,smoothF_mem_curveIdeal r⟩ =
      originalG1 r • conormalGenerator r 1 0+
      originalG2 • conormalGenerator r 1 1+thetaK 1 • conormalGenerator r 1 2 := by
  convert actual_conormal_relation r 1 using 1
  congr 1
  exact Subtype.ext (actualSeedEquation_eq_smoothF r).symm

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.actualSeedEquation_eq_smoothF
#print axioms CycleQ2NormalConnecting.actual_conormal_relation
#print axioms CycleQ2NormalConnecting.smoothF_conormal_relation
end
end

/- Component: continuation_3/cylinder_bridge/SeedNormalResidue.lean -/
section
/-! # Binding the normal connecting coefficient to the checked curve residue

This file retains the actual `g₁g₂` denominator, the actual sextic direction
`A=x₂x₃³w`, and the first-minus-second overlap convention.  Its functional
is `-1/(3r)` times the already checked smooth incidence trace.  It does not
identify this coefficient functional with an Abel--Jacobi pairing.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NormalConnecting
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)

def curveToLaurent (r θ : ℂ) (e : Bool) : CurveRing r θ →+* LaurentChart r θ e :=
  (chartEmbedding r θ e).comp (curveChart r θ e)

@[simp] theorem curveToLaurent_curveMap (r θ : ℂ) (e : Bool) (p : Poly) :
    curveToLaurent r θ e (curveMap r θ p)=laurentEval r θ e p := rfl

def ambientLaurent (r θ : ℂ) (e : Bool) : WeightedPoly →+* LaurentChart r θ e :=
  (laurentEval r θ e).comp substitute.toRingHom

@[simp] theorem curveToLaurent_ambientCurveMap (r θ : ℂ) (e : Bool) (p : WeightedPoly) :
    curveToLaurent r θ e (ambientCurveMap r θ p)=ambientLaurent r θ e p := rfl

def scalarMap (r θ : ℂ) (e : Bool) : ℂ →+* LaurentChart r θ e :=
  (laurentEval r θ e).comp C

theorem ambientLaurent_g1 (r θ : ℂ) (e : Bool) :
    ambientLaurent r θ e (originalG1 r)=
      scalarMap r θ e (3*r^2)*(chartAUnit r θ e : LaurentChart r θ e)^2 := by
  have hh := congrArg (curveToLaurent r θ e) (ambientCurveMap_g1 r θ)
  simpa only [curveToLaurent_ambientCurveMap, curveToLaurent_curveMap,
    map_mul, map_pow, laurentEval_curveA_shared, scalarMap, RingHom.comp_apply] using hh

theorem ambientLaurent_g2 (r θ : ℂ) (e : Bool) :
    ambientLaurent r θ e originalG2=
      scalarMap r θ e 3*(laurentX2Unit r θ e : LaurentChart r θ e)^4 := by
  have hh := congrArg (curveToLaurent r θ e) (ambientCurveMap_g2 r θ)
  simpa only [curveToLaurent_ambientCurveMap, curveToLaurent_curveMap,
    map_mul, map_pow, laurentEval_curveB, scalarMap, RingHom.comp_apply] using hh

def g1Unit (r θ : ℂ) (e : Bool) (hr : r≠0) : (LaurentChart r θ e)ˣ :=
  Units.map (scalarMap r θ e).toMonoidHom
    (Units.mk0 (3*r^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))) * chartAUnit r θ e^2

def g2Unit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (scalarMap r θ e).toMonoidHom (Units.mk0 3 (by norm_num)) * laurentX2Unit r θ e^4

@[simp] theorem coe_g1Unit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    (g1Unit r θ e hr : LaurentChart r θ e)=ambientLaurent r θ e (originalG1 r) := by
  rw [ambientLaurent_g1]
  rfl

@[simp] theorem coe_g2Unit (r θ : ℂ) (e : Bool) :
    (g2Unit r θ e : LaurentChart r θ e)=ambientLaurent r θ e originalG2 := by
  rw [ambientLaurent_g2]
  rfl

theorem coe_g1Unit_inv (r θ : ℂ) (e : Bool) (hr : r≠0) :
    (((g1Unit r θ e hr)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e)=
      scalarMap r θ e ((3*r^2)⁻¹)*((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^2 := by
  unfold g1Unit
  rw [mul_inv_rev, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  exact mul_comm _ _

theorem coe_g2Unit_inv (r θ : ℂ) (e : Bool) :
    (((g2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ) : LaurentChart r θ e)=
      scalarMap r θ e ((3 : ℂ)⁻¹)*((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^4 := by
  unfold g2Unit
  rw [mul_inv_rev, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val]
  exact mul_comm _ _

/-- Pair the fixed-h equation-normal overlap coefficient with the chosen
cubic.  The local lifts are `firstLift` and `secondLift` from the preceding
module, with their actual image equations already proved. -/
def pairedNormalCocycle (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) : LaurentChart r θ e :=
  overlapCoefficient (g1Unit r θ e hr) (g2Unit r θ e)
    (ambientLaurent r θ e (thetaK θ)) (ambientLaurent r θ e derivativeA) 0 *
      laurentEval r θ e p

theorem pairedNormalCocycle_eq_fraction (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) :
    pairedNormalCocycle r θ e hr p =
      scalarMap r θ e (-(9*r^2)⁻¹)*fraction r θ e (derivativeNumerator p) 2 4 := by
  have hc : -((3*r^2)⁻¹*(3 : ℂ)⁻¹)= -(9*r^2)⁻¹ := by
    field_simp [hr]
    <;> ring
  have hp : ambientLaurent r θ e derivativeA*laurentEval r θ e p=
      laurentEval r θ e (derivativeNumerator p) := by
    change laurentEval r θ e (substitute derivativeA)*laurentEval r θ e p = _
    rw [← map_mul, substitute_derivativeA]
  unfold pairedNormalCocycle overlapCoefficient
  simp only [mul_zero, zero_sub, coe_g1Unit_inv, coe_g2Unit_inv]
  calc
    _ = scalarMap r θ e (-((3*r^2)⁻¹*(3 : ℂ)⁻¹))*
        (ambientLaurent r θ e derivativeA*laurentEval r θ e p)*
        ((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^2*
        ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^4 := by
      simp only [map_neg, map_mul]
      ring
    _ = _ := by rw [hc,hp]; simp only [fraction, mul_assoc]

def pairedNormalTrace (r θ : ℂ) (hr : r≠0) (p : Poly) : ℂ :=
  endpointResidue r θ false (pairedNormalCocycle r θ false hr p)-
    endpointResidue r θ true (pairedNormalCocycle r θ true hr p)

theorem endpointResidue_scalarMap (r θ : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r θ e) :
    endpointResidue r θ e (scalarMap r θ e c*z)=c*endpointResidue r θ e z := by
  have hc : scalarMap r θ e c=
      laurentBase r θ e (CycleQ2SeedCech.seriesMap (PowerSeries.C c)) := by
    simp [scalarMap, laurentEval, powerEval_C, chartEmbedding, powerBase, laurentBase]
  rw [hc, endpointResidue_scalar]

theorem pairedNormalTrace_eq_residue (r θ : ℂ) (hr : r≠0) (p : Poly) :
    pairedNormalTrace r θ hr p = -(9*r^2)⁻¹*cechResidue r θ (derivativeNumerator p) 2 4 := by
  simp only [pairedNormalTrace, pairedNormalCocycle_eq_fraction, endpointResidue_scalarMap,
    cechResidue, fractionResidue_eq_endpointResidue]
  ring

/-- The actual fixed-h normal coefficient gives a nonzero multiple of the
smooth incidence trace, with its sign and normalization fully specified. -/
theorem pairedNormalTrace_deformation (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ) :
    pairedNormalTrace r θ hr (cubicDeformation v)= -(3*r)⁻¹*derivativeTrace θ v := by
  rw [pairedNormalTrace_eq_residue, deformation_residue]
  field_simp [hr]
  <;> ring

theorem pairedNormalTrace_nonzero (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ)
    (hv : derivativeTrace θ v≠0) : pairedNormalTrace r θ hr (cubicDeformation v)≠0 := by
  rw [pairedNormalTrace_deformation]
  exact mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero (mul_ne_zero (by norm_num) hr))) hv

theorem overlapProduct_isUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    IsUnit (curveToLaurent r θ e (curveG1 r θ*curveG2 r θ)) := by
  rw [map_mul]
  change IsUnit (ambientLaurent r θ e (originalG1 r)*ambientLaurent r θ e originalG2)
  rw [← coe_g1Unit r θ e hr, ← coe_g2Unit r θ e]
  exact (g1Unit r θ e hr).isUnit.mul (g2Unit r θ e).isUnit

def overlapToLaurent (r θ : ℂ) (e : Bool) (hr : r≠0) : Overlap r θ →+* LaurentChart r θ e :=
  IsLocalization.Away.lift (curveG1 r θ*curveG2 r θ) (overlapProduct_isUnit r θ e hr)

@[simp] theorem overlapToLaurent_base (r θ : ℂ) (e : Bool) (hr : r≠0) (z : CurveRing r θ) :
    overlapToLaurent r θ e hr (algebraMap (CurveRing r θ) (Overlap r θ) z)=
      curveToLaurent r θ e z := IsLocalization.Away.lift_eq _ _ _

theorem overlapToLaurent_firstUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    Units.map (overlapToLaurent r θ e hr).toMonoidHom (firstOverlapUnit r θ)=g1Unit r θ e hr := by
  apply Units.ext
  change overlapToLaurent r θ e hr (firstOverlapUnit r θ : Overlap r θ)=_
  rw [coe_firstOverlapUnit, overlapToLaurent_base, coe_g1Unit]
  rfl

theorem overlapToLaurent_secondUnit (r θ : ℂ) (e : Bool) (hr : r≠0) :
    Units.map (overlapToLaurent r θ e hr).toMonoidHom (secondOverlapUnit r θ)=g2Unit r θ e := by
  apply Units.ext
  change overlapToLaurent r θ e hr (secondOverlapUnit r θ : Overlap r θ)=_
  rw [coe_secondOverlapUnit, overlapToLaurent_base, coe_g2Unit]
  rfl

def pairedNormalOverlap (r θ : ℂ) (p : Poly) : Overlap r θ :=
  normalOverlapCoefficient r θ derivativeA 0*
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)

/-- The residue is evaluated on the actual localization class, not on an
independently chosen Laurent expression. -/
theorem overlapToLaurent_pairedNormalOverlap (r θ : ℂ) (e : Bool) (hr : r≠0) (p : Poly) :
    overlapToLaurent r θ e hr (pairedNormalOverlap r θ p)=pairedNormalCocycle r θ e hr p := by
  have h₁ : overlapToLaurent r θ e hr (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ)=
      (↑((g1Unit r θ e hr)⁻¹) : LaurentChart r θ e) := by
    change (↑((Units.map (overlapToLaurent r θ e hr).toMonoidHom (firstOverlapUnit r θ))⁻¹) :
      LaurentChart r θ e)=_
    rw [overlapToLaurent_firstUnit]
  have h₂ : overlapToLaurent r θ e hr (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)=
      (↑((g2Unit r θ e)⁻¹) : LaurentChart r θ e) := by
    change (↑((Units.map (overlapToLaurent r θ e hr).toMonoidHom (secondOverlapUnit r θ))⁻¹) :
      LaurentChart r θ e)=_
    rw [overlapToLaurent_secondUnit]
  simp only [pairedNormalOverlap, normalOverlapCoefficient, overlapCoefficient,
    overlapAmbient, RingHom.comp_apply, map_zero, mul_zero, zero_sub, map_mul, map_neg,
    overlapToLaurent_base, curveToLaurent_ambientCurveMap, curveToLaurent_curveMap, h₁, h₂,
    pairedNormalCocycle]

theorem actual_overlap_trace_deformation (r θ : ℂ) (hr : r≠0) (v : Fin 9 → ℂ) :
    endpointResidue r θ false (overlapToLaurent r θ false hr
        (pairedNormalOverlap r θ (cubicDeformation v)))-
      endpointResidue r θ true (overlapToLaurent r θ true hr
        (pairedNormalOverlap r θ (cubicDeformation v)))=
      -(3*r)⁻¹*derivativeTrace θ v := by
  rw [overlapToLaurent_pairedNormalOverlap, overlapToLaurent_pairedNormalOverlap]
  exact pairedNormalTrace_deformation r θ hr v

end CycleQ2NormalConnecting

#print axioms CycleQ2NormalConnecting.pairedNormalCocycle_eq_fraction
#print axioms CycleQ2NormalConnecting.pairedNormalTrace_deformation
#print axioms CycleQ2NormalConnecting.actual_overlap_trace_deformation
end
end

/- Component: continuation_3/cylinder_bridge/IncidenceCubicCechTrace.lean -/
section
/-! Every invariant cubic coefficient vector has the actual nine-column
Čech residue formula.  This is independent of any saved tangent matrix:
the chosen nonconstructive tangent can be substituted directly. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceCubicCechTrace
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2SeedTrace
  CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2SegreModularDetectorData

theorem cubic_expansion (η : FullInvariantIndex 3 → ℂ) :
    fullInvariantPolynomial 3 η=
      ∑ j : Fin 9, MvPolynomial.monomial
        (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) (η (cubicIndex j)) := by
  rw [fullInvariantPolynomial,←cubicEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  change MvPolynomial.monomial (fullExponentOf (cubicIndex j).val) (η (cubicIndex j))=_
  rw [cubicIndex_exponent]

theorem substitute_column (j : Fin 9) (c : ℂ) :
    substitute (MvPolynomial.monomial
      (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) c)=C c*cubicColumn j := by
  rw [show MvPolynomial.monomial
      (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) c=
      C c*MvPolynomial.monomial
        (CycleQ2SparseGaussianPolynomial.tupleExponent (cubicExponents j)) (1:ℂ) by
      rw [C_mul_monomial,mul_one]]
  rw [map_mul,show substitute (C c)=C c by simp [substitute],
    ←CycleQ2SparseGaussianPolynomial.monomial_variables]
  fin_cases j <;>
    simp [cubicExponents,CycleQ2SparseGaussianPolynomial.monomial,substitute,cubicColumn,
      mon,Fin.reduceFinMk] <;> ring_nf <;> simp

theorem substitute_cubic (η : FullInvariantIndex 3 → ℂ) :
    substitute (fullInvariantPolynomial 3 η)=cubicDeformation (fun j => η (cubicIndex j)) := by
  rw [cubic_expansion,map_sum]
  simp only [substitute_column,cubicDeformation]

def unscaledTrace (η : FullInvariantIndex 3 → ℂ) : ℂ :=
  Complex.I*η (cubicIndex 1)-(1+Complex.I)*η (cubicIndex 8)

theorem derivativeTrace_eq (η : FullInvariantIndex 3 → ℂ) :
    derivativeTrace 1 (fun j => η (cubicIndex j))=unscaledTrace η/6 :=
  smooth_derivativeTrace_explicit _

theorem cubic_residue (r : ℂ) (η : FullInvariantIndex 3 → ℂ) :
    cechResidue r 1 (derivativeNumerator (substitute (fullInvariantPolynomial 3 η))) 2 4=
      (3*r)*(unscaledTrace η/6) := by
  rw [substitute_cubic,deformation_residue,derivativeTrace_eq]

theorem cubic_trace_one_not_boundary (r : ℂ) (hr : r≠0)
    (η : FullInvariantIndex 3 → ℂ) (hη : unscaledTrace η=6) :
    ¬ CechBoundary r 1 (derivativeNumerator (substitute (fullInvariantPolynomial 3 η))) 2 4 := by
  rw [substitute_cubic]
  apply nonboundary_of_derivativeTrace_ne_zero r 1 hr
  rw [derivativeTrace_eq,hη]
  norm_num

theorem cubic_trace_one_normal_trace (r : ℂ) (hr : r≠0)
    (η : FullInvariantIndex 3 → ℂ) (hη : unscaledTrace η=6) :
    pairedNormalTrace r 1 hr (substitute (fullInvariantPolynomial 3 η))=-(3*r)⁻¹ := by
  rw [substitute_cubic,pairedNormalTrace_deformation,derivativeTrace_eq,hη]
  norm_num

end CycleQ2IncidenceCubicCechTrace

#print axioms CycleQ2IncidenceCubicCechTrace.substitute_cubic
#print axioms CycleQ2IncidenceCubicCechTrace.cubic_trace_one_not_boundary
#print axioms CycleQ2IncidenceCubicCechTrace.cubic_trace_one_normal_trace
end
end

/- Component: continuation_3/SeedCechActualTop.lean -/
section
/-! # The seven-dimensional quotient of the actual seed localization complex -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCechActualTop

open CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates CycleQ2SeedCechTopCohomology

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Degree-zero, character-zero sections inside the actual coordinate localization. -/
def gradedLocal (r ι : R) (s : Finset (Fin 3)) : Submodule R (SeedLocal R r ι s) :=
  (gradedFamilies R).comap (linearCoordinates R r ι s)

def gradedCoordinates (r ι : R) (s : Finset (Fin 3)) :
    gradedLocal R r ι s →ₗ[R] gradedFamilies R where
  toFun p := ⟨linearCoordinates R r ι s p.val, p.property⟩
  map_add' p q := by apply Subtype.ext; exact map_add (linearCoordinates R r ι s) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (linearCoordinates R r ι s) c p.val

@[simp] theorem gradedCoordinates_apply (r ι : R) (s : Finset (Fin 3))
    (p : gradedLocal R r ι s) :
    (gradedCoordinates R r ι s p).val = localizedCoordinates R r ι s p.val := rfl

theorem gradedCoordinates_injective (r ι : R) (s : Finset (Fin 3)) :
    Function.Injective (gradedCoordinates R r ι s) := by
  intro p q hpq
  apply Subtype.ext
  exact localizedCoordinates_injective R r ι s (congrArg Subtype.val hpq)

theorem gradedCoordinates_range (r ι : R) (s : Finset (Fin 3)) :
    LinearMap.range (gradedCoordinates R r ι s) = poleSubmodule R s := by
  ext p
  constructor
  · rintro ⟨q, rfl⟩ ab
    exact localizedCoordinates_hasPoles R r ι s q.val ab
  · intro hp
    obtain ⟨q, hq⟩ := (mem_range_localizedCoordinates R r ι s p.val).mpr hp
    have hqg : q ∈ gradedLocal R r ι s := by
      change linearCoordinates R r ι s q ∈ gradedFamilies R
      rw [linearCoordinates_apply, hq]
      exact p.property
    refine ⟨⟨q, hqg⟩, ?_⟩
    exact Subtype.ext hq

def totalEquiv (r ι : R) : gradedLocal R r ι Finset.univ ≃ₗ[R] gradedFamilies R :=
  LinearEquiv.ofBijective (gradedCoordinates R r ι Finset.univ)
    ⟨gradedCoordinates_injective R r ι Finset.univ, by
      intro p
      have hp : p ∈ poleSubmodule R Finset.univ := by
        intro ab e i hi _
        exact False.elim (hi (Finset.mem_univ i))
      rw [← gradedCoordinates_range R r ι Finset.univ] at hp
      exact hp⟩

@[simp] theorem totalEquiv_apply (r ι : R) (p : gradedLocal R r ι Finset.univ) :
    totalEquiv R r ι p = gradedCoordinates R r ι Finset.univ p := rfl

def gradedRestriction (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    gradedLocal R r ι s →ₗ[R] gradedLocal R r ι t where
  toFun p := ⟨restrictionLinear R r ι hst p.val, by
    intro ab
    change HasGrade ab 0 (localizedCoordinates R r ι t (restriction R r ι hst p.val) ab)
    rw [coordinates_restriction]
    exact p.property ab⟩
  map_add' p q := by apply Subtype.ext; exact map_add (restrictionLinear R r ι hst) p.val q.val
  map_smul' c p := by apply Subtype.ext; exact map_smul (restrictionLinear R r ι hst) c p.val

theorem gradedCoordinates_restriction (r ι : R)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    (gradedCoordinates R r ι t).comp (gradedRestriction R r ι hst) =
      gradedCoordinates R r ι s := by
  ext p ab e
  change (localizedCoordinates R r ι t (restriction R r ι hst p.val) ab).coeff e =
    (localizedCoordinates R r ι s p.val ab).coeff e
  rw [coordinates_restriction]

/-- The boundary submodule is the sum of the images of the actual three
canonical ring restrictions from pair-open sections. -/
def actualBoundary (r ι : R) : Submodule R (gradedLocal R r ι Finset.univ) :=
  LinearMap.range (gradedRestriction R r ι (show ({0, 1} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R r ι (show ({0, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide)) ⊔
  LinearMap.range (gradedRestriction R r ι (show ({1, 2} : Finset (Fin 3)) ⊆ Finset.univ by decide))

theorem map_actualBoundary (r ι : R) :
    (actualBoundary R r ι).map (totalEquiv R r ι).toLinearMap = topBoundary R := by
  change (actualBoundary R r ι).map (gradedCoordinates R r ι Finset.univ) = _
  simp only [actualBoundary, Submodule.map_sup, ← LinearMap.range_comp,
    gradedCoordinates_restriction, gradedCoordinates_range, topBoundary]

abbrev ActualTopCechQuotient (r ι : R) :=
  gradedLocal R r ι Finset.univ ⧸ actualBoundary R r ι

def actualTopEquiv (r ι : R) : ActualTopCechQuotient R r ι ≃ₗ[R] TopCechQuotient R :=
  Submodule.Quotient.equiv _ _ (totalEquiv R r ι) (map_actualBoundary R r ι)

def actualTopBasis (r ι : R) : Module.Basis TopIndex R (ActualTopCechQuotient R r ι) :=
  (topCechBasis R).map (actualTopEquiv R r ι).symm

@[simp] theorem actualTopBasis_apply (r ι : R) (q : TopIndex) :
    actualTopEquiv R r ι (actualTopBasis R r ι q) =
      Submodule.Quotient.mk (basisSection R q) := by
  simp [actualTopBasis]

theorem actualTop_rank_seven (r ι : R) :
    Module.finrank R (ActualTopCechQuotient R r ι) = 7 := by
  rw [Module.finrank_eq_card_basis (actualTopBasis R r ι), topIndex_count]

end CycleQ2SeedCechActualTop

#print axioms CycleQ2SeedCechActualTop.actualTop_rank_seven
end
end
