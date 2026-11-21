import Proposal.GeometricLiteralThreefoldOverlapLocalization
import Proposal.GeometricLiteralThreefoldLiftTransition
import Proposal.GeometricLiteralThreefoldChartVolume
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! The common open of a source and a destination gradient chart on a weighted
coordinate overlap. Its cotangent basis consists of the three retained
coordinates from the destination Jacobian presentation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralThreefoldDeformedOverlap

open Module CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldResidueChartMaps
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldOverlapLocalization
  CycleQ2LiteralThreefoldResidueMinors

variable (i : Fin 4) (k : Fin 3) (a b : Fin 4)

def denominator : FixedOverlap i k :=
  sourceMap i k (gradient i a) * fixedTargetMap i k (gradient (i.succAbove k) b)

abbrev Ring := Localization.Away (denominator i k a b)

def κ : FixedOverlap i k →ₐ[ℂ] Ring i k a b :=
  IsScalarTower.toAlgHom ℂ (FixedOverlap i k) (Ring i k a b)

def targetMap : T (i.succAbove k) →ₐ[ℂ] Ring i k a b :=
  (κ i k a b).comp (fixedTargetMap i k)

theorem source_unit : IsUnit (κ i k a b (sourceMap i k (gradient i a))) :=
  IsLocalization.Away.isUnit_of_dvd (S := Ring i k a b) (denominator i k a b) (dvd_mul_right _ _)

theorem target_unit : IsUnit (κ i k a b (fixedTargetMap i k (gradient (i.succAbove k) b))) :=
  IsLocalization.Away.isUnit_of_dvd (S := Ring i k a b) (denominator i k a b) (dvd_mul_left _ _)

private theorem gradient_avoids (j : Fin 4) {S : Type} [CommRing S]
    (f : T j →+* S) (p : PrimeSpectrum S) : ∃ r, f (gradient j r) ∉ p.asIdeal := by
  by_contra! h
  obtain ⟨c, e⟩ := CycleQ2LiteralThreefoldChartVolume.chartBezout j
  have eq := congrArg f e
  simp only [map_sum, map_mul, map_one] at eq
  apply p.isPrime.one_notMem
  rw [← eq]
  exact p.asIdeal.sum_mem fun r _ => p.asIdeal.mul_mem_left _ (h r)

/-- The common gradient opens cover the entire ordered chart intersection. -/
theorem denominator_cover (p : PrimeSpectrum (FixedOverlap i k)) :
    ∃ a b : Fin 4, denominator i k a b ∉ p.asIdeal := by
  obtain ⟨a, ha⟩ := gradient_avoids i (sourceMap i k).toRingHom p
  obtain ⟨b, hb⟩ := gradient_avoids (i.succAbove k) (fixedTargetMap i k).toRingHom p
  exact ⟨a, b, fun h => (p.isPrime.mem_or_mem h).elim ha hb⟩

def targetMonoid : Submonoid (T (i.succAbove k)) :=
  letI := (fixedTargetMap i k).toRingHom.toAlgebra
  IsLocalization.localizationLocalizationSubmodule (Submonoid.powers (sourceAxis i k))
    (Submonoid.powers (denominator i k a b))

private theorem composite_localization {A B S : Type} [CommRing A] [CommRing B] [CommRing S]
    [Algebra B S] (f : A →+* B) (x : A) (y : B)
    (h : @IsLocalization A _ (Submonoid.powers x) B _ f.toAlgebra) [IsLocalization.Away y S] :
    letI := f.toAlgebra
    letI := ((algebraMap B S).comp f).toAlgebra
    IsLocalization (IsLocalization.localizationLocalizationSubmodule (Submonoid.powers x)
      (Submonoid.powers y)) S := by
  let := f.toAlgebra
  let := ((algebraMap B S).comp f).toAlgebra
  let : IsLocalization.Away x B := h
  let : IsScalarTower A B S := IsScalarTower.of_algebraMap_eq' rfl
  exact IsLocalization.localization_localization_isLocalization (Submonoid.powers x)
    (Submonoid.powers y) S

theorem target_isLocalization :
    letI := (targetMap i k a b).toRingHom.toAlgebra
    IsLocalization (targetMonoid i k a b) (Ring i k a b) :=
  composite_localization (S := Ring i k a b) (fixedTargetMap i k).toRingHom
    (sourceAxis i k) (denominator i k a b) (fixedTargetMap_isLocalization i k)

section Transfer

variable {R P S : Type} [CommRing R] [CommRing P] [CommRing S]
  [Algebra ℂ R] [Algebra ℂ P] [Algebra ℂ S] [Algebra R P] [IsScalarTower ℂ R P]
  (g : R →ₐ[ℂ] S) (M : Submonoid R) (m : R) [IsLocalization.Away m P]
  (hM : @IsLocalization R _ M S _ g.toRingHom.toAlgebra) (hm : IsUnit (g m))

private def patchMap : P →ₐ[ℂ] S :=
  IsLocalization.Away.liftAlgHom m hm

private def transferBasis (e : Basis (Fin 3) P (KaehlerDifferential ℂ P)) :
    Basis (Fin 3) S (KaehlerDifferential ℂ S) := by
  letI := g.toRingHom.toAlgebra
  letI := (patchMap (P := P) g m hm).toRingHom.toAlgebra
  letI : IsScalarTower ℂ P S := IsScalarTower.of_algHom (patchMap (P := P) g m hm)
  letI : IsScalarTower R P S := IsScalarTower.of_algebraMap_eq fun z =>
    (IsLocalization.Away.lift_eq m hm z).symm
  letI : IsLocalization M S := hM
  letI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization M
  letI : Algebra.FormallyEtale R P := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers m)
  letI : Algebra.FormallyEtale P S := Algebra.FormallyEtale.of_restrictScalars (R := R)
  exact (e.baseChange S).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ P S)

private theorem transferBasis_apply (e : Basis (Fin 3) P (KaehlerDifferential ℂ P)) (r : Fin 3)
    (x : R) (he : e r = KaehlerDifferential.D ℂ P (algebraMap R P x)) :
    transferBasis g M m hM hm e r = KaehlerDifferential.D ℂ S (g x) := by
  let := (patchMap (P := P) g m hm).toRingHom.toAlgebra
  let : IsScalarTower ℂ P S := IsScalarTower.of_algHom (patchMap (P := P) g m hm)
  simp only [transferBasis, Basis.map_apply, Basis.baseChange_apply, he]
  change KaehlerDifferential.mapBaseChange ℂ P S _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  exact congrArg (KaehlerDifferential.D ℂ S) (IsLocalization.Away.lift_eq m hm x)

end Transfer

def basisOn : Basis (Fin 3) (Ring i k a b) (KaehlerDifferential ℂ (Ring i k a b)) :=
  transferBasis (targetMap i k a b) (targetMonoid i k a b) (gradient (i.succAbove k) b)
    (target_isLocalization i k a b) (target_unit i k a b) (basis (i.succAbove k) b)

theorem basisOn_apply (r : Fin 3) :
    basisOn i k a b r = KaehlerDifferential.D ℂ (Ring i k a b)
      (targetMap i k a b (coord (i.succAbove k) (b.succAbove r))) :=
  transferBasis_apply _ _ _ _ _ _ r _ (basis_apply (i.succAbove k) b r)

end CycleQ2LiteralThreefoldDeformedOverlap

#print axioms CycleQ2LiteralThreefoldDeformedOverlap.denominator_cover
#print axioms CycleQ2LiteralThreefoldDeformedOverlap.target_isLocalization
#print axioms CycleQ2LiteralThreefoldDeformedOverlap.basisOn_apply
