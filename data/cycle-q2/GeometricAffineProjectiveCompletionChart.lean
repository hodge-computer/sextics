import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# The standard affine open of projective space over ℂ

The coordinate ring of the basic open at the additional variable is the
degree-zero part of the localized homogeneous polynomial ring. Setting
that variable to one gives an isomorphism with the affine polynomial ring.
Its inverse sends each affine variable to the corresponding homogeneous
coordinate ratio. The resulting open immersion commutes with the two
structure morphisms to the complex point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffineProjectiveCompletionChart

open CategoryTheory AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

variable (ι : Type)
abbrev HomogeneousRing := MvPolynomial (Option ι) ℂ
abbrev AffineRing := MvPolynomial ι ℂ
abbrev grade := homogeneousSubmodule (Option ι) ℂ
abbrev den : HomogeneousRing ι := X none
abbrev ChartRing := HomogeneousLocalization.Away (grade ι) (den ι)
abbrev FullLocalization := Localization.Away (den ι)

theorem den_mem : den ι ∈ grade ι 1 := isHomogeneous_X ℂ none

def dehomogenize : HomogeneousRing ι →+* AffineRing ι :=
  (aeval (fun j : Option ι => j.elim 1 X)).toRingHom

@[simp] theorem dehomogenize_den : dehomogenize ι (den ι) = 1 := by simp [dehomogenize, den]

@[simp] theorem dehomogenize_coordinate (j : ι) : dehomogenize ι (X (some j)) = X j := by
  simp [dehomogenize]

def localDehomogenize : FullLocalization ι →+* AffineRing ι :=
  Localization.awayLift (dehomogenize ι) (den ι) (by simp)

def toAffine : ChartRing ι →+* AffineRing ι :=
  (localDehomogenize ι).comp (algebraMap (ChartRing ι) (FullLocalization ι))

def fraction (n : ℕ) (p : HomogeneousRing ι) (hp : p.IsHomogeneous n) : ChartRing ι :=
  HomogeneousLocalization.Away.mk (grade ι) (den_mem ι) n p (by simpa using hp)

theorem fraction_val (n : ℕ) (p : HomogeneousRing ι) (hp : p.IsHomogeneous n) :
    (fraction ι n p hp).val = algebraMap (HomogeneousRing ι) (FullLocalization ι) p *
      IsLocalization.Away.invSelf (den ι) ^ n := by
  rw [fraction, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp only [map_pow]
  rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf (den ι) ^ n),
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

@[simp] theorem toAffine_fraction (n : ℕ) (p : HomogeneousRing ι) (hp : p.IsHomogeneous n) :
    toAffine ι (fraction ι n p hp) = dehomogenize ι p := by
  change localDehomogenize ι (Localization.mk p ⟨den ι ^ n, n, rfl⟩) = _
  simpa only [localDehomogenize, one_pow, mul_one] using
    Localization.awayLift_mk (dehomogenize ι) (den ι) p 1 (by simp) n

def coefficients : ℂ →+* grade ι 0 := algebraMap ℂ (grade ι 0)

def constants : ℂ →+* ChartRing ι :=
  (HomogeneousLocalization.fromZeroRingHom (grade ι) (Submonoid.powers (den ι))).comp
    (coefficients ι)

@[simp] theorem constants_val (c : ℂ) :
    (constants ι c).val = algebraMap (HomogeneousRing ι) (FullLocalization ι) (C c) := by
  change Localization.mk (C c : HomogeneousRing ι) 1 = _
  exact Localization.mk_one_eq_algebraMap _

@[simp] theorem toAffine_constants (c : ℂ) : toAffine ι (constants ι c) = C c := by
  change localDehomogenize ι (constants ι c).val = _
  rw [constants_val]
  unfold localDehomogenize Localization.awayLift
  rw [IsLocalization.Away.lift_eq]
  simp [dehomogenize]

def ratio (j : Option ι) : ChartRing ι := fraction ι 1 (X j) (isHomogeneous_X ℂ j)

@[simp] theorem ratio_val (j : Option ι) :
    (ratio ι j).val = algebraMap (HomogeneousRing ι) (FullLocalization ι) (X j) *
      IsLocalization.Away.invSelf (den ι) := by simp only [ratio, fraction_val, pow_one]

@[simp] theorem ratio_none : ratio ι none = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [ratio_val, HomogeneousLocalization.val_one]
  exact IsLocalization.Away.mul_invSelf (den ι)

def fromAffine : AffineRing ι →+* ChartRing ι :=
  eval₂Hom (constants ι) (fun i => ratio ι (some i))

private def projectiveEval : HomogeneousRing ι →+* ChartRing ι :=
  eval₂Hom (constants ι) (ratio ι)

private theorem fromAffine_comp_dehomogenize :
    (fromAffine ι).comp (dehomogenize ι) = projectiveEval ι := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [dehomogenize, fromAffine, projectiveEval]
  · rintro (_ | i) <;> simp [dehomogenize, fromAffine, projectiveEval]

private theorem eval_scale {T : Type*} [CommRing T] (f : ℂ →+* T)
    (x : Option ι → T) (c : T) (n : ℕ) (p : HomogeneousRing ι) (hp : p.IsHomogeneous n) :
    eval₂Hom f (fun j => c * x j) p = c ^ n * eval₂Hom f x p := by
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => simp only [map_add, ihp, ihq, mul_add]
  | monomial d a hd =>
    have hdegree : (∑ j ∈ d.support, d j) = n := by
      simpa [Finsupp.weight_apply, Finsupp.sum] using hd
    simp only [eval₂Hom_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdegree]
    ring

private theorem projectiveEval_fraction (n : ℕ) (p : HomogeneousRing ι) (hp : p.IsHomogeneous n) :
    projectiveEval ι p = fraction ι n p hp := by
  let F := algebraMap (HomogeneousRing ι) (FullLocalization ι)
  have heval : eval₂Hom (F.comp C) (fun j => F (X j)) = F := by
    apply MvPolynomial.ringHom_ext <;> intro x <;> simp
  have hcomp : (algebraMap (ChartRing ι) (FullLocalization ι)).comp (projectiveEval ι) =
      eval₂Hom (F.comp C) (fun j => IsLocalization.Away.invSelf (den ι) * F (X j)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [projectiveEval, F]
    · intro j
      simp [projectiveEval, F, mul_comm]
  apply HomogeneousLocalization.val_injective
  change ((algebraMap (ChartRing ι) (FullLocalization ι)).comp (projectiveEval ι)) p = _
  rw [hcomp, eval_scale ι _ _ _ _ _ hp, heval, fraction_val]
  exact mul_comm _ _

/-- The degree-zero ring on the first projective basic open is the polynomial
ring in all the remaining variables. -/
def chartEquiv : ChartRing ι ≃+* AffineRing ι where
  toFun := toAffine ι
  invFun := fromAffine ι
  left_inv z := by
    obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grade ι) (den_mem ι) z
    have h : p.IsHomogeneous n := by simpa using hp
    change fromAffine ι (toAffine ι (fraction ι n p h)) = fraction ι n p h
    rw [toAffine_fraction, ← RingHom.comp_apply, fromAffine_comp_dehomogenize,
      projectiveEval_fraction]
  right_inv p := by
    have h : (toAffine ι).comp (fromAffine ι) = RingHom.id (AffineRing ι) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [fromAffine]
      · intro j
        simp [fromAffine, ratio]
    exact RingHom.congr_fun h p
  map_mul' := map_mul _
  map_add' := map_add _

abbrev affineSpace : Scheme := Spec (CommRingCat.of (AffineRing ι))
abbrev projectiveSpace : Scheme := Proj (grade ι)

def projectiveToComplex : projectiveSpace ι ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero (grade ι) ≫ Spec.map (CommRingCat.ofHom (coefficients ι))

/-- The standard degree-zero ring consists exactly of complex constants. -/
theorem coefficients_surjective : Function.Surjective (coefficients ι) := by
  intro p
  refine ⟨p.val.coeff 0, Subtype.ext ?_⟩
  exact (totalDegree_eq_zero_iff_eq_C.mp
    ((totalDegree_zero_iff_isHomogeneous (Option ι)).mpr p.property)).symm

/-- Finite-dimensional projective space is proper over the complex point. -/
theorem projectiveToComplex_proper [Finite ι] : IsProper (projectiveToComplex ι) := by
  let : IsScalarTower ℂ (grade ι 0) (HomogeneousRing ι) :=
    IsScalarTower.of_algebraMap_eq' (R := ℂ) (S := grade ι 0) (A := HomogeneousRing ι) rfl
  let : Algebra.FiniteType (grade ι 0) (HomogeneousRing ι) :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℂ (grade ι 0) (HomogeneousRing ι)
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (coefficients ι))) :=
    IsClosedImmersion.spec_of_surjective _ (coefficients_surjective ι)
  unfold projectiveToComplex
  infer_instance

def standardOpen : (projectiveSpace ι).Opens := Proj.basicOpen (grade ι) (den ι)

def standardOpenIso : (standardOpen ι).toScheme ≅ affineSpace ι :=
  Proj.basicOpenIsoSpec (grade ι) (den ι) (den_mem ι) (by decide) ≪≫
    Scheme.Spec.mapIso (chartEquiv ι).toCommRingCatIso.symm.op

/-- The standard affine open immersion in projective space. -/
def affineChart : affineSpace ι ⟶ projectiveSpace ι :=
  (Scheme.Spec.mapIso (chartEquiv ι).toCommRingCatIso.symm.op).inv ≫
    Proj.awayι (grade ι) (den ι) (den_mem ι) (by decide)

theorem affineChart_eq_standardOpen :
    affineChart ι = (standardOpenIso ι).inv ≫ (standardOpen ι).ι :=
  (Category.assoc _ _ _).symm

instance : IsOpenImmersion (affineChart ι) := by unfold affineChart; infer_instance

theorem affineChart_isOpenImmersion : IsOpenImmersion (affineChart ι) := inferInstance

theorem affineChart_over :
    affineChart ι ≫ projectiveToComplex ι =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AffineRing ι))) := by
  rw [affineChart, Category.assoc, projectiveToComplex, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (chartEquiv ι).toRingHom) ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (toAffine_constants ι))

end CycleQ2AffineProjectiveCompletionChart
end

#print axioms CycleQ2AffineProjectiveCompletionChart.chartEquiv
#print axioms CycleQ2AffineProjectiveCompletionChart.affineChart_isOpenImmersion
#print axioms CycleQ2AffineProjectiveCompletionChart.affineChart_over
#print axioms CycleQ2AffineProjectiveCompletionChart.projectiveToComplex_proper
