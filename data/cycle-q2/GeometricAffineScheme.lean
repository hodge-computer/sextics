import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Proposal.GeometricFormalInputs03

/-!
# A genuine smooth affine open of the protected hypersurface

This file constructs the scheme on which the regular residue calculation
will live.  Its coordinate ring is the localization of the actual affine
coordinate ring at the actual normal partial derivative.  Smoothness is
proved by a submersive presentation: the hypersurface relation and the
localization relation have Jacobian determinant equal to the square of
that invertible partial derivative.

The four remaining coordinates give a basis of the genuine module of
Kaehler differentials of this open.  Thus the coordinate forms used in
the residue calculation can be related to regular algebraic forms on a
specific smooth scheme, rather than an unspecified vector space.

These constructions do not prove the algebraic/analytic de Rham
comparison or vanishing of the protected residue class.  Source-only
continuation: Lean elaboration and compilation remain deferred.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2GeometricAffineScheme

open MvPolynomial HodgeComputer CycleQ2AffineClearing
open CycleQ2AffineHypersurface

abbrev BaseRing := AffineCoordinateRing

/-- The normal partial as an element of the actual coordinate ring. -/
def normalClass : BaseRing := affineProjection (pderiv 0 affineF)

theorem normalClass_ne_zero : normalClass ≠ 0 := by
  intro h
  apply normal_ne_zero
  change algebraMap BaseRing AffineFunctionField normalClass = 0
  rw [h, map_zero]

/-- The ring of regular functions on the principal Jacobian open. -/
abbrev OpenRing := Localization.Away normalClass

instance openRing_isDomain : IsDomain OpenRing :=
  Localization.Away.isDomain normalClass_ne_zero

theorem normalClass_isUnit :
    IsUnit (algebraMap BaseRing OpenRing normalClass) :=
  IsLocalization.Away.algebraMap_isUnit normalClass

/-- The five original variables and the one original equation, with the
normal coordinate chosen as the Jacobian column. -/
def affinePresentation :
    Algebra.PreSubmersivePresentation ℂ BaseRing (Fin 5) Unit where
  toPresentation :=
    { toGenerators := Algebra.Generators.naive (I := Ideal.span {affineF})
      relation := fun _ => affineF
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_naive]
        simp only [Set.range_const] }
  map := fun _ => 0
  map_inj := fun _ _ _ => Subsingleton.elim _ _

theorem affinePresentation_jacobian :
    affinePresentation.jacobian = normalClass := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

/-- The presentation has six generators (including the inverse of the
normal partial) and two relations. -/
def localizedPresentation :
    Algebra.PreSubmersivePresentation ℂ OpenRing (Unit ⊕ Fin 5) (Unit ⊕ Unit) :=
  (Algebra.PreSubmersivePresentation.localizationAway OpenRing normalClass).comp
    affinePresentation

theorem localizedPresentation_jacobian :
    localizedPresentation.jacobian =
      (algebraMap BaseRing OpenRing normalClass) ^ 2 := by
  rw [localizedPresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    affinePresentation_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    Algebra.smul_def, pow_two]

/-- A submersive presentation of the actual localized coordinate ring;
the unit-Jacobian property is proved, not assumed. -/
def submersivePresentation :
    Algebra.SubmersivePresentation ℂ OpenRing (Unit ⊕ Fin 5) (Unit ⊕ Unit) where
  toPreSubmersivePresentation := localizedPresentation
  jacobian_isUnit := by
    rw [localizedPresentation_jacobian]
    exact normalClass_isUnit.pow 2

theorem submersivePresentation_dimension :
    submersivePresentation.dimension = 4 := by
  norm_num [Algebra.Presentation.dimension, Nat.card_eq_fintype_card]

instance openRing_standardSmooth : Algebra.IsStandardSmooth ℂ OpenRing :=
  submersivePresentation.isStandardSmooth

instance openRing_standardSmooth_dimension :
    Algebra.IsStandardSmoothOfRelativeDimension 4 ℂ OpenRing :=
  submersivePresentation.isStandardSmoothOfRelativeDimension
    submersivePresentation_dimension

instance openRing_smooth : Algebra.Smooth ℂ OpenRing := inferInstance

/-- The four polynomial coordinates other than the eliminated normal
coordinate, as regular functions on this open. -/
def coordinate (i : Fin 4) : OpenRing :=
  algebraMap BaseRing OpenRing (affineProjection (X i.succ))

private def independentVariable (i : Fin 4) : Unit ⊕ Fin 5 := .inr i.succ

private theorem independentVariable_injective :
    Function.Injective independentVariable :=
  Sum.inr_injective.comp (Fin.succ_injective 4)

private theorem independentVariable_complement :
    IsCompl (Set.range independentVariable)
      (Set.range submersivePresentation.map) := by
  apply eq_compl_iff_isCompl.mp
  ext v
  cases v with
  | inl u =>
      cases u
      simp [Set.mem_range, Sum.exists, independentVariable,
        submersivePresentation, localizedPresentation,
        Algebra.PreSubmersivePresentation.comp_map,
        Algebra.PreSubmersivePresentation.localizationAway_map, affinePresentation]
  | inr i =>
      simp [Set.mem_range, Sum.exists, independentVariable,
        submersivePresentation, localizedPresentation,
        Algebra.PreSubmersivePresentation.comp_map,
        Algebra.PreSubmersivePresentation.localizationAway_map, affinePresentation]
      exact not_congr eq_comm

/-- A basis of the genuine regular Kaehler differentials, obtained from
the complementary coordinates in the proved submersive presentation. -/
def coordinateBasis : Module.Basis (Fin 4) OpenRing Ω[OpenRing⁄ℂ] :=
  submersivePresentation.basisKaehlerOfIsCompl
    independentVariable_injective independentVariable_complement

@[simp] theorem coordinateBasis_apply (i : Fin 4) :
    coordinateBasis i = KaehlerDifferential.D ℂ OpenRing
      (algebraMap BaseRing OpenRing (affineProjection (X i.succ))) := by
  rw [coordinateBasis,
    Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

theorem kaehler_rank : Module.rank OpenRing Ω[OpenRing⁄ℂ] = 4 :=
  Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 4

/-- The same presentation after an arbitrary further principal
localization. This allows the support divisor to be removed later. -/
def furtherSubmersivePresentation (s : OpenRing) :
    Algebra.SubmersivePresentation ℂ (Localization.Away s)
      (Unit ⊕ (Unit ⊕ Fin 5)) (Unit ⊕ (Unit ⊕ Unit)) :=
  (Algebra.SubmersivePresentation.localizationAway (Localization.Away s) s).comp
    submersivePresentation

private def furtherIndependentVariable (i : Fin 4) : Unit ⊕ (Unit ⊕ Fin 5) :=
  .inr (independentVariable i)

private theorem furtherIndependentVariable_injective :
    Function.Injective furtherIndependentVariable :=
  Sum.inr_injective.comp independentVariable_injective

private theorem furtherIndependentVariable_complement (s : OpenRing) :
    IsCompl (Set.range furtherIndependentVariable)
      (Set.range (furtherSubmersivePresentation s).map) := by
  apply eq_compl_iff_isCompl.mp
  ext v
  cases v with
  | inl u =>
      cases u
      simp [Set.mem_range, Sum.exists, furtherIndependentVariable,
        furtherSubmersivePresentation, Algebra.SubmersivePresentation.comp,
        Algebra.SubmersivePresentation.localizationAway,
        Algebra.PreSubmersivePresentation.comp_map,
        Algebra.PreSubmersivePresentation.localizationAway_map]
  | inr v =>
      have hv := Set.ext_iff.mp independentVariable_complement.eq_compl v
      simpa [Set.mem_range, Sum.exists, furtherIndependentVariable,
        furtherSubmersivePresentation, Algebra.SubmersivePresentation.comp,
        Algebra.SubmersivePresentation.localizationAway,
        Algebra.PreSubmersivePresentation.comp_map,
        Algebra.PreSubmersivePresentation.localizationAway_map] using hv

/-- A basis of genuine Kaehler differentials on every further principal
open. It uses the same four coordinate functions. -/
def furtherCoordinateBasis (s : OpenRing) :
    Module.Basis (Fin 4) (Localization.Away s) Ω[Localization.Away s⁄ℂ] :=
  (furtherSubmersivePresentation s).basisKaehlerOfIsCompl
    furtherIndependentVariable_injective (furtherIndependentVariable_complement s)

@[simp] theorem furtherCoordinateBasis_apply (s : OpenRing) (i : Fin 4) :
    furtherCoordinateBasis s i = KaehlerDifferential.D ℂ (Localization.Away s)
      (algebraMap OpenRing (Localization.Away s) (coordinate i)) := by
  rw [furtherCoordinateBasis,
    Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

open AlgebraicGeometry CategoryTheory

/-- The actual affine hypersurface scheme, before restricting to the
normal-Jacobian open. -/
def affineHypersurface : Scheme := Spec (CommRingCat.of BaseRing)

/-- The actual affine scheme with the localized coordinate ring. -/
def jacobianOpen : Scheme := Spec (CommRingCat.of OpenRing)

/-- The localization map gives the expected open immersion of schemes. -/
def inclusion : jacobianOpen ⟶ affineHypersurface :=
  Spec.map (CommRingCat.ofHom (algebraMap BaseRing OpenRing))

instance inclusion_isOpenImmersion : IsOpenImmersion inclusion := by
  change IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap BaseRing (Localization.Away normalClass))))
  infer_instance

theorem inclusion_opensRange :
    inclusion.opensRange = PrimeSpectrum.basicOpen normalClass :=
  Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of BaseRing) normalClass

/-- The structure morphism of the open to the complex point. -/
def toComplex : jacobianOpen ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ OpenRing))

instance toComplex_smooth : AlgebraicGeometry.Smooth toComplex := by
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
  exact (RingHom.smooth_algebraMap).mpr openRing_smooth

theorem jacobianOpen_nonempty : Nonempty jacobianOpen :=
  inferInstanceAs (Nonempty (Spec (CommRingCat.of OpenRing)))

/-- Any further principal open, including one used to remove a supported
divisor, remains a smooth affine scheme over the complex numbers. -/
def furtherOpen (s : OpenRing) : Scheme :=
  Spec (CommRingCat.of (Localization.Away s))

def furtherToComplex (s : OpenRing) :
    furtherOpen s ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (Localization.Away s)))

instance furtherToComplex_smooth (s : OpenRing) :
    AlgebraicGeometry.Smooth (furtherToComplex s) := by
  letI : Algebra.IsStandardSmooth OpenRing (Localization.Away s) :=
    Algebra.IsStandardSmooth.localization_away s
  letI : Algebra.IsStandardSmooth ℂ (Localization.Away s) :=
    Algebra.IsStandardSmooth.trans ℂ OpenRing (Localization.Away s)
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
  exact (RingHom.smooth_algebraMap).mpr inferInstance

theorem furtherOpen_nonempty {s : OpenRing} (hs : s ≠ 0) :
    Nonempty (furtherOpen s) := by
  letI : IsDomain (Localization.Away s) := Localization.Away.isDomain hs
  exact inferInstanceAs (Nonempty (Spec (CommRingCat.of (Localization.Away s))))

end CycleQ2GeometricAffineScheme

end
