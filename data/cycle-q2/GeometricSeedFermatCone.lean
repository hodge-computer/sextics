import Proposal.GeometricSeedSmooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Smooth coordinate opens of the actual zero-cubic seed cone

The coordinate rings below are the five principal localizations of the
literal quotient by `seedFamily r 0`. When `r ^ 3 = 2`, the existing
polynomial identity identifies that equation with the weighted Fermat
equation. On the open where a coordinate is invertible, its corresponding
partial derivative is a unit. A six-generator, two-relation submersive
presentation therefore proves smoothness of relative dimension four.

This is smoothness of the punctured affine cone's coordinate opens. Passing
to the weighted projective quotient and constructing an open in the cubic
parameter space are subsequent geometric steps.

The geometric seed follows Ben Diamond's surface-section argument.
Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2SeedFermatCone

open MvPolynomial CycleQ2GeometricSeedSmooth

/-- The affine cone ring of the existing seed family at the zero cubic. -/
abbrev ConeRing (r : ℂ) := SeedPolynomial ⧸ Ideal.span {seedFamily r 0}

def coneQuotient (r : ℂ) : SeedPolynomial →+* ConeRing r :=
  Ideal.Quotient.mk (Ideal.span {seedFamily r 0})

def coordinateClass (r : ℂ) (j : Fin 5) : ConeRing r :=
  coneQuotient r (X j)

/-- The actual principal open obtained by inverting the chosen coordinate. -/
abbrev CoordinateRing (r : ℂ) (j : Fin 5) :=
  Localization.Away (coordinateClass r j)

theorem coordinate_isUnit (r : ℂ) (j : Fin 5) :
    IsUnit (algebraMap (ConeRing r) (CoordinateRing r j) (coordinateClass r j)) :=
  IsLocalization.Away.algebraMap_isUnit (coordinateClass r j)

/-- The exponent in the weighted Fermat equation: six, or three for `w`. -/
def coordinateDegree (j : Fin 5) : ℕ := if j = 4 then 3 else 6

theorem zeroCubic_pderiv (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    pderiv j (seedFamily r 0) =
      C (coordinateDegree j : ℂ) * X j ^ (coordinateDegree j - 1) := by
  rw [seedFamily_zero_of_cube_two r hr]
  fin_cases j <;>
    norm_num [coordinateDegree, map_add, pderiv_pow, Pi.single_apply, Fin.ext_iff,
      map_ofNat] <;>
    ring <;> rfl

/-- The chosen derivative is a proved unit in the actual coordinate open. -/
theorem partial_isUnit (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    IsUnit (algebraMap (ConeRing r) (CoordinateRing r j)
      (coneQuotient r (pderiv j (seedFamily r 0)))) := by
  have hc : IsUnit (coordinateDegree j : ℂ) := by
    apply isUnit_iff_ne_zero.mpr
    unfold coordinateDegree
    split_ifs <;> norm_num
  have hc' := hc.map (algebraMap ℂ (CoordinateRing r j))
  rw [zeroCubic_pderiv r hr j]
  simp only [map_mul, map_pow]
  change IsUnit
    (algebraMap (ConeRing r) (CoordinateRing r j)
        (algebraMap ℂ (ConeRing r) (coordinateDegree j : ℂ)) *
      algebraMap (ConeRing r) (CoordinateRing r j) (coordinateClass r j) ^
        (coordinateDegree j - 1))
  rw [← IsScalarTower.algebraMap_apply ℂ (ConeRing r) (CoordinateRing r j)]
  exact hc'.mul ((coordinate_isUnit r j).pow (coordinateDegree j - 1))

/-- Five original variables and the original equation, with the chosen
coordinate as the Jacobian column. -/
def conePresentation (r : ℂ) (j : Fin 5) :
    Algebra.PreSubmersivePresentation ℂ (ConeRing r) (Fin 5) Unit where
  toPresentation :=
    { toGenerators := Algebra.Generators.naive (I := Ideal.span {seedFamily r 0})
      relation := fun _ => seedFamily r 0
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_naive]
        simp only [Set.range_const] }
  map := fun _ => j
  map_inj := fun _ _ _ => Subsingleton.elim _ _

theorem conePresentation_jacobian (r : ℂ) (j : Fin 5) :
    (conePresentation r j).jacobian = coneQuotient r (pderiv j (seedFamily r 0)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_unique, Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

/-- Adjoining the inverse of the chosen coordinate adds one generator and
one relation to the actual cone presentation. -/
def localizedPresentation (r : ℂ) (j : Fin 5) :
    Algebra.PreSubmersivePresentation ℂ (CoordinateRing r j)
      (Unit ⊕ Fin 5) (Unit ⊕ Unit) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (CoordinateRing r j) (coordinateClass r j)).comp (conePresentation r j)

theorem localizedPresentation_jacobian (r : ℂ) (j : Fin 5) :
    (localizedPresentation r j).jacobian =
      algebraMap (ConeRing r) (CoordinateRing r j)
          (coneQuotient r (pderiv j (seedFamily r 0))) *
        algebraMap (ConeRing r) (CoordinateRing r j) (coordinateClass r j) := by
  rw [localizedPresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    conePresentation_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    Algebra.smul_def]

/-- A submersive presentation with its unit Jacobian supplied by the
actual coordinate and derivative, without a smoothness premise. -/
def submersivePresentation (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    Algebra.SubmersivePresentation ℂ (CoordinateRing r j)
      (Unit ⊕ Fin 5) (Unit ⊕ Unit) where
  toPreSubmersivePresentation := localizedPresentation r j
  jacobian_isUnit := by
    rw [localizedPresentation_jacobian]
    exact (partial_isUnit r hr j).mul (coordinate_isUnit r j)

theorem submersivePresentation_dimension (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    (submersivePresentation r hr j).dimension = 4 := by
  norm_num [Algebra.Presentation.dimension, Nat.card_eq_fintype_card]

/-- Every coordinate open of the actual zero-cubic cone is standard smooth. -/
theorem coordinateRing_standardSmooth (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    Algebra.IsStandardSmooth ℂ (CoordinateRing r j) :=
  (submersivePresentation r hr j).isStandardSmooth

theorem coordinateRing_standardSmooth_dimension
    (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    Algebra.IsStandardSmoothOfRelativeDimension 4 ℂ (CoordinateRing r j) :=
  (submersivePresentation r hr j).isStandardSmoothOfRelativeDimension
    (submersivePresentation_dimension r hr j)

/-- The principal localizations of the exact seed quotient are smooth
complex algebras for the written proof's cube-root-of-two specialization. -/
theorem coordinateRing_smooth (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    Algebra.Smooth ℂ (CoordinateRing r j) := by
  letI := coordinateRing_standardSmooth r hr j
  infer_instance

open AlgebraicGeometry CategoryTheory

/-- The affine scheme of the actual coordinate localization. -/
def coordinatePatch (r : ℂ) (j : Fin 5) : Scheme :=
  Spec (CommRingCat.of (CoordinateRing r j))

/-- Its structure morphism uses the existing complex algebra structure. -/
def toComplex (r : ℂ) (j : Fin 5) :
    coordinatePatch r j ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateRing r j)))

/-- Every one of the five coordinate opens of the zero-cubic seed cone
is a smooth affine scheme over the exact base field. -/
theorem coordinatePatch_smooth (r : ℂ) (hr : r ^ 3 = 2) (j : Fin 5) :
    AlgebraicGeometry.Smooth (toComplex r j) := by
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr
  exact RingHom.smooth_algebraMap.mpr (coordinateRing_smooth r hr j)

#print axioms zeroCubic_pderiv
#print axioms coordinateRing_standardSmooth_dimension
#print axioms coordinatePatch_smooth

end CycleQ2SeedFermatCone

end
