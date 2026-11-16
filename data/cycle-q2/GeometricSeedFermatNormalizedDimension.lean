import Proposal.GeometricSeedFermatNormalized
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent

/-!
# Relative dimension three on the actual normalized seed charts

The literal normalized ring has five generators and the two relations
`seedFamily r 0` and `z_i - 1`. At every prime, some other coordinate
`z_j` is nonzero: otherwise the Fermat equation and `z_i = 1` would give
`1 = 0` in the prime quotient.

For `j` distinct from `i`, the Jacobian columns `j,i` have determinant
`partial_j(seedFamily r 0)`. On the open where `z_j` is invertible this
derivative is a unit. Adjoining the inverse adds one generator and one
relation, so the resulting submersive presentation has relative dimension
`6 - 3 = 3`. The native basic-open/localization isomorphisms and source
locality prove relative dimension three on the entire normalized spectrum.

The geometric seed follows Ben Diamond's
surface-section argument. Prepared for `fqlx` with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedFermatNormalizedDimension

open MvPolynomial CategoryTheory TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricSeedSmooth CycleQ2SeedFermatNormalized

/-- The four coordinates other than the normalized degree-one coordinate. -/
abbrev OtherCoordinate (i : Fin 4) := {j : Fin 5 // j ≠ i.castSucc}

/-- Select one Fermat derivative and the derivative of the normalization. -/
def derivativeColumns (i : Fin 4) (j : OtherCoordinate i) : Fin 2 → Fin 5 :=
  ![j.1, i.castSucc]

theorem derivativeColumns_injective (i : Fin 4) (j : OtherCoordinate i) :
    Function.Injective (derivativeColumns i j) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact (j.2 hab).elim
  · exact (j.2 hab.symm).elim
  · rfl

/-- The presentation uses the exact two defining relations of the
normalized ring, with no substitution of a different algebra. -/
def prePresentation (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.PreSubmersivePresentation ℂ (NormalizedRing r i) (Fin 5) (Fin 2) :=
  Algebra.PreSubmersivePresentation.naive
    (v := normalizedRelation r i) (derivativeColumns i j)
    (derivativeColumns_injective i j)

theorem prePresentation_jacobian (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (prePresentation r i j).jacobian =
      normalizedQuotient r i (pderiv j.1 (seedFamily r 0)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  change normalizedQuotient r i
      (pderiv j.1 (seedFamily r 0) * pderiv i.castSucc (X i.castSucc - 1) -
        pderiv j.1 (X i.castSucc - 1) * pderiv i.castSucc (seedFamily r 0)) = _
  simp [MvPolynomial.pderiv_X, MvPolynomial.pderiv_one, Pi.single_apply, j.2, Ne.symm j.2]

/-- The actual localization at a non-normalized coordinate. -/
abbrev CoordinateRing (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :=
  Localization.Away (normalizedCoordinate r i j.1)

theorem coordinate_isUnit (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    IsUnit (algebraMap (NormalizedRing r i) (CoordinateRing r i j)
      (normalizedCoordinate r i j.1)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The actual Fermat derivative is a unit on this coordinate open. -/
theorem partial_isUnit (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4)
    (j : OtherCoordinate i) :
    IsUnit (algebraMap (NormalizedRing r i) (CoordinateRing r i j)
      (normalizedQuotient r i (pderiv j.1 (seedFamily r 0)))) := by
  have hc : IsUnit (CycleQ2SeedFermatCone.coordinateDegree j.1 : ℂ) := by
    apply isUnit_iff_ne_zero.mpr
    rcases j with ⟨j, hj⟩
    fin_cases j <;> norm_num [CycleQ2SeedFermatCone.coordinateDegree, Fin.ext_iff]
  have hc' := hc.map (algebraMap ℂ (CoordinateRing r i j))
  rw [CycleQ2SeedFermatCone.zeroCubic_pderiv r hr j.1]
  simp only [map_mul, map_pow]
  change IsUnit
    (algebraMap (NormalizedRing r i) (CoordinateRing r i j)
        (algebraMap ℂ (NormalizedRing r i)
          (CycleQ2SeedFermatCone.coordinateDegree j.1 : ℂ)) *
      algebraMap (NormalizedRing r i) (CoordinateRing r i j)
        (normalizedCoordinate r i j.1) ^
          (CycleQ2SeedFermatCone.coordinateDegree j.1 - 1))
  rw [← IsScalarTower.algebraMap_apply ℂ (NormalizedRing r i) (CoordinateRing r i j)]
  exact hc'.mul ((coordinate_isUnit r i j).pow _)

/-- Inverting the chosen coordinate adds one generator and one relation
to the original five-generator, two-relation presentation. -/
def localizedPresentation (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.PreSubmersivePresentation ℂ (CoordinateRing r i j)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) :=
  (Algebra.PreSubmersivePresentation.localizationAway
    (CoordinateRing r i j) (normalizedCoordinate r i j.1)).comp
      (prePresentation r i j)

theorem localizedPresentation_jacobian (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (localizedPresentation r i j).jacobian =
      algebraMap (NormalizedRing r i) (CoordinateRing r i j)
          (normalizedQuotient r i (pderiv j.1 (seedFamily r 0))) *
        algebraMap (NormalizedRing r i) (CoordinateRing r i j)
          (normalizedCoordinate r i j.1) := by
  rw [localizedPresentation,
    Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
    prePresentation_jacobian,
    Algebra.PreSubmersivePresentation.localizationAway_jacobian,
    Algebra.smul_def]

def submersivePresentation (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4)
    (j : OtherCoordinate i) :
    Algebra.SubmersivePresentation ℂ (CoordinateRing r i j)
      (Unit ⊕ Fin 5) (Unit ⊕ Fin 2) where
  toPreSubmersivePresentation := localizedPresentation r i j
  jacobian_isUnit := by
    rw [localizedPresentation_jacobian]
    exact (partial_isUnit r hr i j).mul (coordinate_isUnit r i j)

theorem submersivePresentation_dimension (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4)
    (j : OtherCoordinate i) :
    (submersivePresentation r hr i j).dimension = 3 := by
  change Nat.card (Unit ⊕ Fin 5) - Nat.card (Unit ⊕ Fin 2) = 3
  norm_num [Nat.card_eq_fintype_card]

theorem coordinateRing_standardSmooth_dimension (r : ℂ) (hr : r ^ 3 = 2)
    (i : Fin 4) (j : OtherCoordinate i) :
    Algebra.IsStandardSmoothOfRelativeDimension 3 ℂ (CoordinateRing r i j) :=
  (submersivePresentation r hr i j).isStandardSmoothOfRelativeDimension
    (submersivePresentation_dimension r hr i j)

/-- The actual affine normalized scheme, using its inherited coefficients. -/
def normalizedScheme (r : ℂ) (i : Fin 4) : Scheme :=
  Spec (CommRingCat.of (NormalizedRing r i))

def normalizedToComplex (r : ℂ) (i : Fin 4) :
    normalizedScheme r i ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (NormalizedRing r i)))

/-- At least one of the other coordinates is nonzero at every prime. -/
theorem exists_otherCoordinate_not_mem (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4)
    (q : normalizedScheme r i) :
    ∃ j : OtherCoordinate i, normalizedCoordinate r i j.1 ∉ q.asIdeal := by
  classical
  by_contra! h
  letI : q.asIdeal.IsPrime := q.isPrime
  have hz (j : Fin 5) :
      Ideal.Quotient.mk q.asIdeal (normalizedCoordinate r i j) =
        if j = i.castSucc then 1 else 0 := by
    by_cases hj : j = i.castSucc
    · subst j
      simp
    · simpa only [if_neg hj] using
        Ideal.Quotient.eq_zero_iff_mem.mpr (h ⟨j, hj⟩)
  have hF := congrArg (Ideal.Quotient.mk q.asIdeal) (normalizedFermatRelation r hr i)
  simp only [map_add, map_pow, map_zero, hz] at hF
  fin_cases i <;> norm_num [Fin.ext_iff] at hF

def coordinateOpen (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (normalizedScheme r i).Opens :=
  PrimeSpectrum.basicOpen (normalizedCoordinate r i j.1)

theorem coordinateOpens_cover (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    (⨆ j : OtherCoordinate i, coordinateOpen r i j) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  obtain ⟨j, hj⟩ := exists_otherCoordinate_not_mem r hr i q
  exact Opens.mem_iSup.mpr ⟨j, hj⟩

def coordinatePatch (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) : Scheme :=
  Spec (CommRingCat.of (CoordinateRing r i j))

def coordinatePatchToComplex (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    coordinatePatch r i j ⟶ Spec (CommRingCat.of ℂ) :=
  Spec.map (CommRingCat.ofHom (algebraMap ℂ (CoordinateRing r i j)))

theorem coordinatePatch_smoothOfRelativeDimension (r : ℂ) (hr : r ^ 3 = 2)
    (i : Fin 4) (j : OtherCoordinate i) :
    SmoothOfRelativeDimension 3 (coordinatePatchToComplex r i j) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 3)).mpr
  apply RingHom.locally_of (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := 3))
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 3).mpr
    (coordinateRing_standardSmooth_dimension r hr i j)

def coordinatePatchToNormalized (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    coordinatePatch r i j ⟶ normalizedScheme r i :=
  Spec.map (CommRingCat.ofHom
    (algebraMap (NormalizedRing r i) (CoordinateRing r i j)))

theorem coordinatePatchToNormalized_comp_toComplex (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) :
    coordinatePatchToNormalized r i j ≫ normalizedToComplex r i =
      coordinatePatchToComplex r i j := by
  unfold coordinatePatchToNormalized normalizedToComplex coordinatePatchToComplex
  rw [← Spec.map_comp]
  congr 1

/-- This is the native basic-open/localization isomorphism. -/
def coordinateOpenIsoPatch (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (coordinateOpen r i j).toScheme ≅ coordinatePatch r i j :=
  basicOpenIsoSpecAway (R := CommRingCat.of (NormalizedRing r i))
    (normalizedCoordinate r i j.1)

theorem coordinateOpenIsoPatch_hom_toNormalized (r : ℂ) (i : Fin 4)
    (j : OtherCoordinate i) :
    (coordinateOpenIsoPatch r i j).hom ≫ coordinatePatchToNormalized r i j =
      (coordinateOpen r i j).ι :=
  basicOpenIsoSpecAway_hom_SpecMap (R := CommRingCat.of (NormalizedRing r i))
    (normalizedCoordinate r i j.1)

theorem coordinateOpen_toComplex_eq (r : ℂ) (i : Fin 4) (j : OtherCoordinate i) :
    (coordinateOpen r i j).ι ≫ normalizedToComplex r i =
      (coordinateOpenIsoPatch r i j).hom ≫ coordinatePatchToComplex r i j := by
  rw [← coordinateOpenIsoPatch_hom_toNormalized r i j, Category.assoc,
    coordinatePatchToNormalized_comp_toComplex]

theorem coordinateOpen_smoothOfRelativeDimension (r : ℂ) (hr : r ^ 3 = 2)
    (i : Fin 4) (j : OtherCoordinate i) :
    SmoothOfRelativeDimension 3
      ((coordinateOpen r i j).ι ≫ normalizedToComplex r i) := by
  rw [coordinateOpen_toComplex_eq]
  exact IsZariskiLocalAtSource.comp (P := @SmoothOfRelativeDimension 3)
    (coordinatePatch_smoothOfRelativeDimension r hr i j) (coordinateOpenIsoPatch r i j).hom

/-- Every literal normalized seed chart is smooth of relative dimension
three over the original complex coefficient field. -/
theorem normalizedRing_smoothOfRelativeDimension (r : ℂ) (hr : r ^ 3 = 2) (i : Fin 4) :
    SmoothOfRelativeDimension 3
      (Spec.map (CommRingCat.ofHom (algebraMap ℂ (NormalizedRing r i)))) := by
  change SmoothOfRelativeDimension 3 (normalizedToComplex r i)
  exact IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension 3)
    (fun j : OtherCoordinate i => coordinateOpen r i j)
    (coordinateOpens_cover r hr i) (coordinateOpen_smoothOfRelativeDimension r hr i)

end CycleQ2SeedFermatNormalizedDimension

end

#print axioms CycleQ2SeedFermatNormalizedDimension.prePresentation_jacobian
#print axioms CycleQ2SeedFermatNormalizedDimension.coordinateRing_standardSmooth_dimension
#print axioms CycleQ2SeedFermatNormalizedDimension.coordinateOpens_cover
#print axioms CycleQ2SeedFermatNormalizedDimension.normalizedRing_smoothOfRelativeDimension
