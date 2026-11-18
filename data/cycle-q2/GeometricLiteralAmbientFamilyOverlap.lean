import Proposal.GeometricSeedFamilyChart

/-!
# The two restrictions on the weight-one projective overlap

For the cubic family, the chart rings at two weight-one coordinates
restrict to the degree-zero localization at their product. A homogeneous
numerator of degree `n` changes by the `n`th power of the coordinate
ratio. Both restrictions give the native overlap maps to the family.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientFamilyOverlap

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedCubicFamily CycleQ2SeedProjectiveFamily CycleQ2SeedFamilyChart
  CycleQ2GeometricIncidenceProj

local instance familyCommRing (r : ℂ) : CommRing (FamilyRing r) :=
  Ideal.Quotient.commRing (familyIdeal r)

abbrev pairDen (r : ℂ) (i j : Fin 4) : FamilyRing r :=
  familyCoordinate r i.castSucc * familyCoordinate r j.castSucc

abbrev PairRing (r : ℂ) (i j : Fin 4) :=
  HomogeneousLocalization.Away (familyGrade r) (pairDen r i j)

private theorem pairDen_comm (r : ℂ) (i j : Fin 4) :
    pairDen r i j = familyCoordinate r j.castSucc * familyCoordinate r i.castSucc :=
  mul_comm (familyCoordinate r i.castSucc) (familyCoordinate r j.castSucc)

def leftRestriction (r : ℂ) (i j : Fin 4) : ChartRing r i →+* PairRing r i j :=
  HomogeneousLocalization.awayMap (familyGrade r) (coordinate_mem_grade r j) rfl

def rightRestriction (r : ℂ) (i j : Fin 4) : ChartRing r j →+* PairRing r i j :=
  HomogeneousLocalization.awayMap (familyGrade r) (coordinate_mem_grade r i) (pairDen_comm r i j)

private theorem localizationElement (r : ℂ) (i j : Fin 4) :
    HomogeneousLocalization.Away.isLocalizationElem (coordinate_mem_grade r i)
      (coordinate_mem_grade r j) = coordinateRatio r i j.castSucc := by
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.isLocalizationElem, coordinateRatio, homogeneousFraction,
    CycleQ2SeedFermatProj.geometricWeight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

theorem leftRestriction_isLocalization (r : ℂ) (i j : Fin 4) :
    letI := (leftRestriction r i j).toAlgebra
    IsLocalization.Away (coordinateRatio r i j.castSucc) (PairRing r i j) := by
  let := (leftRestriction r i j).toAlgebra
  rw [← localizationElement]
  exact HomogeneousLocalization.Away.isLocalization_mul (coordinate_mem_grade r i)
    (coordinate_mem_grade r j) rfl (by decide)

theorem rightRestriction_isLocalization (r : ℂ) (i j : Fin 4) :
    letI := (rightRestriction r i j).toAlgebra
    IsLocalization.Away (coordinateRatio r j i.castSucc) (PairRing r i j) := by
  let := (rightRestriction r i j).toAlgebra
  rw [← localizationElement]
  exact HomogeneousLocalization.Away.isLocalization_mul (coordinate_mem_grade r j)
    (coordinate_mem_grade r i) (pairDen_comm r i j) (by decide)

private theorem restriction_fraction_val (r : ℂ) (i j : Fin 4) (x : FamilyRing r)
    (hx : x = pairDen r i j) (n : ℕ) (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (HomogeneousLocalization.awayMap (familyGrade r) (coordinate_mem_grade r j) hx
      (homogeneousFraction r i n p hp)).val =
      Localization.mk (familyQuotient r p * familyCoordinate r j.castSucc ^ n)
        ⟨x ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers x) n⟩ := by
  rw [homogeneousFraction, HomogeneousLocalization.awayMap_mk, HomogeneousLocalization.Away.val_mk]

/-- Clearing the chart-ratio denominator compares the two restrictions
of the same homogeneous numerator in every degree. -/
theorem fraction_change (r : ℂ) (i j : Fin 4) (n : ℕ) (p : FamilyPolynomial)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    rightRestriction r i j (homogeneousFraction r j n p hp) *
      leftRestriction r i j (coordinateRatio r i j.castSucc) ^ n =
        leftRestriction r i j (homogeneousFraction r i n p hp) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  simp only [leftRestriction, rightRestriction, coordinateRatio,
    restriction_fraction_val, CycleQ2SeedFermatProj.geometricWeight_castSucc]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow, one_mul,
    pairDen, mul_pow, pow_one, familyCoordinate]
  ring

private theorem restrictions_square {A σ : Type} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G] (a b : A)
    (ha : a ∈ G 1) (hb : b ∈ G 1) :
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap G hb (x := a * b) rfl)) ≫
      Proj.awayι G a ha (by decide) =
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.awayMap G ha (mul_comm a b))) ≫
      Proj.awayι G b hb (by decide) := by
  rw [Proj.SpecMap_awayMap_awayι, Proj.SpecMap_awayMap_awayι]

set_option maxHeartbeats 1200000 in
/-- The two overlap restrictions induce the same morphism to the projective family. -/
theorem normalized_away_square (r : ℂ) (i j : Fin 4) :
    Spec.map (CommRingCat.ofHom (leftRestriction r i j)) ≫
      Proj.awayι (familyGrade r) (familyCoordinate r i.castSucc) (coordinate_mem_grade r i)
        (by decide) =
    Spec.map (CommRingCat.ofHom (rightRestriction r i j)) ≫
      Proj.awayι (familyGrade r) (familyCoordinate r j.castSucc) (coordinate_mem_grade r j)
        (by decide) :=
  restrictions_square (familyGrade r) (familyCoordinate r i.castSucc)
    (familyCoordinate r j.castSucc) (coordinate_mem_grade r i) (coordinate_mem_grade r j)

end CycleQ2LiteralAmbientFamilyOverlap
end

#print axioms CycleQ2LiteralAmbientFamilyOverlap.fraction_change
#print axioms CycleQ2LiteralAmbientFamilyOverlap.leftRestriction_isLocalization
#print axioms CycleQ2LiteralAmbientFamilyOverlap.normalized_away_square
