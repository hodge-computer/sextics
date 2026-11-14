import Proposal.GeometricSurfaceBindings
import Proposal.GeometricCartierCechNonboundary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricSurfaceAdjunction

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian
open CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceImageLine CycleQ2GeometricIncidenceProj

abbrev LiteralOriginalGrade := surfaceGrade (seedPoint (57 : ℂ) Complex.I)
abbrev LiteralCartierGrade := CycleQ2CartierSurfaceGrading.surfaceGrade 57 1

/-- The original quotient equivalence preserves weighted degree because
it sends each literal polynomial to precisely the same polynomial class. -/
def literalToCartierGraded : LiteralOriginalGrade →+*ᵍ LiteralCartierGrade where
  toRingHom := literalPointSurfaceEquiv.toRingHom
  map_mem := by
    rintro n a ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    exact (literalPointSurfaceEquiv_polynomial p).symm

def literalFromCartierGraded : LiteralCartierGrade →+*ᵍ LiteralOriginalGrade where
  toRingHom := literalPointSurfaceEquiv.symm.toRingHom
  map_mem := by
    rintro n a ⟨p, hp, rfl⟩
    refine ⟨p, hp, ?_⟩
    apply literalPointSurfaceEquiv.injective
    exact (literalPointSurfaceEquiv_polynomial p).trans
      (literalPointSurfaceEquiv.apply_symm_apply _).symm

@[simp] theorem literalToCartierGraded_apply
    (a : PointSurface (seedPoint (57 : ℂ) Complex.I)) :
    literalToCartierGraded a = literalPointSurfaceEquiv a := rfl

@[simp] theorem literalFromCartierGraded_apply (a : SurfaceRing (57 : ℂ) 1) :
    literalFromCartierGraded a = literalPointSurfaceEquiv.symm a := rfl

@[simp] theorem literalToCartierGraded_polynomial (p : WeightedPoly) :
    literalToCartierGraded (Ideal.Quotient.mk
      (pointEquations (seedPoint (57 : ℂ) Complex.I)) p) =
        CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p :=
  literalPointSurfaceEquiv_polynomial p

@[simp] theorem literalFromCartierGraded_polynomial (p : WeightedPoly) :
    literalFromCartierGraded (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) =
      Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) p := by
  apply literalPointSurfaceEquiv.injective
  exact (literalPointSurfaceEquiv.apply_symm_apply _).trans
    (literalPointSurfaceEquiv_polynomial p).symm

theorem literalFromToCartierGraded :
    literalFromCartierGraded.comp literalToCartierGraded =
      GradedRingHom.id LiteralOriginalGrade := by
  apply GradedRingHom.ext
  intro a
  exact literalPointSurfaceEquiv.symm_apply_apply a

theorem literalToFromCartierGraded :
    literalToCartierGraded.comp literalFromCartierGraded =
      GradedRingHom.id LiteralCartierGrade := by
  apply GradedRingHom.ext
  intro a
  exact literalPointSurfaceEquiv.apply_symm_apply a

theorem literalCartier_irrelevant_le_map :
    HomogeneousIdeal.irrelevant LiteralCartierGrade ≤
      (HomogeneousIdeal.irrelevant LiteralOriginalGrade).map literalToCartierGraded := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le LiteralCartierGrade).mpr
  intro n hn a ha
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem LiteralOriginalGrade hn
    (literalFromCartierGraded.map_mem ha)
  have hmap := Ideal.mem_map_of_mem literalToCartierGraded hmem
  have he : literalToCartierGraded (literalFromCartierGraded a) = a :=
    literalPointSurfaceEquiv.apply_symm_apply a
  exact he ▸ hmap

theorem literalOriginal_irrelevant_le_map :
    HomogeneousIdeal.irrelevant LiteralOriginalGrade ≤
      (HomogeneousIdeal.irrelevant LiteralCartierGrade).map literalFromCartierGraded := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le LiteralOriginalGrade).mpr
  intro n hn a ha
  have hmem := HomogeneousIdeal.mem_irrelevant_of_mem LiteralCartierGrade hn
    (literalToCartierGraded.map_mem ha)
  have hmap := Ideal.mem_map_of_mem literalFromCartierGraded hmem
  have he : literalFromCartierGraded (literalToCartierGraded a) = a :=
    literalPointSurfaceEquiv.symm_apply_apply a
  exact he ▸ hmap

/-- The incoming actual Cartier projective surface is the ORIGINAL
incidence-point projective surface, via the actual degree-preserving
quotient isomorphism. This is a constructed scheme isomorphism. -/
def literalCartierProjectiveIso :
    literalIncidenceSurface ≅ CycleQ2CartierProjectiveCover.projectiveSurface 57 1 where
  hom := Proj.map literalFromCartierGraded literalOriginal_irrelevant_le_map
  inv := Proj.map literalToCartierGraded literalCartier_irrelevant_le_map
  hom_inv_id := by
    change (Proj.map literalFromCartierGraded literalOriginal_irrelevant_le_map ≫
      Proj.map literalToCartierGraded literalCartier_irrelevant_le_map) =
        𝟙 (Proj LiteralOriginalGrade)
    simpa only [literalFromToCartierGraded, Proj.map_id] using
      (Proj.map_comp literalToCartierGraded literalFromCartierGraded
        literalCartier_irrelevant_le_map literalOriginal_irrelevant_le_map).symm
  inv_hom_id := by
    change (Proj.map literalToCartierGraded literalCartier_irrelevant_le_map ≫
      Proj.map literalFromCartierGraded literalOriginal_irrelevant_le_map) =
        𝟙 (Proj LiteralCartierGrade)
    simpa only [literalToFromCartierGraded, Proj.map_id] using
      (Proj.map_comp literalFromCartierGraded literalToCartierGraded
        literalOriginal_irrelevant_le_map literalCartier_irrelevant_le_map).symm

theorem literalCartierProjectiveIso_preimage_coordinate (j : Fin 5) :
    literalCartierProjectiveIso.hom ⁻¹ᵁ
        CycleQ2CartierProjectiveCover.coordinatePatch 57 1 j =
      Proj.basicOpen LiteralOriginalGrade (literalSurfaceCoordinate j) := by
  change (Proj.map literalFromCartierGraded literalOriginal_irrelevant_le_map) ⁻¹ᵁ
    Proj.basicOpen LiteralCartierGrade
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X j)) = _
  rw [Proj.map_preimage_basicOpen, literalFromCartierGraded_polynomial]
  rfl

/-- On every homogeneous basic open, the structure-sheaf map of this
scheme isomorphism is exactly the map of degree-zero fractions. -/
theorem literalCartierProjectiveIso_section_naturality
    {n : ℕ} (a : PointSurface (seedPoint (57 : ℂ) Complex.I))
    (ha : a ∈ LiteralOriginalGrade n) :
    Proj.awayToSection LiteralOriginalGrade a ≫
      Scheme.Hom.appLE literalCartierProjectiveIso.inv
        (Proj.basicOpen LiteralOriginalGrade a)
        (Proj.basicOpen LiteralCartierGrade (literalToCartierGraded a)) (by rfl) =
      CommRingCat.ofHom (HomogeneousLocalization.Away.map literalToCartierGraded a) ≫
        Proj.awayToSection LiteralCartierGrade (literalToCartierGraded a) :=
  Proj.awayToSection_comp_appLE literalToCartierGraded literalCartier_irrelevant_le_map ha

private theorem literalToCartier_powers (p : WeightedPoly) :
    Submonoid.powers (Ideal.Quotient.mk
      (pointEquations (seedPoint (57 : ℂ) Complex.I)) p) ≤
        (Submonoid.powers (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p)).comap
          literalToCartierGraded := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  simp only [Submonoid.mem_comap, map_pow, literalToCartierGraded_polynomial]

private theorem literalFromCartier_powers (p : WeightedPoly) :
    Submonoid.powers (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) ≤
      (Submonoid.powers (Ideal.Quotient.mk
        (pointEquations (seedPoint (57 : ℂ) Complex.I)) p)).comap
          literalFromCartierGraded := by
  rintro _ ⟨n, rfl⟩
  refine ⟨n, ?_⟩
  change (Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) p) ^ n =
    literalFromCartierGraded ((CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) ^ n)
  calc
    _ = (literalFromCartierGraded
        (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p)) ^ n :=
      congrArg (fun a : PointSurface (seedPoint (57 : ℂ) Complex.I) => a ^ n)
        (literalFromCartierGraded_polynomial p).symm
    _ = _ := (literalFromCartierGraded.toRingHom.map_pow _ n).symm

section LocalizationBinding

local instance literalOriginalGrading : GradedRing LiteralOriginalGrade :=
  CycleQ2GeometricIncidenceProj.surfaceGradedRing (seedPoint (57 : ℂ) Complex.I)

local instance literalCartierGrading : GradedRing LiteralCartierGrade :=
  CycleQ2CartierSurfaceGrading.surfaceGradedRing 57 1

abbrev LiteralOriginalLocalization (p : WeightedPoly) :=
  HomogeneousLocalization.Away LiteralOriginalGrade
    (show PointSurface (seedPoint (57 : ℂ) Complex.I) from
      Ideal.Quotient.mk (pointEquations (seedPoint (57 : ℂ) Complex.I)) p)

abbrev LiteralCartierLocalization (p : WeightedPoly) :=
  HomogeneousLocalization.Away LiteralCartierGrade
    (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p)

def literalToCartierLocalization (p : WeightedPoly) :
    LiteralOriginalLocalization p →+* LiteralCartierLocalization p :=
  HomogeneousLocalization.map literalToCartierGraded (literalToCartier_powers p)

def literalFromCartierLocalization (p : WeightedPoly) :
    LiteralCartierLocalization p →+* LiteralOriginalLocalization p :=
  HomogeneousLocalization.map literalFromCartierGraded (literalFromCartier_powers p)

theorem literalFromToCartierLocalization (p : WeightedPoly) (x : LiteralOriginalLocalization p) :
    literalFromCartierLocalization p (literalToCartierLocalization p x) = x := by
  simpa only [literalFromCartierLocalization, literalToCartierLocalization,
    literalFromToCartierGraded, HomogeneousLocalization.map_id, RingHom.id_apply] using
      HomogeneousLocalization.map_map (f := literalToCartierGraded)
        (g := literalFromCartierGraded) (literalToCartier_powers p) (literalFromCartier_powers p) x

theorem literalToFromCartierLocalization (p : WeightedPoly) (x : LiteralCartierLocalization p) :
    literalToCartierLocalization p (literalFromCartierLocalization p x) = x := by
  simpa only [literalFromCartierLocalization, literalToCartierLocalization,
    literalToFromCartierGraded, HomogeneousLocalization.map_id, RingHom.id_apply] using
      HomogeneousLocalization.map_map (f := literalFromCartierGraded)
        (g := literalToCartierGraded) (literalFromCartier_powers p) (literalToCartier_powers p) x

/-- The same binding on actual homogeneous localizations, retaining the
literal denominator polynomial on both sides. -/
def literalCartierLocalizationEquiv (p : WeightedPoly) :
    LiteralOriginalLocalization p ≃+* LiteralCartierLocalization p :=
  { literalToCartierLocalization p with
    invFun := literalFromCartierLocalization p
    left_inv := literalFromToCartierLocalization p
    right_inv := literalToFromCartierLocalization p }

end LocalizationBinding

end CycleQ2GeometricSurfaceAdjunction
end
