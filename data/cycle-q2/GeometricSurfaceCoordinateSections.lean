import Proposal.GeometricSurfaceOverlap

/-!
# Homogeneous coordinate changes in the actual surface section rings

Source-only draft; compilation and replay are deferred at the user's
request. The coordinate maps below are the existing projective chart
maps followed by the actual structure-sheaf restrictions. The transition
identity is proved in the original homogeneous localizations and then
transported through their existing section isomorphisms.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceCoordinateSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceOverlap CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport

variable (r θ : ℂ)

/-- The original chart polynomial map into the actual section ring. -/
def coordinatePolynomialSection (i : Fin 4) (V : (projectiveSurface r θ).Opens)
    (hi : V ≤ coordinatePatch r θ i.castSucc) : WeightedPoly →+* Γ(projectiveSurface r θ, V) :=
  (chartSection (coordinateAffineChart r θ i) (Over.mk (homOfLE hi))).comp
    ((dehomogenizedMap r θ i).comp (dehomogenize i).toRingHom)

private theorem basicOpen_sectionMap (j : Fin 4)
    {B : Type} [CommRing B] (q : CoordinateRing r θ j ≃+* B) :
    (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫
        (Proj.basicOpenToSpec (surfaceGrade r θ) (coordinateDen r θ j) ≫
          Spec.map (CommRingCat.ofHom q.symm.toRingHom)).appTop ≫
        (Proj.basicOpen (surfaceGrade r θ) (coordinateDen r θ j)).topIso.hom =
      CommRingCat.ofHom q.symm.toRingHom ≫
        (Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ j)
          (coordinate_mem_grade r θ j) (by decide)).hom := by
  rw [Scheme.Hom.comp_appTop, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality_assoc]
  dsimp only [Scheme.Hom.appTop]
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id, Proj.basicOpenIsoAway_hom]

theorem coordinate_chartSection_top (i : Fin 4) :
    chartSection (coordinateAffineChart r θ i)
        (Over.mk (𝟙 (coordinatePatch r θ i.castSucc))) =
      (coordinateSectionsEquiv r θ i).symm.toRingHom := by
  have hcat : CommRingCat.ofHom
      (chartSection (coordinateAffineChart r θ i)
        (Over.mk (𝟙 (coordinatePatch r θ i.castSucc)))) =
      CommRingCat.ofHom (coordinateSectionsEquiv r θ i).symm.toRingHom := by
    rw [chartSection_top]
    exact basicOpen_sectionMap r θ i (coordinateChartEquiv r θ i)
  exact congrArg CommRingCat.Hom.hom hcat

theorem coordinate_chartSection_subopen (i : Fin 4)
    (V : Over (coordinatePatch r θ i.castSucc)) (a : DehomogenizedRing r θ i) :
    chartSection (coordinateAffineChart r θ i) V a =
      (projectiveSurface r θ).presheaf.map V.hom.op
        ((coordinateSectionsEquiv r θ i).symm a) := by
  calc
    _ = (projectiveSurface r θ).presheaf.map V.hom.op
        (chartSection (coordinateAffineChart r θ i)
          (chartTop (coordinatePatch r θ i.castSucc)) a) :=
      (chartSection_naturality (coordinateAffineChart r θ i) (toChartTop V) a).symm
    _ = _ := by
      rw [show chartSection (coordinateAffineChart r θ i)
        (chartTop (coordinatePatch r θ i.castSucc)) =
          (coordinateSectionsEquiv r θ i).symm.toRingHom from coordinate_chartSection_top r θ i]
      rfl

/-- A homogeneous numerator gives its original homogeneous fraction,
under the actual structure-sheaf restriction. -/
theorem coordinatePolynomialSection_fraction (i : Fin 4)
    (V : (projectiveSurface r θ).Opens) (hi : V ≤ coordinatePatch r θ i.castSucc)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    coordinatePolynomialSection r θ i V hi p =
      (projectiveSurface r θ).presheaf.map (homOfLE hi).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ i)
          (coordinate_mem_grade r θ i) (by decide)).hom
          (homogeneousFraction r θ i n p hp)) := by
  change chartSection (coordinateAffineChart r θ i) (Over.mk (homOfLE hi))
      (dehomogenizedMap r θ i (dehomogenize i p)) = _
  rw [coordinate_chartSection_subopen]
  apply congrArg ((projectiveSurface r θ).presheaf.map (homOfLE hi).op)
  apply (coordinateSectionsEquiv r θ i).injective
  rw [RingEquiv.apply_symm_apply]
  change dehomogenizedMap r θ i (dehomogenize i p) =
    coordinateChartEquiv r θ i
      ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ i)
        (coordinate_mem_grade r θ i) (by decide)).inv
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ i)
          (coordinate_mem_grade r θ i) (by decide)).hom
          (homogeneousFraction r θ i n p hp)))
  rw [Iso.hom_inv_id_apply, coordinateChartEquiv_homogeneousFraction]

def pairDen (j k : Fin 4) : SurfaceRing r θ := coordinateDen r θ j * coordinateDen r θ k
abbrev PairRing (j k : Fin 4) := HomogeneousLocalization.Away (surfaceGrade r θ) (pairDen r θ j k)

def pairOpen (j k : Fin 4) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (pairDen r θ j k)

theorem pairOpen_eq (j k : Fin 4) :
    pairOpen r θ j k = coordinatePatch r θ j.castSucc ⊓ coordinatePatch r θ k.castSucc :=
  Proj.basicOpen_mul _ _ _

theorem pair_le_left (j k : Fin 4) : pairOpen r θ j k ≤ coordinatePatch r θ j.castSucc :=
  (pairOpen_eq r θ j k).le.trans inf_le_left

theorem pair_le_right (j k : Fin 4) : pairOpen r θ j k ≤ coordinatePatch r θ k.castSucc :=
  (pairOpen_eq r θ j k).le.trans inf_le_right

theorem pairDen_mem_grade (j k : Fin 4) : pairDen r θ j k ∈ surfaceGrade r θ 2 :=
  SetLike.mul_mem_graded (coordinate_mem_grade r θ j) (coordinate_mem_grade r θ k)

def pairSectionsIso (j k : Fin 4) :
    CommRingCat.of (PairRing r θ j k) ≅ Γ(projectiveSurface r θ, pairOpen r θ j k) :=
  Proj.basicOpenIsoAway (surfaceGrade r θ) (pairDen r θ j k)
    (pairDen_mem_grade r θ j k) (by decide)

def pairSection (j k : Fin 4) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ pairOpen r θ j k) : PairRing r θ j k →+* Γ(projectiveSurface r θ, V) :=
  ((projectiveSurface r θ).presheaf.map (homOfLE hV).op).hom.comp
    (pairSectionsIso r θ j k).hom.hom

theorem pairSection_left (j k : Fin 4) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ pairOpen r θ j k) (a : CoordinateRing r θ j) :
    pairSection r θ j k V hV
        (coordinateRestriction r θ j k (pairDen r θ j k) rfl a) =
      (projectiveSurface r θ).presheaf.map
        (homOfLE (hV.trans (pair_le_left r θ j k))).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ j)
          (coordinate_mem_grade r θ j) (by decide)).hom a) := by
  have h := congrArg (fun f => f a)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coordinate_mem_grade r θ k) (rfl : pairDen r θ j k = _)).symm
  change (projectiveSurface r θ).presheaf.map (homOfLE (pair_le_left r θ j k)).op
      ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ j)
        (coordinate_mem_grade r θ j) (by decide)).hom a) =
    (pairSectionsIso r θ j k).hom
      (coordinateRestriction r θ j k (pairDen r θ j k) rfl a) at h
  change (projectiveSurface r θ).presheaf.map (homOfLE hV).op
    ((pairSectionsIso r θ j k).hom _) = _
  rw [← h]
  change ((projectiveSurface r θ).presheaf.map (homOfLE (pair_le_left r θ j k)).op ≫
    (projectiveSurface r θ).presheaf.map (homOfLE hV).op) _ = _
  rw [← Functor.map_comp]
  rfl

theorem pairSection_right (j k : Fin 4) (V : (projectiveSurface r θ).Opens)
    (hV : V ≤ pairOpen r θ j k) (a : CoordinateRing r θ k) :
    pairSection r θ j k V hV
        (coordinateRestriction r θ k j (pairDen r θ j k) (mul_comm _ _) a) =
      (projectiveSurface r θ).presheaf.map
        (homOfLE (hV.trans (pair_le_right r θ j k))).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ k)
          (coordinate_mem_grade r θ k) (by decide)).hom a) := by
  have h := congrArg (fun f => f a)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coordinate_mem_grade r θ j) (mul_comm (coordinateDen r θ j) (coordinateDen r θ k))).symm
  change (projectiveSurface r θ).presheaf.map (homOfLE (pair_le_right r θ j k)).op
      ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ k)
        (coordinate_mem_grade r θ k) (by decide)).hom a) =
    (pairSectionsIso r θ j k).hom
      (coordinateRestriction r θ k j (pairDen r θ j k) (mul_comm _ _) a) at h
  change (projectiveSurface r θ).presheaf.map (homOfLE hV).op
    ((pairSectionsIso r θ j k).hom _) = _
  rw [← h]
  change ((projectiveSurface r θ).presheaf.map (homOfLE (pair_le_right r θ j k)).op ≫
    (projectiveSurface r θ).presheaf.map (homOfLE hV).op) _ = _
  rw [← Functor.map_comp]
  rfl

/-- The coordinate transition in the original homogeneous localization. -/
theorem pair_fraction_change (j k : Fin 4) (n : ℕ) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight n) :
    coordinateRestriction r θ j k (pairDen r θ j k) rfl
        (homogeneousFraction r θ j n p hp) *
      coordinateRestriction r θ k j (pairDen r θ j k) (mul_comm _ _)
        (coordinateRatio r θ k j.castSucc) ^ n =
    coordinateRestriction r θ k j (pairDen r θ j k) (mul_comm _ _)
      (homogeneousFraction r θ k n p hp) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow]
  simp only [coordinateRatio, restriction_homogeneousFraction_val, weight_castSucc]
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_one, Submonoid.coe_mul, SubmonoidClass.coe_pow, one_mul,
    pairDen, mul_pow, pow_one]
  ring

/-- The weighted transition is an identity of actual restricted sections. -/
theorem coordinatePolynomialSection_change (j k : Fin 4)
    (V : (projectiveSurface r θ).Opens)
    (hj : V ≤ coordinatePatch r θ j.castSucc) (hk : V ≤ coordinatePatch r θ k.castSucc)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    coordinatePolynomialSection r θ k V hk p =
      coordinatePolynomialSection r θ k V hk (X j.castSucc) ^ n *
        coordinatePolynomialSection r θ j V hj p := by
  let hV : V ≤ pairOpen r θ j k := (le_inf hj hk).trans (pairOpen_eq r θ j k).ge
  have h := congrArg (pairSection r θ j k V hV) (pair_fraction_change r θ j k n p hp)
  rw [map_mul, map_pow, pairSection_left, pairSection_right, pairSection_right] at h
  have hX : (X j.castSucc : WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight j.castSucc
  have hratio := coordinatePolynomialSection_fraction r θ k V hk 1 (X j.castSucc) hX
  have hleft := coordinatePolynomialSection_fraction r θ j V hj n p hp
  have hright := coordinatePolynomialSection_fraction r θ k V hk n p hp
  have hratio' :
      (projectiveSurface r θ).presheaf.map (homOfLE hk).op
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ k)
          (coordinate_mem_grade r θ k) (by decide)).hom (coordinateRatio r θ k j.castSucc)) =
      coordinatePolynomialSection r θ k V hk (X j.castSucc) := by
    simpa only [coordinateRatio, weight_castSucc] using hratio.symm
  rw [← hleft, ← hright, hratio'] at h
  exact h.symm.trans (mul_comm _ _)

theorem coordinatePolynomialSection_self (i : Fin 4)
    (V : (projectiveSurface r θ).Opens) (hi : V ≤ coordinatePatch r θ i.castSucc) :
    coordinatePolynomialSection r θ i V hi (X i.castSucc) = 1 := by
  change chartSection (coordinateAffineChart r θ i) (Over.mk (homOfLE hi))
    (dehomogenizedMap r θ i (dehomogenize i (X i.castSucc))) = 1
  rw [dehomogenize_self, map_one, map_one]

/-- Both ratios are actual sections and are inverses on every common subopen. -/
theorem coordinateRatio_inverse (j k : Fin 4)
    (V : (projectiveSurface r θ).Opens)
    (hj : V ≤ coordinatePatch r θ j.castSucc) (hk : V ≤ coordinatePatch r θ k.castSucc) :
    coordinatePolynomialSection r θ j V hj (X k.castSucc) *
      coordinatePolynomialSection r θ k V hk (X j.castSucc) = 1 := by
  have hX : (X k.castSucc : WeightedPoly).IsWeightedHomogeneous weight 1 := by
    simpa only [weight_castSucc] using isWeightedHomogeneous_X ℂ weight k.castSucc
  have h := coordinatePolynomialSection_change r θ j k V hj hk 1 (X k.castSucc) hX
  rw [coordinatePolynomialSection_self, pow_one] at h
  exact (mul_comm _ _).trans h.symm

/-- Bind the generic coordinate section to the unchanged first chart. -/
theorem first_chart_polynomial_section
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ coordinatePatch r θ 1)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    chartSection (firstAffineChart r θ) (Over.mk (homOfLE hV))
      (algebraMap SurfacePoly (SurfaceChartRing (firstEquations r θ))
        (firstSurfaceDehomogenize p)) =
      coordinatePolynomialSection r θ 1 V hV p := by
  rw [first_chartSection_subopen, coordinatePolynomialSection_fraction r θ 1 V hV n p hp]
  apply congrArg ((projectiveSurface r θ).presheaf.map (homOfLE hV).op)
  apply (firstSectionsEquiv r θ).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (surfaceChartIdeal (firstEquations r θ))
      (firstSurfaceDehomogenize p) =
    firstChartEquiv r θ
      ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 1)
        (coordinate_mem_grade r θ 1) (by decide)).inv
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 1)
          (coordinate_mem_grade r θ 1) (by decide)).hom
          (homogeneousFraction r θ 1 n p hp)))
  rw [Iso.hom_inv_id_apply, firstChartEquiv_homogeneousFraction]

/-- Bind the generic coordinate section to the unchanged second chart. -/
theorem second_chart_polynomial_section
    (V : (projectiveSurface r θ).Opens) (hV : V ≤ coordinatePatch r θ 2)
    (n : ℕ) (p : WeightedPoly) (hp : p.IsWeightedHomogeneous weight n) :
    chartSection (secondAffineChart r θ) (Over.mk (homOfLE hV))
      (algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
        (secondSurfaceDehomogenize p)) =
      coordinatePolynomialSection r θ 2 V hV p := by
  rw [second_chartSection_subopen, coordinatePolynomialSection_fraction r θ 2 V hV n p hp]
  apply congrArg ((projectiveSurface r θ).presheaf.map (homOfLE hV).op)
  apply (secondSectionsEquiv r θ).injective
  rw [RingEquiv.apply_symm_apply]
  change Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ))
      (secondSurfaceDehomogenize p) =
    secondChartEquiv r θ
      ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 2)
        (coordinate_mem_grade r θ 2) (by decide)).inv
        ((Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateDen r θ 2)
          (coordinate_mem_grade r θ 2) (by decide)).hom
          (homogeneousFraction r θ 2 n p hp)))
  rw [Iso.hom_inv_id_apply, secondChartEquiv_homogeneousFraction]

#print axioms coordinatePolynomialSection_fraction
#print axioms coordinatePolynomialSection_change
#print axioms coordinateRatio_inverse
#print axioms first_chart_polynomial_section
#print axioms second_chart_polynomial_section

end CycleQ2SurfaceCoordinateSections

end
