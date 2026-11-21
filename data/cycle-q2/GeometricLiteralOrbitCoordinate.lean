import Proposal.GeometricLiteralOrbitAction
import Proposal.GeometricCartierOrbitCompatibility
import Proposal.GeometricCanonicalCoordinateH2
import Proposal.GeometricSurfaceProjectiveCoefficients

/-!
# Pullback on the three-coordinate intersection of the original surface

The diagonal action fixes the product of the three coordinates. Its pullback on
the full intersection therefore acts on fractions by substituting in their
numerators. Through the projective chart isomorphism this gives the same action
on sections as the localized substitution used in the Laurent trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralOrbitCoordinate
open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization MvPolynomial
  CycleQ2LiteralOrbitAction CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCoordinateCharacter CycleQ2SeedCyclicLocalization CycleQ2OrbitTraceBridge
  CycleQ2GradedAwaySpecialization CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2CartierSurfaceGrading
  CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierProjectiveCover CycleQ2SeedCyclicAction
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2 CycleQ2SeedCechThreeOpen

theorem coordinateProduct_action (z : ℂ) (hz : z^3 = 1) (s : Finset (Fin 3)) :
    surfaceGradedAction z hz (coordinateProduct 57 1 s) =
      surfaceQuotient 57 1 (C (baseFactor z s)) * coordinateProduct 57 1 s := by
  rw [coordinateProduct_eq]
  change surfaceAction z hz (surfaceQuotient 57 1 (baseProductPoly _)) = _
  rw [surfaceAction_polynomial, polynomialAction_baseProduct, map_mul]
  rfl

theorem coordinateIntersection_preimage (z : ℂ) (hz : z^3 = 1) (s : Finset (Fin 3)) :
    (closedProjectiveAction z hz).hom ⁻¹ᵁ coordinateIntersection 57 1 s =
      coordinateIntersection 57 1 s := by
  have hunit : IsUnit (surfaceQuotient 57 1 (C (baseFactor z s))) :=
    (baseFactor_isUnit z hz s).map ((surfaceQuotient 57 1).comp C)
  have htop : Proj.basicOpen (surfaceGrade 57 1) (surfaceQuotient 57 1 (C (baseFactor z s))) = ⊤ := by
    apply top_unique
    rw [← Proj.basicOpen_one (surfaceGrade 57 1)]
    exact Proj.basicOpen_mono _ _ _ hunit.dvd
  change (Proj.map (surfaceGradedAction z hz) _) ⁻¹ᵁ Proj.basicOpen _ _ = _
  rw [Proj.map_preimage_basicOpen, coordinateProduct_action, Proj.basicOpen_mul, htop, top_inf_eq]
  rfl

theorem coordinateOpen_preimage (z : ℂ) (hz : z^3 = 1) (i : Fin 3) :
    (closedProjectiveAction z hz).hom ⁻¹ᵁ coordinateOpen 57 1 i = coordinateOpen 57 1 i := by
  simpa only [coordinateIntersection_singleton] using coordinateIntersection_preimage z hz {i}

theorem triple_fixed (z : ℂ) (hz : z^3 = 1) :
    surfaceGradedAction z hz (coordinateProduct 57 1 Finset.univ) = coordinateProduct 57 1 Finset.univ := by
  rw [coordinateProduct_action, baseFactor_univ z hz, map_one, map_one, one_mul]

def tripleAction (z : ℂ) (hz : z^3 = 1) :
    HomogeneousCoordinateTop 57 →+* HomogeneousCoordinateTop 57 :=
  awayMapOfEq (surfaceGradedAction z hz) _ _ (triple_fixed z hz)

private def ordinaryTripleAction (z : ℂ) (hz : z^3 = 1) :
    CoordinateLocal 57 1 Finset.univ →+* CoordinateLocal 57 1 Finset.univ :=
  ((seedCoordinateEquiv 57 Finset.univ).symm.toRingHom).comp
    ((localAction z hz 57 Complex.I Finset.univ).comp (seedCoordinateEquiv 57 Finset.univ).toRingHom)

private theorem ordinaryTripleAction_base (z : ℂ) (hz : z^3 = 1) (a : SurfaceRing 57 1) :
    ordinaryTripleAction z hz (algebraMap _ _ a) =
      algebraMap _ (CoordinateLocal 57 1 Finset.univ) (surfaceGradedAction z hz a) := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  apply (seedCoordinateEquiv 57 Finset.univ).injective
  change (seedCoordinateEquiv 57 Finset.univ)
    ((seedCoordinateEquiv 57 Finset.univ).symm (localAction z hz 57 Complex.I Finset.univ
      ((seedCoordinateEquiv 57 Finset.univ) (algebraMap _ _ (quotientMap 57 1 p))))) =
    seedCoordinateEquiv 57 Finset.univ (algebraMap _ _ (quotientMap 57 1 (polynomialAction z p)))
  rw [RingEquiv.apply_symm_apply, seedCoordinateEquiv_polynomial, seedCoordinateEquiv_polynomial,
    localAction_mk]

private theorem mk_cancel {a : SurfaceRing 57 1} (n : ℕ) (ha : a ∈ surfaceGrade 57 1 (n • 3)) :
    (Away.mk _ (coordinateProduct_univ_mem_grade 57) n a ha).val *
      algebraMap _ (CoordinateLocal 57 1 Finset.univ) (coordinateProduct 57 1 Finset.univ ^ n) =
      algebraMap _ _ a := by
  rw [Away.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec _ _ _

theorem tripleAction_val (z : ℂ) (hz : z^3 = 1) (x : HomogeneousCoordinateTop 57) :
    (tripleAction z hz x).val = coordinateLinearAction z hz 57 x.val := by
  change (tripleAction z hz x).val = ordinaryTripleAction z hz x.val
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective _ (coordinateProduct_univ_mem_grade 57) x
  have h := congrArg (ordinaryTripleAction z hz) (mk_cancel n ha)
  rw [map_mul, ordinaryTripleAction_base, ordinaryTripleAction_base, map_pow, triple_fixed] at h
  have hi : IsUnit (algebraMap _ (CoordinateLocal 57 1 Finset.univ)
      (coordinateProduct 57 1 Finset.univ ^ n)) := by
    rw [map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit (coordinateProduct 57 1 Finset.univ)).pow n
  apply hi.mul_right_cancel
  rw [tripleAction, awayMapOfEq_mk _ _ _ _ _ (coordinateProduct_univ_mem_grade 57), mk_cancel, h]

private theorem appLE_chart {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    {a : A} {b : B} (he : f a = b) {n : ℕ} (ha : a ∈ 𝒜 n)
    (q : Away 𝒜 a) (le : Proj.basicOpen ℬ b ≤ (Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 a) :
    (Proj.map f hf).appLE _ _ le (Proj.awayToSection 𝒜 a q) =
      Proj.awayToSection ℬ b (awayMapOfEq f a b he q) := by
  subst b
  exact ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f hf ha) q

theorem sectionAt_preimage (z : ℂ) (hz : z^3 = 1) (O : (projectiveSurface 57 1).Opens)
    (hO : O = coordinateIntersection 57 1 Finset.univ) :
    (closedProjectiveAction z hz).hom ⁻¹ᵁ O = O := by
  subst O
  exact coordinateIntersection_preimage z hz Finset.univ

theorem projectiveAction_sectionsAt (z : ℂ) (hz : z^3 = 1) (O : (projectiveSurface 57 1).Opens)
    (hO : O = coordinateIntersection 57 1 Finset.univ) (q : HomogeneousCoordinateTop 57) :
    (closedProjectiveAction z hz).hom.appLE O O (sectionAt_preimage z hz O hO).ge
      (sectionsAt 57 1 Finset.univ (by simp) O hO q) =
      sectionsAt 57 1 Finset.univ (by simp) O hO (tripleAction z hz q) := by
  subst O
  change (closedProjectiveAction z hz).hom.appLE _ _ _ ((projectiveSurface 57 1).presheaf.map (𝟙 _)
    ((Proj.awayToSection _ _) q)) = (projectiveSurface 57 1).presheaf.map (𝟙 _)
      ((Proj.awayToSection _ _) (tripleAction z hz q))
  rw [(projectiveSurface 57 1).presheaf.map_id]
  exact appLE_chart _ _ (surfaceGradedAction z hz) (cyclic_irrelevant_le_map _ (surfaceAction_cube z hz))
      (triple_fixed z hz) (coordinateProduct_univ_mem_grade 57) q (coordinateIntersection_preimage z hz Finset.univ).ge

theorem projectiveAction_tripleSections (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    (closedProjectiveAction z hz).hom.appLE _ _
      (sectionAt_preimage z hz _ (coordinateIntersection_univ 57 1).symm).ge
      (tripleSections 57 1 q) = tripleSections 57 1 (tripleAction z hz q) :=
  projectiveAction_sectionsAt z hz _ (coordinateIntersection_univ 57 1).symm q

open CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricDifferentialSheaf

abbrev tripleCoefficient := basicOpenCoefficient 57 1 (coordinateProduct 57 1 Finset.univ)

theorem tripleCoefficient_val (c : ℂ) :
    (tripleCoefficient c).val = algebraMap ℂ (CoordinateLocal 57 1 Finset.univ) c := by
  change Localization.mk (algebraMap ℂ (SurfaceRing 57 1) c) 1 = _
  rw [Localization.mk_one_eq_algebraMap]
  rfl

theorem tripleSections_coefficient (c : ℂ) :
    tripleSections 57 1 (tripleCoefficient c) =
      coefficientOn (projectiveSurface 57 1).sheaf (projectiveGlobalCoefficient 57 1)
        CycleQ2CanonicalCoordinateH2.TripleOpen c := by
  have he (O : (projectiveSurface 57 1).Opens) (hO : O = coordinateIntersection 57 1 Finset.univ) :
      sectionsAt 57 1 Finset.univ (by simp) O hO (tripleCoefficient c) =
        coefficientOn (projectiveSurface 57 1).sheaf (projectiveGlobalCoefficient 57 1) O c := by
    subst O
    change (projectiveSurface 57 1).presheaf.map (𝟙 _)
      ((coordinateSections 57 1 Finset.univ (by simp)) (tripleCoefficient c)) = _
    rw [(projectiveSurface 57 1).presheaf.map_id]
    exact (ConcreteCategory.congr_hom (C := CommRingCat)
      (globalCoefficient_restriction 57 1 _ (coordinateProduct_univ_mem_grade 57) (by decide)) c).symm
  exact he _ (coordinateIntersection_univ 57 1).symm

def weightedTriple (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    HomogeneousCoordinateTop 57 :=
  q + tripleCoefficient (z^2) * tripleAction z hz q +
    tripleCoefficient z * tripleAction z hz (tripleAction z hz q)

theorem weightedTriple_val (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    (weightedTriple z hz q).val = coordinateTwistedOrbit z hz 57 q.val := by
  rw [coordinateTwistedOrbit_eq_twistedLinear]
  simp only [weightedTriple, HomogeneousLocalization.val_add, HomogeneousLocalization.val_mul,
    tripleCoefficient_val, tripleAction_val, twistedOrbit, Algebra.smul_def]

def pullTriple (z : ℂ) (hz : z^3 = 1) :
    Γ(projectiveSurface 57 1, CycleQ2CanonicalCoordinateH2.TripleOpen) →+*
      Γ(projectiveSurface 57 1, CycleQ2CanonicalCoordinateH2.TripleOpen) :=
  ((closedProjectiveAction z hz).hom.appLE _ _
    (sectionAt_preimage z hz _ (coordinateIntersection_univ 57 1).symm).ge).hom

theorem weightedTriple_section (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    let c : ℂ →+* Γ(projectiveSurface 57 1, CycleQ2CanonicalCoordinateH2.TripleOpen) :=
      coefficientOn (projectiveSurface 57 1).sheaf (projectiveGlobalCoefficient 57 1)
        CycleQ2CanonicalCoordinateH2.TripleOpen
    let s := tripleSections 57 1 q
    tripleSections 57 1 (weightedTriple z hz q) =
      s + c (z ^ 2) * pullTriple z hz s + c z * pullTriple z hz (pullTriple z hz s) := by
  dsimp only
  have pull (x : HomogeneousCoordinateTop 57) :
      pullTriple z hz (tripleSections 57 1 x) = tripleSections 57 1 (tripleAction z hz x) :=
    projectiveAction_tripleSections z hz x
  simp only [weightedTriple, map_add, map_mul, tripleSections_coefficient, pull]
  rfl

theorem tripleAction_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1)
    (q : HomogeneousCoordinateTop 57) :
    tripleAction z hz (tripleAction w hw q) = tripleAction (z*w) (cubeRoot_mul hz hw) q := by
  obtain ⟨n,a,ha,rfl⟩ := Away.mk_surjective _ (coordinateProduct_univ_mem_grade 57) q
  simp only [tripleAction, awayMapOfEq_mk _ _ _ _ _ (coordinateProduct_univ_mem_grade 57)]
  have he := DFunLike.congr_fun (surfaceGradedAction_comp z w hz hw) a
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk]
  congr 1

theorem tripleAction_coefficient (z : ℂ) (hz : z^3 = 1) (c : ℂ) :
    tripleAction z hz (tripleCoefficient c) = tripleCoefficient c := by
  apply HomogeneousLocalization.val_injective
  rw [tripleAction_val, tripleCoefficient_val]
  change ordinaryTripleAction z hz (algebraMap ℂ (CoordinateLocal 57 1 Finset.univ) c) = _
  rw [IsScalarTower.algebraMap_apply ℂ (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ),
    ordinaryTripleAction_base]
  exact congrArg (algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ))
    ((surfaceAction z hz).commutes c)

/-- Pullback of a triple section with the character of the normal generator. -/
def normalPull (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    HomogeneousCoordinateTop 57 :=
  tripleCoefficient (z^2) * tripleAction z hz q

theorem normalPull_section (z : ℂ) (hz : z^3 = 1) (q : HomogeneousCoordinateTop 57) :
    let c : ℂ →+* Γ(projectiveSurface 57 1, CycleQ2CanonicalCoordinateH2.TripleOpen) :=
      coefficientOn (projectiveSurface 57 1).sheaf (projectiveGlobalCoefficient 57 1)
        CycleQ2CanonicalCoordinateH2.TripleOpen
    tripleSections 57 1 (normalPull z hz q) =
      c (z^2) * pullTriple z hz (tripleSections 57 1 q) := by
  dsimp only
  rw [normalPull, map_mul, tripleSections_coefficient]
  rw [show pullTriple z hz (tripleSections 57 1 q) = _ from projectiveAction_tripleSections z hz q]
  rfl

theorem normalPull_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1)
    (q : HomogeneousCoordinateTop 57) :
    normalPull z hz (normalPull w hw q) = normalPull (z*w) (cubeRoot_mul hz hw) q := by
  unfold normalPull
  rw [map_mul (tripleAction z hz), tripleAction_coefficient, tripleAction_comp, mul_pow,
    map_mul, mul_assoc]

theorem weightedTriple_eq_normalPull (z : ℂ) (hz : z^3 = 1) (hz₂ : (z^2)^3 = 1)
    (q : HomogeneousCoordinateTop 57) :
    weightedTriple z hz q = q + normalPull z hz q + normalPull (z^2) hz₂ q := by
  have he : (z^2)^2 = z := by linear_combination z * hz
  simp only [weightedTriple, normalPull, tripleAction_comp, he, ← pow_two]
end CycleQ2LiteralOrbitCoordinate
end

#print axioms CycleQ2LiteralOrbitCoordinate.coordinateOpen_preimage
#print axioms CycleQ2LiteralOrbitCoordinate.tripleAction_val
#print axioms CycleQ2LiteralOrbitCoordinate.weightedTriple_section

#print axioms CycleQ2LiteralOrbitCoordinate.normalPull_comp
#print axioms CycleQ2LiteralOrbitCoordinate.weightedTriple_eq_normalPull
