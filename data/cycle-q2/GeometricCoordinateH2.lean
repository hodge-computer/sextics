import Proposal.GeometricCartierCechNonboundary
import Proposal.GeometricThreeOpenH2
import Proposal.GeometricCartierCoordinateDescent
import Proposal.GeometricCartierCharacter
import Proposal.GeometricCartierOrbit

section SourceProjectiveThreeCover

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveCoordinateCohomology

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial
open CycleQ2SeedTrace CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricSurfaceCoordinates
  CycleQ2SeedQuotientFiniteFree CycleQ2CartierSurfaceGrading
  CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveHOne
open scoped BigOperators

/-- The same three coordinate elements used by the actual homogeneous
coordinate descendant, now viewed as actual opens of the same Proj. -/
def coordinateOpen (r θ : ℂ) (i : Fin 3) : (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (coordinateElement r θ i)

def coordinateIntersection (r θ : ℂ) (s : Finset (Fin 3)) :
    (projectiveSurface r θ).Opens :=
  Proj.basicOpen (surfaceGrade r θ) (coordinateProduct r θ s)

abbrev HomogeneousCoordinateLocal (r θ : ℂ) (s : Finset (Fin 3)) :=
  HomogeneousLocalization.Away (surfaceGrade r θ) (coordinateProduct r θ s)

theorem coordinateElement_mem_grade (r θ : ℂ) (i : Fin 3) :
    coordinateElement r θ i ∈ surfaceGrade r θ 1 := by
  have hw : weight (remainingIndex i) = 1 := by fin_cases i <;> rfl
  apply surfaceQuotient_mem_grade r θ
  change (X (remainingIndex i) : WeightedPoly).IsWeightedHomogeneous weight 1
  simpa only [hw] using isWeightedHomogeneous_X ℂ weight (remainingIndex i)

theorem coordinateProduct_mem_grade (r θ : ℂ) (s : Finset (Fin 3)) :
    coordinateProduct r θ s ∈ surfaceGrade r θ s.card := by
  simpa [coordinateProduct] using SetLike.prod_mem_graded (surfaceGrade r θ)
    (fun _ : Fin 3 => 1) (coordinateElement r θ)
    (fun i _ => coordinateElement_mem_grade r θ i) (F := s)

/-- For theta nonzero the actual surface equations show that x₁,x₂,x₃
cover every relevant homogeneous prime. No cover hypothesis is supplied. -/
theorem coordinate_cover (r θ : ℂ) (hθ : θ ≠ 0) :
    (⨆ i : Fin 3, coordinateOpen r θ i) = ⊤ := by
  classical
  apply top_le_iff.mp
  intro q _
  apply Opens.mem_iSup.mpr
  change ∃ i : Fin 3, coordinateElement r θ i ∉ q.asHomogeneousIdeal.toIdeal
  by_contra! hbad
  letI : q.asHomogeneousIdeal.toIdeal.IsPrime := q.isPrime
  have hall : ∀ j : Fin 5, surfaceQuotient r θ (X j) ∈ q.asHomogeneousIdeal.toIdeal :=
    surface_coordinates_mem_of_three r θ hθ q.asHomogeneousIdeal.toIdeal
      (hbad 0) (hbad 1) (hbad 2)
  have hq : q ∈ ⨆ j : Fin 5, coordinatePatch r θ j := by
    rw [coordinatePatches_cover]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hq
  exact hj (hall j)

theorem coordinate_three_cover (r θ : ℂ) (hθ : θ ≠ 0) :
    (coordinateOpen r θ 0 ⊔ coordinateOpen r θ 1) ⊔ coordinateOpen r θ 2 = ⊤ := by
  apply le_antisymm le_top
  rw [← coordinate_cover r θ hθ]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_of_le_left le_sup_left
  · exact le_sup_of_le_left le_sup_right
  · exact le_sup_right

@[simp] theorem coordinateIntersection_singleton (r θ : ℂ) (i : Fin 3) :
    coordinateIntersection r θ {i} = coordinateOpen r θ i := by
  simp [coordinateIntersection, coordinateProduct, coordinateOpen]

theorem coordinateIntersection_pair (r θ : ℂ) (i j : Fin 3) :
    coordinateIntersection r θ {i,j} = coordinateOpen r θ i ⊓ coordinateOpen r θ j := by
  by_cases hij : i = j
  · subst j
    simp
  · simp [coordinateIntersection, coordinateProduct, Finset.prod_pair hij,
      Proj.basicOpen_mul, coordinateOpen]

theorem coordinateIntersection_univ (r θ : ℂ) :
    coordinateIntersection r θ Finset.univ =
      (coordinateOpen r θ 0 ⊓ coordinateOpen r θ 2) ⊓
        (coordinateOpen r θ 1 ⊓ coordinateOpen r θ 2) := by
  change Proj.basicOpen (surfaceGrade r θ) (∏ i, coordinateElement r θ i) = _
  rw [Fin.prod_univ_three, Proj.basicOpen_mul, Proj.basicOpen_mul]
  change (coordinateOpen r θ 0 ⊓ coordinateOpen r θ 1) ⊓ coordinateOpen r θ 2 = _
  ext x
  constructor
  · rintro ⟨⟨h0,h1⟩,h2⟩
    exact ⟨⟨h0,h2⟩,⟨h1,h2⟩⟩
  · rintro ⟨⟨h0,h2⟩,⟨h1,_⟩⟩
    exact ⟨⟨h0,h1⟩,h2⟩

theorem coordinateProduct_factor (r θ : ℂ) {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateProduct r θ t = coordinateProduct r θ s * coordinateProduct r θ (t \ s) := by
  unfold coordinateProduct
  rw [mul_comm]
  exact (Finset.prod_sdiff hst).symm

theorem coordinateIntersection_mono (r θ : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    coordinateIntersection r θ t ≤ coordinateIntersection r θ s :=
  Proj.basicOpen_mono (surfaceGrade r θ) (coordinateProduct r θ s)
    (coordinateProduct r θ t) ⟨coordinateProduct r θ (t \ s), coordinateProduct_factor r θ hst⟩

/-- Every nonempty finite intersection is the actual affine chart of
the weighted Proj, with the actual degree-zero localization ring. -/
def coordinateChart (r θ : ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty) :
    (coordinateIntersection r θ s).toScheme ≅
      Spec (CommRingCat.of (HomogeneousCoordinateLocal r θ s)) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (coordinateProduct r θ s)
    (coordinateProduct_mem_grade r θ s) (Finset.card_pos.mpr hs)

def coordinateOpenChart (r θ : ℂ) (i : Fin 3) :
    (coordinateOpen r θ i).toScheme ≅
      Spec (CommRingCat.of (HomogeneousLocalization.Away (surfaceGrade r θ)
        (coordinateElement r θ i))) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ) (coordinateElement r θ i)
    (coordinateElement_mem_grade r θ i) (by decide)

def coordinateSections (r θ : ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty) :
    HomogeneousCoordinateLocal r θ s ≃+*
      Γ(projectiveSurface r θ, coordinateIntersection r θ s) :=
  (Proj.basicOpenIsoAway (surfaceGrade r θ) (coordinateProduct r θ s)
    (coordinateProduct_mem_grade r θ s) (Finset.card_pos.mpr hs)).commRingCatIsoToRingEquiv

def coordinateHomogeneousRestriction (r θ : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) :
    HomogeneousCoordinateLocal r θ s →+* HomogeneousCoordinateLocal r θ t :=
  HomogeneousLocalization.awayMap (surfaceGrade r θ)
    (coordinateProduct_mem_grade r θ (t \ s)) (coordinateProduct_factor r θ hst)

/-- Actual homogeneous fraction restriction is actual structure-sheaf
restriction, on every homogeneous section and with no chosen comparison. -/
theorem coordinateSections_restrict (r θ : ℂ) {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (z : HomogeneousCoordinateLocal r θ s) :
    (projectiveSurface r θ).presheaf.map (homOfLE (coordinateIntersection_mono r θ hst)).op
      (coordinateSections r θ s hs z) =
        coordinateSections r θ t ht (coordinateHomogeneousRestriction r θ hst z) := by
  exact congrArg (fun k => k z)
    (Proj.awayMap_awayToSection (surfaceGrade r θ)
      (coordinateProduct_mem_grade r θ (t \ s)) (coordinateProduct_factor r θ hst)).symm

local instance schemeSheavesHasExt (S : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Affineness of these exact three opens supplies the H¹ vanishing
needed by the derived three-open comparison. -/
theorem coordinateOpen_H_one_subsingleton (r θ : ℂ) (i : Fin 3) :
    Subsingleton ((structureAdditiveSheaf (projectiveSurface r θ)).H' 1
      (coordinateOpen r θ i)) :=
  affineFrameHOne_subsingleton (coordinateOpenChart r θ i)
    (structureAdditiveSheaf (projectiveSurface r θ)) (Iso.refl _)

theorem coordinateIntersection_H_one_subsingleton (r θ : ℂ)
    (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Subsingleton ((structureAdditiveSheaf (projectiveSurface r θ)).H' 1
      (coordinateIntersection r θ s)) :=
  affineFrameHOne_subsingleton (coordinateChart r θ s hs)
    (structureAdditiveSheaf (projectiveSurface r θ)) (Iso.refl _)

end CycleQ2ProjectiveCoordinateCohomology

end
end SourceProjectiveThreeCover

section SourceProjectiveCoordinateH2

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveCoordinateH2

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricSurfaceCoordinates
  CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2GeometricProjectiveHOne CycleQ2ProjectiveCoordinateCohomology
  CycleQ2GeometricSheafCohomologyRestriction CycleQ2GeometricLaurentTop

local instance schemeSheavesHasExt (S : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology S) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- The ordinary value of the actual homogeneous restriction is the
canonical ordinary localization restriction. -/
theorem coordinateHomogeneousRestriction_val (r θ : ℂ)
    {s t : Finset (Fin 3)} (hst : s ⊆ t) (z : HomogeneousCoordinateLocal r θ s) :
    (coordinateHomogeneousRestriction r θ hst z).val =
      coordinateRestriction r θ hst z.val := by
  rw [coordinateHomogeneousRestriction, HomogeneousLocalization.val_awayMap]
  have hu : IsUnit (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ t)
      (coordinateProduct r θ s)) :=
    isUnit_of_dvd_unit
      (map_dvd _ ⟨coordinateProduct r θ (t \ s), coordinateProduct_factor r θ hst⟩)
      (IsLocalization.Away.algebraMap_isUnit (coordinateProduct r θ t))
  have hm : Localization.awayLift (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ t))
      (coordinateProduct r θ s) hu = (coordinateRestriction r θ hst).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (coordinateProduct r θ s))
    apply RingHom.ext
    intro x
    change IsLocalization.Away.lift (coordinateProduct r θ s) hu
      (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) x) =
        coordinateRestriction r θ hst
          (algebraMap (SurfaceRing r θ) (CoordinateLocal r θ s) x)
    rw [IsLocalization.Away.lift_eq, coordinateRestriction_base]
  exact DFunLike.congr_fun hm z.val

/-- Canonical homogeneous sections on an equal actual open. The only
transport here is the structure presheaf's map on the equality of opens. -/
def sectionsAt (r θ : ℂ) (s : Finset (Fin 3)) (hs : s.Nonempty)
    (O : (projectiveSurface r θ).Opens) (hO : O = coordinateIntersection r θ s) :
    HomogeneousCoordinateLocal r θ s ≃+* Γ(projectiveSurface r θ, O) :=
  (coordinateSections r θ s hs).trans
    (((projectiveSurface r θ).presheaf.mapIso (eqToIso hO).op).commRingCatIsoToRingEquiv)

theorem sectionsAt_restrict (r θ : ℂ) {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (O P : (projectiveSurface r θ).Opens)
    (hO : O = coordinateIntersection r θ s) (hP : P = coordinateIntersection r θ t)
    (hPO : P ≤ O) (z : HomogeneousCoordinateLocal r θ s) :
    (projectiveSurface r θ).presheaf.map (homOfLE hPO).op
      (sectionsAt r θ s hs O hO z) =
        sectionsAt r θ t ht P hP (coordinateHomogeneousRestriction r θ hst z) := by
  subst O
  subst P
  simpa [sectionsAt, Iso.commRingCatIsoToRingEquiv] using
    coordinateSections_restrict r θ hs ht hst z

def pairSections (r θ : ℂ) (i j : Fin 3) :
    HomogeneousCoordinateLocal r θ {i,j} ≃+*
      Γ(projectiveSurface r θ, coordinateOpen r θ i ⊓ coordinateOpen r θ j) :=
  sectionsAt r θ {i,j} (by simp) _ (coordinateIntersection_pair r θ i j).symm

def tripleSections (r θ : ℂ) :
    HomogeneousCoordinateLocal r θ Finset.univ ≃+*
      Γ(projectiveSurface r θ,
        CycleQ2ThreeOpenCechH2.TripleOpen
          (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)) :=
  sectionsAt r θ Finset.univ (by simp) _ (coordinateIntersection_univ r θ).symm

/-- The actual homogeneous degree-zero differential on the three stable
coordinate opens, with the same alternating signs as the ordinary one. -/
def homogeneousBoundary (r θ : ℂ) :
    (HomogeneousCoordinateLocal r θ {0,1} ×
      HomogeneousCoordinateLocal r θ {0,2} ×
      HomogeneousCoordinateLocal r θ {1,2}) →+
        HomogeneousCoordinateLocal r θ Finset.univ where
  toFun p :=
    coordinateHomogeneousRestriction r θ (Finset.subset_univ {1,2}) p.2.2 -
      coordinateHomogeneousRestriction r θ (Finset.subset_univ {0,2}) p.2.1 +
      coordinateHomogeneousRestriction r θ (Finset.subset_univ {0,1}) p.1
  map_zero' := by simp
  map_add' := by
    intro p q
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    abel

/-- The actual homogeneous and actual structure-sheaf differentials agree
on every cochain. This preserves the representative, not only its class. -/
theorem tripleSections_boundary (r θ : ℂ)
    (a : HomogeneousCoordinateLocal r θ {0,1})
    (b : HomogeneousCoordinateLocal r θ {0,2})
    (c : HomogeneousCoordinateLocal r θ {1,2}) :
    tripleSections r θ (homogeneousBoundary r θ (a,b,c)) =
      CycleQ2ThreeOpenSectionH2.boundary (structureAdditiveSheaf (projectiveSurface r θ))
        (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)
        (pairSections r θ 0 1 a, pairSections r θ 0 2 b, pairSections r θ 1 2 c) := by
  let U := coordinateOpen r θ 0
  let V := coordinateOpen r θ 1
  let W := coordinateOpen r θ 2
  have h12 := sectionsAt_restrict r θ (s := {1,2}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {1,2})
    (V ⊓ W) ((U ⊓ W) ⊓ (V ⊓ W))
    (coordinateIntersection_pair r θ 1 2).symm (coordinateIntersection_univ r θ).symm
    inf_le_right c
  have h02 := sectionsAt_restrict r θ (s := {0,2}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {0,2})
    (U ⊓ W) ((U ⊓ W) ⊓ (V ⊓ W))
    (coordinateIntersection_pair r θ 0 2).symm (coordinateIntersection_univ r θ).symm
    inf_le_left b
  have h01 := sectionsAt_restrict r θ (s := {0,1}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {0,1})
    (U ⊓ V) ((U ⊓ W) ⊓ (V ⊓ W))
    (coordinateIntersection_pair r θ 0 1).symm (coordinateIntersection_univ r θ).symm
    (inf_le_inf (inf_le_left : U ⊓ W ≤ U) (inf_le_left : V ⊓ W ≤ V)) a
  change tripleSections r θ
    (coordinateHomogeneousRestriction r θ (Finset.subset_univ {1,2}) c -
      coordinateHomogeneousRestriction r θ (Finset.subset_univ {0,2}) b +
      coordinateHomogeneousRestriction r θ (Finset.subset_univ {0,1}) a) = _
  rw [map_add, map_sub]
  exact congrArg₂ (· + ·) (congrArg₂ (· - ·) h12.symm h02.symm) h01.symm

/-- The actual section is sent to derived H² by the two genuine
Mayer--Vietoris connecting maps already constructed. -/
def coordinateConnecting (r θ : ℂ) :
    HomogeneousCoordinateLocal r θ Finset.univ →+
      (structureAdditiveSheaf (projectiveSurface r θ)).H' 2
        ((coordinateOpen r θ 0 ⊔ coordinateOpen r θ 1) ⊔ coordinateOpen r θ 2) :=
  (CycleQ2ThreeOpenSectionH2.connecting (structureAdditiveSheaf (projectiveSurface r θ))
    (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)).comp
    (tripleSections r θ).toAddMonoidHom

theorem coordinateConnecting_eq_zero_iff (r θ : ℂ)
    (q : HomogeneousCoordinateLocal r θ Finset.univ) :
    coordinateConnecting r θ q = 0 ↔
      ∃ (a : HomogeneousCoordinateLocal r θ {0,1})
        (b : HomogeneousCoordinateLocal r θ {0,2})
        (c : HomogeneousCoordinateLocal r θ {1,2}),
        homogeneousBoundary r θ (a,b,c) = q := by
  let F := structureAdditiveSheaf (projectiveSurface r θ)
  letI : Subsingleton (F.H' 1 (coordinateOpen r θ 0)) :=
    coordinateOpen_H_one_subsingleton r θ 0
  letI : Subsingleton (F.H' 1 (coordinateOpen r θ 1)) :=
    coordinateOpen_H_one_subsingleton r θ 1
  letI : Subsingleton (F.H' 1 (coordinateOpen r θ 2)) :=
    coordinateOpen_H_one_subsingleton r θ 2
  constructor
  · intro hq
    obtain ⟨a,b,c,habc⟩ :=
      (CycleQ2ThreeOpenSectionH2.connecting_eq_zero_iff F
        (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)
        (tripleSections r θ q)).mp hq
    refine ⟨(pairSections r θ 0 1).symm a, (pairSections r θ 0 2).symm b,
      (pairSections r θ 1 2).symm c, ?_⟩
    apply (tripleSections r θ).injective
    rw [tripleSections_boundary]
    simpa only [RingEquiv.apply_symm_apply] using habc
  · rintro ⟨a,b,c,rfl⟩
    change CycleQ2ThreeOpenSectionH2.connecting F
      (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)
      (tripleSections r θ (homogeneousBoundary r θ (a,b,c))) = 0
    rw [tripleSections_boundary]
    exact CycleQ2ThreeOpenSectionH2.connecting_boundary F _ _ _ _

/-- A nonzero all-negative ordinary coefficient detects the same actual
homogeneous section in derived H². Arbitrary pole orders are retained. -/
theorem coordinateConnecting_ne_zero_of_negative (r : ℂ)
    (q : HomogeneousCoordinateLocal r 1 Finset.univ)
    (hneg : ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent r Finset.univ q.val ab).coeff e ≠ 0) :
    coordinateConnecting r 1 q ≠ 0 := by
  intro hq
  obtain ⟨a,b,c,habc⟩ := (coordinateConnecting_eq_zero_iff r 1 q).mp hq
  have ho :
      coordinateRestriction r 1 (Finset.subset_univ {1,2}) c.val -
        coordinateRestriction r 1 (Finset.subset_univ {0,2}) b.val +
        coordinateRestriction r 1 (Finset.subset_univ {0,1}) a.val = q.val := by
    have hv := congrArg (fun z : HomogeneousCoordinateLocal r 1 Finset.univ => z.val) habc
    change (coordinateHomogeneousRestriction r 1 (Finset.subset_univ {1,2}) c -
      coordinateHomogeneousRestriction r 1 (Finset.subset_univ {0,2}) b +
      coordinateHomogeneousRestriction r 1 (Finset.subset_univ {0,1}) a).val = q.val at hv
    simpa only [HomogeneousLocalization.val_add, HomogeneousLocalization.val_sub,
      coordinateHomogeneousRestriction_val] using hv
  have hz := (coordinate_all_negative_zero_iff r q.val).mpr ⟨a.val,b.val,c.val,ho⟩
  obtain ⟨ab,e,he,hne⟩ := hneg
  exact hne (hz ab e he)

/-- The proved coordinate cover identifies the union's derived group with
global cohomology of the same actual structure sheaf. -/
def unionGlobalEquiv (r θ : ℂ) (hθ : θ ≠ 0) :
    (structureAdditiveSheaf (projectiveSurface r θ)).H' 2
      ((coordinateOpen r θ 0 ⊔ coordinateOpen r θ 1) ⊔ coordinateOpen r θ 2) ≃+
        (structureAdditiveSheaf (projectiveSurface r θ)).H 2 :=
  (((structureAdditiveSheaf (projectiveSurface r θ)).cohomologyPresheaf 2).mapIso
    (eqToIso (coordinate_three_cover r θ hθ).symm).op).addCommGroupIsoToAddEquiv.trans
      (terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r θ))
        (structureAdditiveSheaf (projectiveSurface r θ)) ⊤ isTerminalTop 2)

def globalConnecting (r θ : ℂ) (hθ : θ ≠ 0) :
    HomogeneousCoordinateLocal r θ Finset.univ →+
      (structureAdditiveSheaf (projectiveSurface r θ)).H 2 :=
  (unionGlobalEquiv r θ hθ).toAddMonoidHom.comp (coordinateConnecting r θ)

theorem globalConnecting_ne_zero_of_negative (r : ℂ)
    (q : HomogeneousCoordinateLocal r 1 Finset.univ)
    (hneg : ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent r Finset.univ q.val ab).coeff e ≠ 0) :
    globalConnecting r 1 one_ne_zero q ≠ 0 := by
  intro hq
  apply coordinateConnecting_ne_zero_of_negative r q hneg
  apply (unionGlobalEquiv r 1 one_ne_zero).injective
  exact hq.trans (map_zero _).symm

end CycleQ2ProjectiveCoordinateH2

end
end SourceProjectiveCoordinateH2

section SourceLiteralProjectiveH2

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ProjectiveCoordinateH2

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2GeometricCoordinateCharacter CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCartierCech CycleQ2GeometricFourOpenCech
  CycleQ2NormalConnecting CycleQ2GeometricLaurentTop

attribute [local instance] schemeSheavesHasExt

/-- The character-one homogeneous projection of the same descended
Cartier representative gives a nonzero global derived cohomology class.
The source retains the actual descent equations and its actual cubic
test; no geometric character action on derived cohomology is assumed. -/
theorem literal_projected_globalConnecting_ne_zero
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    globalConnecting 57 1 one_ne_zero (homogeneousProject 57 1 q) ≠ 0 := by
  apply globalConnecting_ne_zero_of_negative
  simpa only [homogeneousProject_val] using
    literal_character_one_negative d hcd q hq

/-- A closed literal result in the actual global derived H² of the
actual projective surface's structure sheaf. The displayed class is
constructed from the original Cartier descendant, then projected on the
stable coordinate cover. -/
theorem literal_global_H_two_nonzero :
    ∃ x : (structureAdditiveSheaf (projectiveSurface 57 1)).H 2, x ≠ 0 := by
  obtain ⟨d,q,hcd,hq,_,_⟩ := literal_homogeneous_character_one_nonzero
  exact ⟨globalConnecting 57 1 one_ne_zero (homogeneousProject 57 1 q),
    literal_projected_globalConnecting_ne_zero d hcd q hq⟩

end CycleQ2ProjectiveCoordinateH2

end
end SourceLiteralProjectiveH2

section SourceLiteralProjectiveOrbitH2

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ProjectiveCoordinateH2

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2GeometricCoordinateCharacter CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCartierCech CycleQ2GeometricFourOpenCech CycleQ2NormalConnecting

attribute [local instance] schemeSheavesHasExt

/-- The actual homogeneous section above the original coordinate-local
twisted orbit. The underlying fraction identity fixes the binding. -/
theorem homogeneous_twistedOrbit_val (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (r : ℂ) (q : HomogeneousCoordinateTop r) :
    ((3 : ℕ) • homogeneousProject r 1 q).val =
      coordinateTwistedOrbit ζ hζ r (coordinateProject r Finset.univ 1 q.val) := by
  rw [HomogeneousLocalization.val_nsmul, homogeneousProject_val,
    coordinateTwistedOrbit_projected]

theorem literal_twisted_globalConnecting_ne_zero (ζ : ℂ) (hζ : ζ ^ 3 = 1)
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d)
    (q : HomogeneousCoordinateTop 57)
    (hq : q.val = coordinateTopRepresentative 57 d) :
    globalConnecting 57 1 one_ne_zero ((3 : ℕ) • homogeneousProject 57 1 q) ≠ 0 := by
  apply globalConnecting_ne_zero_of_negative
  rw [homogeneous_twistedOrbit_val ζ hζ]
  exact literal_projected_twistedOrbit_negative ζ hζ d hcd q hq

/-- Additivity of the genuine connecting maps records the exact factor
three in global derived cohomology as well as in the local fraction. -/
theorem globalConnecting_twisted_factor (r : ℂ) (q : HomogeneousCoordinateTop r) :
    globalConnecting r 1 one_ne_zero ((3 : ℕ) • homogeneousProject r 1 q) =
      (3 : ℕ) • globalConnecting r 1 one_ne_zero (homogeneousProject r 1 q) :=
  map_nsmul _ _ _

end CycleQ2ProjectiveCoordinateH2

end
end SourceLiteralProjectiveOrbitH2
