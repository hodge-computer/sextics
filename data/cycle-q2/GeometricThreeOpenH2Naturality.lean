import Proposal.GeometricThreeOpenH2
import Proposal.GeometricProjectiveDescent
import Proposal.GeometricCanonicalCechBoundary

/-!
# Naturality of the actual three-open degree-two connecting map

The maps below are the original two Mayer--Vietoris boundaries, followed only
by the isomorphism induced by the proved equality of the union with the top
open. Naturality follows from the existing Ext-composition naturality and
the existing canonical comparison between sections and degree-zero cohomology.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ThreeOpenH2Naturality

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2GeometricConeCech.HZero CycleQ2ThreeOpenCechH2
  CycleQ2GeometricCanonicalCechBoundary

variable {X : TopCat.{0}}
variable [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
variable {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}}

/-- The actual map of cohomology presheaves, at the indicated open. -/
def cohomologyMap (f : F ⟶ G) (n : ℕ) (O : Opens X) : F.H' n O →+ G.H' n O :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app
    (op O)).hom

/-- Every genuine additive-sheaf morphism commutes with both original
Mayer--Vietoris boundaries and retains the actual input section. -/
theorem connecting_naturality (f : F ⟶ G) (U V W : Opens X)
    (s : F.obj.obj (op (TripleOpen U V W))) :
    cohomologyMap f 2 ((U ⊔ V) ⊔ W)
        (CycleQ2ThreeOpenSectionH2.connecting F U V W s) =
      CycleQ2ThreeOpenSectionH2.connecting G U V W
        (f.hom.app (op (TripleOpen U V W)) s) := by
  let S := outerSquare U V W
  let T := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  let x := (sectionsEquiv F (TripleOpen U V W)).symm s
  change (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 2).map f).app
      (op S.X₄)) (S.δ F 1 2 rfl (T.δ F 0 1 rfl x)) =
    S.δ G 1 2 rfl (T.δ G 0 1 rfl
      ((sectionsEquiv G (TripleOpen U V W)).symm
        (f.hom.app (op (TripleOpen U V W)) s)))
  exact (mayerVietoris_delta_naturality f S 1 2 rfl _).trans
    (congrArg (S.δ G 1 2 rfl)
      ((mayerVietoris_delta_naturality f T 0 1 rfl x).trans
        (congrArg (T.δ G 0 1 rfl) (sectionsEquiv_symm_map f _ s))))

/-- The top-open comparison uses the given equality of actual opens. -/
def connectingAtTop (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (U V W : Opens X) (hcover : (U ⊔ V) ⊔ W = ⊤) :
    F.obj.obj (op (TripleOpen U V W)) →+ F.H' 2 ⊤ :=
  (((F.cohomologyPresheaf 2).mapIso
    (eqToIso hcover.symm).op).addCommGroupIsoToAddEquiv).toAddMonoidHom.comp
      (CycleQ2ThreeOpenSectionH2.connecting F U V W)

/-- Naturality persists after the same proved cover equality is applied
to the two cohomology presheaves. -/
theorem connectingAtTop_naturality (f : F ⟶ G) (U V W : Opens X)
    (hcover : (U ⊔ V) ⊔ W = ⊤)
    (s : F.obj.obj (op (TripleOpen U V W))) :
    cohomologyMap f 2 ⊤ (connectingAtTop F U V W hcover s) =
      connectingAtTop G U V W hcover (f.hom.app (op (TripleOpen U V W)) s) := by
  let α := (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 2).map f
  have h := ConcreteCategory.congr_hom
    (α.naturality (eqToIso hcover.symm).op.hom)
    (CycleQ2ThreeOpenSectionH2.connecting F U V W s)
  change cohomologyMap f 2 ⊤ (connectingAtTop F U V W hcover s) =
    (G.cohomologyPresheaf 2).map (eqToIso hcover.symm).op.hom
      (cohomologyMap f 2 ((U ⊔ V) ⊔ W)
        (CycleQ2ThreeOpenSectionH2.connecting F U V W s)) at h
  exact h.trans (congrArg
    ((G.cohomologyPresheaf 2).map (eqToIso hcover.symm).op.hom)
    (connecting_naturality f U V W s))

/-- Vanishing is exactly an actual alternating boundary on the three
pair intersections, once the three actual local H¹ groups vanish. -/
theorem connectingAtTop_eq_zero_iff
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (U V W : Opens X) (hcover : (U ⊔ V) ⊔ W = ⊤)
    [Subsingleton (F.H' 1 U)] [Subsingleton (F.H' 1 V)] [Subsingleton (F.H' 1 W)]
    (s : F.obj.obj (op (TripleOpen U V W))) :
    connectingAtTop F U V W hcover s = 0 ↔
      ∃ (a : F.obj.obj (op (U ⊓ V))) (b : F.obj.obj (op (U ⊓ W)))
        (c : F.obj.obj (op (V ⊓ W))),
        CycleQ2ThreeOpenSectionH2.boundary F U V W (a,b,c) = s := by
  let e := ((F.cohomologyPresheaf 2).mapIso
    (eqToIso hcover.symm).op).addCommGroupIsoToAddEquiv
  have he : connectingAtTop F U V W hcover s = 0 ↔
      CycleQ2ThreeOpenSectionH2.connecting F U V W s = 0 := by
    constructor
    · intro hs
      apply e.injective
      exact hs.trans e.map_zero.symm
    · intro hs
      change e (CycleQ2ThreeOpenSectionH2.connecting F U V W s) = 0
      rw [hs, map_zero]
  exact he.trans (CycleQ2ThreeOpenSectionH2.connecting_eq_zero_iff F U V W s)

#print axioms connecting_naturality
#print axioms connectingAtTop_naturality
#print axioms connectingAtTop_eq_zero_iff

end CycleQ2ThreeOpenH2Naturality

end

/-! The native coordinate comparison is checked before specializing the
incidence parameter. Keeping this comparison behind an imported theorem
also avoids repeating derived-cohomology reductions at the literal seed. -/

noncomputable section

namespace CycleQ2CoordinateTopDescent

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCartierCech CycleQ2GeometricCartierNormalLift
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2GeometricFourOpenCech CycleQ2GeometricHomogeneousPrincipal
  CycleQ2ProjectiveMixedSections CycleQ2ThreeOpenH2Naturality
  CycleQ2GeometricHomogeneousWeight

local instance surfaceHasExt {T : Type} [TopologicalSpace T] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

private theorem connectingAtTop_apply {X : TopCat.{0}}
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (U V W : Opens X) (h : (U ⊔ V) ⊔ W = ⊤)
    (s : F.obj.obj (op (CycleQ2ThreeOpenCechH2.TripleOpen U V W))) :
    connectingAtTop F U V W h s =
      (F.cohomologyPresheaf 2).map (eqToIso h.symm).op.hom
        (CycleQ2ThreeOpenSectionH2.connecting F U V W s) := rfl

private theorem coordinateConnecting_apply (r θ : ℂ)
    (q : HomogeneousCoordinateLocal r θ Finset.univ) :
    coordinateConnecting r θ q =
      CycleQ2ThreeOpenSectionH2.connecting (structureAdditiveSheaf (projectiveSurface r θ))
        (coordinateOpen r θ 0) (coordinateOpen r θ 1) (coordinateOpen r θ 2)
        (tripleSections r θ q) := rfl

theorem coordinateSurfaceHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (show TopCat from projectiveSurface r θ))
      AddCommGrpCat.{0}) := HasExt.standard _

attribute [local instance] coordinateSurfaceHasExt

private theorem rightFiniteClass_eq_coordinateMap (r : ℂ)
    (hcover : (⨆ i, family (surfaceGrade r 1) (CycleQ2GeometricCartierCech.coordinateCover r) i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    rightFiniteClass (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r) hcover d =
      ((structureAdditiveSheaf (projectiveSurface r 1)).cohomologyPresheaf 2).map
        (eqToIso (coordinate_three_cover r 1 one_ne_zero).symm).op.hom
          (coordinateConnecting r 1 (homogeneousCoordinateRepresentative r dH)) := by
  exact CycleQ2CoordinateMVBinding.finite_coordinate_top_eq r hcover _
    (rightFinite_normalized (surfaceGrade r 1) (coverElement r 1) (CycleQ2GeometricCartierCech.coordinateCover r) d.val)
    (rightFinite_closed (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r) hcover d)
    (homogeneousCoordinateRepresentative r dH)
    (CycleQ2CoordinateMVBinding.selectedTriple_rightFinite r d dH hR)

private theorem rightFiniteClass_eq_coordinateTop (r : ℂ)
    (hcover : (⨆ i, family (surfaceGrade r 1) (CycleQ2GeometricCartierCech.coordinateCover r) i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    rightFiniteClass (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1)
      (coordinateCover_mem_grade r) hcover d =
      connectingAtTop (X := (show TopCat from projectiveSurface r 1))
        (structureAdditiveSheaf (projectiveSurface r 1))
        (coordinateOpen r 1 0) (coordinateOpen r 1 1) (coordinateOpen r 1 2)
        (coordinate_three_cover r 1 one_ne_zero)
        (tripleSections r 1 (homogeneousCoordinateRepresentative r dH)) := by
  have h := congrArg
    (fun z : (structureAdditiveSheaf (projectiveSurface r 1)).H' 2
        ((coordinateOpen r 1 0 ⊔ coordinateOpen r 1 1) ⊔ coordinateOpen r 1 2) =>
      ((structureAdditiveSheaf (projectiveSurface r 1)).cohomologyPresheaf 2).map
        (eqToIso (coordinate_three_cover r 1 one_ne_zero).symm).op.hom z)
    (coordinateConnecting_apply r 1 (homogeneousCoordinateRepresentative r dH))
  exact (rightFiniteClass_eq_coordinateMap r hcover d dH hR).trans
    (h.trans (connectingAtTop_apply (X := (show TopCat from projectiveSurface r 1))
      (structureAdditiveSheaf (projectiveSurface r 1))
      (coordinateOpen r 1 0) (coordinateOpen r 1 1) (coordinateOpen r 1 2)
      (coordinate_three_cover r 1 one_ne_zero)
      (tripleSections r 1 (homogeneousCoordinateRepresentative r dH))).symm)

private theorem homogeneousCoordinateRepresentative_neg (r : ℂ)
    (dH : TwoCocycles (homogeneousCoordinateSystem r)) :
    homogeneousCoordinateRepresentative r (-dH) =
      -homogeneousCoordinateRepresentative r dH := rfl

theorem rightFiniteClass_neg_eq_coordinateTop (r : ℂ)
    (hcover : (⨆ i, family (surfaceGrade r 1) (CycleQ2GeometricCartierCech.coordinateCover r) i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    rightFiniteClass (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1)
      (coordinateCover_mem_grade r) hcover (-d) =
      connectingAtTop (X := (show TopCat from projectiveSurface r 1))
        (structureAdditiveSheaf (projectiveSurface r 1))
        (coordinateOpen r 1 0) (coordinateOpen r 1 1) (coordinateOpen r 1 2)
        (coordinate_three_cover r 1 one_ne_zero)
        (tripleSections r 1 (-homogeneousCoordinateRepresentative r dH)) := by
  let f := (homogeneousRightEmpty (surfaceGrade r 1)
    (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
    (CycleQ2GeometricCartierCech.coordinateCover r) (fun _ => 1)
    (coordinateCover_mem_grade r)).mapCycle
  have hneg : f (-d) = -dH := (_root_.map_neg f d).trans
    (congrArg (fun z : TwoCocycles (homogeneousCoordinateSystem r) => -z) hR)
  have h := rightFiniteClass_eq_coordinateTop r hcover (-d) (-dH) hneg
  exact h.trans (congrArg (fun q : HomogeneousCoordinateTop r =>
    connectingAtTop (X := (show TopCat from projectiveSurface r 1))
      (structureAdditiveSheaf (projectiveSurface r 1))
      (coordinateOpen r 1 0) (coordinateOpen r 1 1) (coordinateOpen r 1 2)
      (coordinate_three_cover r 1 one_ne_zero) (tripleSections r 1 q))
    (homogeneousCoordinateRepresentative_neg r dH))

open CycleQ2LiteralProjectiveDescent

/-- Specialize the signed native comparison before using the cubic map. -/
theorem literalRightClass_neg_eq_coordinateTop
    (d : TwoCocycles (literalSystem.right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (hR : literalRightEmpty.mapCycle d = dH) :
    literalRightClass (-d) =
      connectingAtTop (X := (show TopCat from projectiveSurface 57 1))
        (structureAdditiveSheaf (projectiveSurface 57 1))
        (coordinateOpen 57 1 0) (coordinateOpen 57 1 1) (coordinateOpen 57 1 2)
        (coordinate_three_cover 57 1 one_ne_zero)
        (tripleSections 57 1 (-homogeneousCoordinateRepresentative 57 dH)) :=
  rightFiniteClass_neg_eq_coordinateTop 57 literalCoordinateCover d dH hR

/-- The retained original class has the same signed native representative. -/
theorem literalDerivedClassAtTop_eq_coordinateTop
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (c : TwoCocycles (literalSystem.left ∅)) (d : TwoCocycles (literalSystem.right ∅))
    (hL : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hR : literalRightEmpty.mapCycle d = dH)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop =
      connectingAtTop (X := (show TopCat from projectiveSurface 57 1))
        (structureAdditiveSheaf (projectiveSurface 57 1))
        (coordinateOpen 57 1 0) (coordinateOpen 57 1 1) (coordinateOpen 57 1 2)
        (coordinate_three_cover 57 1 one_ne_zero)
        (tripleSections 57 1 (-homogeneousCoordinateRepresentative 57 dH)) :=
  (literal_secondDescent_class c d hL hcd).trans
    (literalRightClass_neg_eq_coordinateTop d dH hR)

/-- Apply a coordinate-compatible map to the retained original class. -/
theorem map_literalDerivedClassAtTop_eq {M : Type*}
    (f : (structureAdditiveSheaf (projectiveSurface (57 : ℂ) 1)).H' 2 ⊤ → M)
    (g : HomogeneousCoordinateTop 57 → M)
    (hfg : ∀ q, f (connectingAtTop (X := (show TopCat from projectiveSurface 57 1))
      (structureAdditiveSheaf (projectiveSurface 57 1))
      (coordinateOpen 57 1 0) (coordinateOpen 57 1 1) (coordinateOpen 57 1 2)
      (coordinate_three_cover 57 1 one_ne_zero) (tripleSections 57 1 q)) = g q)
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (c : TwoCocycles (literalSystem.left ∅)) (d : TwoCocycles (literalSystem.right ∅))
    (hL : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hR : literalRightEmpty.mapCycle d = dH)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    f CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop =
      g (-homogeneousCoordinateRepresentative 57 dH) := by
  exact (congrArg f (literalDerivedClassAtTop_eq_coordinateTop dH c d hL hR hcd)).trans
    (hfg (-homogeneousCoordinateRepresentative 57 dH))

#print axioms rightFiniteClass_neg_eq_coordinateTop
#print axioms literalRightClass_neg_eq_coordinateTop
#print axioms literalDerivedClassAtTop_eq_coordinateTop
#print axioms map_literalDerivedClassAtTop_eq

end CycleQ2CoordinateTopDescent

end

/-!
## A three-open subcover of the original four-open Čech class

The finite-family injective descent already restricts to every selected
triple of opens.  When that triple covers the whole space, its two actual
Mayer--Vietoris boundaries are the same derived class.  In particular,
the last face of a four-open cocycle is retained without rescaling.
-/

noncomputable section
namespace CycleQ2FourOpenThreeSubcover

open CategoryTheory Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2FiniteInjectiveCech (Two NormalizedTwo IsTwoCocycle)
open CycleQ2FiniteCechDescent (cechTwoClass)
open CycleQ2FourToFiniteCech
  (extendTwo extendTwo_normalized extendTwo_closed finiteClass_eq_fourClass
    faceValue_extendTwo)
open CycleQ2ThreeOpenInjectiveComparison
  (selectedTriple mv_eq_finiteClass_restriction)
open CycleQ2ThreeOpenH2Naturality (connectingAtTop)
open CycleQ2ThreeOpenCechH2 (TripleOpen)

variable {X : TopCat.{0}}
local instance subcoverHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X}

/-- A selected three-open subcover computes the same existing finite
Čech class through the original positive degree-two MV normalization. -/
theorem finiteClass_eq_connectingAtTop {ι : Type} [Fintype ι]
    (A : ι → Opens X) (hcover : (⨆ i, A i) = ⊤)
    (c : Two F A) (hn : NormalizedTwo F A c) (hc : IsTwoCocycle F A c)
    (i j k : ι) (hthree : (A i ⊔ A j) ⊔ A k = ⊤) :
    cechTwoClass A hcover c hn hc =
      connectingAtTop F (A i) (A j) (A k) hthree (selectedTriple A c i j k) := by
  let e := ((F.cohomologyPresheaf 2).mapIso
    (eqToIso hthree.symm).op).addCommGroupIsoToAddEquiv
  apply e.symm.injective
  change e.symm (cechTwoClass A hcover c hn hc) =
    e.symm (e (CycleQ2ThreeOpenSectionH2.connecting F (A i) (A j) (A k)
      (selectedTriple A c i j k)))
  rw [AddEquiv.symm_apply_apply]
  change (F.cohomologyPresheaf 2).map (eqToHom hthree).op
    (cechTwoClass A hcover c hn hc) = _
  have he : (eqToHom hthree : (A i ⊔ A j) ⊔ A k ⟶ (⊤ : Opens X)) =
      homOfLE le_top := Subsingleton.elim _ _
  rw [he]
  exact (mv_eq_finiteClass_restriction A hcover c hn hc i j k).symm

variable (U : Fin 4 → Opens X)

/-- The literal 123 face, restricted only to the equivalent intersection
used by the three-open Mayer--Vietoris construction. -/
def lastFace (c : CycleQ2CechTwoToDerived.Two F U) :
    Sections F (TripleOpen (U 1) (U 2) (U 3)) :=
  res F (le_inf
    (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
    (inf_le_left.trans inf_le_right)) c.2.2.2

theorem selectedTriple_extendTwo_last (c : CycleQ2CechTwoToDerived.Two F U) :
    selectedTriple U (extendTwo U c) 1 2 3 = lastFace U c := by
  rw [selectedTriple, faceValue_extendTwo]
  rfl

/-- If the last three opens cover the space, the original four-open
class is exactly the actual three-open connecting image of its 123 face.
No affine vanishing or additional class-transport premise is used. -/
theorem fourClass_eq_lastFace_connectingAtTop (hcover : (⨆ i, U i) = ⊤)
    (hthree : (U 1 ⊔ U 2) ⊔ U 3 = ⊤)
    (c : CycleQ2CechTwoToDerived.Two F U)
    (hc : CycleQ2CechTwoToDerived.d2 F U c = 0) :
    CycleQ2CechTwoToDerived.cechTwoClass U hcover c hc =
      connectingAtTop F (U 1) (U 2) (U 3) hthree (lastFace U c) := by
  have h := finiteClass_eq_connectingAtTop U hcover (extendTwo U c)
    (extendTwo_normalized U c) (extendTwo_closed U hcover c hc) 1 2 3 hthree
  rw [finiteClass_eq_fourClass U hcover c hc, selectedTriple_extendTwo_last] at h
  exact h

end CycleQ2FourOpenThreeSubcover
end

#print axioms CycleQ2FourOpenThreeSubcover.finiteClass_eq_connectingAtTop
#print axioms CycleQ2FourOpenThreeSubcover.fourClass_eq_lastFace_connectingAtTop
