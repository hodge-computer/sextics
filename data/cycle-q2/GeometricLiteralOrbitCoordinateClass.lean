import Proposal.GeometricAutomorphismCechTwo
import Proposal.GeometricLiteralOrbitCoordinateClassRepresentative
import Proposal.GeometricThreeOpenH2Naturality

/-!
# The pullback of the coordinate Mayer–Vietoris class

The finite-cover construction of the two successive Mayer–Vietoris boundaries
allows one to evaluate the pullback on the same three coordinate opens.
The selected triple of the restricted pullback is the pullback of the
original selected triple.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitCoordinateClass

open CategoryTheory TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2ThreeOpenInjectiveComparison CycleQ2ThreeOpenCechH2
  CycleQ2FiniteCechOrbitPullback CycleQ2FiniteCechRefinement
  CycleQ2ThreeOpenH2Naturality CycleQ2CoordinateMVBinding

section Pullback

variable {X : TopCat.{0}} {ι : Type} (g : X ⟶ X) {F G : AbSheaf X}
  (φ : F ⟶ push g G) (U : ι → Opens X) (hU : ∀ i, U i ≤ pre g (U i))

include hU in
theorem triple_stable (i j k : ι) : TripleOpen (U i) (U j) (U k) ≤
    pre g (TripleOpen (U i) (U j) (U k)) :=
  inf_le_inf (inf_le_inf (hU i) (hU k)) (inf_le_inf (hU j) (hU k))

/-- On a stable cover this is the actual inverse-image cocycle restricted back
to the original opens. -/
def stablePullTwo (c : Two F U) : Two G U :=
  restrictTwo (cover g U) U id hU (pullTwo g φ U c)

theorem selectedTriple_stablePullTwo (c : Two F U) (i j k : ι) :
    selectedTriple U (stablePullTwo g φ U hU c) i j k =
      pullTo g φ (triple_stable g U hU i j k) (selectedTriple U c i j k) := by
  unfold selectedTriple stablePullTwo
  rw [faceValue_restrictTwo]
  exact faceValue_pullTwo g φ U c i j k (triple_stable g U hU i j k) _ _ _

local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

theorem stablePullTwo_class [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (c : Two F U) (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    cechTwoClass U hcover (stablePullTwo g φ U hU c)
      (restrictTwo_normalized (cover g U) U id hU _ (pullTwo_normalized g φ U c hn))
      (restrictTwo_closed (cover g U) U id hU _ (pullTwo_closed g φ U c hc)) =
    cechTwoClass (cover g U) (cover_top g U hcover) (pullTwo g φ U c)
      (pullTwo_normalized g φ U c hn) (pullTwo_closed g φ U c hc) :=
  cechTwoClass_refinement (cover g U) U id hU (cover_top g U hcover) hcover _ _ _

theorem finiteClass_selectedTriple [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (i j k : ι) (htop : (U i ⊔ U j) ⊔ U k = ⊤) (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    cechTwoClass U hcover c hn hc =
      connectingAtTop F (U i) (U j) (U k) htop (selectedTriple U c i j k) := by
  let e := ((F.cohomologyPresheaf 2).mapIso (eqToIso htop.symm).op).addCommGroupIsoToAddEquiv
  have h := mv_eq_finiteClass_restriction U hcover c hn hc i j k
  exact ((congrArg e h).trans (coverIso_restriction F _ htop _)).symm

/-- The derived pullback cocycle is evaluated on the same actual coordinate
triple. The fourth open and any other auxiliary opens only enter the descent. -/
theorem pullTwoClass_selectedTriple [Fintype ι] (hcover : (⨆ i, U i) = ⊤)
    (i j k : ι) (htop : (U i ⊔ U j) ⊔ U k = ⊤) (c : Two F U)
    (hn : NormalizedTwo F U c) (hc : IsTwoCocycle F U c) :
    cechTwoClass (cover g U) (cover_top g U hcover) (pullTwo g φ U c)
        (pullTwo_normalized g φ U c hn) (pullTwo_closed g φ U c hc) =
      connectingAtTop G (U i) (U j) (U k) htop
        (pullTo g φ (triple_stable g U hU i j k) (selectedTriple U c i j k)) := by
  rw [← stablePullTwo_class g φ U hU hcover c hn hc,
    finiteClass_selectedTriple U hcover i j k htop, selectedTriple_stablePullTwo]

end Pullback

section Coordinate

open AlgebraicGeometry CycleQ2CartierProjectiveCover CycleQ2GeometricProjectiveHOne
  CycleQ2ProjectiveCoordinateH2 CycleQ2GeometricHomogeneousWeight
  CycleQ2LiteralOrbitCoordinateClassRepresentative CycleQ2ProjectiveCoordinateCohomology
  CycleQ2AutomorphismCohomology CycleQ2AutomorphismCechTwo CycleQ2AutomorphismGlobalSections

variable (r : ℂ)
private abbrev S := projectiveSurface r 1
private abbrev O := structureAdditiveSheaf (S r)
private abbrev A := coordinateFamily r
local instance coordinateHasExt (r : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (S r)) AddCommGrpCat.{0}) := HasExt.standard _

private abbrev UC (s : Sections (O r) (TripleOpen (A r 0) (A r 1) (A r 2))) :=
  connectingAtTop (O r) (A r 0) (A r 1) (A r 2) (coordinate_three_cover r 1 one_ne_zero) s

/-- Exact Ext pullback on a class represented by any homogeneous coordinate
triple section, for a morphism into the direct image preserving the cover. -/
theorem pullH_coordinateSection (e : (show TopCat from S r) ≅ (show TopCat from S r))
    (φ : O r ⟶ (pushFunctor e).obj (O r)) (h : ∀ i, A r i ≤ pre e.hom (A r i))
    (q : HomogeneousCoordinateTop r) :
    pullH e φ 2 (UC r (tripleSections r 1 q)) =
      UC r (pullTo e.hom φ (triple_stable e.hom (A r) h 0 1 2) (tripleSections r 1 q)) := by
  let c := representative r q
  let hn := representative_normalized r q
  let hc := representative_closed r q
  let hU := coordinateFamily_cover r
  let h3 := coordinate_three_cover r 1 one_ne_zero
  have he := finiteClass_selectedTriple (A r) hU 0 1 2 h3 c hn hc
  rw [selectedTriple_representative] at he
  change cechTwoClass (A r) hU c hn hc = UC r (tripleSections r 1 q) at he
  rw [← he, pullH_cechTwoClass e (A r) hU (cover_top e.hom (A r) hU),
    pullTwoClass_selectedTriple e.hom φ (A r) h hU 0 1 2 h3 c hn hc,
    selectedTriple_representative]

/-- The structure-sheaf class of a homogeneous coordinate fraction. -/
def coordinateStructureClass : HomogeneousCoordinateTop r →+ (O r).H' 2 ⊤ :=
  (connectingAtTop (O r) (A r 0) (A r 1) (A r 2) (coordinate_three_cover r 1 one_ne_zero)).comp
    (tripleSections r 1).toRingHom.toAddMonoidHom

/-- Pullback on the same structure-sheaf cohomology group. -/
def coordinateActionH2 (e : (show TopCat from S r) ≅ (show TopCat from S r))
    (φ : O r ⟶ (pushFunctor e).obj (O r)) : (O r).H' 2 ⊤ →+ (O r).H' 2 ⊤ :=
  pullH (B := O r) (D := O r) e φ 2

/-- Transport on H² evaluated at a second, explicitly identified, coordinate section. -/
theorem pullH_coordinateSection_of_eq (e : (show TopCat from S r) ≅ (show TopCat from S r))
    (φ : O r ⟶ (pushFunctor e).obj (O r)) (h : ∀ i, A r i ≤ pre e.hom (A r i))
    (q t : HomogeneousCoordinateTop r)
    (ht : pullTo e.hom φ (triple_stable e.hom (A r) h 0 1 2) (tripleSections r 1 q) =
      tripleSections r 1 t) :
    coordinateActionH2 r e φ (coordinateStructureClass r q) = coordinateStructureClass r t :=
  (pullH_coordinateSection r e φ h q).trans (congrArg (UC r) ht)

/-- Evaluating the original and twice-pulled class on the same cover reduces
the derived orbit sum to the sum of the three coordinate sections. -/
theorem pullH_coordinateOrbit_of_eq (e : (show TopCat from S r) ≅ (show TopCat from S r))
    (φ : O r ⟶ (pushFunctor e).obj (O r)) (h : ∀ i, A r i ≤ pre e.hom (A r i))
    (q t u w : HomogeneousCoordinateTop r)
    (ht : pullTo e.hom φ (triple_stable e.hom (A r) h 0 1 2) (tripleSections r 1 q) =
      tripleSections r 1 t)
    (hu : pullTo e.hom φ (triple_stable e.hom (A r) h 0 1 2) (tripleSections r 1 t) =
      tripleSections r 1 u) (hw : q + t + u = w) :
    coordinateStructureClass r q + coordinateActionH2 r e φ (coordinateStructureClass r q) +
      coordinateActionH2 r e φ (coordinateActionH2 r e φ (coordinateStructureClass r q)) =
    coordinateStructureClass r w := by
  rw [pullH_coordinateSection_of_eq r e φ h q t ht, pullH_coordinateSection_of_eq r e φ h t u hu,
    ← map_add, ← map_add, hw]

end Coordinate

end CycleQ2LiteralOrbitCoordinateClass
end

#print axioms CycleQ2LiteralOrbitCoordinateClass.selectedTriple_stablePullTwo

#print axioms CycleQ2LiteralOrbitCoordinateClass.pullH_coordinateSection
