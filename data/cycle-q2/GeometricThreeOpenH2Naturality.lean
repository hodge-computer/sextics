import Proposal.GeometricThreeOpenH2
import Proposal.GeometricCanonicalCechBoundary

/-!
# Naturality of the actual three-open degree-two connecting map

Status: source-only proof draft; verification is deferred at the user's request.
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
  unfold cohomologyMap CycleQ2ThreeOpenSectionH2.connecting
    CycleQ2ThreeOpenCechH2.connecting
  simp only [AddMonoidHom.comp_apply]
  rw [mayerVietoris_delta_naturality, mayerVietoris_delta_naturality,
    sectionsEquiv_symm_map]

/-- The top-open comparison uses the given equality of actual opens. -/
def connectingAtTop (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (U V W : Opens X) (hcover : (U ⊔ V) ⊔ W = ⊤) :
    F.obj.obj (op (TripleOpen U V W)) →+ F.H' 2 ⊤ :=
  (((F.cohomologyPresheaf 2).mapIso (eqToIso hcover.symm).op)
    .addCommGroupIsoToAddEquiv).toAddMonoidHom.comp
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
  let e := ((F.cohomologyPresheaf 2).mapIso (eqToIso hcover.symm).op)
    .addCommGroupIsoToAddEquiv
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
