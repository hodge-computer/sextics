import Proposal.GeometricAffineCohomology
import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricAffineHigherChartRestriction
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris
import Proposal.GeometricMonicGenericSupport
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-! Acyclicity of affine sections of the finite-rank differential-form sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

section
namespace CycleQ2AffinePowerSheaf
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricSheafCohomologyRestriction (freeAbelianSheaf chartCohomologyEquiv restrictionHEquiv)

variable (X : Scheme.{0}) (I : Type)

private abbrev O := structureAdditiveSheaf X

private def powerPre : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (I → Γ(X,U.unop))
  map f := AddCommGrpCat.ofHom
    { toFun := fun x i => X.presheaf.map f (x i)
      map_zero' := by funext i; exact map_zero _
      map_add' := by intro x y; funext i; exact map_add _ _ _ }
  map_id U := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext i
    exact ConcreteCategory.congr_hom (X.presheaf.map_id U) (x i)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext i
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp f g) (x i)

def power : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} := by
  refine ⟨powerPre X I, ?_⟩
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS
  apply CycleQ2SheafForLocalCoordinates.isSheafFor
    (Q := X.presheaf ⋙ forget CommRingCat)
    (fun {_} _ => Equiv.refl _) (fun _ _ _ _ => rfl)
  exact (Presheaf.isSheaf_comp_of_isSheaf _ X.presheaf (forget CommRingCat) X.sheaf.property).isSheafFor S hS

private def proj (i : I) : power X I ⟶ O X where
  hom := { app := fun _ => AddCommGrpCat.ofHom (Pi.evalAddMonoidHom _ i)
           naturality := fun _ _ _ => rfl }

private def incl [DecidableEq I] (i : I) : O X ⟶ power X I where
  hom := { app := fun U => AddCommGrpCat.ofHom (AddMonoidHom.single (fun _ : I => Γ(X,U.unop)) i)
           naturality := by
             intro U V f
             apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext j
             let a : Γ(X,U.unop) := x
             let φ : Γ(X,U.unop) →+* Γ(X,V.unop) := (X.presheaf.map f).hom
             change Pi.single (M := fun _ : I => Γ(X,V.unop)) i (φ a) j =
               φ (Pi.single (M := fun _ : I => Γ(X,U.unop)) i a j)
             by_cases h : j = i
             · subst j; simp only [Pi.single_eq_same]
             · simp only [Pi.single_eq_of_ne h, map_zero] }

private theorem decomposition [Fintype I] [DecidableEq I] :
    ∑ i, proj X I i ≫ incl X I i = 𝟙 (power X I) := by
  apply (sheafToPresheaf _ _).map_injective
  rw [Functor.map_sum]
  apply NatTrans.ext; funext U
  rw [NatTrans.app_sum]
  apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext; intro x; funext j
  have hs (s : Finset I) :
      ((∑ i ∈ s, (proj X I i ≫ incl X I i).hom.app U) x) j =
        ∑ i ∈ s, Pi.single (M := fun _ : I => Γ(X,U.unop)) i (x i) j := by
    induction s using Finset.induction_on with
    | empty => simp only [Finset.sum_empty]; rfl
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, AddCommGrpCat.hom_add_apply]
      change Pi.single (M := fun _ : I => Γ(X,U.unop)) i (x i) j +
        ((∑ k ∈ s, (proj X I k ≫ incl X I k).hom.app U) x) j = _
      rw [ih]
  exact (hs Finset.univ).trans (Fintype.sum_pi_single (M := fun _ : I => Γ(X,U.unop)) j (fun i => x i))

variable {X}
attribute [local instance] HasExt.standard

private theorem O_vanish {W : X.Opens} (hW : IsAffineOpen W) (k : ℕ) :
    Subsingleton ((O X).H' (k+1) W) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of Γ(X,W)))).H (k+1)) :=
    CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton k Γ(X,W)
  exact (chartCohomologyEquiv (Opens.grothendieckTopology X) W
    (Opens.grothendieckTopology (Spec (CommRingCat.of Γ(X,W))))
    (CycleQ2GeometricAffineChartSections.chartOpensEquiv hW.isoSpec) ⊤ isTerminalTop
    (O X) (structureAdditiveSheaf (Spec (CommRingCat.of Γ(X,W))))
    (CycleQ2GeometricProjectiveHOne.chartStructureOverIso hW.isoSpec) (k+1)).injective.subsingleton

theorem power_vanishing [Fintype I] {W : X.Opens} (hW : IsAffineOpen W) (k : ℕ) :
    Subsingleton ((power X I).H' (k+1) W) := by
  classical
  let H := extFunctorObj (freeAbelianSheaf (Opens.grothendieckTopology X) W) (k+1)
  have hO : IsZero (H.obj (O X)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (O_vanish hW k)
  have h : IsZero (H.obj (power X I)) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    rw [← H.map_id, ← decomposition X I, H.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [H.map_comp, hO.eq_of_tgt (H.map (proj X I i)) 0, zero_comp]
  exact AddCommGrpCat.isZero_iff_subsingleton.mp h

theorem affine_vanishing [Fintype I] {W : X.Opens} (hW : IsAffineOpen W)
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (e : F.over W ≅ (power X I).over W) (k : ℕ) :
    Subsingleton (F.H' (k+1) W) := by
  let J := Opens.grothendieckTopology X
  let eqv := ((restrictionHEquiv J W F (k+1)).trans
    (((Sheaf.functorH (J.over W) (k+1)).mapIso e).addCommGroupIsoToAddEquiv)).trans
    (restrictionHEquiv J W (power X I) (k+1)).symm
  let := power_vanishing I hW k
  exact eqv.injective.subsingleton

end CycleQ2AffinePowerSheaf
end

namespace CycleQ2FramedOverDescent

open CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  (F : C ⥤ D) [F.Full] (J : GrothendieckTopology D) [F.IsCoverDense J] (W : C)

theorem coverDense : (Over.post (X := W) F).IsCoverDense (J.over (F.obj W)) where
  is_cover U := by
    rw [GrothendieckTopology.mem_over_iff]
    apply J.superset_covering _ (F.is_cover_of_isCoverDense J U.left)
    rintro T a ⟨⟨b,l,m,h⟩⟩
    rw [Sieve.overEquiv_iff]
    let q : b ⟶ W := F.preimage (m ≫ U.hom)
    have hq : F.map q = m ≫ U.hom := F.map_preimage _
    let B := Over.mk q
    let t : (Over.post F).obj B ⟶ U := Over.homMk m hq.symm
    let s : Over.mk (a ≫ U.hom) ⟶ (Over.post F).obj B :=
      Over.homMk l (by change l ≫ F.map q = a ≫ U.hom; rw [hq, ← Category.assoc, h])
    exact ⟨⟨B, s, t, Over.OverMorphism.ext h⟩⟩

variable [F.Faithful]
variable {A : Type*} [Category* A]
  {M N : Sheaf (J.over (F.obj W)) A}

/-- A sheaf isomorphism over a basis object determined by basis coordinates and restrictions. -/
def sheafIso (e : (Over.post (X := W) F).op ⋙ M.obj ≅ (Over.post (X := W) F).op ⋙ N.obj) :
    M ≅ N := by
  letI := coverDense F J W
  exact Functor.IsCoverDense.sheafIso e

end CycleQ2FramedOverDescent

section
namespace CycleQ2FramedOpenFormCoefficients
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2SmoothRelativeFrames CycleQ2IntrinsicFramedAffineSite
open CycleQ2IntrinsicDeRhamSheaves CycleQ2IntrinsicFramedAffineCoordinates
open CycleQ2RelativeAffineOverlap CycleQ2ExactFrameThreeDeRham
open CycleQ2WeightedCoordinateExterior
variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  (W : FramedOpen p r) (q : ℕ)

abbrev index := Set.powersetCard (Fin r) q

abbrev overBasis := Over.post (X := W) (inclusion p r)

abbrev basisFormsAt : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Over.forget W).op ⋙ forms p r q

abbrev powerOnBasis : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (overBasis p r W).op ⋙ ((CycleQ2AffinePowerSheaf.power X (index r q)).over W.1).obj

def basisCoefficients : basisFormsAt p r W q ≅ powerOnBasis p r W q := by
  refine NatIso.ofComponents (fun V => ?_) ?_
  · letI : Algebra k Γ(X,V.unop.left.1) := (sectionCoefficients p V.unop.left.1).toAlgebra
    exact AddEquiv.toAddCommGrpIso ((transported p r V.unop.hom).exteriorPower q).equivFun.toAddEquiv
  · intro V T a
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    funext i
    let : Algebra k Γ(X,V.unop.left.1) := (sectionCoefficients p V.unop.left.1).toAlgebra
    let : Algebra k Γ(X,T.unop.left.1) := (sectionCoefficients p T.unop.left.1).toAlgebra
    exact exteriorCoordinates_natural p r V.unop.hom a.unop.left q s i

/-- On a framed affine open the intrinsic exterior sheaf is a finite power of the
 structure sheaf. The coordinates here use restrictions of the frame on `W`. -/
def overIso : (sheafForms p r q).over W.1 ≅
    (CycleQ2AffinePowerSheaf.power X (index r q)).over W.1 := by
  letI : (inclusion p r).IsCoverDense (Opens.grothendieckTopology X) := cover_dense p r
  apply CycleQ2FramedOverDescent.sheafIso (inclusion p r) _ W
  exact Functor.isoWhiskerLeft (Over.forget W).op (onBasisIso p r q) ≪≫ basisCoefficients p r W q

attribute [local instance] HasExt.standard

theorem forms_acyclic (n : ℕ) : Subsingleton ((sheafForms p r q).H' (n+1) W.1) :=
  CycleQ2AffinePowerSheaf.affine_vanishing (index r q) W.2.1 (sheafForms p r q) (overIso p r W q) n

/-- All actual de Rham terms are acyclic for sections on the framed open. -/
theorem term_acyclic (m : ℤ) (n : ℕ) :
    Subsingleton (Ext.{1} (CycleQ2InjectiveCech.freeOpen W.1) ((relativeDeRhamInt p r).X m) (n+1)) := by
  let E := extFunctorObj (CycleQ2InjectiveCech.freeOpen W.1) (n+1)
  cases m with
  | ofNat q =>
    let e : (relativeDeRhamInt p r).X (q : ℤ) ≅ sheafForms p r q :=
      (relativeDeRham p r).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add _)
    let : Subsingleton (E.obj (sheafForms p r q)) := forms_acyclic p r W q n
    exact (E.mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton
  | negSucc q =>
    have hz : IsZero ((relativeDeRhamInt p r).X (Int.negSucc q)) :=
      (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) _
        (by intro a ha; change (0:ℤ) + a = Int.negSucc q at ha; omega)
    exact AddCommGrpCat.isZero_iff_subsingleton.mp (E.map_isZero hz)

end CycleQ2FramedOpenFormCoefficients
end
