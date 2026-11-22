import Proposal.GeometricAffineExteriorLocalization
import Proposal.GeometricFramedAffineAcyclicity

/-! On every affine open of a smooth scheme, intrinsic de Rham terms are the associated sheaves of their ordinary exterior modules. All their positive section cohomology vanishes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section

namespace CycleQ2AffineProjectivePositive
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech
open CycleQ2GeometricSheafCohomologyRestriction (terminalFreeSheafIso)
open CycleQ2AffineProjectiveHOne (associated X)
variable (A : Type) [CommRing A]
private abbrev freeTop := freeOpen (⊤ : (X A).Opens)
attribute [local instance] HasExt.standard
private def unitIso :
    (associated A).obj (ModuleCat.of A A) ≅
      CycleQ2GeometricAffineCohomology.additiveStructureSheaf A :=
  (SheafOfModules.toSheaf.{0} (X A).ringCatSheaf).mapIso (tildeSelf (R := CommRingCat.of A))

abbrev cohomology (n : ℕ) : ModuleCat.{0} A ⥤ AddCommGrpCat.{1} :=
  associated A ⋙ extFunctorObj (freeTop A) (n+1)

private theorem unit_acyclic (n : ℕ) :
    IsZero ((cohomology A n).obj (ModuleCat.of A A)) := by
  let G := CycleQ2GeometricAffineCohomology.additiveStructureSheaf A
  apply ((extFunctorObj (freeTop A) (n+1)).mapIso (unitIso A)).isZero_iff.mpr
  let J := Opens.grothendieckTopology (X A)
  let e := ((extFunctor (n+1)).mapIso (terminalFreeSheafIso J
    (⊤ : (X A).Opens) isTerminalTop).op).app G
  apply e.isZero_iff.mp
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr
    (CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton n A)

private theorem free_acyclic (n m : ℕ) :
    IsZero ((cohomology A n).obj (ModuleCat.of A (Fin m → A))) := by
  let H := cohomology A n
  let family : Fin m → ModuleCat A := fun _ => ModuleCat.of A A
  let : H.Additive := inferInstanceAs ((associated A ⋙ extFunctorObj (freeTop A) (n+1)).Additive)
  let cone : Fan family := Fan.mk (ModuleCat.of A (Fin m → A))
    (fun j => ModuleCat.ofHom (LinearMap.proj j))
  have limitCone : IsLimit cone :=
    { lift s := ModuleCat.ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom)
      fac s j := rfl
      uniq s t ht := ModuleCat.hom_ext (LinearMap.ext (fun x => funext (fun j =>
        DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (ht ⟨j⟩)) x))) }
  exact (isLimitOfPreserves H limitCone).isZero_pt
    ((Functor.isZero_iff _).mpr (fun _ => unit_acyclic A n))

/-- The additive sheaf of a finite projective module on an affine scheme
has zero positive-degree cohomology. -/
theorem module_acyclic (n : ℕ) (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    IsZero ((cohomology A n).obj (ModuleCat.of A M)) := by
  obtain ⟨m, p, hp⟩ := Module.Finite.exists_fin' A M
  obtain ⟨j, hj⟩ := Module.projective_lifting_property p (LinearMap.id (R := A) (M := M)) hp
  let q : ModuleCat.of A (Fin m → A) ⟶ ModuleCat.of A M := ModuleCat.ofHom p
  let s : ModuleCat.of A M ⟶ ModuleCat.of A (Fin m → A) := ModuleCat.ofHom j
  let H := cohomology A n
  have h : s ≫ q = 𝟙 _ := ModuleCat.hom_ext hj
  have hz : 𝟙 (H.obj (ModuleCat.of A M)) = H.map s ≫ H.map q :=
    (H.map_id _).symm.trans ((congrArg H.map h).symm.trans (H.map_comp s q))
  apply (IsZero.iff_id_eq_zero _).mpr
  refine hz.trans ?_
  rw [(free_acyclic A n m).eq_of_tgt (H.map s) 0, zero_comp]

end CycleQ2AffineProjectivePositive

namespace CycleQ2AffineExteriorForms
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericAffineKahlerLocalization (X p basic)
open CycleQ2ExteriorPrincipal (sheaf localAddIso localAddIso_natural)
open CycleQ2GenericAffineKahlerSheaf (basisAffine)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (onBasisIso sheafForms)
open CycleQ2NativeTraceRestrictions (formRestriction)
open CycleQ2RelativeOpenKahler (formIso restriction_natural affine_image sectionIso)
open CycleQ2RankOneOpenRestriction (onImage)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (baseChangeFrame baseChangeFrame_apply restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open scoped KaehlerDifferential
attribute [local instance] HasExt.standard

variable (k A : Type) [Field k] [CommRing A] [Algebra k A] (r : ℕ)

private abbrev Principal := {a : A // HasFrame (p k A) r (basic A a)}
private abbrev siteOpen (a : Principal k A r) : (X A).Opens := basic A a.1
private abbrev Site := InducedCategory ((X A).Opens) (siteOpen k A r)
private abbrev incl := inducedFunctor (siteOpen k A r)

private instance dense [SmoothOfRelativeDimension r (p k A)] :
    (incl k A r).IsCoverDense (Opens.grothendieckTopology (X A)) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).mpr
  rw [Opens.isBasis_iff_nbhd]
  intro W x hx
  obtain ⟨U,hU,hxU,hUW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis (p k A) r)) hx
  obtain ⟨_,⟨_,⟨a,rfl⟩,rfl⟩,hxa,haU⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  let a' : Principal k A r := ⟨a,hasFrame_of_affine_le (p k A) r haU hU.1 (basisAffine A a) hU.2⟩
  exact ⟨basic A a,⟨a',rfl⟩,hxa,haU.trans hUW⟩

variable [CharZero k] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k))
    (j : X A ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = p k A)
    [SmoothOfRelativeDimension r f]

private def frameImage (a : Site k A r) : FramedOpen f r := by
  let V := basic A a.1
  letI : Algebra k Γ(Y,j ''ᵁ V) := (sectionCoefficients f (j ''ᵁ V)).toAlgebra
  letI : Algebra k Γ(X A,V) := (sectionCoefficients (p k A) V).toAlgebra
  let e := (sectionIso f (p k A) j hj V).symm
  letI : Algebra Γ(X A,V) Γ(Y,j ''ᵁ V) := e.toRingHom.toAlgebra
  letI : IsScalarTower k Γ(X A,V) Γ(Y,j ''ᵁ V) := IsScalarTower.of_algHom e.toAlgHom
  letI : Algebra.Etale Γ(X A,V) Γ(Y,j ''ᵁ V) := (RingHom.Etale.of_bijective e.bijective).toAlgebra
  refine ⟨j ''ᵁ V,affine_image (j := j) (basisAffine A a.1),?_⟩
  obtain ⟨u,b,hb⟩ := a.2
  exact ⟨fun i => e (u i),baseChangeFrame b,baseChangeFrame_apply b u hb⟩


private def extAlgEquiv {L H : Type} [CommRing L] [CommRing H] [Algebra k L] [Algebra k H]
    (e : L ≃ₐ[k] H) (n : ℕ) : Form k L n ≃+ Form k H n where
  toFun := exteriorPullback e.toAlgHom n
  invFun := exteriorPullback e.symm.toAlgHom n
  left_inv w := by
    rw [← CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp,AlgEquiv.symm_comp,
      CycleQ2AffineDeRhamFunctorial.exteriorPullback_id]
  right_inv w := by
    rw [← CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp,AlgEquiv.comp_symm,
      CycleQ2AffineDeRhamFunctorial.exteriorPullback_id]
  map_add' := map_add _

variable (n : ℕ) [Algebra.Smooth k A]

private abbrev F := (onImage j).obj (sheafForms f r n)
private abbrev G := addSheaf (sheaf k A n)

private def component (a : Site k A r) :
    (F k A r f j n).obj.obj (op (basic A a.1)) ≃+ (G k A n).obj.obj (op (basic A a.1)) := by
  let V := basic A a.1
  letI : Algebra k Γ(Y,j ''ᵁ V) := (sectionCoefficients f (j ''ᵁ V)).toAlgebra
  letI : Algebra k Γ(X A,V) := (sectionCoefficients (p k A) V).toAlgebra
  exact ((onBasisIso f r n).app (op (frameImage k A r f j hj a))).addCommGroupIsoToAddEquiv.trans
    ((extAlgEquiv k (sectionIso f (p k A) j hj V) n).trans (localAddIso k A n a.1))

private theorem component_natural {a b : Site k A r} (h : b ⟶ a)
    (w : (F k A r f j n).obj.obj (op (basic A a.1))) :
    component k A r f j hj n b ((F k A r f j n).obj.map (homOfLE h.hom.le).op w) =
      (G k A n).obj.map (homOfLE h.hom.le).op (component k A r f j hj n a w) := by
  let e := (onBasisIso f r n).hom
  let ai := frameImage k A r f j hj a
  let bi := frameImage k A r f j hj b
  let m : bi ⟶ ai := homOfLE (j.image_mono h.hom.le)
  let : Algebra k Γ(Y,ai.1) := (sectionCoefficients f ai.1).toAlgebra
  let : Algebra k Γ(Y,bi.1) := (sectionCoefficients f bi.1).toAlgebra
  let : Algebra k Γ(X A,basic A a.1) := (sectionCoefficients (p k A) (basic A a.1)).toAlgebra
  let : Algebra k Γ(X A,basic A b.1) := (sectionCoefficients (p k A) (basic A b.1)).toAlgebra
  let : Algebra k Γ(Y,j ''ᵁ basic A a.1) := (sectionCoefficients f (j ''ᵁ basic A a.1)).toAlgebra
  let : Algebra k Γ(Y,j ''ᵁ basic A b.1) := (sectionCoefficients f (j ''ᵁ basic A b.1)).toAlgebra
  let i := sectionIso f (p k A) j hj (basic A a.1)
  let i' := sectionIso f (p k A) j hj (basic A b.1)
  have he := NatTrans.naturality_apply e m.op w
  change e.app (op bi) ((F k A r f j n).obj.map (homOfLE h.hom.le).op w) =
    exteriorPullback (restrict f m.le) n (e.app (op ai) w) at he
  change localAddIso k A n b.1 (exteriorPullback i'.toAlgHom n
      (e.app (op bi) ((F k A r f j n).obj.map (homOfLE h.hom.le).op w))) = _
  rw [he]
  have hs : i'.toAlgHom.comp (restrict f m.le) = (restrict (p k A) h.hom.le).comp i.toAlgHom := by
    apply AlgHom.ext
    intro t
    exact ConcreteCategory.congr_hom (j.appIso_hom_naturality (homOfLE h.hom.le).op) t
  have hr : exteriorPullback i'.toAlgHom n (exteriorPullback (restrict f m.le) n (e.app (op ai) w)) =
      exteriorPullback (restrict (p k A) h.hom.le) n (exteriorPullback i.toAlgHom n (e.app (op ai) w)) := by
    let z : Form k Γ(Y,ai.1) n := e.app (op ai) w
    exact (CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp (restrict f m.le) i'.toAlgHom n z).symm.trans
      ((congrArg (fun g : Γ(Y,ai.1) →ₐ[k] Γ(X A,basic A b.1) => exteriorPullback g n z) hs).trans
        (CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp i.toAlgHom (restrict (p k A) h.hom.le) n z))
  exact (congrArg (localAddIso k A n b.1) hr).trans (localAddIso_natural k A n h.hom.le _)

/-- The ambient sheaf in any de Rham degree restricts on a smooth affine
open to the associated sheaf of the corresponding exterior module. -/
def comparison [SmoothOfRelativeDimension r (p k A)] : F k A r f j n ≅ G k A n :=
  Functor.IsCoverDense.sheafIso (G := incl k A r) (K := Opens.grothendieckTopology (X A))
    (NatIso.ofComponents (fun a => (component k A r f j hj n a.unop).toAddCommGrpIso)
      (fun h => by ext w; exact component_natural k A r f j hj n h.unop w))

end CycleQ2AffineExteriorForms

namespace CycleQ2AffineExteriorComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RankOneOpenRestriction (onImage)
open CycleQ2GeometricSheafCohomologyRestriction (chartCohomologyEquiv terminalFreeSheafIso)
open CycleQ2GeometricAffineChartSections (chartOpensEquiv chartOpensEquiv_obj)
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms relativeDeRham relativeDeRhamInt)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open scoped KaehlerDifferential
attribute [local instance] HasExt.standard
variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r p]
  {U : X.Opens} (hU : IsAffineOpen U)

private abbrev Z := Spec (CommRingCat.of Γ(X,U))
private abbrev j := hU.fromSpec
private abbrev q := Spec.map (CommRingCat.ofHom (sectionCoefficients p U))

omit [CharZero k] in
include hU in
private theorem over_chart : j hU ≫ p = q p (U := U) :=
  CycleQ2IntegralCurveNormalization.fromSpec_over k p hU

omit [CharZero k] in
include hU in
private theorem smooth_chart : SmoothOfRelativeDimension r (q p (U := U)) := by
  rw [← over_chart p hU]
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 r (j hU) p

private def chartPush : AbSheaf (show TopCat from Z (X := X) (U := U)) ⥤
    Sheaf (((Opens.grothendieckTopology X)).over U) AddCommGrpCat.{0} :=
  (chartOpensEquiv hU.isoSpec).functor.sheafPushforwardContinuous AddCommGrpCat
    ((Opens.grothendieckTopology X).over U)
    (Opens.grothendieckTopology (Z (X := X) (U := U)))

private theorem chart_image (W : Over U) :
    j hU ''ᵁ (chartOpensEquiv hU.isoSpec).functor.obj W = W.left := by
  rw [chartOpensEquiv_obj, ← Scheme.Hom.comp_preimage,
    ← IsAffineOpen.fromSpec, Scheme.Hom.image_preimage_eq_opensRange_inf,
    hU.opensRange_fromSpec, inf_eq_right.mpr W.hom.le]

private def chartRestriction (D : AbSheaf (show TopCat from X)) :
    D.over U ≅ (chartPush hU).obj ((onImage (j hU)).obj D) := by
  let F := D
  refine ObjectProperty.isoMk _ (NatIso.ofComponents (fun W =>
    F.obj.mapIso (eqToIso (chart_image hU W.unop)).op) ?_)
  intro V W a
  change F.obj.map a.unop.left.op ≫ F.obj.map (eqToHom (chart_image hU W.unop)).op =
    F.obj.map (eqToHom (chart_image hU V.unop)).op ≫
      F.obj.map (((j hU).opensFunctor.map ((chartOpensEquiv hU.isoSpec).functor.map a.unop)).op)
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg F.obj.map (Subsingleton.elim _ _)


include hU in
/-- On an arbitrary affine open the intrinsic degree-a de Rham sheaf is acyclic
in every positive cohomological degree. -/
theorem forms_acyclic (a n : ℕ) : Subsingleton ((sheafForms p r a).H' (n+1) U) := by
  let : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  let T := (⊤ : (Z (X := X) (U := U)).Opens)
  let J := Opens.grothendieckTopology (Z (X := X) (U := U))
  let G := addSheaf (CycleQ2ExteriorPrincipal.sheaf k Γ(X,U) a)
  let : SmoothOfRelativeDimension r (q p (U := U)) := smooth_chart p r hU
  have hsm : Smooth (q p (U := U)) := SmoothOfRelativeDimension.smooth r _
  let : Algebra.Smooth k Γ(X,U) :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  let : Module.Projective Γ(X,U) (Form k Γ(X,U) a) := CycleQ2ProjectiveExteriorBaseChange.projective a
  have hz : IsZero (G.H' (n+1) T) := CycleQ2AffineProjectivePositive.module_acyclic Γ(X,U) n (Form k Γ(X,U) a)
  let : Subsingleton (G.H' (n+1) T) := AddCommGrpCat.isZero_iff_subsingleton.mp hz
  let e : G.H (n+1) ≃+ G.H' (n+1) T :=
    (((extFunctor (n+1)).mapIso (terminalFreeSheafIso J T isTerminalTop).op).app G).addCommGroupIsoToAddEquiv
  let : Subsingleton (G.H (n+1)) := e.injective.subsingleton
  let d := CycleQ2AffineExteriorForms.comparison k Γ(X,U) r p (j hU) (over_chart p hU) a
  exact (chartCohomologyEquiv (Opens.grothendieckTopology X) U J
    (chartOpensEquiv hU.isoSpec) T isTerminalTop (sheafForms p r a) G
    (chartRestriction hU (sheafForms p r a) ≪≫ (chartPush hU).mapIso d) (n+1)).injective.subsingleton

/-- The global sections of the actual ambient exterior sheaf on the specified
affine open are the ordinary exterior forms of its section algebra. -/
def forms_sections (a : ℕ) :
    letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
    (sheafForms p r a).obj.obj (op U) ≃+ Form k Γ(X,U) a := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  letI : SmoothOfRelativeDimension r (q p (U := U)) := smooth_chart p r hU
  have hsm : Smooth (q p (U := U)) := SmoothOfRelativeDimension.smooth r _
  letI : Algebra.Smooth k Γ(X,U) :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  let e := CycleQ2AffineExteriorForms.comparison k Γ(X,U) r p (j hU) (over_chart p hU) a
  let t := (((sheafToPresheaf (Opens.grothendieckTopology (Z (X := X) (U := U))) AddCommGrpCat).mapIso e).app
    (op (⊤ : (Z (X := X) (U := U)).Opens))).addCommGroupIsoToAddEquiv
  have hi : j hU ''ᵁ ⊤ = U := (j hU).image_top_eq_opensRange.trans hU.opensRange_fromSpec
  let toTop := ((sheafForms p r a).obj.mapIso (eqToIso hi).op).addCommGroupIsoToAddEquiv
  exact toTop.trans (t.trans (tilde.isoTop (R := CommRingCat.of Γ(X,U))
    (CycleQ2ExteriorPrincipal.M k Γ(X,U) a)).toLinearEquiv.toAddEquiv.symm)

include hU in
/-- Every degree of the actual integer-indexed de Rham complex is acyclic
for sections on any affine open. -/
theorem term_acyclic (m : ℤ) (n : ℕ) :
    Subsingleton (Ext.{1} (CycleQ2InjectiveCech.freeOpen U) ((relativeDeRhamInt p r).X m) (n+1)) := by
  let E := extFunctorObj (CycleQ2InjectiveCech.freeOpen U) (n+1)
  cases m with
  | ofNat a =>
    let e : (relativeDeRhamInt p r).X (a : ℤ) ≅ sheafForms p r a :=
      (relativeDeRham p r).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add _)
    let : Subsingleton (E.obj (sheafForms p r a)) := forms_acyclic p r hU a n
    exact (E.mapIso e).addCommGroupIsoToAddEquiv.injective.subsingleton
  | negSucc a =>
    have hz : IsZero ((relativeDeRhamInt p r).X (Int.negSucc a)) :=
      (relativeDeRham p r).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) _
        (by intro b hb; change (0:ℤ) + b = Int.negSucc a at hb; omega)
    exact AddCommGrpCat.isZero_iff_subsingleton.mp (E.map_isZero hz)

end CycleQ2AffineExteriorComparison

end

#print axioms CycleQ2AffineExteriorComparison.forms_sections
#print axioms CycleQ2AffineExteriorComparison.term_acyclic

/-! The literal exterior sheaves and the intrinsic affine de Rham sheaves
on the original fixed threefold. The comparison is built from the
canonical ordinary-to-sheaf map on the already constructed gradient
atlas; it does not choose a free cotangent frame on a larger affine open. -/

noncomputable section
namespace CycleQ2LiteralIntrinsicExterior

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralThreefoldSecondDifferential (FormModule ordinaryExteriorIso
  ordinaryExteriorIso_apply ordinaryExteriorIso_restrict)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2GeometricSectionDifferentials (sectionAlgebra SectionRing SectionForms
  sectionRestriction)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2OrdinaryExteriorSections (toExterior)
open CycleQ2ExteriorSectionNaturality (exteriorDifferentialMap)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms onBasisIso onBasisIso_d)
open CycleQ2WeightedCoordinateExterior (Form)

local instance : SmoothOfRelativeDimension 3 structural :=
  CycleQ2LiteralAmbientSmooth.literal_fiber_smooth

abbrev Literal (n : ℕ) := addSheaf (FormModule n)
abbrev Intrinsic (n : ℕ) := sheafForms structural 3 n

/-- Both constructions use the same original structural morphism to
define the scalar action on sections. -/
theorem coefficients_eq (W : X.Opens) :
    coefficientOn X.sheaf coeff W =
      CycleQ2SmoothRelativeFrames.sectionCoefficients structural W := rfl

def framed (V : FramedAffine) :
    CycleQ2IntrinsicFramedAffineSite.FramedOpen structural 3 :=
  ⟨V.carrier, V.affine, ⟨coordinates V, nativeFrame V, nativeFrame_apply V⟩⟩

private def component (n : ℕ) (V : FramedAffine) :
    (Intrinsic n).obj.obj (op V.carrier) ≃+
      (Literal n).obj.obj (op V.carrier) :=
  (((onBasisIso structural 3 n).app (op (framed V))).addCommGroupIsoToAddEquiv).trans
    (ordinaryExteriorIso V n).toAddEquiv

private theorem component_natural (n : ℕ) (V W : FramedAffine)
    (h : V.carrier ≤ W.carrier) (s : (Intrinsic n).obj.obj (op W.carrier)) :
    component n V ((Intrinsic n).obj.map (homOfLE h).op s) =
      (Literal n).obj.map (homOfLE h).op (component n W s) := by
  letI := sectionAlgebra X.sheaf coeff W.carrier
  letI := sectionAlgebra X.sheaf coeff V.carrier
  let a : framed V ⟶ framed W := homOfLE h
  have he := NatTrans.naturality_apply (onBasisIso structural 3 n).hom a.op s
  change (onBasisIso structural 3 n).hom.app (op (framed V))
      ((Intrinsic n).obj.map (homOfLE h).op s) =
    exteriorDifferentialMap (sectionRestriction X.sheaf coeff h) n
      ((onBasisIso structural 3 n).hom.app (op (framed W)) s) at he
  change ordinaryExteriorIso V n
      ((onBasisIso structural 3 n).hom.app (op (framed V))
        ((Intrinsic n).obj.map (homOfLE h).op s)) =
    (FormModule n).val.map (homOfLE h).op
      (ordinaryExteriorIso W n
        ((onBasisIso structural 3 n).hom.app (op (framed W)) s))
  apply (ordinaryExteriorIso V n).symm.injective
  rw [LinearEquiv.symm_apply_apply, ordinaryExteriorIso_restrict,
    LinearEquiv.symm_apply_apply]
  exact he

private def onAtlas (n : ℕ) :
    (inducedFunctor FramedAffine.carrier).op ⋙ (Intrinsic n).obj ≅
      (inducedFunctor FramedAffine.carrier).op ⋙ (Literal n).obj :=
  NatIso.ofComponents (fun V => (component n V.unop).toAddCommGrpIso) (by
    intro V W h
    apply ConcreteCategory.hom_ext
    intro s
    exact component_natural n W.unop V.unop h.unop.hom.le s)

private def toLiteral (n : ℕ) : Intrinsic n ⟶ Literal n where
  hom := TopCat.Sheaf.restrictHomEquivHom (Intrinsic n).obj (Literal n)
    framed_isBasis (onAtlas n).hom

private def fromLiteral (n : ℕ) : Literal n ⟶ Intrinsic n where
  hom := TopCat.Sheaf.restrictHomEquivHom (Literal n).obj (Intrinsic n)
    framed_isBasis (onAtlas n).inv

private theorem toLiteral_on (n : ℕ) (V : FramedAffine)
    (s : (Intrinsic n).obj.obj (op V.carrier)) :
    (toLiteral n).hom.app (op V.carrier) s = component n V s :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app
    (F := (Intrinsic n).obj) (F' := Literal n) framed_isBasis (onAtlas n).hom V) s

private theorem fromLiteral_on (n : ℕ) (V : FramedAffine)
    (s : (Literal n).obj.obj (op V.carrier)) :
    (fromLiteral n).hom.app (op V.carrier) s = (component n V).symm s :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app
    (F := (Literal n).obj) (F' := Intrinsic n) framed_isBasis (onAtlas n).inv V) s

/-- The literal exterior sheaf used by the marked test cochain is the
intrinsic exterior sheaf on the same fixed scheme. -/
def comparison (n : ℕ) : Intrinsic n ≅ Literal n where
  hom := toLiteral n
  inv := fromLiteral n
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ framed_isBasis
    intro V
    apply ConcreteCategory.hom_ext
    intro s
    change (fromLiteral n).hom.app (op V.carrier)
      ((toLiteral n).hom.app (op V.carrier) s) = s
    rw [toLiteral_on, fromLiteral_on, AddEquiv.symm_apply_apply]
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext
    apply TopCat.Sheaf.hom_ext _ _ framed_isBasis
    intro V
    apply ConcreteCategory.hom_ext
    intro s
    change (toLiteral n).hom.app (op V.carrier)
      ((fromLiteral n).hom.app (op V.carrier) s) = s
    rw [fromLiteral_on, toLiteral_on, AddEquiv.apply_symm_apply]

/-- On each original gradient subchart, the comparison is the canonical
ordinary exterior section map, including its normalization on wedges. -/
theorem comparison_native (n : ℕ) (V : FramedAffine)
    (ω : letI := sectionAlgebra X.sheaf coeff V.carrier
      Form ℂ (SectionRing X.sheaf V.carrier) n) :
    (comparison n).hom.hom.app (op V.carrier)
      ((onBasisIso structural 3 n).inv.app (op (framed V)) ω) =
        toExterior X.sheaf coeff V.carrier n ω := by
  rw [show (comparison n).hom = toLiteral n from rfl, toLiteral_on]
  change ordinaryExteriorIso V n
    ((onBasisIso structural 3 n).hom.app (op (framed V))
      ((onBasisIso structural 3 n).inv.app (op (framed V)) ω)) = _
  rw [Iso.inv_hom_id_apply]
  exact ordinaryExteriorIso_apply V n ω

/-- The same normalization holds on every intrinsic exact affine chart,
even when it was not chosen from the sixteen native gradient charts. -/
theorem comparison_framed (n : ℕ)
    (W : CycleQ2IntrinsicFramedAffineSite.FramedOpen structural 3)
    (ω : letI := sectionAlgebra X.sheaf coeff W.1
      Form ℂ (SectionRing X.sheaf W.1) n) :
    (comparison n).hom.hom.app (op W.1)
      ((onBasisIso structural 3 n).inv.app (op W) ω) =
        toExterior X.sheaf coeff W.1 n ω := by
  letI := sectionAlgebra X.sheaf coeff W.1
  let s := (onBasisIso structural 3 n).inv.app (op W) ω
  apply TopCat.Presheaf.IsSheaf.section_ext (Literal n).property
  intro x hx
  obtain ⟨V,hV,hxV,hVW⟩ := Opens.isBasis_iff_nbhd.mp framed_isBasis hx
  obtain ⟨V,rfl⟩ := hV
  letI := sectionAlgebra X.sheaf coeff V.carrier
  refine ⟨V.carrier,hVW,hxV,?_⟩
  let a : framed V ⟶ W := homOfLE hVW
  have hn := NatTrans.naturality_apply (onBasisIso structural 3 n).hom a.op s
  change (onBasisIso structural 3 n).hom.app (op (framed V))
      ((Intrinsic n).obj.map (homOfLE hVW).op s) =
    exteriorDifferentialMap (sectionRestriction X.sheaf coeff hVW) n
      ((onBasisIso structural 3 n).hom.app (op W)
        ((onBasisIso structural 3 n).inv.app (op W) ω)) at hn
  rw [Iso.inv_hom_id_apply] at hn
  have hs : (Intrinsic n).obj.map (homOfLE hVW).op s =
      (onBasisIso structural 3 n).inv.app (op (framed V))
        (exteriorDifferentialMap (sectionRestriction X.sheaf coeff hVW) n ω) := by
    apply (ConcreteCategory.bijective_of_isIso
      ((onBasisIso structural 3 n).hom.app (op (framed V)))).injective
    rw [Iso.inv_hom_id_apply]
    exact hn
  change (Literal n).obj.map (homOfLE hVW).op
      ((comparison n).hom.hom.app (op W.1) s) = _
  rw [← NatTrans.naturality_apply, hs, comparison_native,
    CycleQ2OrdinaryExteriorSections.toExterior_restrict]

section Differential

variable {A : Type} [CommRing A] [Algebra ℂ A]

/-- The general intrinsic exterior derivative and the original
three-dimensional derivative agree for any two exact frames. -/
theorem intrinsicD2_eq_literal
    (b c : Basis (Fin 3) A (KaehlerDifferential ℂ A))
    (u v : Fin 3 → A)
    (hu : ∀ j, b j = KaehlerDifferential.D ℂ A (u j))
    (hv : ∀ j, c j = KaehlerDifferential.D ℂ A (v j))
    (ω : Form ℂ A 2) :
    CycleQ2ArbitraryFrameDifferential.d b 2 ω =
      CycleQ2LiteralThreefoldCartan.exteriorD2 c ω := by
  change CycleQ2ArbitraryFrameDifferential.d b 2 ω =
    CycleQ2LiteralThreefoldExteriorDerivative.additive c ω
  rw [← (b.exteriorPower 2).sum_repr ω, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro J _
  let a := u ∘ Set.powersetCard.ofFinEmbEquiv.symm J
  have he : b.exteriorPower 2 J =
      exteriorPower.ιMulti A 2 (KaehlerDifferential.D ℂ A ∘ a) := by
    rw [exteriorPower.basis_apply, exteriorPower.ιMulti_family]
    apply congrArg (exteriorPower.ιMulti A 2)
    funext j
    exact hu _
  rw [he, CycleQ2FrameCanonicalDifferential.d_exact_symbol b u hu]
  have ha : KaehlerDifferential.D ℂ A ∘ a =
      ![KaehlerDifferential.D ℂ A (a 0), KaehlerDifferential.D ℂ A (a 1)] := by
    funext j
    fin_cases j <;> rfl
  rw [ha]
  exact (CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_exact_wedge
    c v hv _ (a 0) (a 1)).symm

end Differential

/-- The sheaf isomorphisms identify the original second differential,
not merely the underlying sheaves in degrees two and three. -/
theorem comparison_secondDifferential :
    (comparison 2).hom ≫ CycleQ2LiteralThreefoldSecondDifferential.secondDifferential =
      CycleQ2IntrinsicDeRhamSheaves.differential structural 3 2 ≫ (comparison 3).hom := by
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ _ framed_isBasis
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  letI := sectionAlgebra X.sheaf coeff V.carrier
  let W := framed V
  let ω := (onBasisIso structural 3 2).hom.app (op W) s
  have hd := ConcreteCategory.congr_hom (onBasisIso_d structural 3 2 W) s
  change (onBasisIso structural 3 3).hom.app (op W)
      ((CycleQ2IntrinsicDeRhamSheaves.differential structural 3 2).hom.app
        (op V.carrier) s) =
    CycleQ2ArbitraryFrameDifferential.d
      (CycleQ2IntrinsicFramedAffineSite.frame structural 3 W) 2 ω at hd
  change CycleQ2LiteralThreefoldSecondDifferential.secondDifferential.hom.app (op V.carrier)
      ((toLiteral 2).hom.app (op V.carrier) s) =
    (toLiteral 3).hom.app (op V.carrier)
      ((CycleQ2IntrinsicDeRhamSheaves.differential structural 3 2).hom.app
        (op V.carrier) s)
  rw [toLiteral_on, toLiteral_on,
    CycleQ2LiteralThreefoldSecondDifferential.secondDifferential_on]
  change toExterior X.sheaf coeff V.carrier 3
      (CycleQ2LiteralThreefoldCartan.exteriorD2 (nativeFrame V)
        ((ordinaryExteriorIso V 2).symm ((ordinaryExteriorIso V 2) ω))) =
    ordinaryExteriorIso V 3 ((onBasisIso structural 3 3).hom.app (op W)
      ((CycleQ2IntrinsicDeRhamSheaves.differential structural 3 2).hom.app
        (op V.carrier) s))
  rw [LinearEquiv.symm_apply_apply, hd, ordinaryExteriorIso_apply]
  apply congrArg (toExterior X.sheaf coeff V.carrier 3)
  exact (intrinsicD2_eq_literal
    (CycleQ2IntrinsicFramedAffineSite.frame structural 3 W) (nativeFrame V)
    (CycleQ2IntrinsicFramedAffineSite.functions structural 3 W) (coordinates V)
    (CycleQ2IntrinsicFramedAffineSite.frame_apply structural 3 W) (nativeFrame_apply V) ω).symm

/-- Sections of the actual literal exterior sheaf on every smooth
affine open are ordinary exterior forms of its section ring. -/
def affineSections {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff W
    (Literal n).obj.obj (op W) ≃+ Form ℂ (SectionRing X.sheaf W) n := by
  letI := sectionAlgebra X.sheaf coeff W
  let e := (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (comparison n).symm).app (op W)).addCommGroupIsoToAddEquiv
  exact e.trans (CycleQ2AffineExteriorComparison.forms_sections structural 3 hW n)

end CycleQ2LiteralIntrinsicExterior
end

#print axioms CycleQ2LiteralIntrinsicExterior.comparison
#print axioms CycleQ2LiteralIntrinsicExterior.comparison_native
#print axioms CycleQ2LiteralIntrinsicExterior.comparison_secondDifferential
#print axioms CycleQ2LiteralIntrinsicExterior.affineSections

/-! Canonical affine normalization.  The ordinary-to-intrinsic map is
defined before choosing an affine presentation.  Its comparison with
the associated exterior module is checked on the framed principal
basis, so the resulting affine bijectivity retains the actual wedge
section map. -/

noncomputable section

namespace CycleQ2IntrinsicOrdinaryExterior

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (inclusion FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms onBasisIso)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_id exteriorPullback_comp)
open CycleQ2FramedAffineSite (restrict_id restrict_comp)
open CycleQ2WeightedCoordinateExterior (Form)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of k)) (r n : ℕ)
  [SmoothOfRelativeDimension r f]

/-- The ordinary exterior powers on all opens, in every degree. -/
def forms : X.Opensᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj U :=
    letI : Algebra k Γ(X,U.unop) := (sectionCoefficients f U.unop).toAlgebra
    AddCommGrpCat.of (Form k Γ(X,U.unop) n)
  map {U V} h :=
    letI : Algebra k Γ(X,U.unop) := (sectionCoefficients f U.unop).toAlgebra
    letI : Algebra k Γ(X,V.unop) := (sectionCoefficients f V.unop).toAlgebra
    AddCommGrpCat.ofHom (exteriorPullback (restrict f h.unop.le) n).toAddMonoidHom
  map_id U := by
    letI : Algebra k Γ(X,U.unop) := (sectionCoefficients f U.unop).toAlgebra
    ext ω
    change exteriorPullback (restrict f (le_rfl : U.unop ≤ U.unop)) n ω = ω
    rw [restrict_id, exteriorPullback_id]
  map_comp {U V W} a b := by
    letI : Algebra k Γ(X,U.unop) := (sectionCoefficients f U.unop).toAlgebra
    letI : Algebra k Γ(X,V.unop) := (sectionCoefficients f V.unop).toAlgebra
    letI : Algebra k Γ(X,W.unop) := (sectionCoefficients f W.unop).toAlgebra
    ext ω
    change exteriorPullback (restrict f (b.unop.le.trans a.unop.le)) n ω =
      exteriorPullback (restrict f b.unop.le) n
        (exteriorPullback (restrict f a.unop.le) n ω)
    rw [restrict_comp]
    exact exteriorPullback_comp _ _ n ω

local instance : (inclusion f r).IsCoverDense (Opens.grothendieckTopology X) :=
  CycleQ2IntrinsicFramedAffineSite.cover_dense f r

/-- Ordinary exterior forms map canonically to the intrinsic sheaf by
the same ordinary forms on every exact affine frame. -/
def toSheaf : forms f n ⟶ (sheafForms f r n).obj :=
  Functor.IsCoverDense.sheafHom (G := inclusion f r)
    (K := Opens.grothendieckTopology X) (ℱ' := sheafForms f r n)
    (onBasisIso f r n).inv

theorem toSheaf_onBasis (V : FramedOpen f r)
    (ω : (forms f n).obj (op V.1)) :
    (toSheaf f r n).app (op V.1) ω =
      (onBasisIso f r n).inv.app (op V) ω := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (G := inclusion f r)
    (K := Opens.grothendieckTopology X) (ℱ' := sheafForms f r n)
    (onBasisIso f r n).inv
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) ω

end CycleQ2IntrinsicOrdinaryExterior

namespace CycleQ2ExteriorPrincipal

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericAffineKahlerLocalization (X p B fromAffine)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2WeightedCoordinateExterior (Form)

attribute [local instance] CycleQ2GenericAffineKahlerLocalization.sectionsAlgebra
  CycleQ2GenericAffineKahlerLocalization.coefficientsAlgebra

variable (k A : Type) [Field k] [CommRing A] [Algebra k A] (n : ℕ)

theorem fromRing_eq_pullback (U : (X A).Opens) (ω : Form k A n) :
    fromRing k A n U ω =
      exteriorPullback (IsScalarTower.toAlgHom k A (B A U)) n ω := by
  have h : CycleQ2ProjectiveExteriorBaseChange.semi (S := B A U)
      (fromAffine k A U) = onePullback (IsScalarTower.toAlgHom k A (B A U)) := by
    ext z
    exact (CycleQ2CotangentLocalizationTower.pullback_algebraMap z).symm
  change CycleQ2GeometricExteriorSheaf.exteriorMap (algebraMap A (B A U))
    (CycleQ2ProjectiveExteriorBaseChange.semi (S := B A U) (fromAffine k A U)) n ω = _
  rw [h]
  rfl

theorem fromRing_restrict {U V : (X A).Opens} (h : V ≤ U) (ω : Form k A n) :
    exteriorPullback (restrict (p k A) h) n (fromRing k A n U ω) =
      fromRing k A n V ω := by
  rw [fromRing_eq_pullback, fromRing_eq_pullback, ← exteriorPullback_comp]
  have he : (restrict (p k A) h).comp (IsScalarTower.toAlgHom k A (B A U)) =
      IsScalarTower.toAlgHom k A (B A V) := by
    ext a
    exact ConcreteCategory.congr_hom
      (StructureSheaf.algebraMap_self_map A (op V) (op U) (homOfLE h).op) a
  rw [he]

theorem fromRing_top_bijective : Function.Bijective (fromRing k A n ⊤) := by
  let e : A ≃ₐ[k] B A (⊤ : (X A).Opens) :=
    AlgEquiv.ofRingEquiv
      (f := (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv)
      (fun a => (CycleQ2GenericAffineKahlerLocalization.sectionCoefficients_affine
        k A ⊤ a).symm)
  have he : e.toAlgHom = IsScalarTower.toAlgHom k A (B A (⊤ : (X A).Opens)) := by
    ext a
    rfl
  let q := CycleQ2AffineExteriorForms.extAlgEquiv k e n
  have h : (fromRing k A n ⊤ : Form k A n → Form k (B A ⊤) n) = q := by
    funext ω
    rw [fromRing_eq_pullback, ← he]
    rfl
  rw [h]
  exact q.bijective

end CycleQ2ExteriorPrincipal

namespace CycleQ2AffineExteriorForms

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericAffineKahlerLocalization (X p basic B)
open CycleQ2ExteriorPrincipal (sheaf fromRing fromRing_restrict localAddIso)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms onBasisIso)
open CycleQ2RelativeOpenKahler (sectionIso)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2IntrinsicOrdinaryExterior (toSheaf toSheaf_onBasis)

variable (k A : Type) [Field k] [CommRing A] [Algebra k A] (r : ℕ)
  [CharZero k] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of k))
  (j : X A ⟶ Y) [IsOpenImmersion j] (hj : j ≫ f = p k A)
  [SmoothOfRelativeDimension r f] [SmoothOfRelativeDimension r (p k A)]
  (n : ℕ) [Algebra.Smooth k A]

private theorem comparison_onPrincipal (a : Site k A r)
    (ω : (F k A r f j n).obj.obj (op (basic A a.1))) :
    (comparison k A r f j hj n).hom.hom.app (op (basic A a.1)) ω =
      component k A r f j hj n a ω := by
  let e := NatIso.ofComponents
    (fun a : (Site k A r)ᵒᵖ => (component k A r f j hj n a.unop).toAddCommGrpIso)
    (fun h => by ext w; exact component_natural k A r f j hj n h.unop w)
  have h := Functor.IsCoverDense.sheafHom_restrict_eq (G := incl k A r)
    (K := Opens.grothendieckTopology (X A)) (ℱ' := G k A n) e.hom
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op a)) ω

private theorem principal_neighborhood (x : X A) :
    ∃ a : Site k A r, x ∈ basic A a.1 := by
  have hx : x ∈ (⊤ : (X A).Opens) := trivial
  have hb := (TopCat.Opens.coverDense_iff_isBasis (incl k A r)).mp (dense k A r)
  obtain ⟨U,⟨a,rfl⟩,hxU,_⟩ := Opens.isBasis_iff_nbhd.mp hb hx
  exact ⟨a,hxU⟩

private def rawOpenIso :
    j.opensFunctor.op ⋙ CycleQ2IntrinsicOrdinaryExterior.forms f n ≅
      CycleQ2IntrinsicOrdinaryExterior.forms (p k A) n :=
  NatIso.ofComponents (fun U =>
    letI : Algebra k Γ(Y,j ''ᵁ U.unop) := (sectionCoefficients f (j ''ᵁ U.unop)).toAlgebra
    letI : Algebra k Γ(X A,U.unop) := (sectionCoefficients (p k A) U.unop).toAlgebra
    (extAlgEquiv k (sectionIso f (p k A) j hj U.unop) n).toAddCommGrpIso) (by
      intro U V h
      letI : Algebra k Γ(Y,j ''ᵁ U.unop) := (sectionCoefficients f (j ''ᵁ U.unop)).toAlgebra
      letI : Algebra k Γ(Y,j ''ᵁ V.unop) := (sectionCoefficients f (j ''ᵁ V.unop)).toAlgebra
      letI : Algebra k Γ(X A,U.unop) := (sectionCoefficients (p k A) U.unop).toAlgebra
      letI : Algebra k Γ(X A,V.unop) := (sectionCoefficients (p k A) V.unop).toAlgebra
      ext ω
      change exteriorPullback (sectionIso f (p k A) j hj V.unop).toAlgHom n
          (exteriorPullback (restrict f (j.image_mono h.unop.le)) n ω) =
        exteriorPullback (restrict (p k A) h.unop.le) n
          (exteriorPullback (sectionIso f (p k A) j hj U.unop).toAlgHom n ω)
      rw [← exteriorPullback_comp, ← exteriorPullback_comp]
      have he : (sectionIso f (p k A) j hj V.unop).toAlgHom.comp
          (restrict f (j.image_mono h.unop.le)) =
          (restrict (p k A) h.unop.le).comp
            (sectionIso f (p k A) j hj U.unop).toAlgHom := by
        ext a
        exact ConcreteCategory.congr_hom (j.appIso_hom_naturality h) a
      rw [he])

private def rawMap : CycleQ2IntrinsicOrdinaryExterior.forms (p k A) n ⟶ (F k A r f j n).obj :=
  (rawOpenIso k A f j hj n).inv ≫
    Functor.whiskerLeft j.opensFunctor.op (toSheaf f r n)

private theorem top_comparison (ω : Form k A n) :
    (comparison k A r f j hj n).hom.hom.app (op ⊤)
      ((rawMap k A r f j hj n).app (op ⊤) (fromRing k A n ⊤ ω)) =
      tilde.toOpen (R := CommRingCat.of A) (CycleQ2ExteriorPrincipal.M k A n) ⊤ ω := by
  let a := (comparison k A r f j hj n).hom.hom
  let b := rawMap k A r f j hj n
  let z := fromRing k A n (⊤ : (X A).Opens) ω
  apply TopCat.Presheaf.IsSheaf.section_ext (G k A n).property
  intro x _
  obtain ⟨i,hi⟩ := principal_neighborhood k A r x
  let V : (X A).Opens := basic A i.1
  let h : V ≤ ⊤ := le_top
  refine ⟨V,h,hi,?_⟩
  have ha := NatTrans.naturality_apply a (homOfLE h).op (b.app (op ⊤) z)
  have hb := NatTrans.naturality_apply b (homOfLE h).op z
  change b.app (op V) (exteriorPullback (restrict (p k A) h) n z) =
    (F k A r f j n).obj.map (homOfLE h).op (b.app (op ⊤) z) at hb
  change (G k A n).obj.map (homOfLE h).op (a.app (op ⊤) (b.app (op ⊤) z)) =
    (G k A n).obj.map (homOfLE h).op
      (tilde.toOpen (R := CommRingCat.of A) (CycleQ2ExteriorPrincipal.M k A n) ⊤ ω)
  rw [← ha, ← hb, fromRing_restrict]
  rw [show (G k A n).obj.map (homOfLE h).op
      (tilde.toOpen (R := CommRingCat.of A) (CycleQ2ExteriorPrincipal.M k A n) ⊤ ω) =
      tilde.toOpen (R := CommRingCat.of A) (CycleQ2ExteriorPrincipal.M k A n) V ω from
    ConcreteCategory.congr_hom (tilde.toOpen_res (R := CommRingCat.of A)
      (CycleQ2ExteriorPrincipal.M k A n) ⊤ V (homOfLE h)) ω]
  let W := frameImage k A r f j hj i
  letI : Algebra k Γ(Y,W.1) := (sectionCoefficients f W.1).toAlgebra
  letI : Algebra k Γ(X A,V) := (sectionCoefficients (p k A) V).toAlgebra
  change (comparison k A r f j hj n).hom.hom.app (op V)
    ((toSheaf f r n).app (op W.1)
      ((extAlgEquiv k (sectionIso f (p k A) j hj V) n).symm
        (fromRing k A n V ω))) = _
  rw [toSheaf_onBasis f r n W, comparison_onPrincipal k A r f j hj n i]
  change localAddIso k A n i.1
    ((extAlgEquiv k (sectionIso f (p k A) j hj V) n)
      ((onBasisIso f r n).hom.app (op W)
        ((onBasisIso f r n).inv.app (op W)
          ((extAlgEquiv k (sectionIso f (p k A) j hj V) n).symm
            (fromRing k A n V ω))))) = _
  rw [Iso.inv_hom_id_apply, AddEquiv.apply_symm_apply]
  exact CycleQ2ExteriorPrincipal.localIso_fromRing k A n i.1 ω

theorem toSheaf_bijective_on_chart :
    Function.Bijective ((toSheaf f r n).app (op (j ''ᵁ ⊤))) := by
  let a := (comparison k A r f j hj n).hom.hom.app (op ⊤)
  let b := (rawMap k A r f j hj n).app (op ⊤)
  let d := fromRing k A n (⊤ : (X A).Opens)
  have h : Function.Bijective ((a ∘ b) ∘ d) := by
    change Function.Bijective (fun ω => a (b (d ω)))
    have he : (fun ω => a (b (d ω))) =
        fun ω => tilde.toOpen (R := CommRingCat.of A)
          (CycleQ2ExteriorPrincipal.M k A n) ⊤ ω := funext (top_comparison k A r f j hj n)
    rw [he]
    exact (tilde.isoTop (R := CommRingCat.of A)
      (CycleQ2ExteriorPrincipal.M k A n)).toLinearEquiv.bijective
  have hab := (Function.Bijective.of_comp_iff (a ∘ b)
    (CycleQ2ExteriorPrincipal.fromRing_top_bijective k A n)).mp h
  have hb := (Function.Bijective.of_comp_iff'
    (ConcreteCategory.bijective_of_isIso a) b).mp hab
  change Function.Bijective ((toSheaf f r n).app (op (j ''ᵁ ⊤)) ∘
    (rawOpenIso k A f j hj n).inv.app (op ⊤)) at hb
  exact (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso ((rawOpenIso k A f j hj n).inv.app (op ⊤)))).mp hb

end CycleQ2AffineExteriorForms

end

noncomputable section

namespace CycleQ2IntrinsicOrdinaryExterior

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2SmoothRelativeFrames (sectionCoefficients)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of k)) (r n : ℕ)
  [SmoothOfRelativeDimension r f]

/-- The canonical ordinary exterior section map is bijective on an
arbitrary affine open; no global free frame on that open is needed. -/
theorem toSheaf_bijective {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((toSheaf f r n).app (op U)) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients f U).toAlgebra
  let j := hU.fromSpec
  let q := CycleQ2GenericAffineKahlerLocalization.p k Γ(X,U)
  have hj : j ≫ f = q := CycleQ2IntegralCurveNormalization.fromSpec_over k f hU
  letI : SmoothOfRelativeDimension r q := by
    rw [← hj]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 r j f
  have hsm : Smooth q := SmoothOfRelativeDimension.smooth r q
  letI : Algebra.Smooth k Γ(X,U) :=
    RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hsm)
  have h := CycleQ2AffineExteriorForms.toSheaf_bijective_on_chart
    k Γ(X,U) r f j hj n
  have hi : j ''ᵁ ⊤ = U := j.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  exact (congrArg (fun W : X.Opens =>
    Function.Bijective ((toSheaf f r n).app (op W))) hi).mp h

end CycleQ2IntrinsicOrdinaryExterior

namespace CycleQ2LiteralIntrinsicExterior

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2GeometricSectionDifferentials (sectionAlgebra SectionRing)
open CycleQ2OrdinaryExteriorSections (toExterior toExterior_restrict)
open CycleQ2WeightedCoordinateExterior (Form)

local instance : SmoothOfRelativeDimension 3 structural :=
  CycleQ2LiteralAmbientSmooth.literal_fiber_smooth

private def ordinaryToLiteral (n : ℕ) :
    CycleQ2IntrinsicOrdinaryExterior.forms structural n ⟶ (Literal n).obj where
  app U := AddCommGrpCat.ofHom (toExterior X.sheaf coeff U.unop n).toAddMonoidHom
  naturality U V h := by
    ext ω
    exact (toExterior_restrict X.sheaf coeff h.unop.le n ω).symm

private theorem ordinary_comparison (n : ℕ) :
    CycleQ2IntrinsicOrdinaryExterior.toSheaf structural 3 n ≫ (comparison n).hom.hom =
      ordinaryToLiteral n := by
  let J := CycleQ2IntrinsicFramedAffineSite.inclusion structural 3
  letI : J.IsCoverDense (Opens.grothendieckTopology X) :=
    CycleQ2IntrinsicFramedAffineSite.cover_dense structural 3
  apply (Functor.IsCoverDense.restrictHomEquivHom (G := J)
    (K := Opens.grothendieckTopology X) (ℱ' := Literal n)).symm.injective
  ext V ω
  change (comparison n).hom.hom.app (op V.unop.1)
    ((CycleQ2IntrinsicOrdinaryExterior.toSheaf structural 3 n).app (op V.unop.1) ω) = _
  rw [CycleQ2IntrinsicOrdinaryExterior.toSheaf_onBasis]
  exact comparison_framed n V.unop ω

/-- On every actual affine open of the fixed threefold, the canonical
wedge-section map is bijective. -/
theorem toExterior_bijective {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ) :
    Function.Bijective (toExterior X.sheaf coeff W n) := by
  have h := (ConcreteCategory.bijective_of_isIso
    ((comparison n).hom.hom.app (op W))).comp
      (CycleQ2IntrinsicOrdinaryExterior.toSheaf_bijective structural 3 n hW)
  have he := NatTrans.congr_app (ordinary_comparison n) (op W)
  change Function.Bijective
    ((CycleQ2IntrinsicOrdinaryExterior.toSheaf structural 3 n).app (op W) ≫
      (comparison n).hom.hom.app (op W)) at h
  rw [he] at h
  exact h

/-- This affine equivalence has the canonical ordinary section map as
its forward map, so restrictions and exact-wedge formulas are retained. -/
def canonicalAffineSections {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff W
    Form ℂ (SectionRing X.sheaf W) n ≃ₗ[SectionRing X.sheaf W]
      (Literal n).obj.obj (op W) := by
  letI := sectionAlgebra X.sheaf coeff W
  exact LinearEquiv.ofBijective (toExterior X.sheaf coeff W n)
    (toExterior_bijective hW n)

theorem canonicalAffineSections_apply {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ)
    (ω : letI := sectionAlgebra X.sheaf coeff W
      Form ℂ (SectionRing X.sheaf W) n) :
    canonicalAffineSections hW n ω = toExterior X.sheaf coeff W n ω := rfl

/-- Ordinary pullback preserves the displayed exact wedge, including
the order of all factors. -/
theorem pullback_exact_wedge {A B : Type} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (φ : A →ₐ[ℂ] B) (n : ℕ) (a : Fin n → A) :
    CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap φ n
      (exteriorPower.ιMulti A n (KaehlerDifferential.D ℂ A ∘ a)) =
      exteriorPower.ιMulti B n (KaehlerDifferential.D ℂ B ∘ (φ ∘ a)) := by
  rw [CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap_wedge]
  apply congrArg (exteriorPower.ιMulti B n)
  funext j
  exact CycleQ2GeometricAffineOverlap.differentialMap_D φ (a j)

/-- The original sheaf differential has its exact-wedge formula on any
open, without choosing a cotangent basis on that open. -/
theorem secondDifferential_exact_wedge (W : X.Opens) (a b c : Γ(X,W)) :
    letI := sectionAlgebra X.sheaf coeff W
    CycleQ2LiteralThreefoldSecondDifferential.secondDifferential.hom.app (op W)
      (toExterior X.sheaf coeff W 2
        (a • exteriorPower.ιMulti Γ(X,W) 2
          ![KaehlerDifferential.D ℂ Γ(X,W) b, KaehlerDifferential.D ℂ Γ(X,W) c])) =
      toExterior X.sheaf coeff W 3
        (exteriorPower.ιMulti Γ(X,W) 3
          ![KaehlerDifferential.D ℂ Γ(X,W) a, KaehlerDifferential.D ℂ Γ(X,W) b,
            KaehlerDifferential.D ℂ Γ(X,W) c]) := by
  letI := sectionAlgebra X.sheaf coeff W
  let δ := CycleQ2LiteralThreefoldSecondDifferential.secondDifferential
  apply TopCat.Presheaf.IsSheaf.section_ext (Literal 3).property
  intro x hx
  obtain ⟨V,⟨V,rfl⟩,hxV,hVW⟩ := Opens.isBasis_iff_nbhd.mp framed_isBasis hx
  letI := sectionAlgebra X.sheaf coeff V.carrier
  let φ := CycleQ2GeometricSectionDifferentials.sectionRestriction X.sheaf coeff hVW
  refine ⟨V.carrier,hVW,hxV,?_⟩
  rw [← δ.hom.naturality_apply, toExterior_restrict, toExterior_restrict,
    CycleQ2LiteralThreefoldSecondDifferential.secondDifferential_on]
  change toExterior X.sheaf coeff V.carrier 3
    (CycleQ2LiteralThreefoldCartan.exteriorD2 (nativeFrame V)
      ((CycleQ2LiteralThreefoldSecondDifferential.ordinaryExteriorIso V 2).symm
        ((CycleQ2LiteralThreefoldSecondDifferential.ordinaryExteriorIso V 2)
          (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap φ 2
            (a • exteriorPower.ιMulti Γ(X,W) 2
              ![KaehlerDifferential.D ℂ Γ(X,W) b, KaehlerDifferential.D ℂ Γ(X,W) c]))))) =
    toExterior X.sheaf coeff V.carrier 3
      (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap φ 3
        (exteriorPower.ιMulti Γ(X,W) 3
          ![KaehlerDifferential.D ℂ Γ(X,W) a, KaehlerDifferential.D ℂ Γ(X,W) b,
            KaehlerDifferential.D ℂ Γ(X,W) c]))
  rw [LinearEquiv.symm_apply_apply, map_smulₛₗ]
  have h2 : CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap φ 2
      (exteriorPower.ιMulti Γ(X,W) 2
        ![KaehlerDifferential.D ℂ Γ(X,W) b, KaehlerDifferential.D ℂ Γ(X,W) c]) =
      exteriorPower.ιMulti Γ(X,V.carrier) 2
        ![KaehlerDifferential.D ℂ Γ(X,V.carrier) (φ b),
          KaehlerDifferential.D ℂ Γ(X,V.carrier) (φ c)] := by
    rw [CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap_wedge]
    congr 1
    funext j
    fin_cases j <;> apply CycleQ2GeometricAffineOverlap.differentialMap_D
  have h3 : CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap φ 3
      (exteriorPower.ιMulti Γ(X,W) 3
        ![KaehlerDifferential.D ℂ Γ(X,W) a, KaehlerDifferential.D ℂ Γ(X,W) b,
          KaehlerDifferential.D ℂ Γ(X,W) c]) =
      exteriorPower.ιMulti Γ(X,V.carrier) 3
        ![KaehlerDifferential.D ℂ Γ(X,V.carrier) (φ a),
          KaehlerDifferential.D ℂ Γ(X,V.carrier) (φ b),
          KaehlerDifferential.D ℂ Γ(X,V.carrier) (φ c)] := by
    rw [CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap_wedge]
    congr 1
    funext j
    fin_cases j <;> apply CycleQ2GeometricAffineOverlap.differentialMap_D
  rw [h2, h3,
    CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_exact_wedge
      (nativeFrame V) (coordinates V) (nativeFrame_apply V)]

end CycleQ2LiteralIntrinsicExterior

end

#print axioms CycleQ2IntrinsicOrdinaryExterior.toSheaf_bijective
#print axioms CycleQ2LiteralIntrinsicExterior.canonicalAffineSections
