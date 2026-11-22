import Proposal.GeometricAffineExteriorLocalization
import Proposal.GeometricFramedAffineAcyclicity
import Proposal.GeometricSupportedClassNonvanishing

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

/-! Ordinary forms on the actual four-open torus.  The coefficient
equivalence below is the original scheme-section pullback followed by
the original cubic localization, with its complex algebra structure
verified on the native chart coefficients. -/

noncomputable section
namespace CycleQ2LiteralTorusOrdinaryForms

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2LiteralThreefoldFirstDifferential (X structural coeff)
open CycleQ2LiteralThreefoldTopTrace (Face Torus faceSectionEquiv face_affine)
open CycleQ2LiteralThreefoldCubicSectionComparison (toCubicSections
  toCubicSections_chartAlgebraMap)
open CycleQ2LiteralThreefoldCubicCoordinates (LocalCubic localizedMap)
open CycleQ2HodgeTwistLocalization (inverted)
open CycleQ2GeometricSectionDifferentials (sectionAlgebra)
open CycleQ2LiteralIntrinsicExterior (Literal canonicalAffineSections toExterior_bijective)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExteriorSectionNaturality (exteriorDifferentialMap)
open CycleQ2OrdinaryExteriorSections (toExterior)

/-- The actual section equivalence is complex-linear because its
commuting square is already proved on the original affine chart. -/
def sectionEquiv (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) :
    letI := sectionAlgebra X.sheaf coeff (Face S)
    Γ(X,Face S) ≃ₐ[ℂ] LocalCubic i (inverted i S) := by
  letI := sectionAlgebra X.sheaf coeff (Face S)
  refine AlgEquiv.ofRingEquiv
    (f := (faceSectionEquiv S).trans (toCubicSections i S hi)) ?_
  intro a
  change toCubicSections i S hi (faceSectionEquiv S
    (algebraMap ℂ Γ(X,Face S) a)) = algebraMap ℂ (LocalCubic i (inverted i S)) a
  simpa only [AlgHom.commutes] using
    toCubicSections_chartAlgebraMap i S hi
      (algebraMap ℂ (CycleQ2LiteralAbelJacobiContraction.T i) a)

theorem sectionEquiv_chart (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)
    (a : CycleQ2LiteralAbelJacobiContraction.T i) :
    sectionEquiv i S hi
      (CycleQ2LiteralThreefoldHodgeCech.chartAlgebraMap i (Face S) (Finset.inf_le hi) a) =
        localizedMap i (inverted i S) a :=
  toCubicSections_chartAlgebraMap i S hi a

abbrev Cubic := LocalCubic 0 (inverted 0 Finset.univ)
abbrev nativeMap := localizedMap 0 (inverted 0 Finset.univ)

private theorem torus_affine : IsAffineOpen Torus := face_affine Finset.univ (by simp)

local instance : Algebra ℂ Γ(X,Torus) := sectionAlgebra X.sheaf coeff Torus

def torusEquiv : Γ(X,Torus) ≃ₐ[ℂ] Cubic := sectionEquiv 0 Finset.univ (Finset.mem_univ 0)

/-- Every ordinary form on the cubic localization is realized as an
actual exterior sheaf section, and every such section is obtained. -/
def realize (n : ℕ) : Form ℂ Cubic n ≃+ (Literal n).obj.obj (op Torus) :=
  (CycleQ2AffineExteriorForms.extAlgEquiv ℂ torusEquiv.symm n).trans
    (canonicalAffineSections torus_affine n).toAddEquiv

theorem realize_apply (n : ℕ) (ω : Form ℂ Cubic n) :
    realize n ω = toExterior X.sheaf coeff Torus n
      (exteriorDifferentialMap torusEquiv.symm.toAlgHom n ω) := rfl

theorem realize_smul (n : ℕ) (a : Cubic) (ω : Form ℂ Cubic n) :
    realize n (a • ω) = torusEquiv.symm a • realize n ω := by
  rw [realize_apply, map_smulₛₗ, map_smul, realize_apply]

private theorem native_coefficient_map : torusEquiv.symm.toAlgHom.comp nativeMap =
    CycleQ2LiteralThreefoldHodgeCech.chartAlgebraMap 0 Torus
      (Finset.inf_le (Finset.mem_univ 0)) := by
  ext a
  apply torusEquiv.injective
  rw [AlgHom.comp_apply, AlgEquiv.apply_symm_apply]
  exact (sectionEquiv_chart 0 Finset.univ (Finset.mem_univ 0) a).symm

/-- The realization of an original affine chart form is its actual
chart section; this fixes the coefficient and orientation normalization. -/
theorem realize_native (n : ℕ)
    (ω : Form ℂ (CycleQ2LiteralAbelJacobiContraction.T 0) n) :
    realize n (exteriorDifferentialMap nativeMap n ω) =
      CycleQ2ExteriorSectionNaturality.chartExteriorSheafSection
        (CycleQ2LiteralAmbientCharts.fixedChart 0).symm structural
        (by simpa only [Iso.symm_inv, ← Category.assoc,
          CycleQ2LiteralAmbientCharts.chartInclusion] using
            CycleQ2LiteralAmbientCharts.chartInclusion_overComplex 0)
        n (Over.mk (homOfLE (Finset.inf_le (Finset.mem_univ 0)))) ω := by
  rw [realize_apply]
  change toExterior X.sheaf coeff Torus n
    (CycleQ2ExactFrameThreeDeRham.exteriorPullback torusEquiv.symm.toAlgHom n
      (CycleQ2ExactFrameThreeDeRham.exteriorPullback nativeMap n ω)) = _
  rw [← CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp, native_coefficient_map]
  exact CycleQ2ChartExteriorBinding.exteriorSectionLift_differentialMap
    X.sheaf coeff CycleQ2LiteralThreefoldFirstDifferential.OneModule
    (CycleQ2GeometricDifferentialSheaf.universalDifferential X.sheaf coeff) Torus
    _ _ (RingHom.id _) (fun _ => rfl)
    (CycleQ2LiteralThreefoldHodgeCech.chartAlgebraMap 0 Torus
      (Finset.inf_le (Finset.mem_univ 0))) (fun _ => rfl) n ω

/-- Exact two-wedges on the original localized cubic are differentiated
by the original sheaf differential. -/
theorem realize_d_pair (a b c : Cubic) :
    CycleQ2LiteralThreefoldSecondDifferential.secondDifferential.hom.app (op Torus)
      (realize 2 (a • exteriorPower.ιMulti Cubic 2
        ![KaehlerDifferential.D ℂ Cubic b, KaehlerDifferential.D ℂ Cubic c])) =
      realize 3 (exteriorPower.ιMulti Cubic 3
        ![KaehlerDifferential.D ℂ Cubic a, KaehlerDifferential.D ℂ Cubic b,
          KaehlerDifferential.D ℂ Cubic c]) := by
  let φ := torusEquiv.symm.toAlgHom
  have hpair : exteriorDifferentialMap φ 2
      (exteriorPower.ιMulti Cubic 2
        ![KaehlerDifferential.D ℂ Cubic b, KaehlerDifferential.D ℂ Cubic c]) =
      exteriorPower.ιMulti Γ(X,Torus) 2
        ![KaehlerDifferential.D ℂ Γ(X,Torus) (φ b),
          KaehlerDifferential.D ℂ Γ(X,Torus) (φ c)] := by
    rw [CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap_wedge]
    congr 1
    funext j
    fin_cases j <;> apply CycleQ2GeometricAffineOverlap.differentialMap_D
  have htriple : exteriorDifferentialMap φ 3
      (exteriorPower.ιMulti Cubic 3
        ![KaehlerDifferential.D ℂ Cubic a, KaehlerDifferential.D ℂ Cubic b,
          KaehlerDifferential.D ℂ Cubic c]) =
      exteriorPower.ιMulti Γ(X,Torus) 3
        ![KaehlerDifferential.D ℂ Γ(X,Torus) (φ a),
          KaehlerDifferential.D ℂ Γ(X,Torus) (φ b),
          KaehlerDifferential.D ℂ Γ(X,Torus) (φ c)] := by
    rw [CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap_wedge]
    congr 1
    funext j
    fin_cases j <;> apply CycleQ2GeometricAffineOverlap.differentialMap_D
  rw [realize_apply, realize_apply, map_smulₛₗ, hpair, htriple]
  exact CycleQ2LiteralIntrinsicExterior.secondDifferential_exact_wedge Torus (φ a) (φ b) (φ c)

end CycleQ2LiteralTorusOrdinaryForms
end

#print axioms CycleQ2LiteralTorusOrdinaryForms.sectionEquiv_chart
#print axioms CycleQ2LiteralTorusOrdinaryForms.realize_native
#print axioms CycleQ2LiteralTorusOrdinaryForms.realize_d_pair

noncomputable section
namespace CycleQ2LiteralTorusOrdinaryForms

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2LiteralThreefoldFirstDifferential (X structural coeff)
open CycleQ2LiteralThreefoldTopTrace (Torus faceSectionEquiv)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literal_vertex_unit)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen)
open CycleQ2HodgeTwistCech (sections negativeExponent)
open CycleQ2HodgeTwistLocalization (inverted intersectionCoordinates localizationOffset)
open CycleQ2HodgeTwistDehom (chartCoordinates exponentEquiv)
open CycleQ2HodgeTwistCubicFaces (structureCoordinates)
open CycleQ2LiteralThreefoldCubicSectionComparison (toCubicSections)
open CycleQ2LiteralThreefoldCanonicalFrame (canonicalIso)
open CycleQ2LiteralThreefoldChartVolume (chartVolume)
open CycleQ2LiteralThreefoldChartVolumeFrame (chartVolumeEquiv)
open CycleQ2ExteriorSectionNaturality (exteriorDifferentialMap)
open CycleQ2GeometricSectionDifferentials (sectionAlgebra)

local instance : Algebra ℂ Γ(X,Torus) := sectionAlgebra X.sheaf coeff Torus

private theorem intersection_top_coefficient (p : sections ℂ 0 Finset.univ) :
    (CycleQ2SeedCechLocalization.localizationToLaurent ℂ (inverted 0 Finset.univ)
      (intersectionCoordinates ℂ 0 Finset.univ 0 (Finset.mem_univ 0) p 2)).coeff
        (fun _ => -1) = p.val 2 negativeExponent := by
  let e : {e : CycleQ2HodgeTwistCech.Exp //
      CycleQ2HodgeTwistCech.Allowed 0 Finset.univ 2 e} := ⟨negativeExponent, by decide⟩
  let d := exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0) e
  have h := DFunLike.congr_fun
    ((localizationOffset ℂ 0 Finset.univ).apply_symm_apply
      (chartCoordinates 0 0 Finset.univ (Finset.mem_univ 0) p 2)) d
  change (CycleQ2SeedCechLocalization.localizationToLaurent ℂ (inverted 0 Finset.univ)
      (intersectionCoordinates ℂ 0 Finset.univ 0 (Finset.mem_univ 0) p 2)).coeff
        (fun _ => -1) =
    (chartCoordinates 0 0 Finset.univ (Finset.mem_univ 0) p 2) d at h
  refine h.trans ?_
  change Finsupp.equivMapDomain
    (exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0))
    ((p.val 2).subtypeDomain (CycleQ2HodgeTwistCech.Allowed 0 Finset.univ 2))
    (exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0) e) = _
  rw [Finsupp.equivMapDomain_apply, Equiv.symm_apply_apply]
  rfl

/-- The actual structure-sheaf trace reads the ordinary all-minus-one
coefficient of the original cubic power coordinate. -/
theorem structure_trace_cubic
    (s : Γ(threefold literalEval, Finset.univ.inf (coordinateOpen literalEval))) :
    CycleQ2HodgeTwistTorusChart.structureTopSectionTrace literalEval literal_vertex_unit s =
      CycleQ2TorusCubicTrace.residueTrace literalEval 0 literal_vertex_unit
        (inverted 0 Finset.univ) (toCubicSections 0 Finset.univ (Finset.mem_univ 0) s) := by
  let E := intersectionCoordinates ℂ 0 Finset.univ 0 (Finset.mem_univ 0)
  let b := CycleQ2GeometricHodgeThreefoldCubic.localizedBasis
    literalEval 0 literal_vertex_unit
    (Submonoid.powers (CycleQ2SeedCechLocalization.baseProduct ℂ (inverted 0 Finset.univ)))
  let x := toCubicSections 0 Finset.univ (Finset.mem_univ 0) s
  let p := E.symm (b.equivFun x)
  have hp : CycleQ2HodgeTwistCoordinates.read
      (CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit)
      (CycleQ2HodgeTwistAnchor.torus_le_face literalEval Finset.univ) s = p.val := by
    rw [CycleQ2HodgeTwistTorusChart.read_structure_face
      literalEval literal_vertex_unit 0 Finset.univ (Finset.mem_univ 0)]
    change (structureCoordinates literalEval 0 literal_vertex_unit Finset.univ
      (Finset.mem_univ 0) 0
      (CycleQ2GeometricProjectiveCurve.Twisted.resEquiv (threefold literalEval).sheaf
        (CycleQ2HodgeTwistFaces.face_inf literalEval 0 Finset.univ (Finset.mem_univ 0)).le
        (CycleQ2HodgeTwistFaces.face_inf literalEval 0 Finset.univ (Finset.mem_univ 0)).ge
        ((CycleQ2HodgeThreefoldTwist.chartFrame literalEval 0 0 _
          (Finset.inf_le (Finset.mem_univ 0)))
          ((CycleQ2HodgeThreefoldTwist.chartFrame literalEval 0 0 _
            (Finset.inf_le (Finset.mem_univ 0))).symm s)))).val = p.val
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hc := intersection_top_coefficient p
  change (CycleQ2SeedCechLocalization.localizationToLaurent ℂ (inverted 0 Finset.univ)
    (E (E.symm (b.equivFun x)) 2)).coeff (fun _ => -1) = p.val 2 negativeExponent at hc
  rw [AddEquiv.apply_symm_apply] at hc
  change (CycleQ2HodgeTwistCoordinates.read
      (CycleQ2HodgeTwistTorusChart.structureChart literalEval literal_vertex_unit)
      (CycleQ2HodgeTwistAnchor.torus_le_face literalEval Finset.univ) s) 2 negativeExponent =
    (CycleQ2SeedCechLocalization.localizationToLaurent ℂ (inverted 0 Finset.univ)
      (b.equivFun x 2)).coeff (fun _ => -1)
  rw [hp]
  exact hc.symm

abbrev volume : CycleQ2WeightedCoordinateExterior.Form ℂ Cubic 3 :=
  exteriorDifferentialMap nativeMap 3 (chartVolume 0)

private theorem realize_volume_coefficient :
    canonicalIso.hom.val.app (op Torus) (realize 3 volume) = 1 := by
  rw [realize_native, CycleQ2LiteralThreefoldCanonicalFrame.canonicalIso_hom_native]
  have hv : (chartVolumeEquiv 0).symm (chartVolume 0) = 1 := by
    apply (chartVolumeEquiv 0).injective
    rw [LinearEquiv.apply_symm_apply]
    change chartVolume 0 = (1 : CycleQ2LiteralAbelJacobiContraction.T 0) • chartVolume 0
    rw [one_smul]
  simp only [Fin.val_zero, pow_zero, one_mul, hv, map_one]

/-- The canonical-form trace is exactly the scalar cubic residue trace
in the original affine volume, with the zeroth-chart orientation. -/
theorem canonical_trace_realize_volume (a : Cubic) :
    CycleQ2LiteralThreefoldTopTrace.canonicalSectionTrace (realize 3 (a • volume)) =
      CycleQ2TorusCubicTrace.residueTrace literalEval 0 literal_vertex_unit
        (inverted 0 Finset.univ) a := by
  rw [CycleQ2LiteralThreefoldTopTrace.canonicalSectionTrace_coefficient,
    realize_smul, map_smul, realize_volume_coefficient, smul_eq_mul, mul_one,
    structure_trace_cubic]
  change CycleQ2TorusCubicTrace.residueTrace literalEval 0 literal_vertex_unit
    (inverted 0 Finset.univ) (torusEquiv (torusEquiv.symm a)) = _
  rw [AlgEquiv.apply_symm_apply]

end CycleQ2LiteralTorusOrdinaryForms
end

#print axioms CycleQ2LiteralTorusOrdinaryForms.structure_trace_cubic
#print axioms CycleQ2LiteralTorusOrdinaryForms.canonical_trace_realize_volume

/-! The genuine canonical section trace annihilates the exterior
derivative of every actual two-form section on the four-open torus. -/

noncomputable section
namespace CycleQ2LiteralTorusOrdinaryForms

open CategoryTheory Opposite
open CycleQ2LiteralThreefoldTopTrace (Torus canonicalSectionTrace)
open CycleQ2LiteralThreefoldSecondDifferential (secondDifferential)
open CycleQ2LiteralThreefoldCubicCoordinates
open CycleQ2LiteralThreefoldResidueMinors (coord)
open CycleQ2LiteralThreefoldTorusForms (pairLeft pairRight)
open CycleQ2HodgeTwistLocalization (inverted)
open CycleQ2CubicCoefficientTrace (normal)

theorem canonical_trace_d_coordinatePair (a : Cubic) (p : Fin 6) :
    canonicalSectionTrace (secondDifferential.hom.app (op Torus)
      (realize 2 (a • coordinatePair 0 (inverted 0 Finset.univ) p))) = 0 := by
  obtain ⟨b,hb⟩ := exists_native_normal 0 (inverted 0 Finset.univ) a
  rw [← hb]
  change canonicalSectionTrace (secondDifferential.hom.app (op Torus)
    (realize 2 (normal (nativeMap (coord 0 0)) b •
      exteriorPower.ιMulti Cubic 2
        ![KaehlerDifferential.D ℂ Cubic (nativeMap (coord 0 (pairLeft p))),
          KaehlerDifferential.D ℂ Cubic (nativeMap (coord 0 (pairRight p)))]))) = 0
  rw [realize_d_pair,
    native_normal_coordinate_wedge 0 (inverted 0 Finset.univ) b p,
    canonical_trace_realize_volume, nativePairCoefficient_residue_zero]

/-- This is the original sheaf differential and original fixed
canonical trace. The six coordinate wedges span the ordinary module,
and the proved affine comparison realizes every actual sheaf section. -/
theorem canonical_trace_secondDifferential
    (s : (CycleQ2LiteralIntrinsicExterior.Literal 2).obj.obj (op Torus)) :
    canonicalSectionTrace (secondDifferential.hom.app (op Torus) s) = 0 := by
  classical
  obtain ⟨ω,rfl⟩ := (realize 2).surjective s
  obtain ⟨a,ha⟩ := exists_coordinatePair_sum 0 (inverted 0 Finset.univ) ω
  rw [← ha, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  exact canonical_trace_d_coordinatePair (a p) p

end CycleQ2LiteralTorusOrdinaryForms
end

#print axioms CycleQ2LiteralTorusOrdinaryForms.canonical_trace_d_coordinatePair
#print axioms CycleQ2LiteralTorusOrdinaryForms.canonical_trace_secondDifferential

/-! Complete the original finite four-open total complex.  Its middle
maps are the already constructed unfiltered degree-two and degree-three
maps; the upper maps retain the same sign convention. -/

noncomputable section
namespace CycleQ2FourOpenDeRhamTotal

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech CycleQ2CechTwoToDerived CycleQ2CechTwoComparison

variable {X : TopCat.{0}} (U : Fin 4 → Opens X) (F₀ F₁ F₂ F₃ : AbSheaf X)

abbrev TotalZero := Zero F₀ U
abbrev TotalOne := Zero F₁ U × One F₀ U
abbrev TotalFive := Two F₃ U × Three F₂ U
abbrev TotalSix := Three F₃ U

variable {F₀ F₁ F₂ F₃}
  (d : F₀ ⟶ F₁) (e : F₁ ⟶ F₂) (f : F₂ ⟶ F₃)

def differentialZero : TotalZero U F₀ →+ TotalOne U F₀ F₁ where
  toFun x := (mapZero U d x, d0 F₀ U x)
  map_zero' := by rw [mapZero_zero, d0_zero] <;> rfl
  map_add' x y := by rw [mapZero_add, d0_add] <;> rfl

def differentialOne : TotalOne U F₀ F₁ →+ TotalTwo U F₀ F₁ F₂ where
  toFun x := (mapZero U e x.1, d0 F₁ U x.1 - mapOne U d x.2, d1 F₀ U x.2)
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero, mapZero_zero, d0_zero,
      mapOne_zero, d1_zero, sub_self] <;> rfl
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, mapZero_add, d0_add, mapOne_add, d1_add]
    refine Prod.ext rfl (Prod.ext ?_ rfl)
    change _ = (_ - _) + (_ - _)
    abel

def differentialFour : TotalFour U F₁ F₂ F₃ →+ TotalFive U F₂ F₃ where
  toFun x := (d1 F₃ U x.1 + mapTwo U f x.2.1,
    d2 F₂ U x.2.1 - app e _ x.2.2)
  map_zero' := by
    simp only [Prod.fst_zero, Prod.snd_zero, d1_zero, mapTwo_zero,
      d2_zero, map_zero, add_zero, sub_self] <;> rfl
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, d1_add, mapTwo_add, d2_add, map_add]
    refine Prod.ext ?_ ?_ <;>
      simp only [Prod.fst_add, Prod.snd_add] <;> abel

/-- The only incoming map to total degree six is the actual four-face
restriction minus the exterior derivative on the quadruple intersection. -/
def differentialFive : TotalFive U F₂ F₃ →+ TotalSix U F₃ where
  toFun x := d2 F₃ U x.1 - app f _ x.2
  map_zero' := by simp only [Prod.fst_zero, Prod.snd_zero, d2_zero, map_zero, sub_self]
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, d2_add, map_add]
    abel

theorem differentialOne_zero (hd : d ≫ e = 0) (x : TotalZero U F₀) :
    differentialOne U d e (differentialZero U d x) = 0 := by
  change (mapZero U e (mapZero U d x),
    d0 F₁ U (mapZero U d x) - mapOne U d (d0 F₀ U x),
    d1 F₀ U (d0 F₀ U x)) = 0
  rw [mapZero_comp, hd, mapZero_zeroHom, mapOne_d0, sub_self, d1_d0] <;> rfl

theorem boundary_differentialOne (hd : d ≫ e = 0) (he : e ≫ f = 0)
    (x : TotalOne U F₀ F₁) : boundary U d e f (differentialOne U d e x) = 0 := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · change mapZero U f (mapZero U e x.1) = 0
    rw [mapZero_comp, he, mapZero_zeroHom]
  · change d0 F₂ U (mapZero U e x.1) -
      mapOne U e (d0 F₁ U x.1 - mapOne U d x.2) = 0
    rw [mapOne_sub, mapOne_comp, hd, mapOne_zeroHom, sub_zero, mapOne_d0, sub_self]
  · change d1 F₁ U (d0 F₁ U x.1 - mapOne U d x.2) + mapTwo U d (d1 F₀ U x.2) = 0
    rw [d1_sub, d1_d0, mapTwo_d1, zero_sub, neg_add_cancel]
  · exact d2_d1 F₀ U x.2

theorem differentialFour_three (hd : d ≫ e = 0) (he : e ≫ f = 0)
    (x : TotalThree U F₀ F₁ F₂ F₃) :
    differentialFour U e f (differential U d e f x) = 0 := by
  refine Prod.ext ?_ ?_
  · change d1 F₃ U (d0 F₃ U x.1 - mapOne U f x.2.1) +
      mapTwo U f (d1 F₂ U x.2.1 + mapTwo U e x.2.2.1) = 0
    rw [d1_sub, d1_d0, mapTwo_add, mapTwo_comp, he, mapTwo_zeroHom,
      add_zero, mapTwo_d1, zero_sub, neg_add_cancel]
  · change d2 F₂ U (d1 F₂ U x.2.1 + mapTwo U e x.2.2.1) -
      app e _ (d2 F₁ U x.2.2.1 - app d _ x.2.2.2) = 0
    rw [d2_add, d2_d1, map_sub, app_comp, hd, app_zero, sub_zero,
      zero_add, mapThree_d2, sub_self]

theorem differentialFive_four (he : e ≫ f = 0) (x : TotalFour U F₁ F₂ F₃) :
    differentialFive U f (differentialFour U e f x) = 0 := by
  change d2 F₃ U (d1 F₃ U x.1 + mapTwo U f x.2.1) -
    app f _ (d2 F₂ U x.2.1 - app e _ x.2.2) = 0
  rw [d2_add, d2_d1, map_sub, app_comp, he, app_zero, sub_zero,
    zero_add, mapThree_d2, sub_self]

variable (F₀ F₁ F₂ F₃)

/-- All terms of the original finite total complex, with its genuine
zero tail beyond the dimension of the cover and the threefold. -/
def object : ℕ → AddCommGrpCat.{0}
  | 0 => AddCommGrpCat.of (TotalZero U F₀)
  | 1 => AddCommGrpCat.of (TotalOne U F₀ F₁)
  | 2 => AddCommGrpCat.of (TotalTwo U F₀ F₁ F₂)
  | 3 => AddCommGrpCat.of (TotalThree U F₀ F₁ F₂ F₃)
  | 4 => AddCommGrpCat.of (TotalFour U F₁ F₂ F₃)
  | 5 => AddCommGrpCat.of (TotalFive U F₂ F₃)
  | 6 => AddCommGrpCat.of (TotalSix U F₃)
  | _ + 7 => AddCommGrpCat.of PUnit

variable {F₀ F₁ F₂ F₃}

def next : (n : ℕ) → object U F₀ F₁ F₂ F₃ n ⟶ object U F₀ F₁ F₂ F₃ (n+1)
  | 0 => AddCommGrpCat.ofHom (differentialZero U d)
  | 1 => AddCommGrpCat.ofHom (differentialOne U d e)
  | 2 => AddCommGrpCat.ofHom (boundary U d e f)
  | 3 => AddCommGrpCat.ofHom (differential U d e f)
  | 4 => AddCommGrpCat.ofHom (differentialFour U e f)
  | 5 => AddCommGrpCat.ofHom (differentialFive U f)
  | _ + 6 => 0

theorem next_square (hd : d ≫ e = 0) (he : e ≫ f = 0) :
    ∀ n, next U d e f n ≫ next U d e f (n+1) = 0
  | 0 => by ext x; exact differentialOne_zero U d e hd x
  | 1 => by ext x; exact boundary_differentialOne U d e f hd he x
  | 2 => by ext x; exact differential_boundary U d e f hd he x
  | 3 => by ext x; exact differentialFour_three U d e f hd he x
  | 4 => by ext x; exact differentialFive_four U e f he x
  | 5 => by simp only [next, comp_zero]
  | _ + 6 => by simp only [next, zero_comp]

def complex (hd : d ≫ e = 0) (he : e ≫ f = 0) :
    CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (object U F₀ F₁ F₂ F₃) (next U d e f)
    (next_square U d e f hd he)

theorem complex_d (hd : d ≫ e = 0) (he : e ≫ f = 0) (n : ℕ) :
    (complex U d e f hd he).d n (n+1) = next U d e f n :=
  CochainComplex.of_d _ _ n

end CycleQ2FourOpenDeRhamTotal
end

#print axioms CycleQ2FourOpenDeRhamTotal.differentialFive_four
#print axioms CycleQ2FourOpenDeRhamTotal.complex

noncomputable section
namespace CycleQ2LiteralTopDeRhamTrace

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2CechTwoToDerived (Two Three app app_res d2)
open CycleQ2GeometricSheafLocalIso (res res_comp res_self)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldFirstDifferential
  (X functionDifferential differential function_differential_zero)
open CycleQ2LiteralThreefoldSecondDifferential
  (secondDifferential first_second_zero)
open CycleQ2LiteralThreefoldCanonicalFrame
  (CanonicalForms CanonicalAdditiveSheaf globalFrame)
open CycleQ2LiteralThreefoldTopTrace
  (Torus canonicalSectionTrace canonicalTrace canonicalTrace_connecting
    framedGenerator framedSectionTrace_generator)
open CycleQ2HodgeTwistTopDerived
  (nativeTopOpen_eq_ordered nativeTopOrdered nativeTopConnecting_boundary)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)

/-- The full total complex uses the unchanged original three sheaf
differentials and all four original weight-one opens. -/
abbrev complex : CochainComplex AddCommGrpCat.{0} ℕ :=
  CycleQ2FourOpenDeRhamTotal.complex fixedOpen
    functionDifferential differential secondDifferential
    function_differential_zero first_second_zero

private abbrev F := CanonicalAdditiveSheaf
private abbrev OrderedTop := (((fixedOpen 0 ⊓ fixedOpen 1) ⊓ fixedOpen 2) ⊓ fixedOpen 3)

/-- This only transports a section along equality of its two original
open-set expressions. -/
def toNative (G : AbSheaf (show TopCat from X)) : Three G fixedOpen →+ Sections G Torus :=
  res G (nativeTopOpen_eq_ordered fixedOpen).le

theorem toNative_nativeTopOrdered (G : AbSheaf (show TopCat from X))
    (s : Sections G Torus) : toNative G (nativeTopOrdered G fixedOpen s) = s := by
  change res G _ (res G _ s) = s
  rw [res_comp, res_self]

private theorem face₀ : (Finset.univ.erase (0 : Fin 4)).inf fixedOpen =
    ((fixedOpen 1 ⊓ fixedOpen 2) ⊓ fixedOpen 3) := by
  rw [show Finset.univ.erase (0 : Fin 4) = {1,2,3} from by decide]
  simp [inf_assoc]

private theorem face₁ : (Finset.univ.erase (1 : Fin 4)).inf fixedOpen =
    ((fixedOpen 0 ⊓ fixedOpen 2) ⊓ fixedOpen 3) := by
  rw [show Finset.univ.erase (1 : Fin 4) = {0,2,3} from by decide]
  simp [inf_assoc]

private theorem face₂ : (Finset.univ.erase (2 : Fin 4)).inf fixedOpen =
    ((fixedOpen 0 ⊓ fixedOpen 1) ⊓ fixedOpen 3) := by
  rw [show Finset.univ.erase (2 : Fin 4) = {0,1,3} from by decide]
  simp [inf_assoc]

private theorem face₃ : (Finset.univ.erase (3 : Fin 4)).inf fixedOpen =
    ((fixedOpen 0 ⊓ fixedOpen 1) ⊓ fixedOpen 2) := by
  rw [show Finset.univ.erase (3 : Fin 4) = {0,1,2} from by decide]
  simp [inf_assoc]

private def nativeFaces (c : Two F fixedOpen) : NativeTopFaces (F := F) (U := fixedOpen) := by
  intro i
  fin_cases i
  · exact res F face₀.le c.2.2.2
  · exact res F face₁.le c.2.2.1
  · exact res F face₂.le c.2.1
  · exact res F face₃.le c.1

private theorem toNative_d2 (c : Two F fixedOpen) :
    toNative F (d2 F fixedOpen c) = nativeTopBoundary (nativeFaces c) := by
  change res F _
      (res F _ c.2.2.2 - res F _ c.2.2.1 + res F _ c.2.1 - res F _ c.1) =
    res F _ (res F _ c.2.2.2) - res F _ (res F _ c.2.2.1) +
      res F _ (res F _ c.2.1) - res F _ (res F _ c.1)
  simp only [map_sub, map_add, res_comp]

def sectionTrace : Three F fixedOpen →+ ℂ := canonicalSectionTrace.comp (toNative F)

theorem sectionTrace_cech_boundary (c : Two F fixedOpen) :
    sectionTrace (d2 F fixedOpen c) = 0 := by
  change canonicalSectionTrace (toNative F (d2 F fixedOpen c)) = 0
  rw [toNative_d2, ← canonicalTrace_connecting, nativeTopConnecting_boundary, map_zero]

theorem sectionTrace_exterior_boundary
    (η : Three CycleQ2LiteralThreefoldFirstDifferential.Two fixedOpen) :
    sectionTrace (app secondDifferential OrderedTop η) = 0 := by
  change canonicalSectionTrace (res F (nativeTopOpen_eq_ordered fixedOpen).le
    (app secondDifferential OrderedTop η)) = 0
  rw [← app_res]
  exact CycleQ2LiteralTorusOrdinaryForms.canonical_trace_secondDifferential
    (toNative CycleQ2LiteralThreefoldFirstDifferential.Two η)

/-- The trace annihilates the actual degree-five differential of the
full total complex, including both incoming components. -/
theorem sectionTrace_differentialFive
    (x : CycleQ2FourOpenDeRhamTotal.TotalFive fixedOpen
      CycleQ2LiteralThreefoldFirstDifferential.Two F) :
    sectionTrace (CycleQ2FourOpenDeRhamTotal.differentialFive fixedOpen secondDifferential x) = 0 := by
  change sectionTrace (d2 F fixedOpen x.1 - app secondDifferential OrderedTop x.2) = 0
  rw [map_sub, sectionTrace_cech_boundary, sectionTrace_exterior_boundary, sub_self]

private abbrev topShort : ShortComplex AddCommGrpCat.{0} := complex.sc' 5 6 7

private def topHomologyIso : complex.homology 6 ≅ topShort.homology :=
  complex.homologyIsoSc' 5 6 7
    ((ComplexShape.up ℕ).prev_eq' (show (ComplexShape.up ℕ).Rel 5 6 from rfl))
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 6 7 from rfl))

private def homologyCoordinates : complex.homology 6 ≃+
    (topShort.g.hom.ker ⧸ topShort.abToCycles.range) :=
  (topHomologyIso ≪≫ topShort.abHomologyIso).addCommGroupIsoToAddEquiv

private def topCycle : Three F fixedOpen →+ topShort.g.hom.ker where
  toFun s := ⟨s, by
    change complex.d 6 7 s = 0
    rw [CycleQ2FourOpenDeRhamTotal.complex_d] <;> rfl⟩
  map_zero' := Subtype.ext rfl
  map_add' s t := Subtype.ext rfl

/-- The canonical class map into Mathlib homology of the actual finite
Čech–de Rham complex. -/
def sectionClass : Three F fixedOpen →+ complex.homology 6 :=
  homologyCoordinates.symm.toAddMonoidHom.comp
    ((QuotientAddGroup.mk' topShort.abToCycles.range).comp topCycle)

private def quotientTrace : (topShort.g.hom.ker ⧸ topShort.abToCycles.range) →+ ℂ :=
  QuotientAddGroup.lift topShort.abToCycles.range
    (sectionTrace.comp topShort.g.hom.ker.subtype) (by
      rintro _ ⟨x,rfl⟩
      change sectionTrace (complex.d 5 6 x) = 0
      rw [CycleQ2FourOpenDeRhamTotal.complex_d]
      exact sectionTrace_differentialFive x)

/-- The fixed canonical trace on genuine total degree-six homology. -/
def trace : complex.homology 6 →+ ℂ :=
  quotientTrace.comp homologyCoordinates.toAddMonoidHom

theorem trace_sectionClass (s : Three F fixedOpen) :
    trace (sectionClass s) = sectionTrace s := by
  change quotientTrace (homologyCoordinates (homologyCoordinates.symm
    (QuotientAddGroup.mk (topCycle s)))) = sectionTrace s
  rw [AddEquiv.apply_symm_apply] <;> rfl

/-- The same normalized Laurent generator used by the original fixed
canonical trace, expressed on the ordered quadruple intersection. -/
def generator (a : ℂ) : Three F fixedOpen :=
  nativeTopOrdered F fixedOpen (framedGenerator CanonicalForms globalFrame a)

theorem sectionTrace_generator (a : ℂ) : sectionTrace (generator a) = a := by
  change canonicalSectionTrace (toNative F (nativeTopOrdered F fixedOpen
    (framedGenerator CanonicalForms globalFrame a))) = a
  rw [toNative_nativeTopOrdered]
  exact framedSectionTrace_generator CanonicalForms globalFrame a

def normalizedClass (a : ℂ) : complex.homology 6 := sectionClass (generator a)

theorem trace_normalizedClass (a : ℂ) : trace (normalizedClass a) = a := by
  rw [normalizedClass, trace_sectionClass, sectionTrace_generator]

/-- The original residue-one generator survives every degree-five
boundary in the unfiltered finite Čech–de Rham total complex. -/
theorem normalizedClass_one_ne_zero : normalizedClass 1 ≠ 0 := by
  intro h
  have ht := congrArg trace h
  rw [trace_normalizedClass, map_zero] at ht
  exact one_ne_zero ht

end CycleQ2LiteralTopDeRhamTrace
end

#print axioms CycleQ2LiteralTopDeRhamTrace.sectionTrace_differentialFive
#print axioms CycleQ2LiteralTopDeRhamTrace.trace_normalizedClass
#print axioms CycleQ2LiteralTopDeRhamTrace.normalizedClass_one_ne_zero

/-! The top-degree comparison uses the original source Mayer--Vietoris
triangles and affine representatives. No total-complex comparison or
degeneration of a spectral sequence is supplied as an assumption. -/

noncomputable section

namespace CycleQ2DerivedSourceBoundary

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u
variable {C : Type u} [Category.{v} C] [Abelian C]
  [HasDerivedCategory.{w} C] [HasExt.{w} C]

private abbrev E := DerivedCategory.singleFunctor C 0
private abbrev shiftOne := shiftFunctor (DerivedCategory C) (1 : ℤ)

/-- The actual source connecting map, with the target shifted by one. -/
def connecting {S : ShortComplex C} (hS : S.ShortExact)
    (T : DerivedCategory C) (n : ℤ) :
    (E.obj S.X₁ ⟶ T⟦n⟧) →+ (E.obj S.X₃ ⟶ T⟦n+1⟧) where
  toFun a := hS.singleδ ≫ shiftOne.map a ≫
    (shiftFunctorAdd (DerivedCategory C) n 1).inv.app T
  map_zero' := by simp
  map_add' a b := by simp [Functor.map_add,Preadditive.comp_add,Preadditive.add_comp]

theorem connecting_image {S : ShortComplex C} (hS : S.ShortExact)
    (T : DerivedCategory C) (n : ℤ) (b : E.obj S.X₂ ⟶ T⟦n⟧) :
    connecting hS T n (E.map S.f ≫ b) = 0 := by
  have hz : hS.singleδ ≫ shiftOne.map (E.map S.f) = 0 :=
    comp_distTriang_mor_zero₃₁ hS.singleTriangle hS.singleTriangle_distinguished
  change hS.singleδ ≫ shiftOne.map (E.map S.f ≫ b) ≫ _ = 0
  simp only [Functor.map_comp,← Category.assoc,hz,zero_comp]

theorem connecting_eq_zero_iff {S : ShortComplex C} (hS : S.ShortExact)
    (T : DerivedCategory C) (n : ℤ) (a : E.obj S.X₁ ⟶ T⟦n⟧) :
    connecting hS T n a = 0 ↔ ∃ b : E.obj S.X₂ ⟶ T⟦n⟧, E.map S.f ≫ b = a := by
  constructor
  · intro ha
    have hz : hS.extClass.hom ≫ shiftOne.map a = 0 := by
      rw [hS.extClass_hom]
      apply (cancel_mono ((shiftFunctorAdd (DerivedCategory C) n 1).inv.app T)).mp
      simpa only [Category.assoc,zero_comp] using ha
    obtain ⟨b,hb⟩ := CycleQ2LogDetection.extension_of_connecting_zero hS a hz
    exact ⟨b,hb.symm⟩
  · rintro ⟨b,rfl⟩
    exact connecting_image hS T n b

/-- Vanishing on the two middle source summands makes the source
connecting map surjective. -/
theorem connecting_surjective {S : ShortComplex C} (hS : S.ShortExact)
    (T : DerivedCategory C) (n : ℤ)
    (hmid : ∀ b : E.obj S.X₂ ⟶ T⟦n+1⟧, b = 0) :
    Function.Surjective (connecting hS T n) := by
  intro y
  obtain ⟨c,hc⟩ := hS.singleTriangle.yoneda_exact₃
    hS.singleTriangle_distinguished y (hmid _)
  let J := (shiftFunctorAdd (DerivedCategory C) n 1).app T
  refine ⟨shiftOne.preimage (c ≫ J.hom),?_⟩
  change hS.singleδ ≫ shiftOne.map (shiftOne.preimage (c ≫ J.hom)) ≫ J.inv = y
  simpa only [Functor.map_preimage,Category.assoc,J.hom_inv_id,Category.comp_id] using hc.symm

/-- Naturality uses the morphism of the original short exact source
triangles, including their prescribed signs. -/
theorem connecting_natural {S R : ShortComplex C}
    (hS : S.ShortExact) (hR : R.ShortExact) (m : S ⟶ R)
    (T : DerivedCategory C) (n : ℤ) (a : E.obj R.X₁ ⟶ T⟦n⟧) :
    E.map m.τ₃ ≫ connecting hR T n a =
      connecting hS T n (E.map m.τ₁ ≫ a) := by
  have hm := (ShortComplex.ShortExact.singleTriangle.map hS hR m).comm₃
  change E.map m.τ₃ ≫ hR.singleδ = hS.singleδ ≫ shiftOne.map (E.map m.τ₁) at hm
  change E.map m.τ₃ ≫ (hR.singleδ ≫ shiftOne.map a ≫ _) =
    hS.singleδ ≫ shiftOne.map (E.map m.τ₁ ≫ a) ≫ _
  simpa only [Category.assoc,Functor.map_comp] using
    congrArg (fun v => v ≫ shiftOne.map a ≫
      (shiftFunctorAdd (DerivedCategory C) n 1).inv.app T) hm

end CycleQ2DerivedSourceBoundary

namespace CycleQ2DerivedCoverTop

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf)
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2FourOpenH3 (QuadOpen)

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf X) 0

variable (T : DerivedCategory (AbSheaf X))

abbrev H (n : ℤ) (U : Opens X) := E.obj (freeOpen U) ⟶ T⟦n⟧

def restriction (n : ℤ) {U V : Opens X} (h : U ≤ V) : H T n V →+ H T n U where
  toFun a := E.map ((freeOpenSheaf (X := X)).map (homOfLE h)) ≫ a
  map_zero' := by simp
  map_add' a b := Preadditive.comp_add _ a b

theorem restriction_comp (n : ℤ) {U V W : Opens X} (h : U ≤ V) (j : V ≤ W)
    (a : H T n W) : restriction T n h (restriction T n j a) =
      restriction T n (h.trans j) a := by
  change E.map _ ≫ (E.map _ ≫ a) = E.map _ ≫ a
  rw [← Category.assoc,← Functor.map_comp,← Functor.map_comp]
  rfl

theorem restriction_self (n : ℤ) (U : Opens X) (a : H T n U) :
    restriction T n (le_refl U) a = a := by
  change E.map ((freeOpenSheaf (X := X)).map (𝟙 U)) ≫ a = a
  rw [Functor.map_id,Functor.map_id,Category.id_comp]

def restrictionEquiv (n : ℤ) {U V : Opens X} (h : U = V) : H T n U ≃+ H T n V where
  toFun := restriction T n h.ge
  invFun := restriction T n h.le
  left_inv a := by rw [restriction_comp,restriction_self]
  right_inv a := by rw [restriction_comp,restriction_self]
  map_add' a b := map_add (restriction T n h.ge) a b

def delta (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (n : ℤ) :
    H T n S.X₁ →+ H T (n+1) S.X₄ :=
  CycleQ2DerivedSourceBoundary.connecting S.shortComplex_shortExact T n

theorem delta_pair_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (a : H T n S.X₂) (b : H T n S.X₃) :
    delta T S n (restriction T n S.f₁₂.le a - restriction T n S.f₁₃.le b) = 0 := by
  let v : E.obj S.shortComplex.X₂ ⟶ T⟦n⟧ :=
    E.map biprod.fst ≫ a + E.map biprod.snd ≫ b
  have hv : E.map S.shortComplex.f ≫ v =
      restriction T n S.f₁₂.le a - restriction T n S.f₁₃.le b := by
    change E.map (biprod.lift _ (-_)) ≫ v = E.map _ ≫ a - E.map _ ≫ b
    simp only [v,Preadditive.comp_add,← Category.assoc,← Functor.map_comp,
      biprod.lift_fst,biprod.lift_snd,Functor.map_neg,Preadditive.neg_comp,sub_eq_add_neg]
  rw [← hv]
  exact CycleQ2DerivedSourceBoundary.connecting_image S.shortComplex_shortExact T n v

theorem delta_left_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (a : H T n S.X₂) : delta T S n (restriction T n S.f₁₂.le a) = 0 := by
  simpa only [map_zero,sub_zero] using delta_pair_zero T S n a 0

theorem delta_right_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (b : H T n S.X₃) : delta T S n (restriction T n S.f₁₃.le b) = 0 := by
  simpa only [map_zero,map_neg,zero_sub,neg_neg] using delta_pair_zero T S n 0 (-b)

theorem delta_eq_zero_iff (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (x : H T n S.X₁) : delta T S n x = 0 ↔
    ∃ (a : H T n S.X₂) (b : H T n S.X₃),
      restriction T n S.f₁₂.le a - restriction T n S.f₁₃.le b = x := by
  constructor
  · intro hx
    obtain ⟨v,hv⟩ := (CycleQ2DerivedSourceBoundary.connecting_eq_zero_iff
      S.shortComplex_shortExact T n x).mp hx
    refine ⟨E.map biprod.inl ≫ v,E.map biprod.inr ≫ v,?_⟩
    change E.map (biprod.lift _ (-_)) ≫ v = x at hv
    change E.map _ ≫ (E.map biprod.inl ≫ v) - E.map _ ≫ (E.map biprod.inr ≫ v) = x
    simpa only [biprod.lift_eq,Functor.map_add,Functor.map_comp,Functor.map_neg,
      Preadditive.add_comp,Preadditive.neg_comp,Category.assoc,sub_eq_add_neg] using hv
  · rintro ⟨a,b,rfl⟩
    exact delta_pair_zero T S n a b

theorem delta_surjective (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (h₂ : Subsingleton (H T (n+1) S.X₂))
    (h₃ : Subsingleton (H T (n+1) S.X₃)) : Function.Surjective (delta T S n) := by
  apply CycleQ2DerivedSourceBoundary.connecting_surjective S.shortComplex_shortExact T n
  intro b
  have hi : E.map (biprod.inl : freeOpen S.X₂ ⟶ freeOpen S.X₂ ⊞ freeOpen S.X₃) ≫ b = 0 :=
    h₂.elim _ _
  have hj : E.map (biprod.inr : freeOpen S.X₃ ⟶ freeOpen S.X₂ ⊞ freeOpen S.X₃) ≫ b = 0 :=
    h₃.elim _ _
  calc
    b = E.map (𝟙 (freeOpen S.X₂ ⊞ freeOpen S.X₃)) ≫ b := by simp
    _ = E.map (biprod.fst ≫ biprod.inl + biprod.snd ≫ biprod.inr) ≫ b := by
      rw [biprod.total]
    _ = 0 := by
      simp only [Functor.map_add,Functor.map_comp,Preadditive.add_comp,
        Category.assoc,hi,hj,comp_zero,add_zero]

theorem union_zero (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n : ℤ) (h₁ : Subsingleton (H T n S.X₁))
    (h₂ : Subsingleton (H T (n+1) S.X₂)) (h₃ : Subsingleton (H T (n+1) S.X₃)) :
    Subsingleton (H T (n+1) S.X₄) := by
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨a,rfl⟩ := delta_surjective T S n h₂ h₃ y
  rw [h₁.elim a 0,map_zero]

theorem delta_natural (S R : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h₁ : S.X₁ ≤ R.X₁) (h₂ : S.X₂ ≤ R.X₂)
    (h₃ : S.X₃ ≤ R.X₃) (h₄ : S.X₄ ≤ R.X₄) (n : ℤ) (a : H T n R.X₁) :
    restriction T (n+1) h₄ (delta T R n a) = delta T S n (restriction T n h₁ a) :=
  CycleQ2DerivedSourceBoundary.connecting_natural S.shortComplex_shortExact
    R.shortComplex_shortExact (CycleQ2FourOpenH3.squareMap S R h₁ h₂ h₃ h₄) T n a

theorem delta_restriction {U' V' U V : Opens X} (hU : U' ≤ U) (hV : V' ≤ V)
    (n : ℤ) (a : H T n (U ⊓ V)) :
    restriction T (n+1) (sup_le_sup hU hV)
      (delta T (Opens.mayerVietorisSquare U V) n a) =
    delta T (Opens.mayerVietorisSquare U' V') n
      (restriction T n (inf_le_inf hU hV) a) :=
  delta_natural T _ _ (inf_le_inf hU hV) hU hV (sup_le_sup hU hV) n a

def tripleBoundary (n : ℤ) (U V W : Opens X) :
    (H T n (U ⊓ V) × H T n (U ⊓ W) × H T n (V ⊓ W)) →+
      H T n (TripleOpen U V W) where
  toFun a := restriction T n inf_le_right a.2.2 - restriction T n inf_le_left a.2.1 +
    restriction T n (inf_le_inf inf_le_left inf_le_left) a.1
  map_zero' := by simp
  map_add' a b := by
    simp only [Prod.fst_add,Prod.snd_add,map_add]
    abel

def tripleConnecting (n : ℤ) (U V W : Opens X) :
    H T n (TripleOpen U V W) →+ H T (n+1+1) ((U ⊔ V) ⊔ W) :=
  (delta T (CycleQ2ThreeOpenCechH2.outerSquare U V W) (n+1)).comp
    (delta T (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)) n)

private theorem triple_restrict01 (n : ℤ) (U V W : Opens X) (a : H T n (U ⊓ V)) :
    tripleConnecting T n U V W
      (restriction T n (inf_le_inf inf_le_left inf_le_left) a) = 0 := by
  let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  let R := CycleQ2ThreeOpenCechH2.outerSquare U V W
  have hn := delta_restriction T (inf_le_left : U ⊓ W ≤ U)
    (inf_le_left : V ⊓ W ≤ V) n a
  change delta T R (n+1) (delta T S n _) = 0
  rw [← hn]
  exact delta_left_zero T R (n+1) (delta T (Opens.mayerVietorisSquare U V) n a)

theorem triple_boundary_zero (n : ℤ) (U V W : Opens X)
    (a : H T n (U ⊓ V) × H T n (U ⊓ W) × H T n (V ⊓ W)) :
    tripleConnecting T n U V W (tripleBoundary T n U V W a) = 0 := by
  have h02 : tripleConnecting T n U V W (restriction T n inf_le_left a.2.1) = 0 := by
    change delta T _ (n+1) (delta T _ n _) = 0
    rw [delta_left_zero,map_zero]
  have h12 : tripleConnecting T n U V W (restriction T n inf_le_right a.2.2) = 0 := by
    change delta T _ (n+1) (delta T _ n _) = 0
    rw [delta_right_zero,map_zero]
  change tripleConnecting T n U V W
    (restriction T n inf_le_right a.2.2 - restriction T n inf_le_left a.2.1 +
      restriction T n (inf_le_inf inf_le_left inf_le_left) a.1) = 0
  rw [map_add,map_sub,h12,h02,triple_restrict01,sub_self,zero_add]

theorem triple_eq_zero_iff (n : ℤ) (U V W : Opens X)
    (hU : Subsingleton (H T (n+1) U)) (hV : Subsingleton (H T (n+1) V))
    (hW : Subsingleton (H T (n+1) W)) (x : H T n (TripleOpen U V W)) :
    tripleConnecting T n U V W x = 0 ↔
      ∃ a, tripleBoundary T n U V W a = x := by
  constructor
  · intro hx
    let S := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
    let R := CycleQ2ThreeOpenCechH2.outerSquare U V W
    obtain ⟨a₁,b₁,hab⟩ := (delta_eq_zero_iff T R (n+1) _).mp hx
    have hb : b₁ = 0 := hW.elim _ _
    have ha : restriction T (n+1) R.f₁₂.le a₁ = delta T S n x := by
      simpa only [hb,map_zero,sub_zero] using hab
    obtain ⟨a,ha₀⟩ := delta_surjective T (Opens.mayerVietorisSquare U V) n hU hV a₁
    have he : delta T S n
        (restriction T n (inf_le_inf inf_le_left inf_le_left) a) = delta T S n x :=
      (delta_restriction T (inf_le_left : U ⊓ W ≤ U)
        (inf_le_left : V ⊓ W ≤ V) n a).symm.trans
        ((congrArg (restriction T (n+1) R.f₁₂.le) ha₀).trans ha)
    have hz : delta T S n
        (x - restriction T n (inf_le_inf inf_le_left inf_le_left) a) = 0 := by
      rw [map_sub,he,sub_self]
    obtain ⟨b,c,hbc⟩ := (delta_eq_zero_iff T S n _).mp hz
    refine ⟨(a,-b,-c),?_⟩
    change restriction T n inf_le_right (-c) - restriction T n inf_le_left (-b) +
      restriction T n (inf_le_inf inf_le_left inf_le_left) a = x
    rw [map_neg,map_neg]
    change restriction T n inf_le_left b - restriction T n inf_le_right c =
      x - restriction T n (inf_le_inf inf_le_left inf_le_left) a at hbc
    calc
      _ = (restriction T n inf_le_left b - restriction T n inf_le_right c) +
          restriction T n (inf_le_inf inf_le_left inf_le_left) a := by abel
      _ = x := by rw [hbc]; abel
  · rintro ⟨a,rfl⟩
    exact triple_boundary_zero T n U V W a

theorem triple_surjective (n : ℤ) (U V W : Opens X)
    (hU : Subsingleton (H T (n+1+1) U)) (hV : Subsingleton (H T (n+1+1) V))
    (hW : Subsingleton (H T (n+1+1) W))
    (hUV : Subsingleton (H T (n+1) (U ⊓ V)))
    (hUW : Subsingleton (H T (n+1) (U ⊓ W)))
    (hVW : Subsingleton (H T (n+1) (V ⊓ W))) :
    Function.Surjective (tripleConnecting T n U V W) := by
  have huv := union_zero T (Opens.mayerVietorisSquare U V) (n+1) hUV hU hV
  intro y
  obtain ⟨z,hz⟩ := delta_surjective T (CycleQ2ThreeOpenCechH2.outerSquare U V W)
    (n+1) huv hW y
  obtain ⟨s,hs⟩ := delta_surjective T
    (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)) n hUW hVW z
  exact ⟨s,(congrArg (delta T _ (n+1)) hs).trans hz⟩

theorem triple_natural (n : ℤ) {U' V' W' U V W : Opens X}
    (hU : U' ≤ U) (hV : V' ≤ V) (hW : W' ≤ W) (a : H T n (TripleOpen U V W)) :
    restriction T (n+1+1) (sup_le_sup (sup_le_sup hU hV) hW)
      (tripleConnecting T n U V W a) =
    tripleConnecting T n U' V' W'
      (restriction T n (inf_le_inf (inf_le_inf hU hW) (inf_le_inf hV hW)) a) := by
  let S := CycleQ2ThreeOpenCechH2.outerSquare U V W
  let R := CycleQ2ThreeOpenCechH2.outerSquare U' V' W'
  change restriction T (n+1+1) _ (delta T S (n+1) (delta T _ n a)) =
    delta T R (n+1) (delta T _ n _)
  rw [delta_natural T R S
    (sup_le_sup (inf_le_inf hU hW) (inf_le_inf hV hW))
    (sup_le_sup hU hV) hW (sup_le_sup (sup_le_sup hU hV) hW)]
  rw [delta_restriction T (inf_le_inf hU hW) (inf_le_inf hV hW)]

abbrev TripleClasses (n : ℤ) (U V W Z : Opens X) :=
  H T n (TripleOpen U V W) × H T n ((U ⊓ Z) ⊓ (V ⊓ Z)) ×
    H T n ((U ⊓ Z) ⊓ (W ⊓ Z)) × H T n ((V ⊓ Z) ⊓ (W ⊓ Z))

private theorem quad_le_triple (U V W Z : Opens X) : QuadOpen U V W Z ≤ TripleOpen U V W :=
  inf_le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_inf inf_le_left inf_le_left)

def fourBoundary (n : ℤ) (U V W Z : Opens X) :
    TripleClasses T n U V W Z →+ H T n (QuadOpen U V W Z) where
  toFun a := tripleBoundary T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) (a.2.1,a.2.2.1,a.2.2.2) -
    restriction T n (quad_le_triple U V W Z) a.1
  map_zero' := by simp
  map_add' a b := by
    change tripleBoundary T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
      ((a.2.1,a.2.2.1,a.2.2.2) + (b.2.1,b.2.2.1,b.2.2.2)) -
      restriction T n (quad_le_triple U V W Z) (a.1+b.1) = _
    rw [map_add,map_add]
    abel

def fourConnecting (n : ℤ) (U V W Z : Opens X) :
    H T n (QuadOpen U V W Z) →+ H T (n+1+1+1) (((U ⊔ V) ⊔ W) ⊔ Z) :=
  (delta T (CycleQ2FourOpenH3.outerSquare U V W Z) (n+1+1)).comp
    (tripleConnecting T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z))

private theorem four_restrict012 (n : ℤ) (U V W Z : Opens X)
    (a : H T n (TripleOpen U V W)) :
    fourConnecting T n U V W Z (restriction T n (quad_le_triple U V W Z) a) = 0 := by
  change delta T (CycleQ2FourOpenH3.outerSquare U V W Z) (n+1+1)
    (tripleConnecting T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) _) = 0
  rw [← triple_natural T n (inf_le_left : U ⊓ Z ≤ U)
    (inf_le_left : V ⊓ Z ≤ V) (inf_le_left : W ⊓ Z ≤ W)]
  exact delta_left_zero T _ (n+1+1) (tripleConnecting T n U V W a)

theorem four_boundary_zero (n : ℤ) (U V W Z : Opens X)
    (a : TripleClasses T n U V W Z) :
    fourConnecting T n U V W Z (fourBoundary T n U V W Z a) = 0 := by
  change fourConnecting T n U V W Z
    (tripleBoundary T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) (a.2.1,a.2.2.1,a.2.2.2) -
      restriction T n (quad_le_triple U V W Z) a.1) = 0
  rw [map_sub,four_restrict012,sub_zero]
  change delta T _ (n+1+1) (tripleConnecting T n _ _ _ _) = 0
  rw [triple_boundary_zero,map_zero]

theorem four_eq_zero_iff (n : ℤ) (U V W Z : Opens X)
    (hU : Subsingleton (H T (n+1+1) U)) (hV : Subsingleton (H T (n+1+1) V))
    (hW : Subsingleton (H T (n+1+1) W)) (hZ : Subsingleton (H T (n+1+1) Z))
    (hUV : Subsingleton (H T (n+1) (U ⊓ V)))
    (hUW : Subsingleton (H T (n+1) (U ⊓ W)))
    (hVW : Subsingleton (H T (n+1) (V ⊓ W)))
    (hUZ : Subsingleton (H T (n+1) (U ⊓ Z)))
    (hVZ : Subsingleton (H T (n+1) (V ⊓ Z)))
    (hWZ : Subsingleton (H T (n+1) (W ⊓ Z))) (s : H T n (QuadOpen U V W Z)) :
    fourConnecting T n U V W Z s = 0 ↔ ∃ a, fourBoundary T n U V W Z a = s := by
  constructor
  · intro hs
    let S := CycleQ2FourOpenH3.outerSquare U V W Z
    let g := tripleConnecting T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
    obtain ⟨a,b,hab⟩ := (delta_eq_zero_iff T S (n+1+1) (g s)).mp hs
    have hb : b = 0 := hZ.elim _ _
    have ha : restriction T (n+1+1) S.f₁₂.le a = g s := by
      simpa only [hb,map_zero,sub_zero] using hab
    obtain ⟨v,hv⟩ := triple_surjective T n U V W hU hV hW hUV hUW hVW a
    have he : g (restriction T n (quad_le_triple U V W Z) v) = g s :=
      (triple_natural T n (inf_le_left : U ⊓ Z ≤ U)
        (inf_le_left : V ⊓ Z ≤ V) (inf_le_left : W ⊓ Z ≤ W) v).symm.trans
        ((congrArg (restriction T (n+1+1) S.f₁₂.le) hv).trans ha)
    have hz : g (s - restriction T n (quad_le_triple U V W Z) v) = 0 := by
      rw [map_sub,he,sub_self]
    obtain ⟨⟨a₀,b₀,c₀⟩,h₀⟩ :=
      (triple_eq_zero_iff T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) hUZ hVZ hWZ _).mp hz
    refine ⟨(-v,a₀,b₀,c₀),?_⟩
    change tripleBoundary T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) (a₀,b₀,c₀) -
      restriction T n (quad_le_triple U V W Z) (-v) = s
    rw [h₀,map_neg]
    abel
  · rintro ⟨a,rfl⟩
    exact four_boundary_zero T n U V W Z a

theorem four_surjective (n : ℤ) (U V W Z : Opens X)
    (hU : Subsingleton (H T (n+1+1+1) U)) (hV : Subsingleton (H T (n+1+1+1) V))
    (hW : Subsingleton (H T (n+1+1+1) W)) (hZ : Subsingleton (H T (n+1+1+1) Z))
    (hUV : Subsingleton (H T (n+1+1) (U ⊓ V)))
    (hUW : Subsingleton (H T (n+1+1) (U ⊓ W)))
    (hVW : Subsingleton (H T (n+1+1) (V ⊓ W)))
    (hUZ : Subsingleton (H T (n+1+1) (U ⊓ Z)))
    (hVZ : Subsingleton (H T (n+1+1) (V ⊓ Z)))
    (hWZ : Subsingleton (H T (n+1+1) (W ⊓ Z)))
    (hUVW : Subsingleton (H T (n+1) (TripleOpen U V W)))
    (hUVZ : Subsingleton (H T (n+1) ((U ⊓ Z) ⊓ (V ⊓ Z))))
    (hUWZ : Subsingleton (H T (n+1) ((U ⊓ Z) ⊓ (W ⊓ Z))))
    (hVWZ : Subsingleton (H T (n+1) ((V ⊓ Z) ⊓ (W ⊓ Z)))) :
    Function.Surjective (fourConnecting T n U V W Z) := by
  have huv := union_zero T (Opens.mayerVietorisSquare U V) (n+1+1) hUV hU hV
  have hint := union_zero T (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W))
    (n+1) hUVW hUW hVW
  have huvw := union_zero T (CycleQ2ThreeOpenCechH2.outerSquare U V W)
    (n+1+1) hint huv hW
  intro y
  obtain ⟨z,hz⟩ := delta_surjective T (CycleQ2FourOpenH3.outerSquare U V W Z)
    (n+1+1) huvw hZ y
  obtain ⟨s,hs⟩ := triple_surjective T n (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
    hUZ hVZ hWZ hUVZ hUWZ hVWZ z
  exact ⟨s,(congrArg (delta T _ (n+1+1)) hs).trans hz⟩

end CycleQ2DerivedCoverTop

end

noncomputable section
namespace CycleQ2LiteralDerivedTop

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenMap freeOpenSections
  freeOpenSections_naturality)
open CycleQ2CechTwoToDerived (freeOpenSections_postcomp)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2LiteralThreefoldFirstDifferential (X structural FramedAffine framed_isBasis
  nativeFrame coeff)
open CycleQ2LiteralIntrinsicExterior (Literal Intrinsic comparison)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2LiteralThreefoldSecondDifferential (ordinaryExteriorIso secondDifferential)
open CycleQ2GeometricSectionDifferentials (sectionAlgebra)
open CycleQ2DerivedCoverTop (H)

local instance : SmoothOfRelativeDimension 3 structural :=
  CycleQ2LiteralAmbientSmooth.literal_fiber_smooth
local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

abbrev deRham := relativeDeRhamInt structural 3
abbrev target := DerivedCategory.Q.obj deRham

local instance : deRham.IsStrictlyGE 0 := by
  change ((relativeDeRham structural 3).extend (ComplexShape.embeddingUpIntGE 0)).IsStrictlySupported
    (ComplexShape.embeddingUpIntGE 0)
  infer_instance

def termIso (n : ℕ) : deRham.X (n : ℤ) ≅ Literal n :=
  (relativeDeRham structural 3).extendXIso (ComplexShape.embeddingUpIntGE 0)
    (Int.zero_add _) ≪≫ comparison n

def coefficients (W : X.Opens) (n : ℕ) :
    Sections (deRham.X (n : ℤ)) W ≃+ Sections (Literal n) W :=
  (((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (termIso n)).app (op W)).addCommGroupIsoToAddEquiv

theorem coefficients_restrict {U V : X.Opens} (h : U ≤ V) (n : ℕ)
    (s : Sections (deRham.X (n : ℤ)) V) :
    coefficients U n (res _ h s) = res _ h (coefficients V n s) :=
  NatTrans.naturality_apply (termIso n).hom.hom (homOfLE h).op s

theorem literal_above (W : X.Opens) (n : ℕ) (hn : 3 < n)
    (s : Sections (Literal n) W) : s = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext (Literal n).property
  intro x hx
  obtain ⟨_,⟨V,rfl⟩,hxV,hVW⟩ := Opens.isBasis_iff_nbhd.mp framed_isBasis hx
  refine ⟨V.carrier,hVW,hxV,?_⟩
  letI := sectionAlgebra X.sheaf coeff V.carrier
  have hz := CycleQ2SurfaceDeRhamChart.exterior_subsingleton (nativeFrame V) hn
  apply (ordinaryExteriorIso V n).symm.injective
  exact hz.elim _ _

theorem term_above (W : X.Opens) (n : ℕ) (hn : 3 < n)
    (s : Sections (deRham.X (n : ℤ)) W) : s = 0 := by
  apply (coefficients W n).injective
  rw [map_zero]
  exact literal_above W n hn _

theorem affine_above {W : X.Opens} (hW : IsAffineOpen W) (n : ℕ) (hn : 3 < n) :
    Subsingleton (H target (n : ℤ) W) := by
  let P := freeOpen W
  have terms := CycleQ2AffineExteriorComparison.term_acyclic structural 3 hW
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨a,ha,rfl⟩ := CycleQ2AcyclicSectionRepresentatives.surjective P deRham 0 terms (n : ℤ) y
  have ha₀ : a = 0 := by
    apply (freeOpenSections _ W).injective
    rw [map_zero]
    exact term_above W n hn _
  apply (CycleQ2AcyclicSectionRepresentatives.zero_iff P deRham 0 terms (n : ℤ) a ha).mpr
  exact ⟨0,by rw [zero_comp,ha₀]⟩

def representative (W : X.Opens) : Sections (Literal 3) W →+ (freeOpen W ⟶ deRham.X 3) :=
  (freeOpenSections _ W).symm.toAddMonoidHom.comp (coefficients W 3).symm.toAddMonoidHom

theorem representative_sections (W : X.Opens) (s : Sections (Literal 3) W) :
    freeOpenSections _ W (representative W s) = (coefficients W 3).symm s :=
  (freeOpenSections _ W).apply_symm_apply _

theorem representative_closed (W : X.Opens) (s : Sections (Literal 3) W) :
    representative W s ≫ deRham.d 3 4 = 0 := by
  apply (freeOpenSections _ W).injective
  rw [map_zero]
  exact term_above W 4 (by decide) _

private def rawClass (W : X.Opens) (s : Sections (Literal 3) W) : H target 3 W :=
  CycleQ2KInjectiveSections.closedClass (freeOpen W) deRham 3
    (representative W s) (representative_closed W s)

private theorem rawClass_sub (W : X.Opens) (s t : Sections (Literal 3) W) :
    rawClass W (s-t) = rawClass W s - rawClass W t := by
  unfold rawClass
  rw [map_sub]
  exact CycleQ2AcyclicSectionRepresentatives.closedClass_sub (K := deRham) (freeOpen W) 3
    (representative W s) (representative W t) (representative_closed W s) (representative_closed W t)

/-- A literal three-form defines its actual derived de Rham class. -/
def localTop (W : X.Opens) : Sections (Literal 3) W →+ H target 3 W :=
  AddMonoidHom.mk' (rawClass W) (by
    intro s t
    have h := rawClass_sub W (s+t) t
    rw [add_sub_cancel_right] at h
    exact eq_add_of_sub_eq h.symm)

theorem localTop_surjective {W : X.Opens} (hW : IsAffineOpen W) :
    Function.Surjective (localTop W) := by
  intro y
  have terms := CycleQ2AffineExteriorComparison.term_acyclic structural 3 hW
  obtain ⟨a,ha,hy⟩ := CycleQ2AcyclicSectionRepresentatives.surjective
    (freeOpen W) deRham 0 terms 3 y
  refine ⟨coefficients W 3 (freeOpenSections _ W a),?_⟩
  have hr : representative W (coefficients W 3 (freeOpenSections _ W a)) = a := by
    change (freeOpenSections _ W).symm
      ((coefficients W 3).symm (coefficients W 3 (freeOpenSections _ W a))) = a
    rw [AddEquiv.symm_apply_apply,AddEquiv.symm_apply_apply]
  change CycleQ2KInjectiveSections.closedClass _ deRham 3 _ _ = y
  simpa only [hr] using hy

theorem differential_two : deRham.d 2 3 =
    (termIso 2).hom ≫ secondDifferential ≫ (termIso 3).inv := by
  let a := (relativeDeRham structural 3).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add 2)
  let b := (relativeDeRham structural 3).extendXIso (ComplexShape.embeddingUpIntGE 0) (Int.zero_add 3)
  have hd : deRham.d 2 3 = a.hom ≫
      CycleQ2IntrinsicDeRhamSheaves.differential structural 3 2 ≫ b.inv :=
    (relativeDeRham structural 3).extend_d_eq (ComplexShape.embeddingUpIntGE 0)
      (Int.zero_add 2) (Int.zero_add 3)
  rw [hd]
  change a.hom ≫ _ ≫ b.inv =
    (a.hom ≫ (comparison 2).hom) ≫ secondDifferential ≫ ((comparison 3).inv ≫ b.inv)
  simp only [Category.assoc]
  rw [reassoc_of% CycleQ2LiteralIntrinsicExterior.comparison_secondDifferential,
    Iso.hom_inv_id_assoc]

theorem coefficients_differential_two (W : X.Opens) (s : Sections (deRham.X 2) W) :
    coefficients W 3 ((deRham.d 2 3).hom.app (op W) s) =
      secondDifferential.hom.app (op W) (coefficients W 2 s) := by
  have hd : deRham.d 2 3 ≫ (termIso 3).hom = (termIso 2).hom ≫ secondDifferential := by
    rw [differential_two]
    simp only [Category.assoc,Iso.inv_hom_id_assoc]
  exact ConcreteCategory.congr_hom (congrArg (fun f => f.hom.app (op W)) hd) s

theorem localTop_eq_zero_iff {W : X.Opens} (hW : IsAffineOpen W)
    (s : Sections (Literal 3) W) : localTop W s = 0 ↔
      ∃ t : Sections (Literal 2) W, secondDifferential.hom.app (op W) t = s := by
  have terms := CycleQ2AffineExteriorComparison.term_acyclic structural 3 hW
  change CycleQ2KInjectiveSections.closedClass _ deRham 3 _ _ = 0 ↔ _
  rw [CycleQ2AcyclicSectionRepresentatives.zero_iff (freeOpen W) deRham 0 terms]
  constructor
  · rintro ⟨a,ha⟩
    refine ⟨coefficients W 2 (freeOpenSections _ W a),?_⟩
    rw [← coefficients_differential_two,freeOpenSections_postcomp,ha,representative_sections]
    exact (coefficients W 3).apply_symm_apply s
  · rintro ⟨t,ht⟩
    refine ⟨(freeOpenSections _ W).symm ((coefficients W 2).symm t),?_⟩
    apply (freeOpenSections _ W).injective
    apply (coefficients W 3).injective
    rw [representative_sections,← freeOpenSections_postcomp,coefficients_differential_two]
    simpa only [AddEquiv.apply_symm_apply] using ht

theorem representative_restrict {U V : X.Opens} (h : U ≤ V)
    (s : Sections (Literal 3) V) : representative U (res _ h s) =
      freeOpenMap h ≫ representative V s := by
  apply (freeOpenSections _ U).injective
  rw [representative_sections,freeOpenSections_naturality,representative_sections]
  apply (coefficients U 3).injective
  rw [AddEquiv.apply_symm_apply,coefficients_restrict,AddEquiv.apply_symm_apply]

theorem localTop_restrict {U V : X.Opens} (h : U ≤ V) (s : Sections (Literal 3) V) :
    CycleQ2DerivedCoverTop.restriction target 3 h (localTop V s) = localTop U (res _ h s) := by
  change _ = CycleQ2KInjectiveSections.closedClass _ deRham 3 (representative U (res _ h s)) _
  rw [representative_restrict]
  exact (CycleQ2KInjectiveSections.closedClass_precomp (freeOpen V) deRham (freeOpenMap h) 3
    (representative V s) (representative_closed V s)).symm

open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldTopTrace (Face Torus face_affine)
open CycleQ2ThreeOpenCechH2 (TripleOpen)
open CycleQ2FourOpenH3 (QuadOpen)
open CycleQ2CechTwoToDerived (Two Three d2 app app_res)
open CycleQ2GeometricSheafLocalIso (res_comp res_self)

private abbrev Quad := QuadOpen (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3)
private abbrev Union := ((fixedOpen 0 ⊔ fixedOpen 1) ⊔ fixedOpen 2) ⊔ fixedOpen 3

private theorem vertex_affine (i : Fin 4) : IsAffineOpen (fixedOpen i) := by
  simpa only [Face,Finset.inf_singleton] using face_affine {i} (by simp)

private theorem pair_affine (i j : Fin 4) : IsAffineOpen (fixedOpen i ⊓ fixedOpen j) := by
  simpa only [Face,Finset.inf_insert,Finset.inf_singleton] using face_affine {i,j} (by simp)

private theorem triple_affine (i j k : Fin 4) :
    IsAffineOpen (TripleOpen (fixedOpen i) (fixedOpen j) (fixedOpen k)) := by
  have he : TripleOpen (fixedOpen i) (fixedOpen j) (fixedOpen k) = Face {i,j,k} := by
    simp only [TripleOpen,Face,Finset.inf_insert,Finset.inf_singleton,
      inf_assoc,inf_left_comm,inf_comm,inf_idem]
  rw [he]
  exact face_affine _ (by simp)

private theorem quad_eq_torus : Quad = Torus := by
  have hu : (Finset.univ : Finset (Fin 4)) = {0,1,2,3} := by decide
  simp only [Quad,QuadOpen,TripleOpen,Torus,Face,hu,Finset.inf_insert,Finset.inf_singleton,
    inf_assoc,inf_left_comm,inf_comm,inf_idem]

private theorem quad_affine : IsAffineOpen Quad := by
  rw [quad_eq_torus]
  exact face_affine _ (by simp)

private theorem union_eq_top : Union = ⊤ := by
  apply le_antisymm le_top
  rw [← fixedOpen_cover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private theorem ordered_triple_eq (i j k : Fin 4) :
    (fixedOpen i ⊓ fixedOpen j) ⊓ fixedOpen k =
      TripleOpen (fixedOpen i) (fixedOpen j) (fixedOpen k) := by
  simp only [TripleOpen,inf_assoc,inf_left_comm,inf_comm,inf_idem]

private theorem ordered_quad_eq :
    ((fixedOpen 0 ⊓ fixedOpen 1) ⊓ fixedOpen 2) ⊓ fixedOpen 3 = Quad := by
  simp only [Quad,QuadOpen,TripleOpen,inf_assoc,inf_left_comm,inf_comm,inf_idem]

private def sectionsEquivOfEq (F : AbSheaf (show TopCat from X))
    {U V : X.Opens} (h : U = V) : Sections F U ≃+ Sections F V where
  toFun := res F h.ge
  invFun := res F h.le
  left_inv s := by rw [res_comp,res_self]
  right_inv s := by rw [res_comp,res_self]
  map_add' a b := map_add (res F h.ge) a b

def quadSections (F : AbSheaf (show TopCat from X)) : Three F fixedOpen ≃+ Sections F Quad :=
  sectionsEquivOfEq F ordered_quad_eq

private def quadFaces (F : AbSheaf (show TopCat from X)) : Two F fixedOpen ≃+
    CycleQ2FourOpenH3.TripleSections F (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) :=
  AddEquiv.prodCongr (sectionsEquivOfEq F (ordered_triple_eq 0 1 2))
    (AddEquiv.prodCongr (sectionsEquivOfEq F (ordered_triple_eq 0 1 3))
      (AddEquiv.prodCongr (sectionsEquivOfEq F (ordered_triple_eq 0 2 3))
        (sectionsEquivOfEq F (ordered_triple_eq 1 2 3))))

private theorem quadSections_boundary (F : AbSheaf (show TopCat from X)) (c : Two F fixedOpen) :
    quadSections F (d2 F fixedOpen c) = CycleQ2FourOpenH3.boundary F
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) (quadFaces F c) := by
  change res F _ (res F _ c.2.2.2 - res F _ c.2.2.1 + res F _ c.2.1 - res F _ c.1) =
    res F _ (res F _ c.2.2.2) - res F _ (res F _ c.2.2.1) +
      res F _ (res F _ c.2.1) - res F _ (res F _ c.1)
  simp only [map_sub,map_add,res_comp]

private def faceClasses (c : Two (Literal 3) fixedOpen) :
    CycleQ2DerivedCoverTop.TripleClasses target 3
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) :=
  (localTop _ (quadFaces (Literal 3) c).1,localTop _ (quadFaces (Literal 3) c).2.1,
    localTop _ (quadFaces (Literal 3) c).2.2.1,localTop _ (quadFaces (Literal 3) c).2.2.2)

private theorem faceClasses_surjective : Function.Surjective faceClasses := by
  rintro ⟨a,b,c,d⟩
  obtain ⟨a,rfl⟩ := localTop_surjective (triple_affine 0 1 2) a
  obtain ⟨b,rfl⟩ := localTop_surjective (triple_affine 0 1 3) b
  obtain ⟨c,rfl⟩ := localTop_surjective (triple_affine 0 2 3) c
  obtain ⟨d,rfl⟩ := localTop_surjective (triple_affine 1 2 3) d
  refine ⟨(quadFaces (Literal 3)).symm (a,b,c,d),?_⟩
  simp only [faceClasses,AddEquiv.apply_symm_apply]

private theorem localTop_quad_boundary (c : Two (Literal 3) fixedOpen) :
    localTop Quad (quadSections (Literal 3) (d2 (Literal 3) fixedOpen c)) =
      CycleQ2DerivedCoverTop.fourBoundary target 3
        (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) (faceClasses c) := by
  rw [quadSections_boundary]
  change localTop Quad (res _ _ (quadFaces (Literal 3) c).2.2.2 -
      res _ _ (quadFaces (Literal 3) c).2.2.1 + res _ _ (quadFaces (Literal 3) c).2.1 -
      res _ _ (quadFaces (Literal 3) c).1) = _
  simp only [map_sub,map_add,← localTop_restrict] <;> rfl

theorem quadSections_differential (s : Three (Literal 2) fixedOpen) :
    quadSections (Literal 3) (app secondDifferential _ s) =
      app secondDifferential Quad (quadSections (Literal 2) s) :=
  (app_res secondDifferential ordered_quad_eq.ge s).symm

/-- Three original source boundaries take a literal top Čech section
to an actual global derived de Rham class in degree six. -/
def connectingSection : Three (Literal 3) fixedOpen →+ H target 6 ⊤ :=
  (CycleQ2DerivedCoverTop.restrictionEquiv target 6 union_eq_top).toAddMonoidHom.comp
    ((CycleQ2DerivedCoverTop.fourConnecting target 3
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3)).comp
        ((localTop Quad).comp (quadSections (Literal 3)).toAddMonoidHom))

private theorem four_surjective : Function.Surjective
    (CycleQ2DerivedCoverTop.fourConnecting target 3
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3)) :=
  CycleQ2DerivedCoverTop.four_surjective target 3 _ _ _ _
    (affine_above (vertex_affine 0) 6 (by decide)) (affine_above (vertex_affine 1) 6 (by decide))
    (affine_above (vertex_affine 2) 6 (by decide)) (affine_above (vertex_affine 3) 6 (by decide))
    (affine_above (pair_affine 0 1) 5 (by decide)) (affine_above (pair_affine 0 2) 5 (by decide))
    (affine_above (pair_affine 1 2) 5 (by decide)) (affine_above (pair_affine 0 3) 5 (by decide))
    (affine_above (pair_affine 1 3) 5 (by decide)) (affine_above (pair_affine 2 3) 5 (by decide))
    (affine_above (triple_affine 0 1 2) 4 (by decide))
    (affine_above (triple_affine 0 1 3) 4 (by decide))
    (affine_above (triple_affine 0 2 3) 4 (by decide))
    (affine_above (triple_affine 1 2 3) 4 (by decide))

theorem connectingSection_surjective : Function.Surjective connectingSection :=
  (CycleQ2DerivedCoverTop.restrictionEquiv target 6 union_eq_top).surjective.comp
    (four_surjective.comp ((localTop_surjective quad_affine).comp
      (quadSections (Literal 3)).surjective))

private theorem four_eq_zero_iff (s : H target 3 Quad) :
    CycleQ2DerivedCoverTop.fourConnecting target 3
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) s = 0 ↔
    ∃ a, CycleQ2DerivedCoverTop.fourBoundary target 3
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3) a = s :=
  CycleQ2DerivedCoverTop.four_eq_zero_iff target 3 _ _ _ _
    (affine_above (vertex_affine 0) 5 (by decide)) (affine_above (vertex_affine 1) 5 (by decide))
    (affine_above (vertex_affine 2) 5 (by decide)) (affine_above (vertex_affine 3) 5 (by decide))
    (affine_above (pair_affine 0 1) 4 (by decide)) (affine_above (pair_affine 0 2) 4 (by decide))
    (affine_above (pair_affine 1 2) 4 (by decide)) (affine_above (pair_affine 0 3) 4 (by decide))
    (affine_above (pair_affine 1 3) 4 (by decide)) (affine_above (pair_affine 2 3) 4 (by decide)) s

theorem connectingSection_cech (c : Two (Literal 3) fixedOpen) :
    connectingSection (d2 (Literal 3) fixedOpen c) = 0 := by
  change (CycleQ2DerivedCoverTop.restrictionEquiv target 6 union_eq_top)
    (CycleQ2DerivedCoverTop.fourConnecting target 3 _ _ _ _
      (localTop Quad (quadSections (Literal 3) (d2 (Literal 3) fixedOpen c)))) = 0
  rw [localTop_quad_boundary,CycleQ2DerivedCoverTop.four_boundary_zero,map_zero]

theorem connectingSection_exterior (s : Three (Literal 2) fixedOpen) :
    connectingSection (app secondDifferential _ s) = 0 := by
  change (CycleQ2DerivedCoverTop.restrictionEquiv target 6 union_eq_top)
    (CycleQ2DerivedCoverTop.fourConnecting target 3 _ _ _ _
      (localTop Quad (quadSections (Literal 3) (app secondDifferential _ s)))) = 0
  rw [quadSections_differential]
  have hs := (localTop_eq_zero_iff quad_affine
    (app secondDifferential Quad (quadSections (Literal 2) s))).mpr
      ⟨quadSections (Literal 2) s,rfl⟩
  rw [hs,map_zero,map_zero]

theorem connectingSection_differentialFive
    (b : CycleQ2FourOpenDeRhamTotal.TotalFive fixedOpen (Literal 2) (Literal 3)) :
    connectingSection (CycleQ2FourOpenDeRhamTotal.differentialFive fixedOpen secondDifferential b) = 0 := by
  change connectingSection (d2 (Literal 3) fixedOpen b.1 - app secondDifferential _ b.2) = 0
  rw [map_sub,connectingSection_cech,connectingSection_exterior,sub_self]

/-- The exact kernel is the degree-five differential of the original
finite Čech--de Rham total complex, including its minus sign on dΩ². -/
theorem connectingSection_eq_zero_iff (s : Three (Literal 3) fixedOpen) :
    connectingSection s = 0 ↔
    ∃ b : CycleQ2FourOpenDeRhamTotal.TotalFive fixedOpen (Literal 2) (Literal 3),
      CycleQ2FourOpenDeRhamTotal.differentialFive fixedOpen secondDifferential b = s := by
  constructor
  · intro hs
    have hfour : CycleQ2DerivedCoverTop.fourConnecting target 3 _ _ _ _
        (localTop Quad (quadSections (Literal 3) s)) = 0 := by
      apply (CycleQ2DerivedCoverTop.restrictionEquiv target 6 union_eq_top).injective
      simpa only [map_zero] using hs
    obtain ⟨a,ha⟩ := (four_eq_zero_iff _).mp hfour
    obtain ⟨c,hc⟩ := faceClasses_surjective a
    have he : localTop Quad
        (quadSections (Literal 3) (s - d2 (Literal 3) fixedOpen c)) = 0 := by
      rw [map_sub,map_sub,localTop_quad_boundary,hc,ha,sub_self]
    obtain ⟨η,hη⟩ := (localTop_eq_zero_iff quad_affine _).mp he
    let t := (quadSections (Literal 2)).symm η
    have ht : app secondDifferential _ t = s - d2 (Literal 3) fixedOpen c := by
      apply (quadSections (Literal 3)).injective
      rw [quadSections_differential]
      change app secondDifferential Quad
        (quadSections (Literal 2) ((quadSections (Literal 2)).symm η)) = _
      rw [AddEquiv.apply_symm_apply]
      exact hη
    refine ⟨(c,-t),?_⟩
    change d2 (Literal 3) fixedOpen c - app secondDifferential _ (-t) = s
    rw [map_neg,ht]
    abel
  · rintro ⟨b,rfl⟩
    exact connectingSection_differentialFive b

end CycleQ2LiteralDerivedTop
end

noncomputable section
namespace CycleQ2LiteralTopDeRhamTrace

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2CechTwoToDerived (Three)
open CycleQ2LiteralAmbientCharts (fixedOpen)
open CycleQ2LiteralThreefoldFirstDifferential (X)
open CycleQ2LiteralThreefoldSecondDifferential (secondDifferential)
open CycleQ2LiteralDerivedTop (target connectingSection)

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

theorem sectionClass_surjective : Function.Surjective sectionClass := by
  intro x
  obtain ⟨z,hz⟩ := QuotientAddGroup.mk_surjective (homologyCoordinates x)
  refine ⟨z.val,homologyCoordinates.injective ?_⟩
  change homologyCoordinates (homologyCoordinates.symm (QuotientAddGroup.mk (topCycle z.val))) = _
  rw [AddEquiv.apply_symm_apply]
  have he : topCycle z.val = z := Subtype.ext rfl
  exact (congrArg QuotientAddGroup.mk he).trans hz

theorem sectionClass_eq_zero_iff (s : Three F fixedOpen) : sectionClass s = 0 ↔
    ∃ b : CycleQ2FourOpenDeRhamTotal.TotalFive fixedOpen
      (CycleQ2LiteralIntrinsicExterior.Literal 2) F,
      CycleQ2FourOpenDeRhamTotal.differentialFive fixedOpen secondDifferential b = s := by
  have hzero : sectionClass s = 0 ↔
      (QuotientAddGroup.mk (topCycle s) : topShort.g.hom.ker ⧸ topShort.abToCycles.range) = 0 := by
    change homologyCoordinates.symm _ = 0 ↔ _
    rw [← map_zero homologyCoordinates.symm]
    exact homologyCoordinates.symm.injective.eq_iff
  rw [hzero,QuotientAddGroup.eq_zero_iff]
  change (∃ b,topShort.abToCycles b = topCycle s) ↔ _
  refine exists_congr fun b => ?_
  rw [Subtype.ext_iff]
  change complex.d 5 6 b = s ↔ _
  rw [CycleQ2FourOpenDeRhamTotal.complex_d] <;> rfl

private def quotientDerived :
    (topShort.g.hom.ker ⧸ topShort.abToCycles.range) →+
      CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  QuotientAddGroup.lift topShort.abToCycles.range
    (connectingSection.comp topShort.g.hom.ker.subtype) (by
      rintro _ ⟨b,rfl⟩
      change connectingSection (complex.d 5 6 b) = 0
      rw [CycleQ2FourOpenDeRhamTotal.complex_d]
      exact CycleQ2LiteralDerivedTop.connectingSection_differentialFive b)

/-- The comparison is induced by the original three source
Mayer--Vietoris boundaries, applied to the actual top-form class. -/
def toDerived : complex.homology 6 →+ CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  quotientDerived.comp homologyCoordinates.toAddMonoidHom

theorem toDerived_sectionClass (s : Three F fixedOpen) :
    toDerived (sectionClass s) = connectingSection s := by
  change quotientDerived
    (homologyCoordinates (homologyCoordinates.symm (QuotientAddGroup.mk (topCycle s)))) = _
  rw [AddEquiv.apply_symm_apply]
  rfl

theorem toDerived_bijective : Function.Bijective toDerived := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    obtain ⟨s,rfl⟩ := sectionClass_surjective x
    rw [toDerived_sectionClass] at hx
    exact (sectionClass_eq_zero_iff s).mpr
      ((CycleQ2LiteralDerivedTop.connectingSection_eq_zero_iff s).mp hx)
  · intro y
    obtain ⟨s,hs⟩ := CycleQ2LiteralDerivedTop.connectingSection_surjective y
    exact ⟨sectionClass s,(toDerived_sectionClass s).trans hs⟩

/-- The complete degree-six homology of the original finite total
complex is actual global derived de Rham cohomology of the fixed fiber. -/
def derivedEquiv : complex.homology 6 ≃+ CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  AddEquiv.ofBijective toDerived toDerived_bijective

/-- The native Laurent trace on actual global derived de Rham degree six. -/
def derivedTrace : CycleQ2DerivedCoverTop.H target 6 ⊤ →+ ℂ :=
  trace.comp derivedEquiv.symm.toAddMonoidHom

def derivedNormalizedClass (a : ℂ) : CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  derivedEquiv (normalizedClass a)

/-- The original normalized generator is sent to its actual three
Mayer--Vietoris image; no independent choice of a derived generator is made. -/
theorem derivedNormalizedClass_eq_connecting (a : ℂ) :
    derivedNormalizedClass a = connectingSection (generator a) :=
  toDerived_sectionClass (generator a)

theorem derivedTrace_normalizedClass (a : ℂ) :
    derivedTrace (derivedNormalizedClass a) = a := by
  change trace (derivedEquiv.symm (derivedEquiv (normalizedClass a))) = a
  rw [AddEquiv.symm_apply_apply,trace_normalizedClass]

theorem derivedTrace_connecting_generator (a : ℂ) :
    derivedTrace (connectingSection (generator a)) = a := by
  rw [← derivedNormalizedClass_eq_connecting,derivedTrace_normalizedClass]

theorem derivedNormalizedClass_one_ne_zero : derivedNormalizedClass 1 ≠ 0 := by
  intro h
  have hh := congrArg derivedTrace h
  rw [derivedTrace_normalizedClass,map_zero] at hh
  exact one_ne_zero hh

end CycleQ2LiteralTopDeRhamTrace
end

#print axioms CycleQ2LiteralDerivedTop.localTop_eq_zero_iff
#print axioms CycleQ2LiteralDerivedTop.connectingSection_eq_zero_iff
#print axioms CycleQ2LiteralTopDeRhamTrace.derivedEquiv
#print axioms CycleQ2LiteralTopDeRhamTrace.derivedTrace_connecting_generator
#print axioms CycleQ2LiteralTopDeRhamTrace.derivedNormalizedClass_one_ne_zero
