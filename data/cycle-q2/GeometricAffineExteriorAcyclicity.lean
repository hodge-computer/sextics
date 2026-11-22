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

/-! The top-form edge map below is composition with the actual last
term of the intrinsic de Rham complex. Its compatibility with the
original source Mayer--Vietoris maps fixes the derived trace on every
canonical H³ class, including the signed cubic residue class. -/

noncomputable section
namespace CycleQ2LiteralDerivedTop

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf Sections freeOpen freeOpenSections freeOpenMap)
open CycleQ2CechTwoToDerived (Three sectionExtZero freeOpenSections_postcomp)
open CycleQ2LiteralIntrinsicExterior (Literal)
open CycleQ2LiteralThreefoldFirstDifferential (X)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0

private theorem top_closed : (termIso 3).inv ≫ deRham.d 3 4 = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  intro W
  apply ConcreteCategory.hom_ext
  intro s
  change _ = 0
  exact term_above W.unop 4 (by decide) _

/-- The actual top-term inclusion, with its original intrinsic-to-literal
normalization, regarded as a derived morphism of degree three. -/
def topInclusion : E.obj (Literal 3) ⟶ target⟦(3 : ℤ)⟧ :=
  CycleQ2KInjectiveSections.closedClass (Literal 3) deRham 3 (termIso 3).inv top_closed

private def topPostAt (P : AbSheaf (show TopCat from X)) (n : ℕ) (m : ℤ)
    (h : 3 + (n : ℤ) = m) :
    Ext P (Literal 3) n →+ (E.obj P ⟶ target⟦m⟧) where
  toFun a := a.hom.comp topInclusion h
  map_zero' := by simp only [Ext.zero_hom,ShiftedHom.zero_comp]
  map_add' a b := by simp only [Ext.add_hom,ShiftedHom.add_comp]

/-- The top-form edge map is actual shifted composition, not a choice
of a scalar multiple of a generator. -/
def topPost (n : ℕ) (W : X.Opens) :
    (Literal 3).H' n W →+ CycleQ2DerivedCoverTop.H target (3 + (n : ℤ)) W :=
  topPostAt (freeOpen W) n (3 + (n : ℤ)) rfl

private theorem representative_eq_post (W : X.Opens) (s : Sections (Literal 3) W) :
    representative W s = (freeOpenSections (Literal 3) W).symm s ≫ (termIso 3).inv := by
  apply (freeOpenSections _ W).injective
  rw [representative_sections,← freeOpenSections_postcomp,AddEquiv.apply_symm_apply]
  rfl

theorem topPost_section (W : X.Opens) (s : Sections (Literal 3) W) :
    topPost 0 W (sectionExtZero W s) = localTop W s := by
  change (Ext.mk₀ ((freeOpenSections (Literal 3) W).symm s)).hom.comp topInclusion _ = _
  rw [Ext.mk₀_hom,ShiftedHom.mk₀_comp]
  symm
  change CycleQ2KInjectiveSections.closedClass (freeOpen W) deRham 3
    (representative W s) _ = _
  rw [representative_eq_post]
  exact CycleQ2KInjectiveSections.closedClass_precomp (Literal 3) deRham
    ((freeOpenSections (Literal 3) W).symm s) 3 (termIso 3).inv top_closed

private theorem topPostAt_precomp {P Q : AbSheaf (show TopCat from X)}
    (f : Q ⟶ P) (n : ℕ) (m : ℤ) (h : 3 + (n : ℤ) = m)
    (a : Ext P (Literal 3) n) :
    topPostAt Q n m h ((Ext.mk₀ f).comp a (zero_add n)) =
      E.map f ≫ topPostAt P n m h a := by
  change ((Ext.mk₀ f).comp a (zero_add n)).hom.comp topInclusion h = _
  rw [Ext.comp_hom,Ext.mk₀_hom]
  simpa only [ShiftedHom.mk₀_comp] using
    (ShiftedHom.comp_assoc (ShiftedHom.mk₀ (0 : ℤ) rfl (E.map f)) a.hom topInclusion
      (add_zero _) h (by simpa only [add_zero] using h))

theorem topPost_restrict (n : ℕ) {U V : X.Opens} (h : U ≤ V)
    (a : (Literal 3).H' n V) :
    topPost n U (((Literal 3).cohomologyPresheaf n).map (homOfLE h).op a) =
      CycleQ2DerivedCoverTop.restriction target (3 + (n : ℤ)) h (topPost n V a) :=
  topPostAt_precomp (freeOpenMap h) n (3 + (n : ℤ)) rfl a

private theorem topPostAt_boundary {S : ShortComplex (AbSheaf (show TopCat from X))}
    (hS : S.ShortExact) {n n' : ℕ} (hn : 1 + n = n')
    (m : ℤ) (hm : 3 + (n : ℤ) = m) (a : Ext S.X₁ (Literal 3) n) :
    topPostAt S.X₃ n' (m+1) (by omega) (hS.extClass.comp a hn) =
      CycleQ2DerivedSourceBoundary.connecting hS target m (topPostAt S.X₁ n m hm a) := by
  change (hS.extClass.comp a hn).hom.comp topInclusion _ = _
  rw [Ext.comp_hom,hS.extClass_hom]
  calc
    (hS.singleδ.comp a.hom _).comp topInclusion _ =
        hS.singleδ.comp (a.hom.comp topInclusion hm) rfl :=
      ShiftedHom.comp_assoc hS.singleδ a.hom topInclusion (by omega) hm (by omega)
    _ = _ := by
      rw [ShiftedHom.comp,shiftFunctorAdd'_eq_shiftFunctorAdd]
      rfl

private theorem topPost_delta_zero
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (Literal 3).H' 0 S.X₁) :
    topPost 1 S.X₄ (S.δ (Literal 3) 0 1 rfl a) =
      CycleQ2DerivedCoverTop.delta target S 3 (topPost 0 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 3 rfl a

private theorem topPost_delta_one
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (Literal 3).H' 1 S.X₁) :
    topPost 2 S.X₄ (S.δ (Literal 3) 1 2 rfl a) =
      CycleQ2DerivedCoverTop.delta target S 4 (topPost 1 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 4 rfl a

private theorem topPost_delta_two
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) (a : (Literal 3).H' 2 S.X₁) :
    topPost 3 S.X₄ (S.δ (Literal 3) 2 3 rfl a) =
      CycleQ2DerivedCoverTop.delta target S 5 (topPost 2 S.X₁ a) :=
  topPostAt_boundary S.shortComplex_shortExact rfl 5 rfl a

theorem topPost_four (U V W Z : X.Opens)
    (s : Sections (Literal 3) (CycleQ2FourOpenH3.QuadOpen U V W Z)) :
    topPost 3 (((U ⊔ V) ⊔ W) ⊔ Z) (CycleQ2FourOpenH3.connecting (Literal 3) U V W Z s) =
      CycleQ2DerivedCoverTop.fourConnecting target 3 U V W Z
        (localTop (CycleQ2FourOpenH3.QuadOpen U V W Z) s) := by
  let S := CycleQ2FourOpenH3.outerSquare U V W Z
  let R := CycleQ2ThreeOpenCechH2.outerSquare (U ⊓ Z) (V ⊓ Z) (W ⊓ Z)
  let Q := Opens.mayerVietorisSquare ((U ⊓ Z) ⊓ (W ⊓ Z)) ((V ⊓ Z) ⊓ (W ⊓ Z))
  change topPost 3 S.X₄
    (S.δ (Literal 3) 2 3 rfl (R.δ (Literal 3) 1 2 rfl (Q.δ (Literal 3) 0 1 rfl
      ((CycleQ2GeometricConeCech.HZero.sectionsEquiv (Literal 3) Q.X₁).symm s)))) = _
  rw [topPost_delta_two,topPost_delta_one,topPost_delta_zero,
    ← CycleQ2ThreeOpenInjectiveComparison.sectionExtZero_eq_hzero,topPost_section]
  rfl

/-- The actual top-term inclusion commutes with the same ordered three
source boundaries used in the literal residue calculation. -/
theorem topPost_orderedConnecting (s : Three (Literal 3) fixedOpen) :
    topPost 3 ⊤ (CycleQ2FourOpenTopMayerVietoris.orderedConnecting fixedOpen fixedOpen_cover s) =
      connectingSection s := by
  change topPost 3 ⊤ (((Literal 3).cohomologyPresheaf 3).map (homOfLE union_eq_top.ge).op
    (CycleQ2FourOpenH3.connecting (Literal 3)
      (fixedOpen 0) (fixedOpen 1) (fixedOpen 2) (fixedOpen 3)
      (quadSections (Literal 3) s))) = _
  rw [topPost_restrict,topPost_four]
  rfl

end CycleQ2LiteralDerivedTop

namespace CycleQ2LiteralTopDeRhamTrace

open CategoryTheory Opposite TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2CechTwoToDerived (Three)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldFirstDifferential (X)
open CycleQ2LiteralThreefoldCanonicalFrame (CanonicalForms CanonicalAdditiveSheaf globalFrame)
open CycleQ2LiteralThreefoldTopTrace
  (canonicalTrace canonicalTrace_connecting framed_face_acyclic canonicalSectionTrace)
open CycleQ2LiteralDerivedTop (target topPost connectingSection)
open CycleQ2HodgeTwistTopDerived
  (nativeTopOrdered nativeTopConnecting nativeTopConnecting_surjective orderedConnecting_nativeTopOrdered)

local instance : HasExt.{1} (AbSheaf (show TopCat from X)) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

theorem derivedTrace_connectingSection (s : Three F fixedOpen) :
    derivedTrace (connectingSection s) = sectionTrace s := by
  rw [← toDerived_sectionClass]
  change trace (derivedEquiv.symm (derivedEquiv (sectionClass s))) = sectionTrace s
  rw [AddEquiv.symm_apply_apply,trace_sectionClass]

/-- On every actual canonical H³ class, composition with the top de
Rham term preserves the original native trace exactly. -/
theorem derivedTrace_topPost (a : CanonicalAdditiveSheaf.H' 3 ⊤) :
    derivedTrace (topPost 3 ⊤ a) = canonicalTrace a := by
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective CanonicalAdditiveSheaf fixedOpen fixedOpen_cover
    (framed_face_acyclic CanonicalForms globalFrame) a
  calc
    derivedTrace (topPost 3 ⊤ (nativeTopConnecting CanonicalAdditiveSheaf fixedOpen fixedOpen_cover s)) =
        derivedTrace (connectingSection (nativeTopOrdered F fixedOpen s)) := by
      apply congrArg derivedTrace
      rw [← orderedConnecting_nativeTopOrdered]
      exact CycleQ2LiteralDerivedTop.topPost_orderedConnecting _
    _ = canonicalSectionTrace s := by
      rw [derivedTrace_connectingSection]
      change canonicalSectionTrace (toNative F (nativeTopOrdered F fixedOpen s)) = canonicalSectionTrace s
      rw [toNative_nativeTopOrdered]
    _ = canonicalTrace (nativeTopConnecting CanonicalAdditiveSheaf fixedOpen fixedOpen_cover s) :=
      (canonicalTrace_connecting s).symm

theorem topPost_canonicalClass (a : ℂ) :
    topPost 3 ⊤ (CycleQ2LiteralThreefoldTopTrace.canonicalClass a) = derivedNormalizedClass a := by
  rw [derivedNormalizedClass_eq_connecting]
  change topPost 3 ⊤ (nativeTopConnecting CanonicalAdditiveSheaf fixedOpen fixedOpen_cover
    (CycleQ2LiteralThreefoldTopTrace.framedGenerator CanonicalForms globalFrame a)) = _
  rw [← orderedConnecting_nativeTopOrdered]
  exact CycleQ2LiteralDerivedTop.topPost_orderedConnecting _

theorem topPost_injective : Function.Injective (topPost 3 (⊤ : X.Opens)) := by
  intro a b hab
  apply canonicalTrace.injective
  rw [← derivedTrace_topPost,← derivedTrace_topPost,hab]

/-- A nonzero original canonical cohomology class remains nonzero in
the full actual derived de Rham complex. -/
theorem topPost_ne_zero (a : CanonicalAdditiveSheaf.H' 3 ⊤) (ha : a ≠ 0) :
    topPost 3 ⊤ a ≠ 0 := by
  intro hz
  exact ha (topPost_injective (by simpa only [map_zero] using hz))

end CycleQ2LiteralTopDeRhamTrace
end

#print axioms CycleQ2LiteralDerivedTop.topInclusion
#print axioms CycleQ2LiteralDerivedTop.topPost_orderedConnecting
#print axioms CycleQ2LiteralTopDeRhamTrace.derivedTrace_topPost
#print axioms CycleQ2LiteralTopDeRhamTrace.topPost_ne_zero

noncomputable section
namespace CycleQ2LiteralCubicDeRham

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literal_vertex_unit)
open CycleQ2HodgeThreefoldTwist (chartFrame chartFrame_transition)
open CycleQ2HodgeTwistAnchor (torus torus_le torus_le_face)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces NativeTopQuotient nativeTopBoundary nativeTopSectionTrace)
open CycleQ2HodgeTwistTopDerived
  (nativeTopConnecting nativeTopConnecting_surjective nativeTopCohomologyEquiv)
open CycleQ2LiteralAmbientCharts (fixedOpen fixedOpen_cover)
open CycleQ2LiteralThreefoldCanonicalFrame (CanonicalForms CanonicalAdditiveSheaf globalFrame)
open CycleQ2LiteralThreefoldTopTrace
  (Face Torus faceSectionEquiv faceSectionEquiv_restrict framed_face_acyclic
    framedSectionTrace_frame structureSectionTrace_pullback canonicalSectionTrace
    canonicalTrace canonicalTrace_connecting canonicalClass framedGenerator)
open CycleQ2LiteralCubicResidueDetection (ambientCover ambientCover_top)
open CycleQ2LiteralCubicProjectiveCocycle
  (RegularSheaf ambientResidueClass ambientResidueTrace ambientResidueTrace_class)
open CycleQ2LiteralDerivedTop (target topPost)
open CycleQ2LiteralTopDeRhamTrace
  (derivedTrace derivedNormalizedClass derivedTrace_topPost topPost_canonicalClass)

local instance (Y : TopCat.{0}) : HasExt.{1} (AbSheaf Y) := HasExt.standard _
local instance : HasDerivedCategory.{1}
    (AbSheaf (show TopCat from CycleQ2LiteralThreefoldFirstDifferential.X)) :=
  HasDerivedCategory.standard _

private theorem literal_torus_le_face (S : Finset (Fin 4)) : Torus ≤ Face S :=
  Finset.le_inf (fun i _ => Finset.inf_le (Finset.mem_univ i))

/-- The original zero-twist frame, inverse scheme-section pullback by
`literalIso`, and the unchanged global canonical frame give this map
on every actual nonempty standard intersection. -/
def coefficientSection (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) :
    Sections RegularSheaf (S.inf ambientCover) ≃+ Sections CanonicalAdditiveSheaf (Face S) :=
  (chartFrame literalEval 0 i (S.inf ambientCover) (Finset.inf_le hi)).toAddEquiv.trans
    ((faceSectionEquiv S).symm.toAddEquiv.trans
      (globalFrame.app (Face S) le_top).symm.toAddEquiv)

theorem coefficientSection_frame (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)
    (s : Sections RegularSheaf (S.inf ambientCover)) :
    globalFrame.app (Face S) le_top (coefficientSection i S hi s) =
      (faceSectionEquiv S).symm (chartFrame literalEval 0 i (S.inf ambientCover) (Finset.inf_le hi) s) :=
  (globalFrame.app (Face S) le_top).apply_symm_apply _

def coefficientTopSection :
    Sections RegularSheaf (torus literalEval) ≃+ Sections CanonicalAdditiveSheaf Torus :=
  coefficientSection 0 Finset.univ (Finset.mem_univ 0)

/-- The concrete face maps commute with the actual restrictions.
Changing the zero-twist anchor contributes exactly the unit 1. -/
theorem coefficientTopSection_restrict (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)
    (s : Sections RegularSheaf (S.inf ambientCover)) :
    coefficientTopSection (res RegularSheaf (torus_le_face literalEval S) s) =
      res CanonicalAdditiveSheaf (literal_torus_le_face S) (coefficientSection i S hi s) := by
  apply (globalFrame.app Torus le_top).injective
  change globalFrame.app Torus le_top
      (coefficientSection 0 Finset.univ (Finset.mem_univ 0) (res RegularSheaf _ s)) = _
  rw [coefficientSection_frame,← globalFrame.naturality,coefficientSection_frame]
  apply (faceSectionEquiv Finset.univ).injective
  rw [RingEquiv.apply_symm_apply,faceSectionEquiv_restrict,RingEquiv.apply_symm_apply]
  rw [chartFrame_transition literalEval 0 0 i (torus literalEval)
    (torus_le literalEval 0) (torus_le literalEval i)]
  simp only [zpow_zero,Units.val_one,one_mul]
  exact CycleQ2HodgeAtlasLine.coordinate_restrict
    (CycleQ2HodgeThreefoldTwist.cocycle literalEval 0)
    i (Finset.inf_le hi) (torus_le_face literalEval S) s

private def faceAnchor (i : Fin 4) : Fin 4 := if i = 0 then 1 else 0

private theorem faceAnchor_mem (i : Fin 4) : faceAnchor i ∈ Finset.univ.erase i := by
  fin_cases i <;> decide

private def coefficientFaces (c : NativeTopFaces (F := RegularSheaf) (U := ambientCover)) :
    NativeTopFaces (F := CanonicalAdditiveSheaf) (U := fixedOpen) :=
  fun i => coefficientSection (faceAnchor i) (Finset.univ.erase i) (faceAnchor_mem i) (c i)

theorem coefficientTopSection_boundary (c : NativeTopFaces (F := RegularSheaf) (U := ambientCover)) :
    coefficientTopSection (nativeTopBoundary c) = nativeTopBoundary (coefficientFaces c) := by
  change coefficientTopSection
    (res RegularSheaf (torus_le_face literalEval (Finset.univ.erase 0)) (c 0) -
      res RegularSheaf (torus_le_face literalEval (Finset.univ.erase 1)) (c 1) +
      res RegularSheaf (torus_le_face literalEval (Finset.univ.erase 2)) (c 2) -
      res RegularSheaf (torus_le_face literalEval (Finset.univ.erase 3)) (c 3)) = _
  rw [map_sub,map_add,map_sub,
    coefficientTopSection_restrict (faceAnchor 0) _ (faceAnchor_mem 0),
    coefficientTopSection_restrict (faceAnchor 1) _ (faceAnchor_mem 1),
    coefficientTopSection_restrict (faceAnchor 2) _ (faceAnchor_mem 2),
    coefficientTopSection_restrict (faceAnchor 3) _ (faceAnchor_mem 3)]
  rfl

/-- This quotient map is induced by the original scheme and frame
maps, with their proved compatibility with all four boundary faces. -/
def coefficientTopQuotient :
    NativeTopQuotient (F := RegularSheaf) (U := ambientCover) →+
      NativeTopQuotient (F := CanonicalAdditiveSheaf) (U := fixedOpen) :=
  QuotientAddGroup.map _ _ coefficientTopSection.toAddMonoidHom (by
    rintro _ ⟨c,rfl⟩
    exact ⟨coefficientFaces c,(coefficientTopSection_boundary c).symm⟩)

private def sourceComparison := nativeTopCohomologyEquiv RegularSheaf ambientCover ambientCover_top
  (CycleQ2HodgeTwistTopCohomology.twist_face_acyclic literalEval 0)

private def canonicalComparison := nativeTopCohomologyEquiv CanonicalAdditiveSheaf fixedOpen
  fixedOpen_cover (framed_face_acyclic CanonicalForms globalFrame)

/-- Actual native Čech transport followed by the two original
Mayer--Vietoris comparisons gives the canonical cohomology map. -/
def toCanonical : RegularSheaf.H' 3 ⊤ →+ CanonicalAdditiveSheaf.H' 3 ⊤ :=
  canonicalComparison.toAddMonoidHom.comp
    (coefficientTopQuotient.comp sourceComparison.symm.toAddMonoidHom)

theorem toCanonical_connecting (s : Sections RegularSheaf (torus literalEval)) :
    toCanonical (nativeTopConnecting RegularSheaf ambientCover ambientCover_top s) =
      nativeTopConnecting CanonicalAdditiveSheaf fixedOpen fixedOpen_cover (coefficientTopSection s) := by
  change canonicalComparison
    (coefficientTopQuotient (sourceComparison.symm (sourceComparison (QuotientAddGroup.mk s)))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem canonicalSectionTrace_coefficientTopSection (s : Sections RegularSheaf (torus literalEval)) :
    canonicalSectionTrace (coefficientTopSection s) =
      nativeTopSectionTrace (CycleQ2HodgeTwistTorusChart.nativeLaurentSections
        literalEval literal_vertex_unit 0) s := by
  change CycleQ2LiteralThreefoldTopTrace.framedSectionTrace CanonicalForms globalFrame
    (coefficientTopSection s) = _
  rw [framedSectionTrace_frame]
  change CycleQ2LiteralThreefoldTopTrace.structureSectionTrace
    (globalFrame.app Torus le_top (coefficientSection 0 Finset.univ (Finset.mem_univ 0) s)) = _
  rw [coefficientSection_frame,structureSectionTrace_pullback,RingEquiv.apply_symm_apply]
  exact (CycleQ2HodgeTwistTorusChart.twistTopSectionTrace_frame literalEval literal_vertex_unit s).symm

theorem canonicalTrace_toCanonical (a : RegularSheaf.H' 3 ⊤) :
    canonicalTrace (toCanonical a) = ambientResidueTrace a := by
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective RegularSheaf ambientCover ambientCover_top
    (CycleQ2HodgeTwistTopCohomology.twist_face_acyclic literalEval 0) a
  rw [toCanonical_connecting,canonicalTrace_connecting,canonicalSectionTrace_coefficientTopSection]
  exact (CycleQ2HodgeTwistTopDerived.derivedTopTrace_connecting RegularSheaf ambientCover
    (CycleQ2HodgeTwistTorusChart.nativeLaurentSections literalEval literal_vertex_unit 0)
    ambientCover_top (CycleQ2HodgeTwistTopCohomology.twist_face_acyclic literalEval 0) s).symm

theorem coefficientTopSection_generator :
    coefficientTopSection (CycleQ2HodgeTwistTorusChart.twistTopGenerator literalEval literal_vertex_unit) =
      framedGenerator CanonicalForms globalFrame 1 := by
  change (globalFrame.app Torus le_top).symm ((faceSectionEquiv Finset.univ).symm
    (chartFrame literalEval 0 0 (torus literalEval) (torus_le literalEval 0)
      (CycleQ2HodgeTwistTorusChart.twistTopGenerator literalEval literal_vertex_unit))) = _
  rw [CycleQ2HodgeTwistTorusChart.twistTopGenerator_frame]
  rfl

/-- The already-computed negative cubic residue normalization survives
the actual scheme-section and canonical-frame transport. -/
theorem toCanonical_ambientResidueClass : toCanonical ambientResidueClass = -canonicalClass 1 := by
  rw [CycleQ2LiteralCubicProjectiveCocycle.ambientResidueClass_eq_neg_nativeTop,
    map_neg,toCanonical_connecting,coefficientTopSection_generator]
  rfl

/-- The original cubic boundary now lands in the full intrinsic
derived de Rham complex of the fixed proper threefold. -/
def toDeRham : RegularSheaf.H' 3 ⊤ →+ CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  (topPost 3 ⊤).comp toCanonical

theorem derivedTrace_toDeRham (a : RegularSheaf.H' 3 ⊤) :
    derivedTrace (toDeRham a) = ambientResidueTrace a :=
  (derivedTrace_topPost (toCanonical a)).trans (canonicalTrace_toCanonical a)

theorem toDeRham_ne_zero (a : RegularSheaf.H' 3 ⊤) (ha : a ≠ 0) : toDeRham a ≠ 0 := by
  intro hz
  have ht := congrArg derivedTrace hz
  rw [derivedTrace_toDeRham,map_zero] at ht
  apply ha
  apply ambientResidueTrace.injective
  simpa only [map_zero] using ht

theorem toDeRham_ambientResidueClass :
    toDeRham ambientResidueClass = -derivedNormalizedClass 1 := by
  change topPost 3 ⊤ (toCanonical ambientResidueClass) = _
  rw [toCanonical_ambientResidueClass,map_neg,topPost_canonicalClass]

theorem derivedTrace_ambientResidueClass : derivedTrace (toDeRham ambientResidueClass) = -1 := by
  rw [derivedTrace_toDeRham,ambientResidueTrace_class]

/-- The unchanged surface closed-inclusion and residue boundary are
followed by the concrete canonical transport and the actual top edge. -/
def surfaceToDeRham : CycleQ2CanonicalCoordinateH2.CanonicalSheaf.H' 2 ⊤ →+
    CycleQ2DerivedCoverTop.H target 6 ⊤ :=
  toDeRham.comp CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin

theorem surfaceToDeRham_ne_zero (a : CycleQ2CanonicalCoordinateH2.CanonicalSheaf.H' 2 ⊤)
    (ha : a ≠ 0) : surfaceToDeRham a ≠ 0 :=
  toDeRham_ne_zero _ (CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin_ne_zero a ha)

theorem surfaceToDeRham_residueGenerator :
    surfaceToDeRham (CycleQ2CanonicalCoordinateH2.canonicalConnecting
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator) = -derivedNormalizedClass 1 := by
  change toDeRham (CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin _) = _
  rw [CycleQ2LiteralCubicProjectiveCocycle.surfaceGysin_residueGenerator,toDeRham_ambientResidueClass]

theorem derivedTrace_surface_residueGenerator :
    derivedTrace (surfaceToDeRham (CycleQ2CanonicalCoordinateH2.canonicalConnecting
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator)) = -1 := by
  rw [surfaceToDeRham_residueGenerator,map_neg,
    CycleQ2LiteralTopDeRhamTrace.derivedTrace_normalizedClass]

end CycleQ2LiteralCubicDeRham
end

#print axioms CycleQ2LiteralCubicDeRham.coefficientTopSection_restrict
#print axioms CycleQ2LiteralCubicDeRham.toCanonical_ambientResidueClass
#print axioms CycleQ2LiteralCubicDeRham.toDeRham_ambientResidueClass
#print axioms CycleQ2LiteralCubicDeRham.surfaceToDeRham_ne_zero
#print axioms CycleQ2LiteralCubicDeRham.derivedTrace_surface_residueGenerator

/-! A coefficient-general affine hypersurface residue. This is formed in
the actual Kähler module of the polynomial quotient. The gradient span
is later supplied by the original fixed and generic Jacobian certificates. -/

noncomputable section
namespace CycleQ2HodgeHypersurfaceVolume

open Module MvPolynomial
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk)
open CycleQ2HodgeEulerContractionCharts
  (gradientEntry dx Patch patchMap basis basis_apply residueAlong
    partial_smul_residueAlong patchResidue patchResidue_eq patchUnit)
open CycleQ2LiteralThreefoldResidueMinors (signedOmitted signedOmitted_cross)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback_d)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_id)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open CycleQ2ExteriorTopBaseChange (topCoordinateEquiv)
open scoped KaehlerDifferential

variable {K : Type} [CommRing K] (q : Poly K)
  (hg : Ideal.span (Set.range (gradientEntry q)) = ⊤)

theorem bezout : ∃ c : Fin 4 → Hyp q, ∑ j, c j * gradientEntry q j = 1 :=
  Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp hg)

private def coefficient : Fin 4 → Hyp q := Classical.choose (bezout q hg)

private theorem coefficient_identity : ∑ j, coefficient q hg j * gradientEntry q j = 1 :=
  Classical.choose_spec (bezout q hg)

/-- The regular residue on the whole actual affine hypersurface chart. -/
def volume : ⋀[Hyp q]^3 Ω[Hyp q⁄K] :=
  ∑ j, coefficient q hg j • signedOmitted (Hyp q) (dx q (AlgHom.id K (Hyp q))) j

variable {S : Type} [CommRing S] [Algebra K S] (f : Hyp q →ₐ[K] S)

private theorem mapped_coefficient_identity :
    ∑ j, f (coefficient q hg j) * f (gradientEntry q j) = 1 := by
  simpa only [map_sum,map_mul,map_one] using congrArg f (coefficient_identity q hg)

private theorem pull_signedOmitted (j : Fin 4) :
    exteriorPullback f 3 (signedOmitted (Hyp q) (dx q (AlgHom.id K (Hyp q))) j) =
      signedOmitted S (dx q f) j := by
  rw [signedOmitted,map_smulₛₗ,CycleQ2ExactFrameThreeDeRham.exteriorPullback,
    exteriorMap_wedge]
  simp only [map_pow,map_neg,map_one]
  apply congrArg ((-1 : S)^j.val • ·)
  apply congrArg (exteriorPower.ιMulti S 3)
  funext a
  exact onePullback_d f (mk q (X (j.succAbove a)))

/-- All four gradient equations hold after the original algebra map,
including when some individual partials are zero divisors. -/
theorem gradient_smul_volume (j : Fin 4) :
    f (gradientEntry q j) • exteriorPullback f 3 (volume q hg) =
      signedOmitted S (dx q f) j := by
  let z := signedOmitted S (dx q f)
  have hc (a : Fin 4) : f (gradientEntry q j) • z a = f (gradientEntry q a) • z j :=
    signedOmitted_cross _ _ (CycleQ2HodgeEulerContractionCharts.gradient_relation q f) a j
  rw [volume,map_sum]
  simp only [map_smulₛₗ,pull_signedOmitted,Finset.smul_sum]
  change (∑ a, f (gradientEntry q j) • (f (coefficient q hg a) • z a)) = z j
  calc
    _ = ∑ a, (f (coefficient q hg a) * f (gradientEntry q a)) • z j := by
      apply Finset.sum_congr rfl
      intro a _
      rw [smul_comm (f (gradientEntry q j)),hc,mul_smul]
    _ = _ := by rw [← Finset.sum_smul,mapped_coefficient_identity,one_smul]

/-- These equations determine the residue uniquely, so its normalization
does not depend on the chosen Bézout coefficients. -/
theorem volume_unique (ω : ⋀[S]^3 Ω[S⁄K])
    (hω : ∀ j, f (gradientEntry q j) • ω = signedOmitted S (dx q f) j) :
    ω = exteriorPullback f 3 (volume q hg) := by
  let v := exteriorPullback f 3 (volume q hg)
  calc
    ω = (∑ j, f (coefficient q hg j) * f (gradientEntry q j)) • ω := by
      rw [mapped_coefficient_identity,one_smul]
    _ = (∑ j, f (coefficient q hg j) * f (gradientEntry q j)) • v := by
      simp only [Finset.sum_smul,mul_smul]
      exact Finset.sum_congr rfl fun j _ =>
        congrArg (fun a => f (coefficient q hg j) • a)
          ((hω j).trans (gradient_smul_volume q hg f j).symm)
    _ = _ := by rw [mapped_coefficient_identity,one_smul]

theorem volume_eq_residue (j : Fin 4) (hj : IsUnit (f (gradientEntry q j))) :
    exteriorPullback f 3 (volume q hg) = residueAlong q f j hj :=
  (IsUnit.smul_left_cancel hj).mp ((gradient_smul_volume q hg f j).trans
    (partial_smul_residueAlong q f j hj).symm)

theorem volume_on_patch (j : Fin 4) :
    exteriorPullback (patchMap q j) 3 (volume q hg) = patchResidue q j :=
  volume_eq_residue q hg (patchMap q j) j
    (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) _)

theorem coordinateForms_span :
    Submodule.span (Hyp q) (Set.range (dx q (AlgHom.id K (Hyp q)))) = ⊤ := by
  rw [eq_top_iff]
  intro ω _
  obtain ⟨v,rfl⟩ := CycleQ2HodgeCotangentChartPresentation.coordinateMap_surjective q ω
  rw [CycleQ2HodgeCotangentChartPresentation.coordinateMap_apply]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)

private theorem omitted_coordinate (s : Set.powersetCard (Fin 4) 3) :
    ∃ j : Fin 4, Set.powersetCard.ofFinEmbEquiv.symm s = Fin.succAboveOrderEmb j := by
  obtain ⟨s,hs⟩ := s
  change s.card = 3 at hs
  have hcard : sᶜ.card = 1 := by simp [Finset.card_compl,hs]
  obtain ⟨j,hj⟩ := Finset.card_eq_one.mp hcard
  have he : s = {j}ᶜ := by rw [← hj,compl_compl]
  subst s
  exact ⟨j,Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb j⟩

private theorem wedge_coefficient (s : Set.powersetCard (Fin 4) 3) :
    ∃ c : Hyp q, c • volume q hg =
      exteriorPower.ιMulti_family (Hyp q) 3 (dx q (AlgHom.id K (Hyp q))) s := by
  obtain ⟨j,hj⟩ := omitted_coordinate s
  refine ⟨(-1 : Hyp q)^j.val * gradientEntry q j,?_⟩
  have hw := gradient_smul_volume q hg (AlgHom.id K (Hyp q)) j
  rw [exteriorPullback_id] at hw
  rw [exteriorPower.ιMulti_family,hj,mul_smul,hw]
  change (-1 : Hyp q)^j.val • ((-1 : Hyp q)^j.val • _) = _
  rw [← mul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul]

private theorem volume_surjective : Function.Surjective (fun c : Hyp q => c • volume q hg) := by
  let m := LinearMap.toSpanSingleton (Hyp q) (⋀[Hyp q]^3 Ω[Hyp q⁄K]) (volume q hg)
  have hle : Submodule.span (Hyp q)
      (Set.range (exteriorPower.ιMulti_family (Hyp q) 3 (dx q (AlgHom.id K (Hyp q))))) ≤
      LinearMap.range m := by
    apply Submodule.span_le.mpr
    rintro _ ⟨s,rfl⟩
    exact wedge_coefficient q hg s
  have htop := exteriorPower.ιMulti_family_span_of_span (n := 3) (Hyp q) (coordinateForms_span q)
  exact LinearMap.range_eq_top.mp (top_le_iff.mp (htop ▸ hle) : LinearMap.range m = ⊤)

private theorem patch_volume_bijective (j : Fin 4) :
    Function.Bijective (fun c : Patch q j => c • patchResidue q j) := by
  let u : (Patch q j)ˣ := (patchUnit q j)⁻¹ * (-1 : (Patch q j)ˣ)^j.val
  let e := (LinearEquiv.smulOfUnit u : Patch q j ≃ₗ[Patch q j] Patch q j).trans
    (topCoordinateEquiv (basis q j)).symm
  have he (a : Patch q j) : e a = a • patchResidue q j := by
    rw [patchResidue_eq]
    change ((u : Patch q j) * a) • exteriorPower.ιMulti (Patch q j) 3 (basis q j) =
      a • ((u : Patch q j) • exteriorPower.ιMulti (Patch q j) 3 (basis q j))
    rw [smul_smul,mul_comm]
  simpa only [he] using e.bijective

private theorem volume_injective : Function.Injective (fun c : Hyp q => c • volume q hg) := by
  intro c d hcd
  apply Localization.algebraMap_injective_of_span_eq_top _ hg
  funext a
  obtain ⟨a,⟨j,rfl⟩⟩ := a
  simp only [Pi.algebraMap_apply]
  apply (patch_volume_bijective q j).injective
  have he := congrArg (exteriorPullback (patchMap q j) 3) hcd
  simp only [map_smulₛₗ] at he
  rw [volume_on_patch q hg j] at he
  simpa only [AlgHom.toRingHom_eq_coe,patchMap,IsScalarTower.coe_toAlgHom] using he

/-- Every actual three-form has a unique coefficient in this regular
residue, over the coefficient ring itself. -/
theorem volume_bijective : Function.Bijective (fun c : Hyp q => c • volume q hg) :=
  ⟨volume_injective q hg,volume_surjective q hg⟩

def volumeEquiv : Hyp q ≃ₗ[Hyp q] (⋀[Hyp q]^3 Ω[Hyp q⁄K]) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Hyp q) _ (volume q hg))
    (volume_bijective q hg)

theorem volumeEquiv_apply (c : Hyp q) : volumeEquiv q hg c = c • volume q hg := rfl

end CycleQ2HodgeHypersurfaceVolume
end

#print axioms CycleQ2HodgeHypersurfaceVolume.gradient_smul_volume
#print axioms CycleQ2HodgeHypersurfaceVolume.volume_bijective

noncomputable section
namespace CycleQ2HodgeHypersurfaceVolume

open Module TensorProduct
open CycleQ2HodgeEulerChartDerivations (Poly Hyp)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2ProjectiveExteriorBaseChange (raw)
open scoped KaehlerDifferential TensorProduct

variable {K S : Type} [CommRing K] [CommRing S] [Algebra K S]
  (q : Poly K) (hg : Ideal.span (Set.range (gradientEntry q)) = ⊤)
  [Algebra (Hyp q) S] [IsScalarTower K (Hyp q) S]
  [Algebra.FormallyEtale (Hyp q) S]
  [Module.Finite (Hyp q) Ω[Hyp q⁄K]] [Module.Projective (Hyp q) Ω[Hyp q⁄K]]

private theorem cotangent_baseChange :
    IsBaseChange S (KaehlerDifferential.map K K (Hyp q) S) :=
  KaehlerDifferential.isBaseChange_of_formallyEtale K (Hyp q) S

private theorem top_baseChange :
    IsBaseChange S (raw (S := S) 3 (KaehlerDifferential.map K K (Hyp q) S)) :=
  CycleQ2ProjectiveExteriorBaseChange.isBaseChange 3 (cotangent_baseChange (S := S) q)

/-- On every formally étale scalar extension, in particular every
actual chart localization, the same residue remains a basis. -/
def localizedVolumeEquiv : S ≃ₗ[S] (⋀[S]^3 Ω[S⁄K]) :=
  (TensorProduct.AlgebraTensorModule.rid (Hyp q) S S).symm.trans
    (((volumeEquiv q hg).baseChange (Hyp q) S _ _).trans (top_baseChange (S := S) q).equiv)

theorem localizedVolumeEquiv_apply (a : S) :
    localizedVolumeEquiv (S := S) q hg a =
      a • exteriorPullback (IsScalarTower.toAlgHom K (Hyp q) S) 3 (volume q hg) := by
  have ha : (TensorProduct.AlgebraTensorModule.rid (Hyp q) S S).symm a = a ⊗ₜ[Hyp q] (1 : Hyp q) := by
    apply (TensorProduct.AlgebraTensorModule.rid (Hyp q) S S).injective
    rw [LinearEquiv.apply_symm_apply,TensorProduct.AlgebraTensorModule.rid_tmul,one_smul]
  change (top_baseChange (S := S) q).equiv
    (((volumeEquiv q hg).baseChange (Hyp q) S _ _)
      ((TensorProduct.AlgebraTensorModule.rid (Hyp q) S S).symm a)) = _
  rw [ha,LinearEquiv.baseChange_tmul,volumeEquiv_apply,one_smul,IsBaseChange.equiv_tmul] <;> rfl

end CycleQ2HodgeHypersurfaceVolume
end

#print axioms CycleQ2HodgeHypersurfaceVolume.localizedVolumeEquiv_apply

noncomputable section
namespace CycleQ2IntrinsicOrdinaryExterior

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential onBasisIso onBasisIso_d)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback_d)
open CycleQ2GeometricExteriorSheaf (exteriorMap_wedge)
open scoped KaehlerDifferential

section Algebra

variable {k A B : Type} [CommRing k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] (e : A →ₐ[k] B)

theorem pullback_exact_wedge (n : ℕ) (a : Fin n → A) :
    exteriorPullback e n (exteriorPower.ιMulti A n (KaehlerDifferential.D k A ∘ a)) =
      exteriorPower.ιMulti B n (KaehlerDifferential.D k B ∘ (e ∘ a)) := by
  rw [CycleQ2ExactFrameThreeDeRham.exteriorPullback,exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti B n)
  funext j
  exact onePullback_d e (a j)

theorem pullback_exact_symbol (n : ℕ) (c : A) (a : Fin n → A) :
    exteriorPullback e n (c • exteriorPower.ιMulti A n (KaehlerDifferential.D k A ∘ a)) =
      e c • exteriorPower.ιMulti B n (KaehlerDifferential.D k B ∘ (e ∘ a)) := by
  rw [map_smulₛₗ,pullback_exact_wedge]

end Algebra

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension r f]

/-- The actual intrinsic differential has its native exact-symbol
formula on every open. Affineness or a chosen frame on that open is
not required; the equality is checked on its original exact affine
basis and retains the canonical ordinary-to-sheaf section map. -/
theorem differential_exact_symbol (U : X.Opens) (n : ℕ)
    (c : Γ(X,U)) (a : Fin n → Γ(X,U)) :
    letI : Algebra k Γ(X,U) := (sectionCoefficients f U).toAlgebra
    (differential f r n).hom.app (op U)
      ((toSheaf f r n).app (op U)
        (c • exteriorPower.ιMulti Γ(X,U) n (KaehlerDifferential.D k Γ(X,U) ∘ a))) =
      (toSheaf f r (n+1)).app (op U)
        (exteriorPower.ιMulti Γ(X,U) (n+1)
          (KaehlerDifferential.D k Γ(X,U) ∘ Matrix.vecCons c a)) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients f U).toAlgebra
  apply TopCat.Presheaf.IsSheaf.section_ext (sheafForms f r (n+1)).property
  intro x hx
  obtain ⟨V,hV,hxV,hVU⟩ := Opens.isBasis_iff_nbhd.mp
    (CycleQ2FiniteExactAffineAtlas.isBasis f r) hx
  let W : FramedOpen f r := ⟨V,hV⟩
  letI : Algebra k Γ(X,V) := (sectionCoefficients f V).toAlgebra
  let e := restrict f hVU
  let s := c • exteriorPower.ιMulti Γ(X,U) n (KaehlerDifferential.D k Γ(X,U) ∘ a)
  let t := exteriorPower.ιMulti Γ(X,U) (n+1)
    (KaehlerDifferential.D k Γ(X,U) ∘ Matrix.vecCons c a)
  refine ⟨V,hVU,hxV,?_⟩
  change (sheafForms f r (n+1)).obj.map (homOfLE hVU).op
      ((differential f r n).hom.app (op U) ((toSheaf f r n).app (op U) s)) =
    (sheafForms f r (n+1)).obj.map (homOfLE hVU).op
      ((toSheaf f r (n+1)).app (op U) t)
  rw [← (differential f r n).hom.naturality_apply,
    ← (toSheaf f r n).naturality_apply,
    ← (toSheaf f r (n+1)).naturality_apply]
  change (differential f r n).hom.app (op V)
      ((toSheaf f r n).app (op V) (exteriorPullback e n s)) =
    (toSheaf f r (n+1)).app (op V) (exteriorPullback e (n+1) t)
  rw [show s = c • exteriorPower.ιMulti Γ(X,U) n
      (KaehlerDifferential.D k Γ(X,U) ∘ a) from rfl,
    show t = exteriorPower.ιMulti Γ(X,U) (n+1)
      (KaehlerDifferential.D k Γ(X,U) ∘ Matrix.vecCons c a) from rfl,
    pullback_exact_symbol,pullback_exact_wedge,
    toSheaf_onBasis f r n W,toSheaf_onBasis f r (n+1) W]
  apply (ConcreteCategory.bijective_of_isIso
    ((onBasisIso f r (n+1)).hom.app (op W))).injective
  rw [Iso.inv_hom_id_apply]
  have hd := ConcreteCategory.congr_hom (onBasisIso_d f r n W)
    ((onBasisIso f r n).inv.app (op W)
      (e c • exteriorPower.ιMulti Γ(X,V) n
        (KaehlerDifferential.D k Γ(X,V) ∘ (e ∘ a))))
  rw [Iso.inv_hom_id_apply] at hd
  rw [hd,CycleQ2FrameCanonicalDifferential.d_exact_symbol
    (frame f r W) (functions f r W) (frame_apply f r W)]
  apply congrArg (exteriorPower.ιMulti Γ(X,V) (n+1))
  funext j
  cases j using Fin.cases <;> rfl

end CycleQ2IntrinsicOrdinaryExterior
end

#print axioms CycleQ2IntrinsicOrdinaryExterior.differential_exact_symbol

noncomputable section
namespace CycleQ2RelativeAffineChartSections

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricAffineChartSections
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2GenericAffineKahlerLocalization (p)
open CycleQ2RelativeSectionPullback (sectionPull)

attribute [local instance] CycleQ2GenericAffineKahlerLocalization.sectionsAlgebra

variable {k A : Type} [Field k] [CommRing A] [Algebra k A]
  {X : Scheme.{0}} {U : X.Opens}
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of k))
  (h : e.inv ≫ U.ι ≫ f = p k A)

theorem chartSectionIso_coefficients (V : Over U) (c : k) :
    (chartSectionIso e V).hom (sectionCoefficients f V.left c) =
      algebraMap A Γ(Spec (CommRingCat.of A),(chartOpensEquiv e).functor.obj V)
        (algebraMap k A c) := by
  let j := e.inv ≫ U.ι
  let W := (chartOpensEquiv e).functor.obj V
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  letI : Algebra k Γ(Spec (CommRingCat.of A),W) :=
    (sectionCoefficients (p k A) W).toAlgebra
  have hj : j ≫ f = p k A := by simpa only [j,Category.assoc] using h
  have hc := (sectionPull f (p k A) j hj V.left W le_rfl).commutes c
  change j.appLE V.left W le_rfl (sectionCoefficients f V.left c) =
    sectionCoefficients (p k A) W c at hc
  rw [Scheme.Hom.appLE_eq_app] at hc
  exact hc.trans (CycleQ2GenericAffineKahlerLocalization.sectionCoefficients_affine k A W c)

/-- Actual affine chart functions preserve the relative coefficient
field on every subopen, over an arbitrary field. -/
theorem chartSection_coefficients (V : Over U) (c : k) :
    chartSection e V (algebraMap k A c) = sectionCoefficients f V.left c := by
  apply (ConcreteCategory.bijective_of_isIso (chartSectionIso e V).hom).injective
  change (chartSectionIso e V).hom ((chartSectionIso e V).inv
    (algebraMap A Γ(Spec (CommRingCat.of A),(chartOpensEquiv e).functor.obj V)
      (algebraMap k A c))) = _
  rw [Iso.inv_hom_id_apply,chartSectionIso_coefficients e f h]

def chartAlgHom (V : Over U) :
    letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
    A →ₐ[k] Γ(X,V.left) := by
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  exact { toRingHom := chartSection e V
          commutes' := chartSection_coefficients e f h V }

theorem chartAlgHom_restrict {V W : Over U} (a : V ⟶ W) (z : A) :
    X.presheaf.map a.left.op (chartAlgHom e f h W z) = chartAlgHom e f h V z :=
  chartSection_naturality e a z

theorem chartAlgHom_top_bijective :
    Function.Bijective (chartAlgHom e f h (Over.mk (𝟙 U))) := by
  haveI : IsIso (CommRingCat.ofHom (chartSection e (Over.mk (𝟙 U)))) := by
    rw [chartSection_top]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso
    (CommRingCat.ofHom (chartSection e (Over.mk (𝟙 U))))

def chartAlgEquiv :
    letI : Algebra k Γ(X,U) := (sectionCoefficients f U).toAlgebra
    A ≃ₐ[k] Γ(X,U) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients f U).toAlgebra
  exact AlgEquiv.ofBijective (chartAlgHom e f h (Over.mk (𝟙 U)))
    (chartAlgHom_top_bijective e f h)

theorem chartAlgHom_etale (hU : IsAffineOpen U) (V : Over U)
    (hV : IsAffineOpen V.left) : (chartAlgHom e f h V).toRingHom.Etale := by
  have he : (chartAlgHom e f h V).toRingHom =
      (X.presheaf.map V.hom.op).hom.comp
        (chartAlgHom e f h (Over.mk (𝟙 U))).toRingHom := by
    apply RingHom.ext
    intro a
    exact (chartAlgHom_restrict e f h
      (Over.homMk V.hom : V ⟶ Over.mk (𝟙 U)) a).symm
  rw [he]
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (chartAlgHom_top_bijective e f h))
    (CycleQ2RelativeAffineOverlap.restrict_etale V.hom.le hU hV)

end CycleQ2RelativeAffineChartSections
end

#print axioms CycleQ2RelativeAffineChartSections.chartSection_coefficients

noncomputable section
namespace CycleQ2HodgeHypersurfaceSheafVolume

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2HodgeEulerChartDerivations (Poly Hyp)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeHypersurfaceVolume (volume localizedVolumeEquiv localizedVolumeEquiv_apply)
open CycleQ2RelativeAffineChartSections (chartAlgHom chartAlgHom_etale)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)
open CycleQ2IntrinsicOrdinaryExterior (toSheaf toSheaf_bijective)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2WeightedCoordinateExterior (Form)

variable {k : Type} [Field k] [CharZero k] (q : Poly k)
  (hg : Ideal.span (Set.range (gradientEntry q)) = ⊤)
  {X : Scheme.{0}} {U : X.Opens}
  (e : U.toScheme ≅ Spec (CommRingCat.of (Hyp q)))
  (f : X ⟶ Spec (CommRingCat.of k))
  (h : e.inv ≫ U.ι ≫ f = CycleQ2GenericAffineKahlerLocalization.p k (Hyp q))
  [SmoothOfRelativeDimension 3 f]

private theorem chart_smooth : Algebra.Smooth k (Hyp q) := by
  let j := e.inv ≫ U.ι
  have hd := smoothOfRelativeDimension_comp 0 3 j f
  have hj : j ≫ f = CycleQ2GenericAffineKahlerLocalization.p k (Hyp q) := by
    simpa only [j,Category.assoc] using h
  rw [hj] at hd
  letI := hd
  have hs : Smooth (CycleQ2GenericAffineKahlerLocalization.p k (Hyp q)) :=
    SmoothOfRelativeDimension.smooth 3 _
  exact RingHom.smooth_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hs)

/-- The actual affine-chart residue as a genuine intrinsic three-form
section on any subopen of the chart. -/
def sectionVolume (V : Over U) : (sheafForms f 3 3).obj.obj (op V.left) :=
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  (toSheaf f 3 3).app (op V.left)
    (exteriorPullback (chartAlgHom e f h V) 3 (volume q hg))

theorem sectionVolume_restrict {V W : Over U} (a : V ⟶ W) :
    (sheafForms f 3 3).obj.map a.left.op (sectionVolume q hg e f h W) =
      sectionVolume q hg e f h V := by
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  letI : Algebra k Γ(X,W.left) := (sectionCoefficients f W.left).toAlgebra
  change (sheafForms f 3 3).obj.map a.left.op
    ((toSheaf f 3 3).app (op W.left)
      (exteriorPullback (chartAlgHom e f h W) 3 (volume q hg))) = _
  rw [← (toSheaf f 3 3).naturality_apply]
  change (toSheaf f 3 3).app (op V.left)
    (exteriorPullback (restrict f a.left.le) 3
      (exteriorPullback (chartAlgHom e f h W) 3 (volume q hg))) = _
  rw [← exteriorPullback_comp]
  have he : (restrict f a.left.le).comp (chartAlgHom e f h W) = chartAlgHom e f h V := by
    ext z
    exact CycleQ2RelativeAffineChartSections.chartAlgHom_restrict e f h a z
  rw [he]
  rfl

/-- On an arbitrary affine subopen, every actual intrinsic three-form
has a unique coefficient in this same chart residue. The proof uses
the genuine chart restriction, whose étaleness was established from
the actual open immersion. -/
def affineSectionEquiv (hU : IsAffineOpen U) (V : Over U) (hV : IsAffineOpen V.left) :
    Γ(X,V.left) ≃+ (sheafForms f 3 3).obj.obj (op V.left) := by
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  letI : Algebra (Hyp q) Γ(X,V.left) := (chartAlgHom e f h V).toRingHom.toAlgebra
  letI : IsScalarTower k (Hyp q) Γ(X,V.left) := IsScalarTower.of_algHom (chartAlgHom e f h V)
  letI : Algebra.Etale (Hyp q) Γ(X,V.left) := (chartAlgHom_etale e f h hU V hV).toAlgebra
  letI : Algebra.Smooth k (Hyp q) := chart_smooth q e f h
  exact (localizedVolumeEquiv (S := Γ(X,V.left)) q hg).toAddEquiv.trans
    (AddEquiv.ofBijective ((toSheaf f 3 3).app (op V.left)).hom
      (toSheaf_bijective f 3 3 hV))

theorem affineSectionEquiv_apply (hU : IsAffineOpen U) (V : Over U)
    (hV : IsAffineOpen V.left) (c : Γ(X,V.left)) :
    letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
    affineSectionEquiv q hg e f h hU V hV c =
      (toSheaf f 3 3).app (op V.left)
        (c • exteriorPullback (chartAlgHom e f h V) 3 (volume q hg)) := by
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  letI : Algebra (Hyp q) Γ(X,V.left) := (chartAlgHom e f h V).toRingHom.toAlgebra
  letI : IsScalarTower k (Hyp q) Γ(X,V.left) := IsScalarTower.of_algHom (chartAlgHom e f h V)
  letI : Algebra.Etale (Hyp q) Γ(X,V.left) := (chartAlgHom_etale e f h hU V hV).toAlgebra
  letI : Algebra.Smooth k (Hyp q) := chart_smooth q e f h
  change (toSheaf f 3 3).app (op V.left)
    (localizedVolumeEquiv (S := Γ(X,V.left)) q hg c) = _
  rw [localizedVolumeEquiv_apply]
  rfl

theorem affineSectionEquiv_one (hU : IsAffineOpen U) (V : Over U)
    (hV : IsAffineOpen V.left) :
    affineSectionEquiv q hg e f h hU V hV 1 = sectionVolume q hg e f h V := by
  rw [affineSectionEquiv_apply,one_smul]
  rfl

theorem affineSectionEquiv_restrict (hU : IsAffineOpen U) {V W : Over U}
    (hV : IsAffineOpen V.left) (hW : IsAffineOpen W.left)
    (a : V ⟶ W) (c : Γ(X,W.left)) :
    (sheafForms f 3 3).obj.map a.left.op (affineSectionEquiv q hg e f h hU W hW c) =
      affineSectionEquiv q hg e f h hU V hV (X.presheaf.map a.left.op c) := by
  letI : Algebra k Γ(X,V.left) := (sectionCoefficients f V.left).toAlgebra
  letI : Algebra k Γ(X,W.left) := (sectionCoefficients f W.left).toAlgebra
  rw [affineSectionEquiv_apply,affineSectionEquiv_apply,
    ← (toSheaf f 3 3).naturality_apply]
  change (toSheaf f 3 3).app (op V.left)
    (exteriorPullback (restrict f a.left.le) 3
      (c • exteriorPullback (chartAlgHom e f h W) 3 (volume q hg))) = _
  rw [map_smulₛₗ,← exteriorPullback_comp]
  have he : (restrict f a.left.le).comp (chartAlgHom e f h W) = chartAlgHom e f h V := by
    ext z
    exact CycleQ2RelativeAffineChartSections.chartAlgHom_restrict e f h a z
  rw [he]
  rfl

end CycleQ2HodgeHypersurfaceSheafVolume
end

#print axioms CycleQ2HodgeHypersurfaceSheafVolume.affineSectionEquiv_restrict

noncomputable section
namespace CycleQ2HodgeCubicSectionComparison

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeEulerChartBinding (affineChart chartEquiv)
open CycleQ2GeometricHodgeThreefoldCubic (Stage chartEquivAdjoinRoot)
open CycleQ2GeometricAffineChartSections (chartSection chartSection_top chartSection_naturality)
open CycleQ2HodgeTwistLocalization (inverted)
open CycleQ2HodgeTwistFaces (face face_inf sectionsEquiv toFace toFace_section)
open CycleQ2HodgeTwistCubicFaces (faceStage faceStage_toFace)
open CycleQ2TorusCubicTrace (Cubic)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem coordinateChartSection_top (i : Fin 4) (p : ChartRing φ i) :
    chartSection (coordinateChart φ i) (Over.mk (𝟙 (coordinateOpen φ i))) p =
      Proj.awayToSection (grade φ) (coord φ i.castSucc) p := by
  have h : CommRingCat.ofHom (chartSection (coordinateChart φ i)
      (Over.mk (𝟙 (coordinateOpen φ i)))) =
      Proj.awayToSection (grade φ) (coord φ i.castSucc) := by
    rw [chartSection_top]
    simp only [coordinateChart,Proj.basicOpenIsoSpec_hom,
      Proj.basicOpenToSpec_app_top,Category.assoc,Iso.inv_hom_id_assoc,
      Iso.inv_hom_id,Category.comp_id]
  exact ConcreteCategory.congr_hom h p

theorem affineChartSection (i : Fin 4) (W : (threefold φ).Opens)
    (hW : W ≤ coordinateOpen φ i) (p : ChartRing φ i) :
    chartSection (affineChart φ i) (Over.mk (homOfLE hW)) (chartEquiv φ i p) =
      (threefold φ).presheaf.map (homOfLE hW).op
        (Proj.awayToSection (grade φ) (coord φ i.castSucc) p) := by
  have hc : (affineChart φ i).inv ≫ (coordinateOpen φ i).ι ≫ 𝟙 (threefold φ) =
      Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingHom) ≫
        (coordinateChart φ i).inv ≫ (coordinateOpen φ i).ι := by
    change (Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingHom) ≫
      (coordinateChart φ i).inv) ≫ (coordinateOpen φ i).ι ≫ 𝟙 _ = _
    simp only [Category.comp_id,Category.assoc]
  have ht : chartSection (coordinateChart φ i) (Over.mk (𝟙 (coordinateOpen φ i))) p =
      chartSection (affineChart φ i) (Over.mk (𝟙 (coordinateOpen φ i)))
        (chartEquiv φ i p) := by
    simpa only [Scheme.Hom.appLE_eq_app,Scheme.Hom.id_app,ConcreteCategory.id_apply] using
      CycleQ2ChartSectionPullback.chartSection_pullback_top
        (𝟙 (threefold φ)) (coordinateChart φ i) (affineChart φ i)
        (chartEquiv φ i).toRingHom (le_refl _) hc p
  rw [coordinateChartSection_top] at ht
  exact (chartSection_naturality (affineChart φ i)
    (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶
      Over.mk (𝟙 (coordinateOpen φ i))) (chartEquiv φ i p)).symm.trans
    (congrArg ((threefold φ).presheaf.map (homOfLE hW).op) ht.symm)

variable (h : IsUnit (φ vertexCoefficient))

def localizedMap (i : Fin 4) (B : Finset (Fin 3)) :
    CycleQ2HodgeEuler.chart φ i →ₐ[R] Cubic φ i h B :=
  (IsScalarTower.toAlgHom R (Stage φ i h) (Cubic φ i h B)).comp
    (chartEquivAdjoinRoot φ i h).toAlgHom

/-- This is the actual structure-section equivalence on each nonempty
face of the original projective cover, over the coefficient ring. -/
def toCubicSections (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) :
    Γ(threefold φ,S.inf (coordinateOpen φ)) ≃+* Cubic φ i h (inverted i S) :=
  (CycleQ2GeometricProjectiveCurve.Twisted.resEquiv (threefold φ).sheaf
    (face_inf φ i S hi).le (face_inf φ i S hi).ge).trans
      ((sectionsEquiv φ i (inverted i S)).symm.trans (faceStage φ i h (inverted i S)))

theorem toCubicSections_chartSection (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)
    (a : CycleQ2HodgeEuler.chart φ i) :
    toCubicSections φ h i S hi
      (chartSection (affineChart φ i) (Over.mk (homOfLE (Finset.inf_le hi))) a) =
        localizedMap φ h i (inverted i S) a := by
  obtain ⟨p,rfl⟩ := (chartEquiv φ i).surjective a
  let hW : face φ i (inverted i S) ≤ coordinateOpen φ i :=
    (face_inf φ i S hi).le.trans (Finset.inf_le hi)
  have he :
      CycleQ2GeometricProjectiveCurve.Twisted.resEquiv (threefold φ).sheaf
        (face_inf φ i S hi).le (face_inf φ i S hi).ge
        (chartSection (affineChart φ i) (Over.mk (homOfLE (Finset.inf_le hi)))
          (chartEquiv φ i p)) =
      sectionsEquiv φ i (inverted i S) (toFace φ i (inverted i S) p) := by
    calc
      _ = chartSection (affineChart φ i) (Over.mk (homOfLE hW)) (chartEquiv φ i p) :=
        chartSection_naturality (affineChart φ i)
          (Over.homMk (homOfLE (face_inf φ i S hi).le) :
            Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE (Finset.inf_le hi))) _
      _ = (threefold φ).presheaf.map (homOfLE hW).op
          (Proj.awayToSection (grade φ) (coord φ i.castSucc) p) :=
        affineChartSection φ i _ hW p
      _ = _ := (toFace_section φ i (inverted i S) p).symm
  change faceStage φ i h (inverted i S)
    ((sectionsEquiv φ i (inverted i S)).symm _) = _
  rw [he,RingEquiv.symm_apply_apply]
  exact faceStage_toFace φ i h (inverted i S) p

end CycleQ2HodgeCubicSectionComparison
end

noncomputable section
namespace CycleQ2HodgeCubicIntrinsicForms

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen vertexCoefficient)
open CycleQ2HodgeEulerChartBinding (affineChart affineChart_overBase)
open CycleQ2HodgeTwistLocalization (inverted)
open CycleQ2HodgeCubicSectionComparison (toCubicSections toCubicSections_chartSection localizedMap)
open CycleQ2RelativeAffineChartSections (chartSection_coefficients)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential)
open CycleQ2IntrinsicOrdinaryExterior (toSheaf toSheaf_bijective)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2TorusCubicTrace (Cubic)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
  (h : IsUnit (φ vertexCoefficient))

/-- The original projective section comparison is linear over its
actual relative coefficient field, as checked on the original chart. -/
def sectionEquiv (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) :
    letI : Algebra k Γ(threefold φ,S.inf (coordinateOpen φ)) :=
      (sectionCoefficients (toBase φ) (S.inf (coordinateOpen φ))).toAlgebra
    Γ(threefold φ,S.inf (coordinateOpen φ)) ≃ₐ[k] Cubic φ i h (inverted i S) := by
  letI : Algebra k Γ(threefold φ,S.inf (coordinateOpen φ)) :=
    (sectionCoefficients (toBase φ) (S.inf (coordinateOpen φ))).toAlgebra
  refine AlgEquiv.ofRingEquiv (f := toCubicSections φ h i S hi) ?_
  intro a
  rw [show algebraMap k Γ(threefold φ,S.inf (coordinateOpen φ)) a =
      CycleQ2GeometricAffineChartSections.chartSection (affineChart φ i)
        (Over.mk (homOfLE (Finset.inf_le hi)))
        (algebraMap k (CycleQ2HodgeEuler.chart φ i) a) from
      (chartSection_coefficients (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
        (Over.mk (homOfLE (Finset.inf_le hi))) a).symm,
    toCubicSections_chartSection,AlgHom.commutes]

theorem face_affine (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) :
    IsAffineOpen (S.inf (coordinateOpen φ)) := by
  rw [← CycleQ2HodgeTwistFaces.face_inf φ i S hi]
  exact CycleQ2HodgeTwistFaces.face_affine φ i (inverted i S)

variable [SmoothOfRelativeDimension 3 (toBase φ)]

/-- Ordinary forms on the original cubic localization and actual
intrinsic exterior sections on the same projective face. -/
def realize (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S) (n : ℕ) :
    Form k (Cubic φ i h (inverted i S)) n ≃+
      (sheafForms (toBase φ) 3 n).obj.obj (op (S.inf (coordinateOpen φ))) := by
  letI : Algebra k Γ(threefold φ,S.inf (coordinateOpen φ)) :=
    (sectionCoefficients (toBase φ) (S.inf (coordinateOpen φ))).toAlgebra
  exact (CycleQ2AffineExteriorForms.extAlgEquiv k (sectionEquiv φ h i S hi).symm n).trans
    (AddEquiv.ofBijective ((toSheaf (toBase φ) 3 n).app (op (S.inf (coordinateOpen φ)))).hom
      (toSheaf_bijective (toBase φ) 3 n (face_affine φ i S hi)))

theorem realize_exact_symbol (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)
    (n : ℕ) (c : Cubic φ i h (inverted i S))
    (a : Fin n → Cubic φ i h (inverted i S)) :
    (differential (toBase φ) 3 n).hom.app (op (S.inf (coordinateOpen φ)))
      (realize φ h i S hi n
        (c • exteriorPower.ιMulti (Cubic φ i h (inverted i S)) n
          (KaehlerDifferential.D k (Cubic φ i h (inverted i S)) ∘ a))) =
      realize φ h i S hi (n+1)
        (exteriorPower.ιMulti (Cubic φ i h (inverted i S)) (n+1)
          (KaehlerDifferential.D k (Cubic φ i h (inverted i S)) ∘ Matrix.vecCons c a)) := by
  letI : Algebra k Γ(threefold φ,S.inf (coordinateOpen φ)) :=
    (sectionCoefficients (toBase φ) (S.inf (coordinateOpen φ))).toAlgebra
  change (differential (toBase φ) 3 n).hom.app _
    ((toSheaf (toBase φ) 3 n).app _
      (exteriorPullback (sectionEquiv φ h i S hi).symm.toAlgHom n _)) =
    (toSheaf (toBase φ) 3 (n+1)).app _
      (exteriorPullback (sectionEquiv φ h i S hi).symm.toAlgHom (n+1) _)
  rw [CycleQ2IntrinsicOrdinaryExterior.pullback_exact_symbol,
    CycleQ2IntrinsicOrdinaryExterior.pullback_exact_wedge,
    CycleQ2IntrinsicOrdinaryExterior.differential_exact_symbol]
  apply congrArg ((toSheaf (toBase φ) 3 (n+1)).app _)
  apply congrArg (exteriorPower.ιMulti _ (n+1))
  funext j
  cases j using Fin.cases <;> rfl

end CycleQ2HodgeCubicIntrinsicForms
end

#print axioms CycleQ2HodgeCubicSectionComparison.toCubicSections_chartSection
#print axioms CycleQ2HodgeCubicIntrinsicForms.realize_exact_symbol

noncomputable section
namespace CycleQ2HodgeNormalFirstChart

open CategoryTheory AlgebraicGeometry MvPolynomial Module
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient coordinateOpen toBase)
open CycleQ2HodgeEuler (F chart chartMap)
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2GeometricHodgeThreefoldCubic
  (Base cubic cubic_monic cubic_natDegree pack pack_F Stage chartEquivAdjoinRoot)
open CycleQ2CubicCoefficientTrace (normal)
open CycleQ2TorusCubicTrace (Cubic Coefficients root coefficients)
open CycleQ2TorusLogDerivatives (localizedPartial localizedPartial_algebraMap)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

/-- This only permutes the original four affine variables: w first,
then the three retained weight-one coordinates in their original order. -/
def polynomial (i : Fin 4) : Poly R := rename (finRotate 4) (F φ i)

def chartEquiv (i : Fin 4) : chart φ i ≃ₐ[R] Hyp (polynomial φ i) :=
  Ideal.quotientEquivAlg _ _ (MvPolynomial.renameEquiv R (finRotate 4)) (by
    rw [Ideal.map_span,Set.image_singleton]
    rfl)

theorem chartEquiv_polynomial (i : Fin 4) (p : Poly R) :
    chartEquiv φ i (chartMap φ i p) = mk (polynomial φ i) (rename (finRotate 4) p) := rfl

theorem gradient_entry (i j : Fin 4) :
    gradientEntry (polynomial φ i) (finRotate 4 j) =
      chartEquiv φ i (gradientEntry (F φ i) j) := by
  change mk (polynomial φ i) (pderiv (finRotate 4 j) (rename (finRotate 4) (F φ i))) =
    mk (polynomial φ i) (rename (finRotate 4) (pderiv j (F φ i)))
  rw [pderiv_rename (finRotate 4).injective]

/-- The original Jacobian unit-ideal certificate is transported by the
actual quotient isomorphism, rather than assumed again after reordering. -/
theorem gradient_span (i : Fin 4)
    (hg : Ideal.span (Set.range (gradientEntry (F φ i))) = ⊤) :
    Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤ := by
  have hm := congrArg (Ideal.map (chartEquiv φ i).toRingHom) hg
  rw [Ideal.map_span,Ideal.map_top] at hm
  have he : Set.range (gradientEntry (polynomial φ i)) =
      (chartEquiv φ i) '' Set.range (gradientEntry (F φ i)) := by
    ext a
    constructor
    · rintro ⟨j,rfl⟩
      refine ⟨gradientEntry (F φ i) ((finRotate 4).symm j),⟨_,rfl⟩,?_⟩
      simpa only [Equiv.apply_symm_apply] using
        (gradient_entry φ i ((finRotate 4).symm j)).symm
    · rintro ⟨a,⟨j,rfl⟩,rfl⟩
      exact ⟨finRotate 4 j,gradient_entry φ i j⟩
  rw [he]
  exact hm

/-- The same genuine affine chart, with precisely this variable order. -/
def affineChart (i : Fin 4) : (coordinateOpen φ i).toScheme ≅
    Spec (CommRingCat.of (Hyp (polynomial φ i))) :=
  CycleQ2HodgeEulerChartBinding.affineChart φ i ≪≫
    Scheme.Spec.mapIso (chartEquiv φ i).toRingEquiv.toCommRingCatIso.symm.op

theorem affineChart_overBase (i : Fin 4) :
    (affineChart φ i).inv ≫ (coordinateOpen φ i).ι ≫ toBase φ =
      Spec.map (CommRingCat.ofHom (algebraMap R (Hyp (polynomial φ i)))) := by
  change (Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingHom) ≫
    (CycleQ2HodgeEulerChartBinding.affineChart φ i).inv) ≫
      (coordinateOpen φ i).ι ≫ toBase φ = _
  rw [Category.assoc,CycleQ2HodgeEulerChartBinding.affineChart_overBase,← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext (chartEquiv φ i).commutes))

variable [Nontrivial R] (hm : φ vertexCoefficient = 1)

def monicUnit : IsUnit (φ vertexCoefficient) := by
  rw [hm]
  exact isUnit_one

private abbrev normalPack : Poly R ≃ₐ[R] Polynomial (Base R) := MvPolynomial.finSuccEquiv R 3

theorem normalPack_equation (i : Fin 4) :
    normalPack (polynomial φ i) = cubic φ i (monicUnit φ hm) := by
  change pack (F φ i) = _
  rw [pack_F φ i (monicUnit φ hm),hm,map_one,map_one,one_mul]

def cubicEquiv (i : Fin 4) :
    Hyp (polynomial φ i) ≃ₐ[R] Stage φ i (monicUnit φ hm) :=
  Ideal.quotientEquivAlg _ _ normalPack (by
    rw [Ideal.map_span,Set.image_singleton,normalPack_equation φ hm])

theorem cubicEquiv_polynomial (i : Fin 4) (p : Poly R) :
    cubicEquiv φ hm i (mk (polynomial φ i) p) =
      AdjoinRoot.mk (cubic φ i (monicUnit φ hm)) (normalPack p) := rfl

theorem cubicEquiv_chartEquiv (i : Fin 4) (a : chart φ i) :
    cubicEquiv φ hm i (chartEquiv φ i a) = chartEquivAdjoinRoot φ i (monicUnit φ hm) a := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

def baseCoefficients (i : Fin 4) (j : Fin 3) : Base R :=
  (cubic φ i (monicUnit φ hm)).coeff j.val

private theorem cubic_decomposition (i : Fin 4) :
    cubic φ i (monicUnit φ hm) = Polynomial.X^3 +
      Polynomial.C (baseCoefficients φ hm i 0) +
      Polynomial.C (baseCoefficients φ hm i 1) * Polynomial.X +
      Polynomial.C (baseCoefficients φ hm i 2) * Polynomial.X^2 := by
  let p := cubic φ i (monicUnit φ hm)
  have h3 : p.coeff 3 = 1 := by
    have he := (cubic_monic φ i (monicUnit φ hm)).leadingCoeff
    change p.coeff p.natDegree = 1 at he
    simpa only [p,cubic_natDegree] using he
  have hp : p = ∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (p.coeff j) * Polynomial.X^j)]
    exact p.as_sum_range_C_mul_X_pow' (by
      rw [show p.natDegree = 3 from cubic_natDegree φ i (monicUnit φ hm)]
      decide)
  calc
    p = ∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val := hp
    _ = _ := by
      rw [Fin.sum_univ_four]
      simp only [Fin.val_zero,Fin.val_one,show (2 : Fin 4).val = 2 from rfl,
        show (3 : Fin 4).val = 3 from rfl,h3,map_one,pow_zero,pow_one,one_mul,mul_one]
      change _ = Polynomial.X^3 + Polynomial.C (p.coeff 0) +
        Polynomial.C (p.coeff 1) * Polynomial.X + Polynomial.C (p.coeff 2) * Polynomial.X^2
      ring

private theorem normalPack_base (p : Base R) :
    normalPack (rename Fin.succ p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [rename_C] using (normalPack : Poly R ≃ₐ[R] _).commutes a
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p j hp => simp only [map_mul,rename_X,hp,MvPolynomial.finSuccEquiv_X_succ]

/-- The original monic chart equation, in its actual reordered
polynomial quotient, is the cubic with these three base coefficients. -/
theorem polynomial_cubic (i : Fin 4) :
    polynomial φ i = (X 0 : Poly R)^3 + rename Fin.succ (baseCoefficients φ hm i 0) +
      rename Fin.succ (baseCoefficients φ hm i 1) * X 0 +
      rename Fin.succ (baseCoefficients φ hm i 2) * X 0^2 := by
  apply (normalPack : Poly R ≃ₐ[R] _).injective
  rw [normalPack_equation φ hm]
  simp only [map_add,map_mul,map_pow,normalPack_base,MvPolynomial.finSuccEquiv_X_zero]
  exact cubic_decomposition φ hm i

private theorem pderiv_base_normal (p : Base R) : pderiv 0 (rename Fin.succ p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j,_,hj⟩ := MvPolynomial.mem_vars_rename Fin.succ p h
  exact Fin.succ_ne_zero j hj

theorem pderiv_normal (i : Fin 4) :
    pderiv 0 (polynomial φ i) = rename Fin.succ (baseCoefficients φ hm i 1) +
      2 * rename Fin.succ (baseCoefficients φ hm i 2) * X 0 + 3 * X 0^2 := by
  rw [polynomial_cubic φ hm]
  simp only [map_add,pderiv_pow,pderiv_mul,pderiv_X_self,pderiv_base_normal]
  norm_num <;> ring

theorem pderiv_coordinate (i : Fin 4) (j : Fin 3) :
    pderiv j.succ (polynomial φ i) = rename Fin.succ (pderiv j (baseCoefficients φ hm i 0)) +
      rename Fin.succ (pderiv j (baseCoefficients φ hm i 1)) * X 0 +
      rename Fin.succ (pderiv j (baseCoefficients φ hm i 2)) * X 0^2 := by
  have hn : pderiv j.succ (X 0 : Poly R) = 0 := pderiv_X_of_ne (Fin.succ_ne_zero j)
  rw [polynomial_cubic φ hm]
  simp only [map_add,pderiv_pow,pderiv_mul,pderiv_rename (Fin.succ_injective 3),hn,
    mul_zero,add_zero,zero_add]

def localizedMap (i : Fin 4) (S : Finset (Fin 3)) :
    Hyp (polynomial φ i) →ₐ[R] Cubic φ i (monicUnit φ hm) S :=
  (IsScalarTower.toAlgHom R (Stage φ i (monicUnit φ hm))
    (Cubic φ i (monicUnit φ hm) S)).comp (cubicEquiv φ hm i).toAlgHom

private def polynomialEval (i : Fin 4) (S : Finset (Fin 3)) :
    Poly R →ₐ[R] Cubic φ i (monicUnit φ hm) S :=
  (localizedMap φ hm i S).comp (Ideal.Quotient.mkₐ R (Ideal.span {polynomial φ i}))

theorem localizedMap_normal (i : Fin 4) (S : Finset (Fin 3)) :
    localizedMap φ hm i S (mk (polynomial φ i) (X 0)) = root φ i (monicUnit φ hm) S := by
  change algebraMap (Stage φ i (monicUnit φ hm)) _
    (AdjoinRoot.mk _ (normalPack (X 0 : Poly R))) = _
  rw [MvPolynomial.finSuccEquiv_X_zero,AdjoinRoot.mk_X]
  rfl

theorem localizedMap_base (i : Fin 4) (S : Finset (Fin 3)) (p : Base R) :
    localizedMap φ hm i S (mk (polynomial φ i) (rename Fin.succ p)) =
      algebraMap (Coefficients (R := R) S) (Cubic φ i (monicUnit φ hm) S)
        (algebraMap (Base R) (Coefficients (R := R) S) p) := by
  change algebraMap (Stage φ i (monicUnit φ hm)) _
    (AdjoinRoot.mk _ (normalPack (rename Fin.succ p))) = _
  rw [normalPack_base,AdjoinRoot.mk_C]
  simp only [← IsScalarTower.algebraMap_apply]

theorem localizedMap_coordinate (i : Fin 4) (S : Finset (Fin 3)) (j : Fin 3) :
    localizedMap φ hm i S (mk (polynomial φ i) (X j.succ)) =
      algebraMap (Coefficients (R := R) S) (Cubic φ i (monicUnit φ hm) S)
        (algebraMap (Base R) (Coefficients (R := R) S) (X j)) := by
  simpa only [rename_X] using localizedMap_base φ hm i S (X j)

theorem localizedMap_gradient_normal (i : Fin 4) (S : Finset (Fin 3)) :
    localizedMap φ hm i S (gradientEntry (polynomial φ i) 0) =
      normal (root φ i (monicUnit φ hm) S)
        ![coefficients φ i (monicUnit φ hm) S 1,
          2*coefficients φ i (monicUnit φ hm) S 2,3] := by
  change polynomialEval φ hm i S (pderiv 0 (polynomial φ i)) = _
  rw [pderiv_normal φ hm]
  simp only [map_add,map_mul,map_pow,map_ofNat,polynomialEval,
    AlgHom.comp_apply,localizedMap_base,localizedMap_normal,normal,coefficients,
    baseCoefficients,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]

theorem localizedMap_gradient_coordinate (i : Fin 4) (S : Finset (Fin 3)) (j : Fin 3) :
    localizedMap φ hm i S (gradientEntry (polynomial φ i) j.succ) =
      normal (root φ i (monicUnit φ hm) S)
        ((localizedPartial R S j) ∘ coefficients φ i (monicUnit φ hm) S) := by
  change polynomialEval φ hm i S (pderiv j.succ (polynomial φ i)) = _
  rw [pderiv_coordinate φ hm]
  simp only [map_add,map_mul,map_pow,polynomialEval,AlgHom.comp_apply,
    localizedMap_base,localizedMap_normal,normal,coefficients,baseCoefficients,
    Function.comp_apply,localizedPartial_algebraMap]

end CycleQ2HodgeNormalFirstChart
end

#print axioms CycleQ2HodgeNormalFirstChart.gradient_span
#print axioms CycleQ2HodgeNormalFirstChart.affineChart_overBase
#print axioms CycleQ2HodgeNormalFirstChart.polynomial_cubic
#print axioms CycleQ2HodgeNormalFirstChart.localizedMap_gradient_coordinate

noncomputable section
namespace CycleQ2HodgeHypersurfaceVolume

open Module
open CycleQ2HodgeEulerChartDerivations (Poly Hyp)
open CycleQ2HodgeEulerContractionCharts (gradientEntry dx)
open CycleQ2LiteralThreefoldResidueMinors (signedOmitted)
open CycleQ2LiteralThreefoldTorusForms (pairLeft pairRight pairCoefficient expand_pair)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open scoped KaehlerDifferential

variable {K S : Type} [CommRing K] [CommRing S] [Algebra K S]
  (q : Poly K) (hg : Ideal.span (Set.range (gradientEntry q)) = ⊤) (f : Hyp q →ₐ[K] S)

theorem coordinate_triple (j : Fin 4) :
    exteriorPower.ιMulti S 3 (dx q f ∘ j.succAbove) =
      ((-1 : S)^j.val * f (gradientEntry q j)) • exteriorPullback f 3 (volume q hg) := by
  have h := congrArg (fun ω : ⋀[S]^3 Ω[S⁄K] => (-1 : S)^j.val • ω)
    (gradient_smul_volume q hg f j)
  simpa only [signedOmitted,smul_smul,← mul_pow,neg_mul_neg,one_mul,one_pow,one_smul] using h.symm

/-- The same six ordered-pair coefficients apply to every actual
smooth affine hypersurface residue, over its relative base ring. -/
theorem coordinate_wedge (v : Fin 4 → S) (p : Fin 6) :
    exteriorPower.ιMulti S 3 ![∑ j, v j • dx q f j,
      dx q f (pairLeft p),dx q f (pairRight p)] =
      pairCoefficient (fun j => f (gradientEntry q j)) v p • exteriorPullback f 3 (volume q hg) := by
  let e := dx q f
  let g := fun j => f (gradientEntry q j)
  let ω := exteriorPullback f 3 (volume q hg)
  have h0 : e ∘ (0 : Fin 4).succAbove = ![e 1,e 2,e 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : e ∘ (1 : Fin 4).succAbove = ![e 0,e 2,e 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : e ∘ (2 : Fin 4).succAbove = ![e 0,e 1,e 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : e ∘ (3 : Fin 4).succAbove = ![e 0,e 1,e 2] := by
    funext j; fin_cases j <;> rfl
  have he (j : Fin 4) : exteriorPower.ιMulti S 3 (e ∘ j.succAbove) =
      ((-1 : S)^j.val*g j) • ω := coordinate_triple q hg f j
  apply expand_pair e g v ω
  · simpa only [h3,show (3 : Fin 4).val = 3 from rfl,
      pow_succ,pow_zero,mul_one,neg_mul_neg,one_mul,neg_one_mul,neg_smul] using he 3
  · simpa only [h2,show (2 : Fin 4).val = 2 from rfl,neg_one_sq,one_mul] using he 2
  · simpa only [h1,Fin.val_one,pow_one,neg_one_mul,neg_smul] using he 1
  · simpa only [h0,Fin.val_zero,pow_zero,one_mul] using he 0

end CycleQ2HodgeHypersurfaceVolume

namespace CycleQ2HodgeNormalFirstChart

open Module MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)
open CycleQ2HodgeEulerContractionCharts (gradientEntry dx)
open CycleQ2HodgeHypersurfaceVolume (volume coordinate_wedge)
open CycleQ2LiteralThreefoldTorusForms (pairLeft pairRight pairCoefficient)
open CycleQ2CubicCoefficientTrace (normal)
open CycleQ2TorusCubicTrace (Cubic Coefficients root coefficients powerBasis powerBasis_apply residueTrace)
open CycleQ2TorusLogDerivatives (localizedPartial)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open scoped KaehlerDifferential

variable {R : Type} [CommRing R] [Nontrivial R]
  (φ : CoeffRing →+* R) (hm : φ vertexCoefficient = 1) (i : Fin 4) (S : Finset (Fin 3))

def differentialCoefficients (a : Fin 3 → Coefficients (R := R) S) :
    Fin 4 → Cubic φ i (monicUnit φ hm) S :=
  Fin.cons (normal (root φ i (monicUnit φ hm) S) ![a 1,2*a 2,0])
    (fun j => normal (root φ i (monicUnit φ hm) S) ((localizedPartial R S j) ∘ a))

theorem normal_differential (a : Fin 3 → Coefficients (R := R) S) :
    KaehlerDifferential.D R (Cubic φ i (monicUnit φ hm) S)
      (normal (root φ i (monicUnit φ hm) S) a) =
        ∑ j : Fin 4, differentialCoefficients φ hm i S a j •
          dx (polynomial φ i) (localizedMap φ hm i S) j := by
  rw [Fin.sum_univ_succ]
  simpa only [differentialCoefficients,Fin.cons_zero,Fin.cons_succ,dx,
    localizedMap_normal,localizedMap_coordinate] using
    CycleQ2TorusCubicTrace.normal_differential φ i (monicUnit φ hm) S
      (root φ i (monicUnit φ hm) S) a

theorem exists_normal (a : Cubic φ i (monicUnit φ hm) S) :
    ∃ b : Fin 3 → Coefficients (R := R) S, normal (root φ i (monicUnit φ hm) S) b = a :=
  ⟨fun j => (powerBasis φ i (monicUnit φ hm) S).repr a j,
    CycleQ2CubicCoefficientTrace.normal_repr (powerBasis φ i (monicUnit φ hm) S)
      (root φ i (monicUnit φ hm) S) (powerBasis_apply φ i (monicUnit φ hm) S) a⟩

/-- The power-basis differential formula proves spanning directly on
the actual cubic localization, including its branch locus. -/
theorem coordinateForms_span :
    Submodule.span (Cubic φ i (monicUnit φ hm) S)
      (Set.range (dx (polynomial φ i) (localizedMap φ hm i S))) = ⊤ := by
  let Q := Submodule.span (Cubic φ i (monicUnit φ hm) S)
    (Set.range (dx (polynomial φ i) (localizedMap φ hm i S)))
  change Q = ⊤
  rw [eq_top_iff,← KaehlerDifferential.span_range_derivation R (Cubic φ i (monicUnit φ hm) S),
    Submodule.span_le]
  rintro _ ⟨a,rfl⟩
  obtain ⟨b,rfl⟩ := exists_normal φ hm i S a
  rw [normal_differential]
  apply Submodule.sum_mem
  intro j _
  exact Q.smul_mem _ (Submodule.subset_span ⟨j,rfl⟩)

def coordinatePair (p : Fin 6) : ⋀[Cubic φ i (monicUnit φ hm) S]^2
    Ω[Cubic φ i (monicUnit φ hm) S⁄R] :=
  exteriorPower.ιMulti (Cubic φ i (monicUnit φ hm) S) 2
    ![dx (polynomial φ i) (localizedMap φ hm i S) (pairLeft p),
      dx (polynomial φ i) (localizedMap φ hm i S) (pairRight p)]

theorem coordinatePair_span :
    Submodule.span (Cubic φ i (monicUnit φ hm) S) (Set.range (coordinatePair φ hm i S)) = ⊤ := by
  have htwo := exteriorPower.ιMulti_family_span_of_span (n := 2)
    (Cubic φ i (monicUnit φ hm) S) (coordinateForms_span φ hm i S)
  rw [eq_top_iff,← htwo,Submodule.span_le]
  rintro _ ⟨s,rfl⟩
  let v := Set.powersetCard.ofFinEmbEquiv.symm s
  have hall : ∀ a b : Fin 4, a < b →
      ∃ p : Fin 6, pairLeft p = a ∧ pairRight p = b := by decide
  obtain ⟨p,hp,hq⟩ := hall (v 0) (v 1) (v.strictMono (by decide))
  have hv : dx (polynomial φ i) (localizedMap φ hm i S) ∘ v =
      ![dx (polynomial φ i) (localizedMap φ hm i S) (v 0),
        dx (polynomial φ i) (localizedMap φ hm i S) (v 1)] := by
    funext j; fin_cases j <;> rfl
  change exteriorPower.ιMulti (Cubic φ i (monicUnit φ hm) S) 2
    (dx (polynomial φ i) (localizedMap φ hm i S) ∘ v) ∈ _
  rw [hv,← hp,← hq]
  exact Submodule.subset_span ⟨p,rfl⟩

theorem exists_coordinatePair_sum (ω : ⋀[Cubic φ i (monicUnit φ hm) S]^2
    Ω[Cubic φ i (monicUnit φ hm) S⁄R]) :
    ∃ a : Fin 6 → Cubic φ i (monicUnit φ hm) S,
      ∑ p, a p • coordinatePair φ hm i S p = ω := by
  apply Submodule.mem_span_range_iff_exists_fun.mp
  rw [coordinatePair_span]
  exact Submodule.mem_top

def pairResidueCoefficient (a : Fin 3 → Coefficients (R := R) S) (p : Fin 6) :
    Cubic φ i (monicUnit φ hm) S :=
  pairCoefficient (fun j => localizedMap φ hm i S (gradientEntry (polynomial φ i) j))
    (differentialCoefficients φ hm i S a) p

theorem normal_coordinate_wedge
    (hg : Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
    (a : Fin 3 → Coefficients (R := R) S) (p : Fin 6) :
    exteriorPower.ιMulti (Cubic φ i (monicUnit φ hm) S) 3
      ![KaehlerDifferential.D R (Cubic φ i (monicUnit φ hm) S)
          (normal (root φ i (monicUnit φ hm) S) a),
        dx (polynomial φ i) (localizedMap φ hm i S) (pairLeft p),
        dx (polynomial φ i) (localizedMap φ hm i S) (pairRight p)] =
      pairResidueCoefficient φ hm i S a p •
        exteriorPullback (localizedMap φ hm i S) 3 (volume (polynomial φ i) hg) := by
  rw [normal_differential]
  exact coordinate_wedge (polynomial φ i) hg (localizedMap φ hm i S)
    (differentialCoefficients φ hm i S a) p

theorem pairResidueCoefficient_trace_zero (a : Fin 3 → Coefficients (R := R) S) (p : Fin 6) :
    residueTrace φ i (monicUnit φ hm) S (pairResidueCoefficient φ hm i S a p) = 0 := by
  have hH (j : Fin 3) : residueTrace φ i (monicUnit φ hm) S
      (differentialCoefficients φ hm i S a j.succ *
          localizedMap φ hm i S (gradientEntry (polynomial φ i) 0) -
       differentialCoefficients φ hm i S a 0 *
          localizedMap φ hm i S (gradientEntry (polynomial φ i) j.succ)) = 0 := by
    simpa only [differentialCoefficients,Fin.cons_zero,Fin.cons_succ,
      localizedMap_gradient_normal,localizedMap_gradient_coordinate,mul_comm] using
      CycleQ2TorusCubicTrace.residueTrace_horizontal φ i (monicUnit φ hm) S j a
  have hM (j k : Fin 3) : residueTrace φ i (monicUnit φ hm) S
      (differentialCoefficients φ hm i S a k.succ *
          localizedMap φ hm i S (gradientEntry (polynomial φ i) j.succ) -
       differentialCoefficients φ hm i S a j.succ *
          localizedMap φ hm i S (gradientEntry (polynomial φ i) k.succ)) = 0 := by
    simpa only [differentialCoefficients,Fin.cons_succ,localizedMap_gradient_coordinate] using
      CycleQ2TorusCubicTrace.residueTrace_mixed φ i (monicUnit φ hm) S j k a
  fin_cases p
  · exact hM 1 2
  · exact hM 2 0
  · exact hM 0 1
  · exact hH 2
  · let v := differentialCoefficients φ hm i S a
    let g := fun j => localizedMap φ hm i S (gradientEntry (polynomial φ i) j)
    change residueTrace φ i (monicUnit φ hm) S (v 0*g 2-v 2*g 0) = 0
    rw [show v 0*g 2-v 2*g 0 = -(v 2*g 0-v 0*g 2) by abel,map_neg]
    have he := hH 1
    change residueTrace φ i (monicUnit φ hm) S (v 2*g 0-v 0*g 2) = 0 at he
    rw [he,neg_zero]
  · exact hH 0

end CycleQ2HodgeNormalFirstChart
end

#print axioms CycleQ2HodgeNormalFirstChart.coordinateForms_span
#print axioms CycleQ2HodgeNormalFirstChart.normal_coordinate_wedge
#print axioms CycleQ2HodgeNormalFirstChart.pairResidueCoefficient_trace_zero

noncomputable section
namespace CycleQ2HodgeMonicFaceTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen vertexCoefficient)
open CycleQ2HodgeEulerChartDerivations (Hyp mk)
open CycleQ2HodgeEulerContractionCharts (gradientEntry dx)
open CycleQ2HodgeNormalFirstChart
  (polynomial chartEquiv affineChart affineChart_overBase monicUnit cubicEquiv
    cubicEquiv_chartEquiv localizedMap coordinatePair exists_normal exists_coordinatePair_sum
    normal_coordinate_wedge pairResidueCoefficient_trace_zero)
open CycleQ2GeometricAffineChartSections (chartSection)
open CycleQ2RelativeAffineChartSections (chartAlgHom)
open CycleQ2HodgeHypersurfaceSheafVolume (affineSectionEquiv affineSectionEquiv_apply)
open CycleQ2HodgeHypersurfaceVolume (volume)
open CycleQ2HodgeCubicIntrinsicForms (sectionEquiv realize realize_exact_symbol face_affine)
open CycleQ2HodgeTwistLocalization (inverted)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential)
open CycleQ2IntrinsicOrdinaryExterior (toSheaf)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2TorusCubicTrace (Cubic residueTrace)
open CycleQ2LiteralThreefoldTorusForms (pairLeft pairRight)
open scoped KaehlerDifferential

variable {k : Type} [Field k] [CharZero k]
  (φ : CoeffRing →+* k) (hm : φ vertexCoefficient = 1)
  (i : Fin 4) (S : Finset (Fin 4)) (hi : i ∈ S)

theorem normalSection_raw (W : (threefold φ).Opens) (hW : W ≤ coordinateOpen φ i)
    (a : CycleQ2HodgeEuler.chart φ i) :
    chartSection (CycleQ2HodgeEulerChartBinding.affineChart φ i) (Over.mk (homOfLE hW)) a =
      chartSection (affineChart φ i) (Over.mk (homOfLE hW)) (chartEquiv φ i a) := by
  have hc : (affineChart φ i).inv ≫ (coordinateOpen φ i).ι ≫ 𝟙 (threefold φ) =
      Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingHom) ≫
        (CycleQ2HodgeEulerChartBinding.affineChart φ i).inv ≫ (coordinateOpen φ i).ι := by
    change (Spec.map (CommRingCat.ofHom (chartEquiv φ i).toRingHom) ≫
      (CycleQ2HodgeEulerChartBinding.affineChart φ i).inv) ≫
        (coordinateOpen φ i).ι ≫ 𝟙 _ = _
    simp only [Category.comp_id,Category.assoc]
  simpa only [Scheme.Hom.appLE_eq_app,Scheme.Hom.id_app,ConcreteCategory.id_apply] using
    CycleQ2ChartSectionPullback.chartSection_pullback (𝟙 (threefold φ))
      (CycleQ2HodgeEulerChartBinding.affineChart φ i) (affineChart φ i)
      (chartEquiv φ i).toRingHom (le_refl _) hc W hW W hW (le_refl _) a

theorem sectionEquiv_chart (a : Hyp (polynomial φ i)) :
    sectionEquiv φ (monicUnit φ hm) i S hi
      (chartSection (affineChart φ i) (Over.mk (homOfLE (Finset.inf_le hi))) a) =
        localizedMap φ hm i (inverted i S) a := by
  obtain ⟨a,rfl⟩ := (chartEquiv φ i).surjective a
  rw [← normalSection_raw φ i]
  change CycleQ2HodgeCubicSectionComparison.toCubicSections φ (monicUnit φ hm) i S hi
    (chartSection (CycleQ2HodgeEulerChartBinding.affineChart φ i)
      (Over.mk (homOfLE (Finset.inf_le hi))) a) = _
  rw [CycleQ2HodgeCubicSectionComparison.toCubicSections_chartSection]
  change algebraMap (CycleQ2GeometricHodgeThreefoldCubic.Stage φ i (monicUnit φ hm)) _
      (CycleQ2GeometricHodgeThreefoldCubic.chartEquivAdjoinRoot φ i (monicUnit φ hm) a) =
    algebraMap _ _ (cubicEquiv φ hm i (chartEquiv φ i a))
  rw [cubicEquiv_chartEquiv]

variable (hg : Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
  [SmoothOfRelativeDimension 3 (toBase φ)]

private theorem coordinate_affine : IsAffineOpen (coordinateOpen φ i) :=
  Proj.isAffineOpen_basicOpen (CycleQ2GeometricHodgeThreefold.grade φ)
    (CycleQ2GeometricHodgeThreefold.coord φ i.castSucc)
    (CycleQ2GeometricHodgeThreefold.weightOne_mem_grade φ i) (by decide)

private abbrev frame : Γ(threefold φ,S.inf (coordinateOpen φ)) ≃+
    (sheafForms (toBase φ) 3 3).obj.obj (op (S.inf (coordinateOpen φ))) :=
  affineSectionEquiv (polynomial φ i) hg (affineChart φ i) (toBase φ)
    (affineChart_overBase φ i) (coordinate_affine φ i)
    (Over.mk (homOfLE (Finset.inf_le hi))) (face_affine φ i S hi)

def nativeVolume : ⋀[Cubic φ i (monicUnit φ hm) (inverted i S)]^3
    Ω[Cubic φ i (monicUnit φ hm) (inverted i S)⁄k] :=
  exteriorPullback (localizedMap φ hm i (inverted i S)) 3 (volume (polynomial φ i) hg)

theorem realize_volume_coefficient (c : Cubic φ i (monicUnit φ hm) (inverted i S)) :
    realize φ (monicUnit φ hm) i S hi 3 (c • nativeVolume φ hm i S hg) =
      frame φ i S hi hg ((sectionEquiv φ (monicUnit φ hm) i S hi).symm c) := by
  letI : Algebra k Γ(threefold φ,S.inf (coordinateOpen φ)) :=
    (sectionCoefficients (toBase φ) (S.inf (coordinateOpen φ))).toAlgebra
  have he : (sectionEquiv φ (monicUnit φ hm) i S hi).symm.toAlgHom.comp
      (localizedMap φ hm i (inverted i S)) =
    chartAlgHom (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
      (Over.mk (homOfLE (Finset.inf_le hi))) := by
    ext a
    apply (sectionEquiv φ (monicUnit φ hm) i S hi).injective
    rw [AlgHom.comp_apply,AlgEquiv.apply_symm_apply]
    exact (sectionEquiv_chart φ hm i S hi a).symm
  change (toSheaf (toBase φ) 3 3).app _
    (exteriorPullback (sectionEquiv φ (monicUnit φ hm) i S hi).symm.toAlgHom 3
      (c • exteriorPullback (localizedMap φ hm i (inverted i S)) 3
        (volume (polynomial φ i) hg))) = _
  rw [map_smulₛₗ,← exteriorPullback_comp,he]
  exact (affineSectionEquiv_apply (polynomial φ i) hg (affineChart φ i) (toBase φ)
    (affineChart_overBase φ i) (coordinate_affine φ i)
    (Over.mk (homOfLE (Finset.inf_le hi))) (face_affine φ i S hi) _).symm

/-- The actual relative canonical section trace in this original
projective face, with its normal-first affine residue normalization. -/
def sectionTrace : (sheafForms (toBase φ) 3 3).obj.obj (op (S.inf (coordinateOpen φ))) →+ k :=
  (residueTrace φ i (monicUnit φ hm) (inverted i S)).comp
    ((sectionEquiv φ (monicUnit φ hm) i S hi).toAddMonoidHom.comp
      (frame φ i S hi hg).symm.toAddMonoidHom)

theorem sectionTrace_realize_volume (c : Cubic φ i (monicUnit φ hm) (inverted i S)) :
    sectionTrace φ hm i S hi hg
      (realize φ (monicUnit φ hm) i S hi 3 (c • nativeVolume φ hm i S hg)) =
        residueTrace φ i (monicUnit φ hm) (inverted i S) c := by
  rw [realize_volume_coefficient]
  change residueTrace φ i (monicUnit φ hm) (inverted i S)
    (sectionEquiv φ (monicUnit φ hm) i S hi
      ((frame φ i S hi hg).symm ((frame φ i S hi hg)
        ((sectionEquiv φ (monicUnit φ hm) i S hi).symm c)))) = _
  rw [AddEquiv.symm_apply_apply,AlgEquiv.apply_symm_apply]

private theorem trace_coordinate_pair (c : Cubic φ i (monicUnit φ hm) (inverted i S)) (p : Fin 6) :
    sectionTrace φ hm i S hi hg
      ((differential (toBase φ) 3 2).hom.app (op (S.inf (coordinateOpen φ)))
        (realize φ (monicUnit φ hm) i S hi 2
          (c • coordinatePair φ hm i (inverted i S) p))) = 0 := by
  obtain ⟨a,rfl⟩ := exists_normal φ hm i (inverted i S) c
  let c' := CycleQ2CubicCoefficientTrace.normal
    (CycleQ2TorusCubicTrace.root φ i (monicUnit φ hm) (inverted i S)) a
  let v : Fin 2 → Cubic φ i (monicUnit φ hm) (inverted i S) :=
    ![localizedMap φ hm i (inverted i S) (mk (polynomial φ i) (MvPolynomial.X (pairLeft p))),
      localizedMap φ hm i (inverted i S) (mk (polynomial φ i) (MvPolynomial.X (pairRight p)))]
  have h2 : KaehlerDifferential.D k _ ∘ v =
      ![dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairLeft p),
        dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairRight p)] := by
    funext j; fin_cases j <;> rfl
  have h3 : KaehlerDifferential.D k _ ∘ Matrix.vecCons c' v =
      ![KaehlerDifferential.D k _ c',
        dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairLeft p),
        dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairRight p)] := by
    funext j; fin_cases j <;> rfl
  have hd := realize_exact_symbol φ (monicUnit φ hm) i S hi 2 c' v
  rw [h2,h3] at hd
  change (differential (toBase φ) 3 2).hom.app _
      (realize φ (monicUnit φ hm) i S hi 2 (_ • coordinatePair φ hm i (inverted i S) p)) =
    realize φ (monicUnit φ hm) i S hi 3
      (exteriorPower.ιMulti (Cubic φ i (monicUnit φ hm) (inverted i S)) 3
        ![KaehlerDifferential.D k _ _,
          dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairLeft p),
          dx (polynomial φ i) (localizedMap φ hm i (inverted i S)) (pairRight p)]) at hd
  rw [hd,normal_coordinate_wedge φ hm i (inverted i S) hg,
    sectionTrace_realize_volume,pairResidueCoefficient_trace_zero]

/-- Every actual intrinsic two-form section has derivative of zero
trace. The proof covers all six coordinate pairs with arbitrary
coefficients in the original cubic localization. -/
theorem sectionTrace_differential
    (η : (sheafForms (toBase φ) 3 2).obj.obj (op (S.inf (coordinateOpen φ)))) :
    sectionTrace φ hm i S hi hg
      ((differential (toBase φ) 3 2).hom.app (op (S.inf (coordinateOpen φ))) η) = 0 := by
  obtain ⟨ω,rfl⟩ := (realize φ (monicUnit φ hm) i S hi 2).surjective η
  obtain ⟨a,ha⟩ := exists_coordinatePair_sum φ hm i (inverted i S) ω
  rw [← ha,map_sum,map_sum,map_sum]
  exact Finset.sum_eq_zero fun p _ => trace_coordinate_pair φ hm i S hi hg (a p) p

end CycleQ2HodgeMonicFaceTrace
end

#print axioms CycleQ2HodgeMonicFaceTrace.sectionEquiv_chart
#print axioms CycleQ2HodgeMonicFaceTrace.realize_volume_coefficient
#print axioms CycleQ2HodgeMonicFaceTrace.sectionTrace_differential

noncomputable section
namespace CycleQ2HodgeCubicSectionComparison

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen vertexCoefficient)
open CycleQ2HodgeTwistCech (sections negativeExponent)
open CycleQ2HodgeTwistDehom (exponentEquiv chartCoordinates)
open CycleQ2HodgeTwistLocalization (inverted intersectionCoordinates localizationOffset)
open CycleQ2HodgeTwistCubicFaces (structureCoordinates)

variable {R : Type} [CommRing R] [Nontrivial R]
  (φ : CoeffRing →+* R) (h : IsUnit (φ vertexCoefficient))

private theorem intersection_top_coefficient (p : sections R 0 Finset.univ) :
    (CycleQ2SeedCechLocalization.localizationToLaurent R (inverted 0 Finset.univ)
      (intersectionCoordinates R 0 Finset.univ 0 (Finset.mem_univ 0) p 2)).coeff
        (fun _ => -1) = p.val 2 negativeExponent := by
  let e : {e : CycleQ2HodgeTwistCech.Exp //
      CycleQ2HodgeTwistCech.Allowed 0 Finset.univ 2 e} := ⟨negativeExponent,by decide⟩
  let d := exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0) e
  have he := DFunLike.congr_fun
    ((localizationOffset R 0 Finset.univ).apply_symm_apply
      (chartCoordinates 0 0 Finset.univ (Finset.mem_univ 0) p 2)) d
  change (CycleQ2SeedCechLocalization.localizationToLaurent R (inverted 0 Finset.univ)
      (intersectionCoordinates R 0 Finset.univ 0 (Finset.mem_univ 0) p 2)).coeff
        (fun _ => -1) =
    (chartCoordinates 0 0 Finset.univ (Finset.mem_univ 0) p 2) d at he
  refine he.trans ?_
  change Finsupp.equivMapDomain (exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0))
    ((p.val 2).subtypeDomain (CycleQ2HodgeTwistCech.Allowed 0 Finset.univ 2))
    (exponentEquiv 0 2 0 Finset.univ (Finset.mem_univ 0) e) = _
  rw [Finsupp.equivMapDomain_apply,Equiv.symm_apply_apply]
  rfl

/-- The original homogeneous top trace is the same ordinary cubic
residue under the actual scheme-section equivalence, over the entire
coefficient ring. -/
theorem structure_trace_cubic
    (s : Γ(threefold φ,Finset.univ.inf (coordinateOpen φ))) :
    CycleQ2HodgeTwistTorusChart.structureTopSectionTrace φ h s =
      CycleQ2TorusCubicTrace.residueTrace φ 0 h (inverted 0 Finset.univ)
        (toCubicSections φ h 0 Finset.univ (Finset.mem_univ 0) s) := by
  let E := intersectionCoordinates R 0 Finset.univ 0 (Finset.mem_univ 0)
  let b := CycleQ2GeometricHodgeThreefoldCubic.localizedBasis φ 0 h
    (Submonoid.powers (CycleQ2SeedCechLocalization.baseProduct R (inverted 0 Finset.univ)))
  let x := toCubicSections φ h 0 Finset.univ (Finset.mem_univ 0) s
  let p := E.symm (b.equivFun x)
  have hp : CycleQ2HodgeTwistCoordinates.read
      (CycleQ2HodgeTwistTorusChart.structureChart φ h)
      (CycleQ2HodgeTwistAnchor.torus_le_face φ Finset.univ) s = p.val := by
    rw [CycleQ2HodgeTwistTorusChart.read_structure_face φ h 0 Finset.univ (Finset.mem_univ 0)]
    change (structureCoordinates φ 0 h Finset.univ (Finset.mem_univ 0) 0
      (CycleQ2GeometricProjectiveCurve.Twisted.resEquiv (threefold φ).sheaf
        (CycleQ2HodgeTwistFaces.face_inf φ 0 Finset.univ (Finset.mem_univ 0)).le
        (CycleQ2HodgeTwistFaces.face_inf φ 0 Finset.univ (Finset.mem_univ 0)).ge
        ((CycleQ2HodgeThreefoldTwist.chartFrame φ 0 0 _ (Finset.inf_le (Finset.mem_univ 0)))
          ((CycleQ2HodgeThreefoldTwist.chartFrame φ 0 0 _
            (Finset.inf_le (Finset.mem_univ 0))).symm s)))).val = p.val
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hc := intersection_top_coefficient p
  change (CycleQ2SeedCechLocalization.localizationToLaurent R (inverted 0 Finset.univ)
    (E (E.symm (b.equivFun x)) 2)).coeff (fun _ => -1) = p.val 2 negativeExponent at hc
  rw [AddEquiv.apply_symm_apply] at hc
  change (CycleQ2HodgeTwistCoordinates.read (CycleQ2HodgeTwistTorusChart.structureChart φ h)
      (CycleQ2HodgeTwistAnchor.torus_le_face φ Finset.univ) s) 2 negativeExponent =
    (CycleQ2SeedCechLocalization.localizationToLaurent R (inverted 0 Finset.univ)
      (b.equivFun x 2)).coeff (fun _ => -1)
  rw [hp]
  exact hc.symm

end CycleQ2HodgeCubicSectionComparison

namespace CycleQ2HodgeMonicFaceTrace

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen vertexCoefficient)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeNormalFirstChart (polynomial monicUnit)
open CycleQ2HodgeCubicIntrinsicForms (sectionEquiv realize)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)

variable {k : Type} [Field k] [CharZero k]
  (φ : CoeffRing →+* k) (hm : φ vertexCoefficient = 1)
  (hg : Ideal.span (Set.range (gradientEntry (polynomial φ 0))) = ⊤)
  [SmoothOfRelativeDimension 3 (toBase φ)]

/-- The original homogeneous residue generator, multiplied by the
actual relative chart volume and realized in the intrinsic sheaf. -/
def normalizedSection (a : k) :
    (sheafForms (toBase φ) 3 3).obj.obj (op (Finset.univ.inf (coordinateOpen φ))) :=
  realize φ (monicUnit φ hm) 0 Finset.univ (Finset.mem_univ 0) 3
    (sectionEquiv φ (monicUnit φ hm) 0 Finset.univ (Finset.mem_univ 0)
      (CycleQ2HodgeTwistTorusChart.structureTopGenerator φ (monicUnit φ hm) a) •
        nativeVolume φ hm 0 Finset.univ hg)

theorem sectionTrace_normalizedSection (a : k) :
    sectionTrace φ hm 0 Finset.univ (Finset.mem_univ 0) hg
      (normalizedSection φ hm hg a) = a := by
  rw [normalizedSection,sectionTrace_realize_volume]
  change CycleQ2TorusCubicTrace.residueTrace φ 0 (monicUnit φ hm)
    (CycleQ2HodgeTwistLocalization.inverted 0 Finset.univ)
    (CycleQ2HodgeCubicSectionComparison.toCubicSections φ (monicUnit φ hm)
      0 Finset.univ (Finset.mem_univ 0)
      (CycleQ2HodgeTwistTorusChart.structureTopGenerator φ (monicUnit φ hm) a)) = a
  rw [← CycleQ2HodgeCubicSectionComparison.structure_trace_cubic,
    CycleQ2HodgeTwistTorusChart.structureTopSectionTrace_generator]

theorem normalizedSection_ne_zero {a : k} (ha : a ≠ 0) : normalizedSection φ hm hg a ≠ 0 := by
  intro hz
  have he := congrArg (sectionTrace φ hm 0 Finset.univ (Finset.mem_univ 0) hg) hz
  rw [sectionTrace_normalizedSection,map_zero] at he
  exact ha he

end CycleQ2HodgeMonicFaceTrace

namespace CycleQ2GenericHodgeCanonicalTrace

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2MonicGenericAmbientChart (K genericCoeff_vertex)
open CycleQ2MonicGenericSmooth (coeff gradientOpen_unit explicit_projective_smooth)
open CycleQ2GeometricHodgeThreefold (toBase coordinateOpen chartGradient_span)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeNormalFirstChart (polynomial gradient_span)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential)

local instance : SmoothOfRelativeDimension 3 (toBase coeff) := explicit_projective_smooth

theorem normalGradient_span (i : Fin 4) :
    Ideal.span (Set.range (gradientEntry (polynomial coeff i))) = ⊤ :=
  gradient_span coeff i (chartGradient_span coeff gradientOpen_unit i)

def torusSectionTrace :
    (sheafForms (toBase coeff) 3 3).obj.obj (op (Finset.univ.inf (coordinateOpen coeff))) →+ K :=
  CycleQ2HodgeMonicFaceTrace.sectionTrace coeff genericCoeff_vertex 0 Finset.univ
    (Finset.mem_univ 0) (normalGradient_span 0)

theorem torusSectionTrace_differential
    (η : (sheafForms (toBase coeff) 3 2).obj.obj (op (Finset.univ.inf (coordinateOpen coeff)))) :
    torusSectionTrace ((differential (toBase coeff) 3 2).hom.app _ η) = 0 :=
  CycleQ2HodgeMonicFaceTrace.sectionTrace_differential coeff genericCoeff_vertex 0 Finset.univ
    (Finset.mem_univ 0) (normalGradient_span 0) η

def normalizedSection (a : K) :
    (sheafForms (toBase coeff) 3 3).obj.obj (op (Finset.univ.inf (coordinateOpen coeff))) :=
  CycleQ2HodgeMonicFaceTrace.normalizedSection coeff genericCoeff_vertex (normalGradient_span 0) a

theorem torusSectionTrace_normalizedSection (a : K) : torusSectionTrace (normalizedSection a) = a :=
  CycleQ2HodgeMonicFaceTrace.sectionTrace_normalizedSection coeff genericCoeff_vertex
    (normalGradient_span 0) a

theorem normalizedSection_one_ne_zero : normalizedSection 1 ≠ 0 :=
  CycleQ2HodgeMonicFaceTrace.normalizedSection_ne_zero coeff genericCoeff_vertex
    (normalGradient_span 0) one_ne_zero

end CycleQ2GenericHodgeCanonicalTrace
end

#print axioms CycleQ2HodgeCubicSectionComparison.structure_trace_cubic
#print axioms CycleQ2GenericHodgeCanonicalTrace.torusSectionTrace_differential
#print axioms CycleQ2GenericHodgeCanonicalTrace.normalizedSection_one_ne_zero

noncomputable section
namespace CycleQ2HodgeNormalCoordinateChange

open MvPolynomial Module
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2IncidenceDehomogenizedChart (weight_last weight_castSucc)
open CycleQ2GeometricHodgeThreefold (equation equation_homogeneous)
open CycleQ2HodgeEuler (dehom)
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk)
open CycleQ2HodgeNormalFirstChart (polynomial)
open CycleQ2LiteralThreefoldResidueCoordinates
  (linearValues linearDirections jacobianColumns jacobianColumns_det changedCoordinate)
open scoped TensorProduct

variable {K : Type} [CommRing K]

/-- Dehomogenization of the original weighted polynomial, in the
normal-first order used by the actual residue frame. -/
def normalDehom (i : Fin 4) : MvPolynomial (Fin 5) K →ₐ[K] Poly K :=
  (MvPolynomial.renameEquiv K (finRotate 4)).toAlgHom.comp (dehom i)

theorem normalDehom_equation (φ : CoeffRing →+* K) (i : Fin 4) :
    normalDehom i (equation φ) = polynomial φ i := rfl

@[simp] theorem normalDehom_last (i : Fin 4) :
    normalDehom (K := K) i (X (Fin.last 4)) = X 0 := by
  have hj : i.castSucc.succAbove (Fin.last 3) = Fin.last 4 := by fin_cases i <;> decide
  change rename (finRotate 4) (dehom i (X (Fin.last 4))) = X 0
  rw [← hj,CycleQ2HodgeEuler.dehom_X_succAbove,rename_X] <;> rfl

@[simp] theorem normalDehom_linear (i l : Fin 4) :
    normalDehom (K := K) i (X l.castSucc) =
      Fin.insertNth i 1 (fun a : Fin 3 => (X a.succ : Poly K)) l := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) l
  · change rename (finRotate 4) (dehom i (X i.castSucc)) = 1
    rw [CycleQ2HodgeEuler.dehom_X_self,map_one]
  · have hj : i.castSucc.succAbove a.castSucc = (i.succAbove a).castSucc := by
      fin_cases i <;> fin_cases a <;> decide
    change rename (finRotate 4) (dehom i (X (i.succAbove a).castSucc)) = _
    rw [Fin.insertNth_apply_succAbove,← hj,CycleQ2HodgeEuler.dehom_X_succAbove,rename_X]
    congr 1
    fin_cases a <;> decide

variable {R : Type} [CommRing R] [Algebra K R]

theorem eval_linear (i l : Fin 4) (x : Option (Fin 3) → R) :
    aeval (x ∘ finSuccEquiv 3) (normalDehom (K := K) i (X l.castSucc)) =
      linearValues i x l := by
  rw [normalDehom_linear]
  refine Fin.succAboveCases i ?_ (fun a => ?_) l
  · simp [linearValues]
  · simp [linearValues,Function.comp_def]

theorem changed_linear (i j l : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * linearValues i x j = 1) :
    linearValues j (changedCoordinate i j x t) l = t * linearValues i x l := by
  refine Fin.succAboveCases j ?_ (fun a => ?_) l
  · simpa only [linearValues,Fin.insertNth_apply_same] using ht.symm
  · simp only [linearValues,Fin.insertNth_apply_succAbove,changedCoordinate]
    exact mul_comm _ _

/-- The weighted homogeneity of the original equation gives its exact
change in the actual normal-first affine variables over any coefficient
algebra. -/
theorem homogeneous_change (i j : Fin 4) (x : Option (Fin 3) → R) (t : R)
    (ht : t * linearValues i x j = 1) (p : MvPolynomial (Fin 5) K)
    {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    aeval (changedCoordinate i j x t ∘ finSuccEquiv 3) (normalDehom j p) =
      t^n * aeval (x ∘ finSuccEquiv 3) (normalDehom i p) := by
  let f := (aeval (x ∘ finSuccEquiv 3)).comp (normalDehom (K := K) i)
  let y : Fin 5 → R := fun l => f (X l)
  have hf : aeval y = f := by ext l; exact aeval_X y l
  have he : (aeval (changedCoordinate i j x t ∘ finSuccEquiv 3)).comp
      (normalDehom (K := K) j) = aeval (fun l => t^geometricWeight l * y l) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [aeval_X]
    change aeval (changedCoordinate i j x t ∘ finSuccEquiv 3)
      (normalDehom (K := K) j (X l)) =
        t^geometricWeight l * aeval (x ∘ finSuccEquiv 3) (normalDehom (K := K) i (X l))
    refine Fin.lastCases ?_ (fun a => ?_) l
    · rw [normalDehom_last,normalDehom_last,aeval_X,aeval_X,weight_last]
      change x none * t^2 = t^2 * x none
      exact mul_comm _ _
    · rw [eval_linear,eval_linear,weight_castSucc,pow_one,changed_linear i j a x t ht]
  change ((aeval (changedCoordinate i j x t ∘ finSuccEquiv 3)).comp
      (normalDehom (K := K) j)) p = t^n * f p
  rw [he,← hf]
  exact CycleQ2IncidenceDehomogenizedChart.weighted_homogeneous_eval_scale
    (algebraMap K R) y t p n hp

theorem equation_change (φ : CoeffRing →+* K) (i j : Fin 4)
    (x : Option (Fin 3) → R) (t : R) (ht : t * linearValues i x j = 1) :
    aeval (changedCoordinate i j x t ∘ finSuccEquiv 3) (polynomial φ j) =
      t^6 * aeval (x ∘ finSuccEquiv 3) (polynomial φ i) :=
  homogeneous_change i j x t ht (equation φ) (equation_homogeneous φ)

private def realization (x : Option (Fin 3) → R) :
    (Fin 4 → R) →ₗ[R] KaehlerDifferential K R :=
  (Pi.basisFun R (Fin 4)).constr R
    (fun l => KaehlerDifferential.D K R (x (finSuccEquiv 3 l)))

private theorem realization_basis (x : Option (Fin 3) → R) (l : Fin 4) :
    realization (K := K) x (Pi.basisFun R (Fin 4) l) =
      KaehlerDifferential.D K R (x (finSuccEquiv 3 l)) :=
  Basis.constr_basis _ _ _ _

private theorem realization_direction (i : Fin 4) (x : Option (Fin 3) → R) (l : Fin 4) :
    realization (K := K) x (linearDirections (R := R) i l) =
      KaehlerDifferential.D K R (linearValues i x l) := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) l
  · simp [linearDirections,linearValues]
  · simp only [linearDirections,linearValues,Fin.insertNth_apply_succAbove,
      realization_basis,finSuccEquiv_succ]

private theorem realizedColumn (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R)
    (ht : t * x (some k) = 1) (l : Fin 4) :
    realization (K := K) x (jacobianColumns i k x t l) =
      KaehlerDifferential.D K R (changedCoordinate i (i.succAbove k) x t (finSuccEquiv 3 l)) := by
  have hinv := (KaehlerDifferential.D K R).leibniz_of_mul_eq_one ht
  induction l using Fin.cases with
  | zero =>
    simp only [jacobianColumns,Fin.cons_zero,map_sub,map_smul,realization_basis,
      finSuccEquiv_zero,finSuccEquiv_succ,changedCoordinate,Derivation.leibniz,
      Derivation.leibniz_pow,hinv,Nat.reduceSub,pow_one]
    rw [← Nat.cast_smul_eq_nsmul R]
    simp only [Nat.cast_ofNat,smul_smul]
    module
  | succ l =>
    simp only [jacobianColumns,Fin.cons_succ,map_sub,map_smul,realization_direction,
      realization_basis,finSuccEquiv_succ,changedCoordinate,Derivation.leibniz,hinv,
      linearValues,smul_smul]
    module

def coordinateVolume (x : Option (Fin 3) → R) : ⋀[R]^4 (KaehlerDifferential K R) :=
  exteriorPower.ιMulti R 4 (fun l => KaehlerDifferential.D K R (x (finSuccEquiv 3 l)))

theorem coordinateVolume_change (i : Fin 4) (k : Fin 3) (x : Option (Fin 3) → R) (t : R)
    (ht : t * x (some k) = 1) :
    coordinateVolume (K := K) (changedCoordinate i (i.succAbove k) x t) =
      ((-1 : R)^(i.val+(i.succAbove k).val)*t^6) • coordinateVolume (K := K) x := by
  have he := congrArg (exteriorPower.map 4 (realization (K := K) x))
    (CycleQ2ResidueWedgeLinear.topWedge_eq_det_smul
      (Pi.basisFun R (Fin 4)) (jacobianColumns i k x t))
  simpa only [exteriorPower.map_apply_ιMulti,map_smul,Function.comp_def,
    realizedColumn i k x t ht,realization_basis,coordinateVolume,jacobianColumns_det] using he

end CycleQ2HodgeNormalCoordinateChange
end

#print axioms CycleQ2HodgeNormalCoordinateChange.equation_change
#print axioms CycleQ2HodgeNormalCoordinateChange.coordinateVolume_change

noncomputable section
namespace CycleQ2HodgeNormalCoordinateChange

open MvPolynomial Module
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk)
open CycleQ2HodgeNormalFirstChart (polynomial)
open CycleQ2HodgeEulerContractionCharts (gradientEntry dx gradient_relation)
open CycleQ2HodgeHypersurfaceVolume (volume bezout gradient_smul_volume)
open CycleQ2LiteralThreefoldResidueCoordinates (linearValues changedCoordinate)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2ExteriorTopBaseChange
open scoped TensorProduct KaehlerDifferential

variable {K R S : Type} [CommRing K] [CommRing R] [Algebra K R]
  [CommRing S] [Algebra R S] [Algebra K S] [IsScalarTower K R S]

private theorem tensor_scale (a : R) (m : Ω[R⁄K]) :
    (1 : S) ⊗ₜ[R] (a • m) = algebraMap R S a • ((1 : S) ⊗ₜ[R] m) := by
  rw [TensorProduct.tmul_smul]
  exact (IsScalarTower.algebraMap_smul S a _).symm

def chartMap (q : Poly K) (x : Option (Fin 3) → R)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) q) = 0) : Hyp q →ₐ[K] S :=
  Ideal.Quotient.liftₐ _
    ((IsScalarTower.toAlgHom K R S).comp (aeval (x ∘ finSuccEquiv 3)))
    (fun _ hx => (Ideal.span_singleton_le_iff_mem
      (RingHom.ker ((IsScalarTower.toAlgHom K R S).comp
        (aeval (x ∘ finSuccEquiv 3))).toRingHom)).mpr hz hx)

@[simp] theorem chartMap_mk (q : Poly K) (x : Option (Fin 3) → R)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) q) = 0) (p : Poly K) :
    chartMap q x hz (mk q p) = algebraMap R S (aeval (x ∘ finSuccEquiv 3) p) := rfl

def restrictedDifferentials (x : Option (Fin 3) → R) (l : Fin 4) : S ⊗[R] Ω[R⁄K] :=
  (1 : S) ⊗ₜ[R] KaehlerDifferential.D K R (x (finSuccEquiv 3 l))

theorem map_restrictedDifferentials (q : Poly K) (x : Option (Fin 3) → R)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) q) = 0) (l : Fin 4) :
    KaehlerDifferential.mapBaseChange K R S (restrictedDifferentials (K := K) (S := S) x l) =
      dx q (chartMap q x hz) l := by
  rw [restrictedDifferentials,KaehlerDifferential.mapBaseChange_tmul,one_smul,
    KaehlerDifferential.map_D]
  change KaehlerDifferential.D K S _ = KaehlerDifferential.D K S _
  rw [chartMap_mk,aeval_X] <;> rfl

theorem conormal_gradient (q : Poly K) (x : Option (Fin 3) → R)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) q) = 0) :
    (1 : S) ⊗ₜ[R] KaehlerDifferential.D K R (aeval (x ∘ finSuccEquiv 3) q) =
      ∑ l : Fin 4, chartMap q x hz (gradientEntry q l) •
        restrictedDifferentials (K := K) (S := S) x l := by
  rw [CycleQ2PolynomialChainRule.apply (aeval (x ∘ finSuccEquiv 3))
    (KaehlerDifferential.D K R),TensorProduct.tmul_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [tensor_scale]
  simp only [gradientEntry,chartMap_mk,restrictedDifferentials,aeval_X,Function.comp_apply]

theorem targetEquation_zero (φ : CoeffRing →+* K) (i j : Fin 4)
    (x : Option (Fin 3) → R) (t : R) (ht : t * linearValues i x j = 1)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) (polynomial φ i)) = 0) :
    algebraMap R S
      (aeval (changedCoordinate i j x t ∘ finSuccEquiv 3) (polynomial φ j)) = 0 := by
  rw [equation_change φ i j x t ht,map_mul,hz,mul_zero]

theorem conormal_change (φ : CoeffRing →+* K) (i j : Fin 4)
    (x : Option (Fin 3) → R) (t : R) (ht : t * linearValues i x j = 1)
    (hz : algebraMap R S (aeval (x ∘ finSuccEquiv 3) (polynomial φ i)) = 0) :
    (1 : S) ⊗ₜ[R] KaehlerDifferential.D K R
      (aeval (changedCoordinate i j x t ∘ finSuccEquiv 3) (polynomial φ j)) =
      (algebraMap R S t)^6 • ((1 : S) ⊗ₜ[R] KaehlerDifferential.D K R
        (aeval (x ∘ finSuccEquiv 3) (polynomial φ i))) := by
  rw [equation_change φ i j x t ht,Derivation.leibniz,TensorProduct.tmul_add,
    tensor_scale,tensor_scale,hz,zero_smul,add_zero,map_pow]

abbrev Ambient (K : Type) [CommRing K] (k : Fin 3) :=
  Localization.Away (X k.succ : Poly K)

def overlapCoordinates (k : Fin 3) (a : Option (Fin 3)) : Ambient K k :=
  algebraMap (Poly K) (Ambient K k) (X ((finSuccEquiv 3).symm a))

def overlapInverse (k : Fin 3) : Ambient K k :=
  IsLocalization.Away.invSelf (X k.succ : Poly K)

theorem overlapInverse_mul (k : Fin 3) :
    overlapInverse (K := K) k * overlapCoordinates k (some k) = 1 := by
  rw [mul_comm]
  exact IsLocalization.Away.mul_invSelf _

def overlapBasis (k : Fin 3) : Basis (Fin 4) (Ambient K k) Ω[Ambient K k⁄K] := by
  letI : Algebra.FormallyEtale (Poly K) (Ambient K k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Ambient K k)
      (Submonoid.powers (X k.succ : Poly K))
  exact ((KaehlerDifferential.mvPolynomialBasis K (Fin 4)).baseChange (Ambient K k)).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (Poly K) (Ambient K k))

@[simp] theorem overlapBasis_apply (k : Fin 3) (l : Fin 4) :
    overlapBasis (K := K) k l = KaehlerDifferential.D K (Ambient K k)
      (overlapCoordinates k (finSuccEquiv 3 l)) := by
  simp only [overlapBasis,Basis.map_apply,Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change KaehlerDifferential.mapBaseChange K (Poly K) (Ambient K k) _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]
  simp only [overlapCoordinates,Equiv.symm_apply_apply]

variable (φ : CoeffRing →+* K) (i : Fin 4) (k : Fin 3)
  (B : Type) [CommRing B] [Algebra (Ambient K k) B]
  [Algebra K B] [IsScalarTower K (Ambient K k) B]

private theorem overlap_linear_inverse :
    overlapInverse (K := K) k * linearValues i (overlapCoordinates k) (i.succAbove k) = 1 := by
  simpa only [linearValues,Fin.insertNth_apply_succAbove] using overlapInverse_mul (K := K) k

private theorem overlap_factor_unit :
    IsUnit ((algebraMap (Ambient K k) B (overlapInverse k))^6) := by
  have hu : IsUnit (overlapInverse (K := K) k) :=
    isUnit_of_dvd_one ⟨overlapCoordinates k (some k),(overlapInverse_mul k).symm⟩
  exact (hu.map (algebraMap (Ambient K k) B)).pow 6

private theorem restricted_volume_change :
    exteriorPower.ιMulti B 4
      (restrictedDifferentials (K := K) (S := B)
        (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))) =
      ((-1 : B)^(i.val+(i.succAbove k).val) *
        (algebraMap (Ambient K k) B (overlapInverse k))^6) •
      exteriorPower.ιMulti B 4 (restrictedDifferentials (K := K) (S := B) (overlapCoordinates k)) := by
  have he := congrArg (topBaseChange (S := B) (overlapBasis (K := K) k))
    (coordinateVolume_change (K := K) i k (overlapCoordinates k) (overlapInverse k)
      (overlapInverse_mul k))
  simpa only [coordinateVolume,restrictedDifferentials,topBaseChange_wedge,
    map_smulₛₗ,map_mul,map_pow,map_neg,map_one] using he

/-- The two actual regular quotient residues agree after their projective
orientation signs. Both conormals and both ambient volumes have been
computed from the same original weighted equation over the coefficient
ring; no choice of a Jacobian pivot enters this equality. -/
theorem volume_overlap
    (hgi : Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
    (hgj : Ideal.span (Set.range (gradientEntry (polynomial φ (i.succAbove k)))) = ⊤)
    (hf : algebraMap (Ambient K k) B
      (aeval (overlapCoordinates k ∘ finSuccEquiv 3) (polynomial φ i)) = 0) :
    (-1 : B)^(i.succAbove k).val • exteriorPullback
      (chartMap (polynomial φ (i.succAbove k))
        (changedCoordinate i (i.succAbove k) (overlapCoordinates k) (overlapInverse k))
        (targetEquation_zero φ i (i.succAbove k) (overlapCoordinates k) (overlapInverse k)
          (overlap_linear_inverse i k) hf)) 3 (volume (polynomial φ (i.succAbove k)) hgj) =
      (-1 : B)^i.val • exteriorPullback
        (chartMap (polynomial φ i) (overlapCoordinates k) hf) 3 (volume (polynomial φ i) hgi) := by
  let j := i.succAbove k
  let x := overlapCoordinates (K := K) k
  let y := changedCoordinate i j x (overlapInverse k)
  let fx := chartMap (polynomial φ i) x hf
  let fy := chartMap (polynomial φ j) y
    (targetEquation_zero φ i j x (overlapInverse k) (overlap_linear_inverse i k) hf)
  let b := (overlapBasis (K := K) k).baseChange B
  let v := restrictedDifferentials (K := K) (S := B) y
  let q := KaehlerDifferential.mapBaseChange K (Ambient K k) B
  let g := (algebraMap (Ambient K k) B (overlapInverse k))^6
  let a : Fin 4 → B := fun l => fx (gradientEntry (polynomial φ i) l)
  let a' : Fin 4 → B := fun l => fy (gradientEntry (polynomial φ j) l)
  have hb : ⇑b = restrictedDifferentials (K := K) (S := B) x := by
    funext l
    simp only [b,Basis.baseChange_apply,overlapBasis_apply] <;> rfl
  have hx : q ∘ b = dx (polynomial φ i) fx := by
    rw [hb]
    exact funext (map_restrictedDifferentials (polynomial φ i) x hf)
  have hy : q ∘ v = dx (polynomial φ j) fy :=
    funext (map_restrictedDifferentials (polynomial φ j) y _)
  have hz : ∑ l, a l • q (b l) = 0 := by
    change ∑ l, a l • (q ∘ b) l = 0
    rw [hx]
    exact gradient_relation (polynomial φ i) fx
  have hn : ∑ l, a' l • v l = g • ∑ l, a l • b l := by
    rw [hb]
    change (∑ l, fy (gradientEntry (polynomial φ j) l) •
      restrictedDifferentials (K := K) (S := B) y l) = _
    rw [← conormal_gradient,← conormal_gradient]
    exact conormal_change φ i j x (overlapInverse k) (overlap_linear_inverse i k) hf
  have hv0 : b.det v = (-1 : B)^(i.val+j.val) * g := by
    have hw := restricted_volume_change i k B
    rw [← hb] at hw
    have he := congrArg (topCoordinate b) hw
    simpa only [map_smul,topCoordinate_wedge,topCoordinate_basis,smul_eq_mul,mul_one] using he
  have hv : (-1 : B)^j.val * b.det v = g * (-1 : B)^i.val := by
    rw [hv0,pow_add]
    have hs : (-1 : B)^j.val * (-1 : B)^j.val = 1 := by rw [← mul_pow]; simp
    calc
      _ = ((-1 : B)^j.val * (-1 : B)^j.val) * (g * (-1 : B)^i.val) := by ring
      _ = _ := by rw [hs,one_mul]
  obtain ⟨c,hc⟩ := bezout (polynomial φ i) hgi
  obtain ⟨c',hc'⟩ := bezout (polynomial φ j) hgj
  have hcx : ∑ l, fx (c l) * a l = 1 := by
    simpa only [a,map_sum,map_mul,map_one] using congrArg fx hc
  have hcy : ∑ l, fy (c' l) * a' l = 1 := by
    simpa only [a',map_sum,map_mul,map_one] using congrArg fy hc'
  apply CycleQ2LiteralThreefoldResidueGluing.bezout_residue_change
    b q a a' _ _ hcx hcy v g _ _ (overlap_factor_unit k B) hv hn hz
  · intro l
    rw [hx]
    exact gradient_smul_volume (polynomial φ i) hgi fx l
  · intro l
    rw [hy]
    exact gradient_smul_volume (polynomial φ j) hgj fy l

end CycleQ2HodgeNormalCoordinateChange
end

#print axioms CycleQ2HodgeNormalCoordinateChange.volume_overlap

noncomputable section
namespace CycleQ2HodgeCanonicalChartVolumes

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2IncidenceDehomogenizedChart (weight_last weight_castSucc)
open CycleQ2GeometricHodgeThreefold
  (threefold toBase coordinateOpen coord grade quotient quotient_mem_grade
    coord_mem_grade weightOne_mem_grade)
open CycleQ2HodgeEulerChartDerivations (Poly Hyp mk mk_equation)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeNormalFirstChart (polynomial affineChart affineChart_overBase)
open CycleQ2HodgeNormalCoordinateChange
  (normalDehom normalDehom_last normalDehom_linear Ambient overlapCoordinates overlapInverse)
open CycleQ2LiteralThreefoldResidueCoordinates (linearValues changedCoordinate)
open CycleQ2HodgeHypersurfaceVolume (volume)
open CycleQ2HodgeTwistRatios (normalized ratio ratio_self ratio_comp normalized_change transition)
open CycleQ2RelativeAffineChartSections (chartAlgHom)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open scoped KaehlerDifferential

variable {K : Type} [Field K] [CharZero K] (φ : CoeffRing →+* K)

local instance sectionAlgebra (W : (threefold φ).Opens) : Algebra K Γ(threefold φ,W) :=
  (sectionCoefficients (toBase φ) W).toAlgebra

def sectionMap (i : Fin 4) (W : (threefold φ).Opens) (hi : W ≤ coordinateOpen φ i) :
    Hyp (polynomial φ i) →ₐ[K] Γ(threefold φ,W) :=
  chartAlgHom (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
    (Over.mk (homOfLE hi))

/-- The actual normal-first affine chart map sends every homogeneous
polynomial to its original projective fraction. -/
theorem sectionMap_normalized (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (n : ℕ) (p : MvPolynomial (Fin 5) K)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    sectionMap φ i W hi (mk (polynomial φ i) (normalDehom i p)) =
      normalized φ i (quotient φ p) (by simpa using quotient_mem_grade φ p hp) W hi := by
  change CycleQ2GeometricAffineChartSections.chartSection (affineChart φ i)
    (Over.mk (homOfLE hi))
    (CycleQ2HodgeNormalFirstChart.chartEquiv φ i
      (CycleQ2HodgeEuler.chartMap φ i (CycleQ2HodgeEuler.dehom i p))) = _
  rw [← CycleQ2HodgeMonicFaceTrace.normalSection_raw φ i,
    ← CycleQ2HodgeEulerChartBinding.chartEquiv_fraction φ i n p hp,
    CycleQ2HodgeCubicSectionComparison.affineChartSection] <;> rfl

theorem sectionMap_normal (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) :
    sectionMap φ i W hi (mk (polynomial φ i) (X 0)) =
      normalized φ i (coord φ (Fin.last 4))
        (show coord φ (Fin.last 4) ∈ grade φ 2 from coord_mem_grade φ (Fin.last 4)) W hi := by
  simpa only [normalDehom_last,weight_last] using sectionMap_normalized φ i W hi 2
    (X (Fin.last 4)) (by simpa only [weight_last] using
      isWeightedHomogeneous_X K geometricWeight (Fin.last 4))

theorem sectionMap_base (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (a : Fin 3) :
    sectionMap φ i W hi (mk (polynomial φ i) (X a.succ)) = ratio φ i (i.succAbove a) W hi := by
  simpa only [normalDehom_linear,Fin.insertNth_apply_succAbove,weight_castSucc] using
    sectionMap_normalized φ i W hi 1 (X (i.succAbove a).castSucc)
      (by simpa only [weight_castSucc] using
        isWeightedHomogeneous_X K geometricWeight (i.succAbove a).castSucc)

def coordinateValues (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (a : Option (Fin 3)) : Γ(threefold φ,W) :=
  sectionMap φ i W hi (mk (polynomial φ i) (X ((finSuccEquiv 3).symm a)))

theorem linearValues_eq_ratio (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (l : Fin 4) :
    linearValues i (coordinateValues φ i W hi) l = ratio φ i l W hi := by
  refine Fin.succAboveCases i ?_ (fun a => ?_) l
  · rw [ratio_self] <;> rfl
  · change sectionMap φ i W hi (mk (polynomial φ i) (X a.succ)) = _
    exact sectionMap_base φ i W hi a

/-- The scheme-theoretic fractions give exactly the weighted coordinate
change used by the ambient conormal calculation. -/
theorem coordinateValues_change (i j : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (hj : W ≤ coordinateOpen φ j) :
    coordinateValues φ j W hj =
      changedCoordinate i j (coordinateValues φ i W hi) (ratio φ j i W hj) := by
  funext a
  cases a with
  | none =>
    change sectionMap φ j W hj (mk (polynomial φ j) (X 0)) =
      sectionMap φ i W hi (mk (polynomial φ i) (X 0)) * ratio φ j i W hj ^ 2
    rw [sectionMap_normal,sectionMap_normal,
      normalized_change φ j i _ _ W hj hi,mul_comm]
  | some a =>
    change sectionMap φ j W hj (mk (polynomial φ j) (X a.succ)) =
      linearValues i (coordinateValues φ i W hi) (j.succAbove a) * ratio φ j i W hj
    rw [sectionMap_base,linearValues_eq_ratio,mul_comm,ratio_comp]

variable (i : Fin 4) (k : Fin 3) (W : (threefold φ).Opens)
  (hi : W ≤ coordinateOpen φ i) (hj : W ≤ coordinateOpen φ (i.succAbove k))

private theorem overlap_coordinate_unit :
    IsUnit (sectionMap φ i W hi (mk (polynomial φ i) (X k.succ))) := by
  rw [sectionMap_base]
  exact (transition φ i (i.succAbove k) W hi hj).isUnit

def overlapMap : Ambient K k →ₐ[K] Γ(threefold φ,W) where
  toRingHom := IsLocalization.Away.lift (X k.succ : Poly K)
    (g := ((sectionMap φ i W hi).comp (mk (polynomial φ i))).toRingHom)
    (overlap_coordinate_unit φ i k W hi hj)
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply K (Poly K) (Ambient K k),IsLocalization.Away.lift_eq]
    exact ((sectionMap φ i W hi).comp (mk (polynomial φ i))).commutes a

theorem overlapMap_polynomial (p : Poly K) :
    overlapMap φ i k W hi hj (algebraMap (Poly K) (Ambient K k) p) =
      sectionMap φ i W hi (mk (polynomial φ i) p) :=
  IsLocalization.Away.lift_eq _ _ _

theorem overlapMap_coordinate (a : Option (Fin 3)) :
    overlapMap φ i k W hi hj (overlapCoordinates k a) = coordinateValues φ i W hi a :=
  overlapMap_polynomial φ i k W hi hj _

theorem overlapMap_inverse :
    overlapMap φ i k W hi hj (overlapInverse k) = ratio φ (i.succAbove k) i W hj := by
  apply (overlap_coordinate_unit φ i k W hi hj).mul_left_cancel
  have he := congrArg (overlapMap φ i k W hi hj)
    (CycleQ2HodgeNormalCoordinateChange.overlapInverse_mul (K := K) k)
  rw [map_mul,overlapMap_coordinate,map_one] at he
  change overlapMap φ i k W hi hj (overlapInverse k) *
    sectionMap φ i W hi (mk (polynomial φ i) (X k.succ)) = 1 at he
  rw [sectionMap_base]
  rw [sectionMap_base] at he
  rw [mul_comm,he,ratio_comp,ratio_self]

private theorem overlap_evaluation (p : Poly K) :
    overlapMap φ i k W hi hj (aeval (overlapCoordinates k ∘ finSuccEquiv 3) p) =
      sectionMap φ i W hi (mk (polynomial φ i) p) := by
  have he : aeval (overlapCoordinates (K := K) k ∘ finSuccEquiv 3) =
      IsScalarTower.toAlgHom K (Poly K) (Ambient K k) := by
    apply MvPolynomial.algHom_ext
    intro l
    simp only [aeval_X,Function.comp_apply,overlapCoordinates,Equiv.symm_apply_apply] <;> rfl
  rw [he]
  exact overlapMap_polynomial φ i k W hi hj p

/-- The actual affine residue volumes on every common subopen obey the
same projective orientation identity. The comparison ring map is the
original scheme chart-section map, proved on the homogeneous fractions. -/
theorem volume_overlap
    (hgi : Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
    (hgj : Ideal.span (Set.range (gradientEntry (polynomial φ (i.succAbove k)))) = ⊤) :
    (-1 : Γ(threefold φ,W))^(i.succAbove k).val •
      exteriorPullback (sectionMap φ (i.succAbove k) W hj) 3
        (volume (polynomial φ (i.succAbove k)) hgj) =
    (-1 : Γ(threefold φ,W))^i.val • exteriorPullback (sectionMap φ i W hi) 3
      (volume (polynomial φ i) hgi) := by
  letI : Algebra (Ambient K k) Γ(threefold φ,W) := (overlapMap φ i k W hi hj).toRingHom.toAlgebra
  letI : IsScalarTower K (Ambient K k) Γ(threefold φ,W) :=
    IsScalarTower.of_algHom (overlapMap φ i k W hi hj)
  have hf : algebraMap (Ambient K k) Γ(threefold φ,W)
      (aeval (overlapCoordinates k ∘ finSuccEquiv 3) (polynomial φ i)) = 0 := by
    rw [show algebraMap (Ambient K k) Γ(threefold φ,W) = (overlapMap φ i k W hi hj).toRingHom from rfl,
      overlap_evaluation,mk_equation,map_zero]
  let x := overlapCoordinates (K := K) k
  let y := changedCoordinate i (i.succAbove k) x (overlapInverse k)
  have htarget : algebraMap (Ambient K k) Γ(threefold φ,W)
      (aeval (y ∘ finSuccEquiv 3) (polynomial φ (i.succAbove k))) = 0 :=
    CycleQ2HodgeNormalCoordinateChange.targetEquation_zero φ i (i.succAbove k) x
      (overlapInverse k) (by
        simpa only [linearValues,Fin.insertNth_apply_succAbove] using
          CycleQ2HodgeNormalCoordinateChange.overlapInverse_mul (K := K) k) hf
  have hs : CycleQ2HodgeNormalCoordinateChange.chartMap (polynomial φ i) x hf =
      sectionMap φ i W hi := by
    ext a
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact overlap_evaluation φ i k W hi hj p
  have he : (IsScalarTower.toAlgHom K (Ambient K k) Γ(threefold φ,W)).comp
      (aeval (y ∘ finSuccEquiv 3)) =
        (sectionMap φ (i.succAbove k) W hj).comp (mk (polynomial φ (i.succAbove k))) := by
    apply MvPolynomial.algHom_ext
    intro l
    rw [AlgHom.comp_apply,aeval_X]
    have hc := congrFun (coordinateValues_change φ i (i.succAbove k) W hi hj) (finSuccEquiv 3 l)
    change _ = coordinateValues φ (i.succAbove k) W hj (finSuccEquiv 3 l)
    rw [hc]
    cases l using Fin.cases with
    | zero =>
      change overlapMap φ i k W hi hj (x none * overlapInverse k^2) = _
      rw [map_mul,map_pow,overlapMap_coordinate,overlapMap_inverse]
    | succ l =>
      change overlapMap φ i k W hi hj
        (linearValues i x ((i.succAbove k).succAbove l) * overlapInverse k) = _
      rw [map_mul,overlapMap_inverse]
      congr 1
      refine Fin.succAboveCases i ?_ (fun a => ?_) ((i.succAbove k).succAbove l)
      · simp [linearValues]
      · simp only [linearValues,Fin.insertNth_apply_succAbove,overlapMap_coordinate]
  have ht : CycleQ2HodgeNormalCoordinateChange.chartMap
      (polynomial φ (i.succAbove k)) y htarget = sectionMap φ (i.succAbove k) W hj := by
    ext a
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact DFunLike.congr_fun he p
  have hv := CycleQ2HodgeNormalCoordinateChange.volume_overlap φ i k Γ(threefold φ,W) hgi hgj hf
  rw [hs,ht] at hv
  exact hv

end CycleQ2HodgeCanonicalChartVolumes
end

#print axioms CycleQ2HodgeCanonicalChartVolumes.sectionMap_normalized
#print axioms CycleQ2HodgeCanonicalChartVolumes.volume_overlap

noncomputable section
namespace CycleQ2HodgeCanonicalChartVolumes

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen grade coord weightOne_mem_grade)
open CycleQ2HodgeNormalFirstChart (polynomial affineChart affineChart_overBase)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeHypersurfaceVolume (volume)
open CycleQ2HodgeHypersurfaceSheafVolume (affineSectionEquiv affineSectionEquiv_apply)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)
open CycleQ2IntrinsicOrdinaryExterior (toSheaf)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2AffineDeRhamFunctorial (exteriorPullback_comp)
open CycleQ2GeometricSheafLocalIso (res)

variable {K : Type} [Field K] [CharZero K] (φ : CoeffRing →+* K)
  (hg : ∀ i : Fin 4, Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
  [SmoothOfRelativeDimension 3 (toBase φ)]

local instance sectionAlgebra' (W : (threefold φ).Opens) : Algebra K Γ(threefold φ,W) :=
  (sectionCoefficients (toBase φ) W).toAlgebra

theorem coordinate_affine (i : Fin 4) : IsAffineOpen (coordinateOpen φ i) :=
  Proj.isAffineOpen_basicOpen (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide)

/-- The residue frame on any actual affine subopen, with the original
projective orientation. -/
def affineFrame (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (hW : IsAffineOpen W) :
    Γ(threefold φ,W) ≃+ (sheafForms (toBase φ) 3 3).obj.obj (op W) :=
  (LinearEquiv.smulOfUnit ((-1 : Γ(threefold φ,W)ˣ)^i.val) :
    Γ(threefold φ,W) ≃ₗ[Γ(threefold φ,W)] Γ(threefold φ,W)).toAddEquiv.trans
      (affineSectionEquiv (polynomial φ i) (hg i) (affineChart φ i) (toBase φ)
        (affineChart_overBase φ i) (coordinate_affine φ i) (Over.mk (homOfLE hi)) hW)

theorem affineFrame_apply (i : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (hW : IsAffineOpen W) (c : Γ(threefold φ,W)) :
    affineFrame φ hg i W hi hW c =
      (toSheaf (toBase φ) 3 3).app (op W)
        (c • ((-1 : Γ(threefold φ,W))^i.val • exteriorPullback (sectionMap φ i W hi) 3
          (volume (polynomial φ i) (hg i)))) := by
  change affineSectionEquiv (polynomial φ i) (hg i) (affineChart φ i) (toBase φ)
    (affineChart_overBase φ i) (coordinate_affine φ i) (Over.mk (homOfLE hi)) hW
      ((↑((-1 : Γ(threefold φ,W)ˣ)^i.val) : Γ(threefold φ,W)) • c) = _
  rw [affineSectionEquiv_apply]
  simp only [Units.val_pow_eq_pow_val,Units.val_neg,Units.val_one,smul_eq_mul]
  apply congrArg ((toSheaf (toBase φ) 3 3).app (op W))
  rw [smul_smul]
  congr 1
  exact mul_comm _ _

/-- On a common affine open the coefficient frame is independent of
the chosen projective anchor, by the actual residue-volume identity. -/
theorem affineFrame_eq (i j : Fin 4) (W : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (hj : W ≤ coordinateOpen φ j) (hW : IsAffineOpen W) :
    affineFrame φ hg i W hi hW = affineFrame φ hg j W hj hW := by
  obtain rfl | ⟨k,rfl⟩ := i.eq_self_or_eq_succAbove j
  · rfl
  · ext c
    rw [affineFrame_apply,affineFrame_apply,
      volume_overlap φ i k W hi hj (hg i) (hg (i.succAbove k))]

theorem affineFrame_restrict (i : Fin 4) (W V : (threefold φ).Opens)
    (hi : W ≤ coordinateOpen φ i) (hW : IsAffineOpen W) (hV : IsAffineOpen V)
    (h : V ≤ W) (c : Γ(threefold φ,W)) :
    res (sheafForms (toBase φ) 3 3) h (affineFrame φ hg i W hi hW c) =
      affineFrame φ hg i V (h.trans hi) hV ((threefold φ).presheaf.map (homOfLE h).op c) := by
  rw [affineFrame_apply,affineFrame_apply]
  change (sheafForms (toBase φ) 3 3).obj.map (homOfLE h).op
    ((toSheaf (toBase φ) 3 3).app (op W) _) = _
  rw [← (toSheaf (toBase φ) 3 3).naturality_apply]
  change (toSheaf (toBase φ) 3 3).app (op V)
    (exteriorPullback (restrict (toBase φ) h) 3
      (c • ((-1 : Γ(threefold φ,W))^i.val • exteriorPullback (sectionMap φ i W hi) 3 _))) = _
  rw [map_smulₛₗ,map_smulₛₗ,map_pow,map_neg,map_one,← exteriorPullback_comp]
  have he : (restrict (toBase φ) h).comp (sectionMap φ i W hi) =
      sectionMap φ i V (h.trans hi) := by
    ext a
    exact CycleQ2RelativeAffineChartSections.chartAlgHom_restrict
      (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
      (Over.homMk (homOfLE h) : Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi)) a
  rw [he] <;> rfl

theorem coefficient_restrict (i j : Fin 4) (W V : (threefold φ).Opens)
    (hi : V ≤ coordinateOpen φ i) (hj : W ≤ coordinateOpen φ j)
    (hW : IsAffineOpen W) (hV : IsAffineOpen V) (h : V ≤ W)
    (s : (sheafForms (toBase φ) 3 3).obj.obj (op W)) :
    (affineFrame φ hg i V hi hV).symm (res (sheafForms (toBase φ) 3 3) h s) =
      (threefold φ).presheaf.map (homOfLE h).op ((affineFrame φ hg j W hj hW).symm s) := by
  obtain ⟨c,rfl⟩ := (affineFrame φ hg j W hj hW).surjective s
  rw [AddEquiv.symm_apply_apply,affineFrame_restrict,
    affineFrame_eq φ hg i j V hi (h.trans hj) hV,AddEquiv.symm_apply_apply]

theorem affineFrame_zero (W : (threefold φ).Opens)
    (h0 : W ≤ coordinateOpen φ 0) (hW : IsAffineOpen W) :
    affineFrame φ hg 0 W h0 hW =
      affineSectionEquiv (polynomial φ 0) (hg 0) (affineChart φ 0) (toBase φ)
        (affineChart_overBase φ 0) (coordinate_affine φ 0) (Over.mk (homOfLE h0)) hW := by
  ext c
  change affineSectionEquiv (polynomial φ 0) (hg 0) (affineChart φ 0) (toBase φ)
    (affineChart_overBase φ 0) (coordinate_affine φ 0) (Over.mk (homOfLE h0)) hW
      ((↑((-1 : Γ(threefold φ,W)ˣ)^(0 : Fin 4).val) : Γ(threefold φ,W)) • c) = _
  simp only [Fin.val_zero,pow_zero,Units.val_one,one_smul]

end CycleQ2HodgeCanonicalChartVolumes
end

#print axioms CycleQ2HodgeCanonicalChartVolumes.affineFrame_eq
#print axioms CycleQ2HodgeCanonicalChartVolumes.coefficient_restrict

noncomputable section
namespace CycleQ2HodgeMonicCanonicalTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase coordinateOpen vertexCoefficient)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeNormalFirstChart (polynomial monicUnit)
open CycleQ2HodgeCanonicalChartVolumes (affineFrame coefficient_restrict affineFrame_zero)
open CycleQ2HodgeCubicIntrinsicForms (face_affine)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms differential)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)
open CycleQ2HodgeTwistTorusChart
  (structureTopSectionTrace structure_top_boundary_iff_trace_zero)

variable {K : Type} [Field K] [CharZero K] (φ : CoeffRing →+* K)
  (hm : φ vertexCoefficient = 1)
  (hg : ∀ i : Fin 4, Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
  [SmoothOfRelativeDimension 3 (toBase φ)]

private abbrev Torus := Finset.univ.inf (coordinateOpen φ)
private abbrev Canonical := sheafForms (toBase φ) 3 3
private abbrev Structure := structureAdditiveSheaf (threefold φ)

private def faceAnchor (i : Fin 4) : Fin 4 := if i = 0 then 1 else 0

private theorem faceAnchor_mem (i : Fin 4) : faceAnchor i ∈ Finset.univ.erase i := by
  fin_cases i <;> decide

private theorem top_le_face (i : Fin 4) :
    Torus φ ≤ (Finset.univ.erase i).inf (coordinateOpen φ) :=
  Finset.le_inf (fun j _ => Finset.inf_le (Finset.mem_univ j))

/-- The coefficient of an actual torus three-form in the original
oriented chart-zero volume. -/
def torusCoefficient : (Canonical φ).obj.obj (op (Torus φ)) ≃+ Γ(threefold φ,Torus φ) :=
  (affineFrame φ hg 0 (Torus φ) (Finset.inf_le (Finset.mem_univ 0))
    (face_affine φ 0 Finset.univ (Finset.mem_univ 0))).symm

/-- Every face coefficient is read in an actual chart containing that
face; the 123 face uses chart one, with its orientation sign. -/
def faceCoefficients (c : NativeTopFaces (F := Canonical φ) (U := coordinateOpen φ)) :
    NativeTopFaces (F := Structure φ) (U := coordinateOpen φ) := fun i =>
  (affineFrame φ hg (faceAnchor i) ((Finset.univ.erase i).inf (coordinateOpen φ))
    (Finset.inf_le (faceAnchor_mem i))
    (face_affine φ (faceAnchor i) (Finset.univ.erase i) (faceAnchor_mem i))).symm (c i)

theorem torusCoefficient_boundary
    (c : NativeTopFaces (F := Canonical φ) (U := coordinateOpen φ)) :
    torusCoefficient φ hg (nativeTopBoundary c) = nativeTopBoundary (faceCoefficients φ hg c) := by
  have he (i : Fin 4) :
      torusCoefficient φ hg (res (Canonical φ) (top_le_face φ i) (c i)) =
        res (Structure φ) (top_le_face φ i) (faceCoefficients φ hg c i) :=
    coefficient_restrict φ hg 0 (faceAnchor i)
      ((Finset.univ.erase i).inf (coordinateOpen φ)) (Torus φ)
      (Finset.inf_le (Finset.mem_univ 0)) (Finset.inf_le (faceAnchor_mem i))
      (face_affine φ (faceAnchor i) (Finset.univ.erase i) (faceAnchor_mem i))
      (face_affine φ 0 Finset.univ (Finset.mem_univ 0)) (top_le_face φ i) (c i)
  change torusCoefficient φ hg
    (res (Canonical φ) (top_le_face φ 0) (c 0) - res (Canonical φ) (top_le_face φ 1) (c 1) +
      res (Canonical φ) (top_le_face φ 2) (c 2) - res (Canonical φ) (top_le_face φ 3) (c 3)) = _
  rw [map_sub,map_add,map_sub,he 0,he 1,he 2,he 3] <;> rfl

/-- The canonical torus trace uses the genuine homogeneous structure
trace after the actual oriented residue coefficient. -/
def sectionTrace : (Canonical φ).obj.obj (op (Torus φ)) →+ K :=
  (structureTopSectionTrace φ (monicUnit φ hm)).comp (torusCoefficient φ hg).toAddMonoidHom

theorem sectionTrace_eq : sectionTrace φ hm hg =
    CycleQ2HodgeMonicFaceTrace.sectionTrace φ hm 0 Finset.univ (Finset.mem_univ 0) (hg 0) := by
  ext s
  change structureTopSectionTrace φ (monicUnit φ hm) (torusCoefficient φ hg s) = _
  rw [CycleQ2HodgeCubicSectionComparison.structure_trace_cubic,torusCoefficient,affineFrame_zero] <;> rfl

/-- The genuine four-open Čech boundary has zero trace, including the
face not contained in chart zero. -/
theorem sectionTrace_boundary
    (c : NativeTopFaces (F := Canonical φ) (U := coordinateOpen φ)) :
    sectionTrace φ hm hg (nativeTopBoundary c) = 0 := by
  change structureTopSectionTrace φ (monicUnit φ hm)
    (torusCoefficient φ hg (nativeTopBoundary c)) = 0
  rw [torusCoefficient_boundary]
  exact (structure_top_boundary_iff_trace_zero φ (monicUnit φ hm) _).mp
    ⟨faceCoefficients φ hg c,rfl⟩

theorem sectionTrace_differential
    (η : (sheafForms (toBase φ) 3 2).obj.obj (op (Torus φ))) :
    sectionTrace φ hm hg ((differential (toBase φ) 3 2).hom.app (op (Torus φ)) η) = 0 := by
  rw [sectionTrace_eq]
  exact CycleQ2HodgeMonicFaceTrace.sectionTrace_differential φ hm 0 Finset.univ
    (Finset.mem_univ 0) (hg 0) η

theorem sectionTrace_normalizedSection (a : K) :
    sectionTrace φ hm hg (CycleQ2HodgeMonicFaceTrace.normalizedSection φ hm (hg 0) a) = a := by
  rw [sectionTrace_eq]
  exact CycleQ2HodgeMonicFaceTrace.sectionTrace_normalizedSection φ hm (hg 0) a

end CycleQ2HodgeMonicCanonicalTrace

namespace CycleQ2GenericHodgeCanonicalTrace

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2MonicGenericAmbientChart (K genericCoeff_vertex)
open CycleQ2MonicGenericSmooth (coeff explicit_projective_smooth)
open CycleQ2GeometricHodgeThreefold (toBase coordinateOpen)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)

local instance : SmoothOfRelativeDimension 3 (toBase coeff) := explicit_projective_smooth

theorem torusSectionTrace_boundary
    (c : NativeTopFaces (F := sheafForms (toBase coeff) 3 3) (U := coordinateOpen coeff)) :
    torusSectionTrace (nativeTopBoundary c) = 0 := by
  change CycleQ2HodgeMonicFaceTrace.sectionTrace coeff genericCoeff_vertex 0 Finset.univ
    (Finset.mem_univ 0) (normalGradient_span 0) (nativeTopBoundary c) = 0
  rw [← CycleQ2HodgeMonicCanonicalTrace.sectionTrace_eq coeff genericCoeff_vertex normalGradient_span]
  exact CycleQ2HodgeMonicCanonicalTrace.sectionTrace_boundary coeff genericCoeff_vertex
    normalGradient_span c

end CycleQ2GenericHodgeCanonicalTrace
end

#print axioms CycleQ2HodgeMonicCanonicalTrace.torusCoefficient_boundary
#print axioms CycleQ2HodgeMonicCanonicalTrace.sectionTrace_differential
#print axioms CycleQ2GenericHodgeCanonicalTrace.torusSectionTrace_boundary

noncomputable section
namespace CycleQ2HodgeMonicCanonicalTrace

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (toBase coordinateOpen vertexCoefficient)
open CycleQ2HodgeEulerContractionCharts (gradientEntry)
open CycleQ2HodgeNormalFirstChart (polynomial monicUnit)
open CycleQ2HodgeCanonicalChartVolumes (affineFrame)
open CycleQ2HodgeCubicIntrinsicForms (face_affine)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)
open CycleQ2HodgeTwistTorusChart (structure_top_boundary_iff_trace_zero)

variable {K : Type} [Field K] [CharZero K] (φ : CoeffRing →+* K)
  (hm : φ vertexCoefficient = 1)
  (hg : ∀ i : Fin 4, Ideal.span (Set.range (gradientEntry (polynomial φ i))) = ⊤)
  [SmoothOfRelativeDimension 3 (toBase φ)]

theorem faceCoefficients_surjective : Function.Surjective (faceCoefficients φ hg) := by
  intro c
  refine ⟨fun i => affineFrame φ hg (faceAnchor i)
    ((Finset.univ.erase i).inf (coordinateOpen φ)) (Finset.inf_le (faceAnchor_mem i))
    (face_affine φ (faceAnchor i) (Finset.univ.erase i) (faceAnchor_mem i)) (c i),?_⟩
  funext i
  exact AddEquiv.symm_apply_apply _ _

/-- Zero trace is exactly the actual native Čech boundary condition,
because every face coefficient is realized by the same residue frame. -/
theorem sectionTrace_eq_zero_iff (s : (Canonical φ).obj.obj (op (Torus φ))) :
    sectionTrace φ hm hg s = 0 ↔
      ∃ c : NativeTopFaces (F := Canonical φ) (U := coordinateOpen φ), nativeTopBoundary c = s := by
  constructor
  · intro hs
    have h : torusCoefficient φ hg s ∈
        (nativeTopBoundary (F := Structure φ) (U := coordinateOpen φ)).range :=
      (structure_top_boundary_iff_trace_zero φ (monicUnit φ hm) _).mpr hs
    obtain ⟨d,hd⟩ := h
    obtain ⟨c,hc⟩ := faceCoefficients_surjective φ hg d
    refine ⟨c,(torusCoefficient φ hg).injective ?_⟩
    rw [torusCoefficient_boundary,hc]
    exact hd
  · rintro ⟨c,rfl⟩
    exact sectionTrace_boundary φ hm hg c

end CycleQ2HodgeMonicCanonicalTrace

namespace CycleQ2GenericHodgeCanonicalTrace

open CategoryTheory AlgebraicGeometry Opposite
open CycleQ2MonicGenericAmbientChart (genericCoeff_vertex)
open CycleQ2MonicGenericSmooth (coeff explicit_projective_smooth)
open CycleQ2GeometricHodgeThreefold (toBase coordinateOpen)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)
open CycleQ2HodgeTwistCoordinates (NativeTopFaces nativeTopBoundary)

local instance : SmoothOfRelativeDimension 3 (toBase coeff) := explicit_projective_smooth

theorem torusSectionTrace_eq_zero_iff
    (s : (sheafForms (toBase coeff) 3 3).obj.obj (op (Finset.univ.inf (coordinateOpen coeff)))) :
    torusSectionTrace s = 0 ↔
      ∃ c : NativeTopFaces (F := sheafForms (toBase coeff) 3 3) (U := coordinateOpen coeff),
        nativeTopBoundary c = s := by
  change CycleQ2HodgeMonicFaceTrace.sectionTrace coeff genericCoeff_vertex 0 Finset.univ
    (Finset.mem_univ 0) (normalGradient_span 0) s = 0 ↔ _
  rw [← CycleQ2HodgeMonicCanonicalTrace.sectionTrace_eq coeff genericCoeff_vertex normalGradient_span]
  exact CycleQ2HodgeMonicCanonicalTrace.sectionTrace_eq_zero_iff coeff genericCoeff_vertex
    normalGradient_span s

end CycleQ2GenericHodgeCanonicalTrace
end

#print axioms CycleQ2HodgeMonicCanonicalTrace.sectionTrace_eq_zero_iff
#print axioms CycleQ2GenericHodgeCanonicalTrace.torusSectionTrace_eq_zero_iff
