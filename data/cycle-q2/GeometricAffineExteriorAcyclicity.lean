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
