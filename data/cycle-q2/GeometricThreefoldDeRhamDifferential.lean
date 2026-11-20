import Proposal.GeometricLiteralThreefoldDifferentialFrame
import Proposal.GeometricLiteralThreefoldFirstDifferential
import Proposal.GeometricLiteralThreefoldExteriorDescentNative

/-!
# Exterior forms and the genuine second exterior differential

The exterior basis of the actual one-form frame identifies the exterior
presheaf with its sheafification on the chart. The proof retains the
canonical exterior section map. On the original threefold that map
binds the derivative in exact Kähler frames to the exterior sheaves.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2ChartExteriorSections

open AlgebraicGeometry CategoryTheory Opposite Module TopologicalSpace
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricExteriorSheaf CycleQ2GeometricExteriorLocalFrames
open CycleQ2LocalSheafificationFrame CycleQ2LiteralThreefoldDifferentialFrame

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  {d : ℕ} (b : Basis (Fin d) A (KaehlerDifferential ℂ A)) (n : ℕ)

private abbrev Cotangent := differentialSheaf X.sheaf (schemeCoefficient f)
private abbrev P := exteriorPresheaf X.sheaf.obj (Cotangent f).val n
private abbrev E := exteriorSheaf X.sheaf (Cotangent f).val n
private abbrev UnitOn := SheafOfModules.unit ((ringSheaf X.sheaf).over U)
private abbrev presentation :=
  @overPresentation X (ringSheaf X.sheaf) (P f n) U (E f n)
    (toExteriorSheaf X.sheaf (Cotangent f).val n)

local instance sectionModule (N : SheafOfModules.{0} (ringSheaf X.sheaf)) (V : X.Opens) :
    Module Γ(X,V) (N.val.obj (op V)) := by
  change Module ((ringSheaf X.sheaf).obj.obj (op V)) (N.val.obj (op V))
  infer_instance

local instance chartSectionModule (N : ChartModule (X := X) (U := U)) (V : Over U) :
    Module Γ(X,V.left) (N.val.obj (op V)) := by
  change Module (((ringSheaf X.sheaf).over U).obj.obj (op V)) (N.val.obj (op V))
  infer_instance

private def oneBasis (V : Over U) :
    Basis (Fin d) Γ(X,V.left) ((Cotangent f).val.obj (op V.left)) :=
  sectionBasis e f h b V

private def wedgeBasis (V : Over U) :
    Basis (Set.powersetCard (Fin d) n) Γ(X,V.left)
      (⋀[Γ(X,V.left)]^n ((Cotangent f).val.obj (op V.left))) :=
  (oneBasis e f h b V).exteriorPower n

private theorem basis_restrict {V W : Over U} (a : V ⟶ W) (i : Fin d) :
    (Cotangent f).val.map a.left.op (oneBasis e f h b W i) = oneBasis e f h b V i := by
  unfold oneBasis
  erw [sectionBasis_apply, sectionBasis_apply]
  exact sectionLift_restriction X.sheaf (schemeCoefficient f) (Cotangent f)
    (universalDifferential X.sheaf (schemeCoefficient f)) W.left
    (chartSection e W) (chartSection_complex e f h W) V.left a.left.le
    (chartSection e V) (chartSection_complex e f h V) (chartSection_naturality e a) (b i)

private abbrev wedgeRestriction {V W : Over U} (a : V ⟶ W) :=
  exteriorMap (X.presheaf.map a.left.op).hom ((Cotangent f).val.restrictₛₗ a.left.op) n

private theorem wedgeBasis_restrict {V W : Over U} (a : V ⟶ W) (k : Set.powersetCard (Fin d) n) :
    wedgeRestriction f n a (wedgeBasis e f h b n W k) = wedgeBasis e f h b n V k := by
  rw [wedgeBasis, wedgeBasis, exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold wedgeRestriction exteriorPower.ιMulti_family
  erw [exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti Γ(X,V.left) n)
  funext i
  exact basis_restrict e f h b a _

private theorem coord_restrict {V W : Over U} (a : V ⟶ W) (k : Set.powersetCard (Fin d) n)
    (ω : ⋀[Γ(X,W.left)]^n ((Cotangent f).val.obj (op W.left))) :
    (wedgeBasis e f h b n V).coord k (wedgeRestriction f n a ω) =
      X.presheaf.map a.left.op ((wedgeBasis e f h b n W).coord k ω) := by
  classical
  let B := wedgeBasis e f h b n W
  let ρ := (X.presheaf.map a.left.op).hom
  let u := wedgeRestriction f n a
  let v := (wedgeBasis e f h b n V).coord k
  have hcoord : v.comp u = ρ.toSemilinearMap.comp (B.coord k) := by
    apply B.ext
    intro j
    change (wedgeBasis e f h b n V).coord k (wedgeRestriction f n a (B j)) = ρ (B.coord k (B j))
    rw [show wedgeRestriction f n a (B j) = wedgeBasis e f h b n V j from
      wedgeBasis_restrict e f h b n a j]
    by_cases hj : j = k
    · subst j
      simp only [Basis.coord_apply, Basis.repr_self_apply, if_true, map_one]
    · simp only [Basis.coord_apply, Basis.repr_self_apply, if_neg hj, map_zero]
  exact LinearMap.congr_fun hcoord ω

private def rawCoordinate (k : Set.powersetCard (Fin d) n) :
    overPresheaf (ringSheaf X.sheaf) (P f n) U ⟶ (UnitOn (X := X) (U := U)).val where
  app V := by
    change ModuleCat.of Γ(X,V.unop.left)
      (⋀[Γ(X,V.unop.left)]^n ((Cotangent f).val.obj (op V.unop.left))) ⟶
        ModuleCat.of Γ(X,V.unop.left) Γ(X,V.unop.left)
    exact ModuleCat.ofHom ((wedgeBasis e f h b n V.unop).coord k)
  naturality a := by
    apply ConcreteCategory.hom_ext
    intro ω
    exact coord_restrict e f h b n a.unop k ω

local instance presentation_surjective :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology (show TopCat from X)).over U)
      (presentation (U := U) f n) := by
  exact @overPresentation_locallySurjective X (ringSheaf X.sheaf) (P f n) U (E f n)
    (toExteriorSheaf X.sheaf (Cotangent f).val n)
    (exteriorPresentation_locallySurjective X.sheaf (Cotangent f).val n)

local instance presentation_injective :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology (show TopCat from X)).over U)
      (presentation (U := U) f n) := by
  exact @overPresentation_locallyInjective X (ringSheaf X.sheaf) (P f n) U (E f n)
    (toExteriorSheaf X.sheaf (Cotangent f).val n)
    (exteriorPresentation_locallyInjective X.sheaf (Cotangent f).val n)

private abbrev chartSectionMap (V : Over U) :
    (⋀[Γ(X,V.left)]^n ((Cotangent f).val.obj (op V.left))) →ₗ[Γ(X,V.left)]
      (E f n).val.obj (op V.left) :=
  exteriorSection X.sheaf (Cotangent f).val n V.left

private def coordinate (k : Set.powersetCard (Fin d) n) :
    (E f n).over U ⟶ UnitOn where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective (presentation (U := U) f n)
    (UnitOn (X := X) (U := U)).isSheaf).symm (rawCoordinate e f h b n k)

private def coordValue (V : Over U) (k : Set.powersetCard (Fin d) n)
    (ω : (E f n).val.obj (op V.left)) : Γ(X,V.left) :=
  (coordinate e f h b n k).val.app (op V) ω

private theorem coord_section (V : Over U) (k : Set.powersetCard (Fin d) n)
    (ω : (P f n).obj (op V.left)) :
    coordValue e f h b n V k (chartSectionMap f n V ω) =
      (wedgeBasis e f h b n V).coord k ω := by
  have hh := (PresheafOfModules.homEquivOfIsLocallyBijective (presentation (U := U) f n)
    (UnitOn (X := X) (U := U)).isSheaf).apply_symm_apply (rawCoordinate e f h b n k)
  exact congrArg (fun g => g.app (op V) ω) hh

private def reconstructTerm (k : Set.powersetCard (Fin d) n) : (E f n).over U ⟶ (E f n).over U :=
  coordinate e f h b n k ≫ unitMapFromChart ((E f n).over U)
    (chartSectionMap f n (chartTop U) (wedgeBasis e f h b n (chartTop U) k))

private def evaluate (V : Over U) (ω : (E f n).val.obj (op V.left)) :
    ((E f n).over U ⟶ (E f n).over U) →+ (E f n).val.obj (op V.left) where
  toFun g := g.val.app (op V) ω
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem term_apply (V : Over U) (k : Set.powersetCard (Fin d) n)
    (ω : (E f n).val.obj (op V.left)) :
    evaluate f n V ω (reconstructTerm e f h b n k) =
      coordValue e f h b n V k ω •
        chartSectionMap f n V (wedgeBasis e f h b n V k) := by
  change (unitMapFromChart ((E f n).over U) _).val.app (op V)
    (coordValue e f h b n V k ω) = _
  erw [unitMapFromChart_apply, exteriorSection_restrict]
  exact congrArg (fun z => coordValue e f h b n V k ω •
    chartSectionMap f n V z) (wedgeBasis_restrict e f h b n (toChartTop V) k)

private theorem reconstruction :
    ∑ k, reconstructTerm e f h b n k = 𝟙 ((E f n).over U) := by
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective (presentation (U := U) f n)
    ((E f n).over U).isSheaf).injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro ω
  let η := chartSectionMap f n V.unop
  change evaluate f n V.unop (η ω) (∑ k, reconstructTerm e f h b n k) = η ω
  rw [map_sum]
  simp only [term_apply]
  let B := wedgeBasis e f h b n V.unop
  calc
    _ = ∑ k, B.repr ω k • η (B k) := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun a : Γ(X,V.unop.left) => a • η (B k))
        (coord_section e f h b n V.unop k ω)
    _ = η (∑ k, B.repr ω k • B k) := by rw [map_sum]; simp only [map_smul]
    _ = η ω := congrArg η (B.sum_repr ω)

include e h b in
theorem exteriorSection_bijective (V : Over U) :
    Function.Bijective (chartSectionMap f n V) := by
  let η := chartSectionMap f n V
  constructor
  · intro u v hh
    apply (wedgeBasis e f h b n V).repr.injective
    ext k
    exact (coord_section e f h b n V k u).symm.trans
      ((congrArg (coordValue e f h b n V k) hh).trans
        (coord_section e f h b n V k v))
  · intro ω
    refine ⟨∑ k, coordValue e f h b n V k ω • wedgeBasis e f h b n V k, ?_⟩
    have he := congrArg (evaluate f n V ω) (reconstruction e f h b n)
    rw [map_sum] at he
    simp only [term_apply] at he
    change _ = ω at he
    simpa only [map_sum, map_smul] using he

end CycleQ2ChartExteriorSections

#print axioms CycleQ2ChartExteriorSections.exteriorSection_bijective

namespace CycleQ2LiteralThreefoldSecondDifferential

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials
open CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricExteriorSheaf
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2OrdinaryExteriorSections CycleQ2ExteriorSectionNaturality
open CycleQ2LiteralThreefoldFirstDifferential
open CycleQ2LiteralThreefoldGradientAtlas
open CycleQ2LiteralThreefoldResidueFrame (basis)

abbrev FormModule (n : ℕ) := Exterior X.sheaf coeff n
abbrev ThreeModule := FormModule 3
abbrev Three := addSheaf ThreeModule

local instance sectionModule (M : X.Modules) (W : X.Opens) :
    Module (SectionRing X.sheaf W) (M.val.obj (op W)) :=
  (M.val.obj (op W)).isModule

local instance formModule (n : ℕ) (W : X.Opens) :
    Module (SectionRing X.sheaf W) ((FormModule n).val.obj (op W)) :=
  ((FormModule n).val.obj (op W)).isModule

private abbrev realizeOrdinary (W : X.Opens) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff W
    (⋀[SectionRing X.sheaf W]^n (SectionForms X.sheaf coeff W)) →ₗ[SectionRing X.sheaf W]
      (FormModule n).val.obj (op W) :=
  toExterior X.sheaf coeff W n

private def ordinaryMap (V : FramedAffine) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    (⋀[SectionRing X.sheaf V.carrier]^n (SectionForms X.sheaf coeff V.carrier)) →ₗ[SectionRing X.sheaf V.carrier]
      (⋀[SectionRing X.sheaf V.carrier]^n (OneModule.val.obj (op V.carrier))) := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  exact exteriorPower.map n (ordinaryIso V).toLinearMap

private theorem ordinaryMap_bijective (V : FramedAffine) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    Function.Bijective (ordinaryMap V n) := by
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  let e := ordinaryIso V
  let L := exteriorPower.map n e.symm.toLinearMap
  have hLeft : Function.LeftInverse L (ordinaryMap V n) := by
    intro ω
    change exteriorPower.map n e.symm.toLinearMap (exteriorPower.map n e.toLinearMap ω) = ω
    erw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearEquiv.symm_comp,
      exteriorPower.map_id, LinearMap.id_apply]
  have hRight : Function.RightInverse L (ordinaryMap V n) := by
    intro ω
    change exteriorPower.map n e.toLinearMap (exteriorPower.map n e.symm.toLinearMap ω) = ω
    erw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearEquiv.comp_symm,
      exteriorPower.map_id, LinearMap.id_apply]
  exact ⟨hLeft.injective, hRight.surjective⟩

private abbrev realizeExterior (W : X.Opens) (n : ℕ) :
    (⋀[SectionRing X.sheaf W]^n (OneModule.val.obj (op W))) →ₗ[SectionRing X.sheaf W]
      (FormModule n).val.obj (op W) :=
  exteriorSection X.sheaf OneModule.val n W

private theorem toExterior_factor (V : FramedAffine) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    realizeOrdinary V.carrier n =
      (realizeExterior V.carrier n).comp (ordinaryMap V n) := by
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  apply exteriorPower.linearMap_ext
  ext ω
  change realizeOrdinary V.carrier n
    (exteriorPower.ιMulti (SectionRing X.sheaf V.carrier) n ω) = _
  erw [toExterior_wedge]
  change _ = realizeExterior V.carrier n
    (exteriorPower.map n (ordinaryIso V).toLinearMap (exteriorPower.ιMulti _ n ω))
  erw [exteriorPower.map_apply_ιMulti]
  rfl

def ordinaryExteriorIso (V : FramedAffine) (n : ℕ) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    (⋀[SectionRing X.sheaf V.carrier]^n (SectionForms X.sheaf coeff V.carrier)) ≃ₗ[SectionRing X.sheaf V.carrier]
      (FormModule n).val.obj (op V.carrier) := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  apply LinearEquiv.ofBijective (realizeOrdinary V.carrier n)
  rw [toExterior_factor]
  exact (CycleQ2ChartExteriorSections.exteriorSection_bijective (gradientIso V.i V.j)
    structural (gradient_overComplex V.i V.j) (basis V.i V.j) n (chartObject V)).comp
    (ordinaryMap_bijective V n)

theorem ordinaryExteriorIso_apply (V : FramedAffine) (n : ℕ)
    (ω : letI := sectionAlgebra X.sheaf coeff V.carrier
      ⋀[SectionRing X.sheaf V.carrier]^n (SectionForms X.sheaf coeff V.carrier)) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    ordinaryExteriorIso V n ω = realizeOrdinary V.carrier n ω := rfl

theorem ordinaryExteriorIso_restrict (V W : FramedAffine) (h : V.carrier ≤ W.carrier) (n : ℕ)
    (s : (FormModule n).val.obj (op W.carrier)) :
    letI := sectionAlgebra X.sheaf coeff W.carrier
    letI := sectionAlgebra X.sheaf coeff V.carrier
    (ordinaryExteriorIso V n).symm ((FormModule n).val.map (homOfLE h).op s) =
      exteriorDifferentialMap (sectionRestriction X.sheaf coeff h) n ((ordinaryExteriorIso W n).symm s) := by
  let _ := sectionAlgebra X.sheaf coeff W.carrier
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  apply (ordinaryExteriorIso V n).injective
  erw [LinearEquiv.apply_symm_apply, ordinaryExteriorIso_apply, ← toExterior_restrict]
  exact congrArg ((FormModule n).val.map (homOfLE h).op)
    ((LinearEquiv.apply_symm_apply (ordinaryExteriorIso W n) s).symm)

def onTwo (V : FramedAffine) : Two.obj.obj (op V.carrier) →+ Three.obj.obj (op V.carrier) := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  exact (realizeOrdinary V.carrier 3).toAddMonoidHom.comp
    ((CycleQ2LiteralThreefoldExteriorDerivative.additive (nativeFrame V)).comp
      (ordinaryExteriorIso V 2).symm.toAddMonoidHom)

theorem onTwo_restrict (W V : FramedAffine) (h : V.carrier ≤ W.carrier)
    (s : Two.obj.obj (op W.carrier)) :
    onTwo V (Two.obj.map (homOfLE h).op s) = Three.obj.map (homOfLE h).op (onTwo W s) := by
  let _ := sectionAlgebra X.sheaf coeff W.carrier
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  change realizeOrdinary V.carrier 3
    (CycleQ2LiteralThreefoldCartan.exteriorD2 (nativeFrame V)
      ((ordinaryExteriorIso V 2).symm (TwoModule.val.map (homOfLE h).op s))) =
    ThreeModule.val.map (homOfLE h).op (realizeOrdinary W.carrier 3
      (CycleQ2LiteralThreefoldCartan.exteriorD2 (nativeFrame W)
        ((ordinaryExteriorIso W 2).symm s)))
  let ω := (ordinaryExteriorIso W 2).symm s
  have hR := ordinaryExteriorIso_restrict V W h 2 s
  have hD := CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_natural
    (nativeFrame W) (coordinates W) (nativeFrame_apply W)
    (sectionRestriction X.sheaf coeff h) (nativeFrame V) (coordinates V) (nativeFrame_apply V) ω
  exact (congrArg (fun z => realizeOrdinary V.carrier 3
    (CycleQ2LiteralThreefoldCartan.exteriorD2 (nativeFrame V) z)) hR).trans
      ((congrArg (realizeOrdinary V.carrier 3) hD).trans (toExterior_restrict X.sheaf coeff h 3 _).symm)

private def onBasis : (inducedFunctor FramedAffine.carrier).op ⋙ Two.obj ⟶
    (inducedFunctor FramedAffine.carrier).op ⋙ Three.obj where
  app V := AddCommGrpCat.ofHom (onTwo V.unop)
  naturality W V j := by
    apply ConcreteCategory.hom_ext
    exact onTwo_restrict W.unop V.unop j.unop.hom.le

def secondDifferential : Two ⟶ Three where
  hom := TopCat.Sheaf.restrictHomEquivHom Two.obj Three framed_isBasis onBasis

theorem secondDifferential_on (V : FramedAffine) (s : Two.obj.obj (op V.carrier)) :
    secondDifferential.hom.app (op V.carrier) s = onTwo V s :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app (F := Two.obj) (F' := Three)
    framed_isBasis onBasis V) s

private theorem onTwo_toExterior (V : FramedAffine)
    (ω : letI := sectionAlgebra X.sheaf coeff V.carrier
      ⋀[SectionRing X.sheaf V.carrier]^2 (SectionForms X.sheaf coeff V.carrier)) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    onTwo V (realizeOrdinary V.carrier 2 ω) =
      realizeOrdinary V.carrier 3 (CycleQ2LiteralThreefoldExteriorDerivative.additive (nativeFrame V) ω) := by
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  change realizeOrdinary V.carrier 3 (CycleQ2LiteralThreefoldExteriorDerivative.additive
    (nativeFrame V) ((ordinaryExteriorIso V 2).symm ((ordinaryExteriorIso V 2) ω))) = _
  rw [LinearEquiv.symm_apply_apply]

theorem first_second_zero : differential ≫ secondDifferential = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ Three framed_isBasis
  intro V
  apply ConcreteCategory.hom_ext
  intro ω
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  change secondDifferential.hom.app (op V.carrier) (differential.hom.app (op V.carrier) ω) = 0
  rw [differential_on, secondDifferential_on]
  change onTwo V (realizeOrdinary V.carrier 2 (CycleQ2ThreefoldExteriorOneFrame.differential
    (nativeFrame V) ((ordinaryIso V).symm.toFun ω))) = 0
  rw [onTwo_toExterior, CycleQ2ThreefoldExteriorOneFrame.differential_two_one
    (nativeFrame V) (coordinates V) (nativeFrame_apply V), map_zero]
  rfl

section Test

open CycleQ2LiteralAmbientCharts (fixedOpen fixedChart chartInclusion chartInclusion_overComplex)
open CycleQ2InjectiveCech (Sections AbSheaf)
open CycleQ2GeometricSheafLocalIso (res res_comp)
open CycleQ2CechTwoToDerived (app app_res)
open CycleQ2LiteralThreefoldHodgeCech
open CycleQ2LiteralThreefoldResidueChartMaps (fixedTargetMap)
open CycleQ2LiteralThreefoldLiftTransition (sourceMap)
open CycleQ2LiteralThreefoldResidueCoordinates (FixedOverlap)
open CycleQ2LiteralThreefoldDeformedCocycle (chartThreeForm)
open CycleQ2LiteralThreefoldDeformedEdgeDerivative (edgeDerivative)
open CycleQ2LiteralThreefoldTestEdges (nativeEdge)
open CycleQ2LiteralThreefoldExteriorDescent (differential_represents)
open CycleQ2LiteralThreefoldExteriorDescentNative (overlapSeparated edge_differential)
open CycleQ2ChartExteriorBinding (exteriorSectionLift_differentialMap
  chartExteriorSheafSection chartExteriorSheafSection_restrict)

attribute [local instance] CycleQ2LiteralThreefoldHodgeCech.complexOn

private theorem sections_equal_on_basis {F : AbSheaf (show TopCat from X)} {W : X.Opens}
    {x y : Sections F W}
    (h : ∀ V : FramedAffine, ∀ hV : V.carrier ≤ W, res F hV x = res F hV y) : x = y := by
  apply TopCat.Presheaf.IsSheaf.section_ext F.property
  intro z hz
  obtain ⟨_, ⟨V, rfl⟩, hzV, hV⟩ := Opens.isBasis_iff_nbhd.mp framed_isBasis hz
  exact ⟨V.carrier, hV, hzV, h V hV⟩

abbrev Four := addSheaf (FormModule 4)

theorem exterior_four_zero (W : X.Opens) (s : Sections Four W) : s = 0 := by
  apply sections_equal_on_basis
  intro V hV
  let _ := sectionAlgebra X.sheaf coeff V.carrier
  let e := ordinaryExteriorIso V 4
  obtain ⟨ω, hω⟩ := e.surjective (res Four hV s)
  have hz : ω = 0 := by
    let b := (nativeFrame V).exteriorPower 4
    apply b.repr.injective
    ext k
    have h := Finset.card_le_univ k.1
    simp at h
  rw [← hω, hz, map_zero, map_zero]
  rfl

private def evaluate {A : Type} [CommRing A] [Algebra ℂ A] {W : X.Opens}
    (φ : A →ₐ[ℂ] RingOn W) (n : ℕ) :
    (⋀[A]^n (KaehlerDifferential ℂ A)) →+ (FormModule n).val.obj (op W) :=
  (CycleQ2ExteriorSectionNaturality.exteriorSectionLift X.sheaf coeff OneModule
    (universalDifferential X.sheaf coeff) W φ.toRingHom φ.commutes n).toAddMonoidHom

private theorem evaluate_eq_ordinary {A : Type} [CommRing A] [Algebra ℂ A] {W : X.Opens}
    (φ : A →ₐ[ℂ] RingOn W) (n : ℕ) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    evaluate φ n ω = realizeOrdinary W n (exteriorDifferentialMap φ n ω) := by
  exact (exteriorSectionLift_differentialMap X.sheaf coeff OneModule
    (universalDifferential X.sheaf coeff) W φ.toRingHom φ.commutes
    (RingHom.id _) (fun _ => rfl) φ (fun _ => rfl) n ω).symm

def vertexThree (i : Fin 4) : Sections Three (fixedOpen i) :=
  evaluate (chartAlgebraMap i (fixedOpen i) le_rfl) 3 (chartThreeForm i)

private theorem chart_over (i : Fin 4) :
    (fixedChart i).symm.inv ≫ (fixedOpen i).ι ≫ structural =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CycleQ2LiteralAbelJacobiContraction.T i))) := by
  simpa only [Category.assoc, Iso.symm_inv, chartInclusion] using chartInclusion_overComplex i

private theorem vertexThree_restrict (i : Fin 4) (W : X.Opens) (h : W ≤ fixedOpen i) :
    res Three h (vertexThree i) = evaluate (chartAlgebraMap i W h) 3 (chartThreeForm i) := by
  let a : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 (fixedOpen i)) := Over.homMk (homOfLE h)
  exact chartExteriorSheafSection_restrict (fixedChart i).symm structural (chart_over i) a
    3 (chartThreeForm i)

private theorem evaluate_overlap_source (i : Fin 4) (k : Fin 3) (W : X.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))
    (ω : CycleQ2LiteralThreefoldCartan.Forms (CycleQ2LiteralAbelJacobiContraction.T i) 3) :
    evaluate (overlapAlgebraMap i k W h) 3 (exteriorDifferentialMap (sourceMap i k) 3 ω) =
      evaluate (chartAlgebraMap i W (h.trans inf_le_left)) 3 ω := by
  exact exteriorSectionLift_differentialMap X.sheaf coeff OneModule
    (universalDifferential X.sheaf coeff) W
    _ _ _ _ (sourceMap i k)
    (fun a => DFunLike.congr_fun (overlapAlgebraMap_source i k W h) a) 3 ω

private theorem evaluate_overlap_target (i : Fin 4) (k : Fin 3) (W : X.Opens)
    (h : W ≤ fixedOpen i ⊓ fixedOpen (i.succAbove k))
    (ω : CycleQ2LiteralThreefoldCartan.Forms (CycleQ2LiteralAbelJacobiContraction.T (i.succAbove k)) 3) :
    evaluate (overlapAlgebraMap i k W h) 3 (exteriorDifferentialMap (fixedTargetMap i k) 3 ω) =
      evaluate (chartAlgebraMap (i.succAbove k) W (h.trans inf_le_right)) 3 ω := by
  exact exteriorSectionLift_differentialMap X.sheaf coeff OneModule
    (universalDifferential X.sheaf coeff) W
    _ _ _ _ (fixedTargetMap i k)
    (fun a => DFunLike.congr_fun (overlapAlgebraMap_target i k W h) a) 3 ω

private theorem local_second {A : Type} [CommRing A] [Algebra ℂ A]
    (V : FramedAffine) (φ : A →ₐ[ℂ] RingOn V.carrier)
    (hA : CycleQ2LiteralThreefoldExteriorDescent.Separated A)
    (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    app secondDifferential V.carrier (evaluate φ 2 ω) =
      evaluate φ 3 (CycleQ2LiteralThreefoldExteriorDescent.differential hA ω) := by
  let F := app secondDifferential V.carrier
  have hL := congrArg F (evaluate_eq_ordinary φ 2 ω)
  have hApp := secondDifferential_on V
    (realizeOrdinary V.carrier 2 (exteriorDifferentialMap φ 2 ω))
  have hD := onTwo_toExterior V (exteriorDifferentialMap φ 2 ω)
  have hDiff := differential_represents hA ω
    (RingOn V.carrier) φ (nativeFrame V) (coordinates V) (nativeFrame_apply V)
  have hR := evaluate_eq_ordinary φ 3 (CycleQ2LiteralThreefoldExteriorDescent.differential hA ω)
  refine hL.trans ?_
  refine hApp.trans ?_
  refine hD.trans ?_
  refine Eq.trans ?_ hR.symm
  exact congrArg (realizeOrdinary V.carrier 3) hDiff.symm

private abbrev pairOpen (i : Fin 4) (k : Fin 3) := fixedOpen i ⊓ fixedOpen (i.succAbove k)

/-- On the original pair overlap, the genuine sheaf differential gives the
two restrictions of the original vertex corrections. -/
theorem secondDifferential_test_edge (i : Fin 4) (k : Fin 3) :
    app secondDifferential (pairOpen i k)
      (overlapSection i k (pairOpen i k) le_rfl (nativeEdge i k)) =
      res Three (inf_le_left : pairOpen i k ≤ fixedOpen i) (vertexThree i) -
        res Three inf_le_right (vertexThree (i.succAbove k)) := by
  apply sections_equal_on_basis
  intro V h
  let φ := overlapAlgebraMap i k V.carrier h
  let η := overlapSection i k (pairOpen i k) le_rfl (nativeEdge i k)
  let hi : V.carrier ≤ fixedOpen i := h.trans inf_le_left
  let hj : V.carrier ≤ fixedOpen (i.succAbove k) := h.trans inf_le_right
  have hEdge : res Two h η = evaluate φ 2 (nativeEdge i k) :=
    overlapSection_restrict i k le_rfl h (nativeEdge i k)
  have hLift := (app_res secondDifferential h η).symm.trans
    (congrArg (app secondDifferential V.carrier) hEdge)
  have hLocal := (local_second V φ (overlapSeparated i k) (nativeEdge i k)).trans
    (congrArg (evaluate φ 3) (edge_differential i k))
  have hD := ((evaluate φ 3).map_sub _ _).trans
    (congrArg₂ (· - ·) (evaluate_overlap_source i k V.carrier h (chartThreeForm i))
      (evaluate_overlap_target i k V.carrier h (chartThreeForm (i.succAbove k))))
  have hS := (res_comp Three inf_le_left h (vertexThree i)).trans (vertexThree_restrict i V.carrier hi)
  have hT := (res_comp Three inf_le_right h (vertexThree (i.succAbove k))).trans
    (vertexThree_restrict (i.succAbove k) V.carrier hj)
  exact hLift.trans (hLocal.trans (hD.trans
    ((congrArg₂ (· - ·) hS.symm hT.symm).trans ((res Three h).map_sub _ _).symm)))

end Test

end CycleQ2LiteralThreefoldSecondDifferential

#print axioms CycleQ2LiteralThreefoldSecondDifferential.first_second_zero
#print axioms CycleQ2LiteralThreefoldSecondDifferential.secondDifferential_test_edge
#print axioms CycleQ2LiteralThreefoldSecondDifferential.exterior_four_zero
