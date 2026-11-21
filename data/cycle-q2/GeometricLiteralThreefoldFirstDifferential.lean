import Proposal.GeometricOrdinaryExteriorSections
import Proposal.GeometricLiteralThreefoldGradientAtlas
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# The actual first exterior differential on the original fixed threefold

Affine subopens of the sixteen original gradient charts form a basis.
On each such open the ordinary exact-frame differential is transported
through the actual ordinary-to-sheaf isomorphism, then mapped to the
actual exterior-square sheaf. Naturality for any two exact frames makes
these operators agree under every restriction, so they extend to one
genuine morphism of additive sheaves on the original fixed fiber.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldFirstDifferential
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralAbelJacobiContraction
open CycleQ2LiteralThreefoldGradientAtlas CycleQ2LiteralThreefoldResidueFrame
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricSectionDifferentials
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2OrdinaryExteriorSections (toExterior toExterior_restrict)
open CycleQ2ThreefoldExteriorOneFrame (differential_natural differential_scalar_log)

abbrev X := IncidenceFiber 57
abbrev structural := incidenceFiberToComplex 57
abbrev coeff := schemeCoefficient structural
abbrev OneModule : X.Modules := differentialSheaf X.sheaf coeff
abbrev TwoModule : X.Modules := CycleQ2OrdinaryExteriorSections.Exterior X.sheaf coeff 2
abbrev One := addSheaf OneModule
abbrev Two := addSheaf TwoModule

structure FramedAffine where
  carrier : X.Opens
  affine : IsAffineOpen carrier
  i : Fin 4
  j : Fin 4
  within : carrier ≤ gOpen i j

theorem framed_isBasis : Opens.IsBasis (Set.range FramedAffine.carrier) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  have hc : x ∈ ⨆ i, ⨆ j, gOpen i j := by rw [gOpen_cover]; trivial
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hc
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hi
  obtain ⟨W,hW,hxW,hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens (show x ∈ V ⊓ gOpen i j from ⟨hx,hj⟩)
  exact ⟨W,⟨⟨W,hW,i,j,hWV.trans inf_le_right⟩,rfl⟩,hxW,hWV.trans inf_le_left⟩

theorem gradient_overComplex (i j : Fin 4) :
    (gradientIso i j).inv ≫ (gOpen i j).ι ≫ structural =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch i j))) := by
  rw [← Category.assoc,gradientIso_inv_ι,Category.assoc]
  change _ ≫ chartInclusion i ≫ incidenceFiberToComplex 57 = _
  rw [chartInclusion_overComplex,← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)).commutes)

abbrev chartObject (V : FramedAffine) := Over.mk (homOfLE V.within)

def coordinates (V : FramedAffine) (r : Fin 3) : SectionRing X.sheaf V.carrier :=
  chartSection (gradientIso V.i V.j) (chartObject V)
    (algebraMap (T V.i) (Patch V.i V.j)
      (Ideal.Quotient.mk _ (MvPolynomial.X ((_root_.finSuccEquiv 3) (V.j.succAbove r)))))

def nativeFrame (V : FramedAffine) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    Basis (Fin 3) (SectionRing X.sheaf V.carrier) (SectionForms X.sheaf coeff V.carrier) :=
  CycleQ2AffineExactCotangentFrames.nativeFrame (gradientIso V.i V.j) structural
    (gradient_overComplex V.i V.j) (basis V.i V.j) (chartObject V) V.affine

theorem nativeFrame_apply (V : FramedAffine) (r : Fin 3) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    nativeFrame V r = KaehlerDifferential.D ℂ (SectionRing X.sheaf V.carrier) (coordinates V r) :=
  CycleQ2AffineExactCotangentFrames.nativeFrame_apply (gradientIso V.i V.j) structural
    (gradient_overComplex V.i V.j) (basis V.i V.j) _ (basis_apply V.i V.j) (chartObject V) V.affine r

def ordinaryIso (V : FramedAffine) :
    letI := sectionAlgebra X.sheaf coeff V.carrier
    SectionForms X.sheaf coeff V.carrier ≃ₗ[SectionRing X.sheaf V.carrier] OneModule.val.obj (op V.carrier) := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  exact LinearEquiv.ofBijective (toSheaf X.sheaf coeff V.carrier)
    (CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen coeff V.carrier V.affine)

theorem ordinaryIso_restrict (V W : FramedAffine) (h : V.carrier ≤ W.carrier)
    (s : OneModule.val.obj (op W.carrier)) :
    letI := sectionAlgebra X.sheaf coeff W.carrier
    letI := sectionAlgebra X.sheaf coeff V.carrier
    (ordinaryIso V).symm (OneModule.val.map (homOfLE h).op s) =
      CycleQ2GeometricAffineOverlap.differentialMap (sectionRestriction X.sheaf coeff h) ((ordinaryIso W).symm s) := by
  letI := sectionAlgebra X.sheaf coeff W.carrier
  letI := sectionAlgebra X.sheaf coeff V.carrier
  apply (ordinaryIso V).injective
  rw [LinearEquiv.apply_symm_apply]
  change OneModule.val.map (homOfLE h).op s = toSheaf X.sheaf coeff V.carrier
    (CycleQ2GeometricAffineOverlap.differentialMap (sectionRestriction X.sheaf coeff h) ((ordinaryIso W).symm s))
  rw [← toSheaf_restrict]
  change OneModule.val.map (homOfLE h).op s = OneModule.val.map (homOfLE h).op
    ((ordinaryIso W) ((ordinaryIso W).symm s))
  rw [LinearEquiv.apply_symm_apply]

def on (V : FramedAffine) : One.obj.obj (op V.carrier) →+ Two.obj.obj (op V.carrier) := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  exact (toExterior X.sheaf coeff V.carrier 2).toAddMonoidHom.comp
    ((CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame V)).comp (ordinaryIso V).symm.toAddMonoidHom)

theorem on_restrict (W V : FramedAffine) (h : V.carrier ≤ W.carrier)
    (s : One.obj.obj (op W.carrier)) :
    on V (One.obj.map (homOfLE h).op s) = Two.obj.map (homOfLE h).op (on W s) := by
  letI := sectionAlgebra X.sheaf coeff W.carrier
  letI := sectionAlgebra X.sheaf coeff V.carrier
  change toExterior X.sheaf coeff V.carrier 2
    (CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame V)
      ((ordinaryIso V).symm (OneModule.val.map (homOfLE h).op s))) =
    TwoModule.val.map (homOfLE h).op (toExterior X.sheaf coeff W.carrier 2
      (CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame W) ((ordinaryIso W).symm s)))
  rw [ordinaryIso_restrict]
  rw [← differential_natural (nativeFrame W) (coordinates W) (nativeFrame_apply W)
    (sectionRestriction X.sheaf coeff h) (nativeFrame V) (coordinates V) (nativeFrame_apply V)]
  exact (toExterior_restrict X.sheaf coeff h 2 _).symm

private def onBasis : (inducedFunctor FramedAffine.carrier).op ⋙ One.obj ⟶
    (inducedFunctor FramedAffine.carrier).op ⋙ Two.obj where
  app V := AddCommGrpCat.ofHom (on V.unop)
  naturality W V j := by
    apply ConcreteCategory.hom_ext
    exact on_restrict W.unop V.unop j.unop.hom.le

/-- The actual global exterior differential from one-forms to two-forms. -/
def differential : One ⟶ Two where
  hom := TopCat.Sheaf.restrictHomEquivHom One.obj Two framed_isBasis onBasis

theorem differential_on (V : FramedAffine) (s : One.obj.obj (op V.carrier)) :
    differential.hom.app (op V.carrier) s = on V s :=
  ConcreteCategory.congr_hom (TopCat.Sheaf.extend_hom_app (F := One.obj) (F' := Two)
    framed_isBasis onBasis V) s

/-- The original universal differential of functions as an additive sheaf morphism. -/
def functionDifferential : structureAdditiveSheaf X ⟶ One where
  hom.app V := AddCommGrpCat.ofHom ((universalDifferential X.sheaf coeff).d (X := V))
  hom.naturality {V W} h := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (universalDifferential X.sheaf coeff).d_map h a

theorem on_exact (V : FramedAffine) (a : SectionRing X.sheaf V.carrier) :
    on V ((universalDifferential X.sheaf coeff).d (X := op V.carrier) a) = 0 := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  have he : (ordinaryIso V).symm ((universalDifferential X.sheaf coeff).d (X := op V.carrier) a) =
      KaehlerDifferential.D ℂ (SectionRing X.sheaf V.carrier) a := by
    apply (ordinaryIso V).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  change toExterior X.sheaf coeff V.carrier 2
    (CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame V)
      ((ordinaryIso V).symm ((universalDifferential X.sheaf coeff).d (X := op V.carrier) a))) = 0
  rw [he,CycleQ2ThreefoldExteriorOneFrame.differential_D (nativeFrame V) (coordinates V) (nativeFrame_apply V),map_zero]

/-- The first two arrows of the actual global de Rham sequence compose to zero. -/
theorem function_differential_zero : functionDifferential ≫ differential = 0 := by
  apply CategoryTheory.Sheaf.hom_ext
  apply TopCat.Sheaf.hom_ext _ Two framed_isBasis
  intro V
  apply ConcreteCategory.hom_ext
  intro a
  change differential.hom.app (op V.carrier) ((universalDifferential X.sheaf coeff).d a) = 0
  rw [differential_on]
  exact on_exact V a

def scaledLog (W : X.Opens) (a : Γ(X,W)) (v : Γ(X,W)ˣ) : One.obj.obj (op W) :=
  a • ((v⁻¹ : Γ(X,W)ˣ).val • (universalDifferential X.sheaf coeff).d (X := op W) (v : Γ(X,W)))

def scalarLog (W : X.Opens) (c : ℂ) (v : Γ(X,W)ˣ) : One.obj.obj (op W) :=
  scaledLog W (coefficientOn X.sheaf coeff W c) v

theorem scaledLog_restrict {W V : X.Opens} (h : V ≤ W) (a : Γ(X,W)) (v : Γ(X,W)ˣ) :
    One.obj.map (homOfLE h).op (scaledLog W a v) =
      scaledLog V (X.presheaf.map (homOfLE h).op a)
        (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom v) := by
  unfold scaledLog
  change OneModule.val.map (homOfLE h).op _ = _
  rw [OneModule.val.map_smul,OneModule.val.map_smul]
  have hd := ((universalDifferential X.sheaf coeff).d_map (homOfLE h).op (v : Γ(X,W))).symm
  change OneModule.val.map (homOfLE h).op ((universalDifferential X.sheaf coeff).d (X := op W) (v : Γ(X,W))) =
    (universalDifferential X.sheaf coeff).d (X := op V) (X.presheaf.map (homOfLE h).op (v : Γ(X,W))) at hd
  change (X.presheaf.map (homOfLE h).op a) •
    (X.presheaf.map (homOfLE h).op ((v⁻¹ : Γ(X,W)ˣ).val)) •
      (OneModule.val.map (homOfLE h).op ((universalDifferential X.sheaf coeff).d (X := op W) (v : Γ(X,W)))) = _
  rw [hd]
  rfl

theorem scalarLog_restrict {W V : X.Opens} (h : V ≤ W) (c : ℂ) (v : Γ(X,W)ˣ) :
    One.obj.map (homOfLE h).op (scalarLog W c v) =
      scalarLog V c (Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom v) := by
  have hc := ConcreteCategory.congr_hom ((coefficientMap X.sheaf coeff).naturality (homOfLE h).op) c
  change coefficientOn X.sheaf coeff V c =
    X.presheaf.map (homOfLE h).op (coefficientOn X.sheaf coeff W c) at hc
  unfold scalarLog
  rw [scaledLog_restrict,← hc]

theorem on_scalar_log (V : FramedAffine) (c : ℂ) (v : Γ(X,V.carrier)ˣ) :
    on V (scalarLog V.carrier c v) = 0 := by
  letI := sectionAlgebra X.sheaf coeff V.carrier
  let w : (SectionRing X.sheaf V.carrier)ˣ := v
  have he : scalarLog V.carrier c v = toSheaf X.sheaf coeff V.carrier
      ((algebraMap ℂ (SectionRing X.sheaf V.carrier) c) •
        ((w⁻¹ : (SectionRing X.sheaf V.carrier)ˣ).val • KaehlerDifferential.D ℂ (SectionRing X.sheaf V.carrier) (w : SectionRing X.sheaf V.carrier))) := by
    rw [map_smul,map_smul,toSheaf_D]
    rfl
  rw [he]
  change toExterior X.sheaf coeff V.carrier 2
    (CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame V)
      ((ordinaryIso V).symm ((ordinaryIso V) _))) = 0
  rw [LinearEquiv.symm_apply_apply,differential_scalar_log (nativeFrame V) (coordinates V) (nativeFrame_apply V),map_zero]

/-- Every canonical constant multiple of a logarithmic unit differential
is closed in the actual global one-to-two-form sheaf differential. -/
theorem scalar_log_closed (W : X.Opens) (c : ℂ) (v : Γ(X,W)ˣ) :
    differential.hom.app (op W) (scalarLog W c v) = 0 := by
  let I := {V : FramedAffine // V.carrier ≤ W}
  let C : I → X.Opens := fun V => V.val.carrier
  have hc : W ≤ ⨆ V : I, C V := by
    intro x hx
    obtain ⟨V,⟨A,rfl⟩,hxV,hVW⟩ := Opens.isBasis_iff_nbhd.mp framed_isBasis hx
    exact Opens.mem_iSup.mpr ⟨⟨A,hVW⟩,hxV⟩
  apply Two.eq_of_locally_eq' C W (fun V => homOfLE V.property) hc
  intro V
  change Two.obj.map (homOfLE V.property).op (differential.hom.app (op W) (scalarLog W c v)) =
    Two.obj.map (homOfLE V.property).op 0
  rw [map_zero,← differential.hom.naturality_apply,differential_on,scalarLog_restrict]
  exact on_scalar_log V.val c _

end CycleQ2LiteralThreefoldFirstDifferential
end
#print axioms CycleQ2LiteralThreefoldFirstDifferential.differential_on
#print axioms CycleQ2LiteralThreefoldFirstDifferential.function_differential_zero

#print axioms CycleQ2LiteralThreefoldFirstDifferential.scalar_log_closed
