import Proposal.GeometricCanonicalResidueExact
import Proposal.GeometricCartierNormalBinding

/-!
# The actual Cartier-to-canonical residue diagram

For any actual global two-form on the literal surface, multiplication
gives a morphism from the unchanged Cartier inverse-ideal sequence to the
actual canonical residue sequence. The right vertical map is constructed
by the cokernel property of the original Cartier reduction. It is not an
arbitrarily chosen cohomology operation.

The final identities retain the original normal class, its fixed Cartier
boundary, and the original Ext convention for both connecting maps. A
specific global cubic form and nonvanishing of the canonical connecting
image remain separate geometric obligations.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalResidueDiagram

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricIntrinsicHomMaps CycleQ2GeometricIntrinsicCartierSequence
  CycleQ2GeometricCanonicalGluing CycleQ2LocalHomFrame
  CycleQ2CanonicalResidueSheaf CycleQ2GeometricSheafLocalExactness
  CycleQ2SurfaceExteriorFrameBinding CycleQ2NormalPushforwardIso
  CycleQ2GeometricIntrinsicCartierCohomology CycleQ2GeometricModuleLocalIso

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

abbrev GlobalForm := CanonicalForms.val.obj (op (⊤ : Surface.Opens))
abbrev StructureModule := SheafOfModules.unit (ringSheaf Surface.sheaf)

local instance canonicalSectionModule (O : Surface.Opens) :
    Module Γ(Surface,O) (CanonicalForms.val.obj (op O)) :=
  (CanonicalForms.val.obj (op O)).isModule

/-- Restriction of an actual global form, in the existing exterior sheaf. -/
def formRestriction (σ : GlobalForm) (O : Surface.Opens) :
    CanonicalForms.val.obj (op O) :=
  CanonicalForms.val.map (homOfLE (show O ≤ ⊤ from le_top)).op σ

theorem formRestriction_restrict (σ : GlobalForm) {O P : Surface.Opens}
    (hPO : P ≤ O) :
    CanonicalForms.val.map (homOfLE hPO).op (formRestriction σ O) =
      formRestriction σ P := by
  unfold formRestriction
  rw [← PresheafOfModules.map_comp_apply]
  congr 2

def formSections (σ : GlobalForm) : CanonicalForms.sections :=
  PresheafOfModules.sectionsMk (fun O => formRestriction σ O.unop)
    (fun {_ _} f => formRestriction_restrict σ f.unop.le)

/-- Literal multiplication by the restrictions of the given global form. -/
def formMultiplication (σ : GlobalForm) : StructureModule ⟶ CanonicalForms :=
  (SheafOfModules.unitHomEquiv CanonicalForms).symm (formSections σ)

theorem formMultiplication_app (σ : GlobalForm) (O : Surface.Opens)
    (r : Γ(Surface, O)) :
    (formMultiplication σ).val.app (op O) r = r • formRestriction σ O := rfl

/-- Postcomposition on the actual internal-Hom sheaf of the original ideal. -/
def poleMultiplication (σ : GlobalForm) : inverseIdealSheaf immersion ⟶ PoleForms :=
  moduleHomPostcompose Surface.sheaf IdealSheaf (formMultiplication σ)

theorem poleMultiplication_app (σ : GlobalForm) (O : Surface.Opens)
    (f : (inverseIdealSheaf immersion).val.obj (op O))
    (V : Over O) (x : IdealSheaf.val.obj (op V.left)) :
    ((poleMultiplication σ).val.app (op O) f).val.app (op V) x =
      (f.val.app (op V) x : Γ(Surface, V.left)) • formRestriction σ V.left := rfl

/-- The original scalar inclusion and the actual regular-form inclusion
commute with multiplication by the given global form. -/
theorem scalar_regular_square (σ : GlobalForm) :
    inverseIdealScalar immersion ≫ poleMultiplication σ =
      formMultiplication σ ≫ idealRegularInclusion immersion CanonicalForms := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  apply localLinearHom_ext
  intro V x
  let rV : Γ(Surface,V.left) := Surface.presheaf.map V.hom.op
    (show Γ(Surface,O.unop) from r)
  let c : Γ(Surface,V.left) := inclusionCoefficient Surface.sheaf IdealSheaf
    (kernel.ι (schemeStructureMap immersion)) V.left x
  change (rV * c) • formRestriction σ V.left =
    c • CanonicalForms.val.map V.hom.op
      ((show Γ(Surface,O.unop) from r) • formRestriction σ O.unop)
  have hres : CanonicalForms.val.map V.hom.op
      ((show Γ(Surface,O.unop) from r) • formRestriction σ O.unop) =
      rV • formRestriction σ V.left :=
    (CanonicalForms.val.map_smul V.hom.op
      (show Γ(Surface,O.unop) from r) (formRestriction σ O.unop)).trans
      (congrArg (fun z : CanonicalForms.val.obj (op V.left) => rV • z)
        (formRestriction_restrict σ V.hom.le))
  exact (congrArg (fun z : Γ(Surface,V.left) => z • formRestriction σ V.left)
    (mul_comm rV c)).trans ((smul_smul c rV (formRestriction σ V.left)).symm.trans
      (congrArg (fun z : CanonicalForms.val.obj (op V.left) => c • z) hres.symm))

/-- The pole/residue composite kills the unchanged scalar inclusion. -/
theorem scalar_pole_residue_zero (σ : GlobalForm) :
    inverseIdealScalar immersion ≫ (poleMultiplication σ ≫ canonicalResidue) = 0 := by
  rw [← Category.assoc, scalar_regular_square, Category.assoc,
    canonicalResidue_regular, comp_zero]

local instance originalReduction_epi : Epi (inverseIdealReduction immersion) :=
  literalInverseIdealComplex_shortExact.epi_g

local instance originalComplexReduction_epi : Epi (literalInverseIdealComplex (57 : ℂ) 1).g :=
  literalInverseIdealComplex_shortExact.epi_g

/-- Contraction by the global form is uniquely induced by the original
Cartier quotient. This definition needs no new choice of normal sheaf. -/
def normalContractionOfGlobal (σ : GlobalForm) :
    normalDirectImageSheaf immersion ⟶ ResidueTarget :=
  literalInverseIdealComplex_shortExact.exact.desc
    (poleMultiplication σ ≫ canonicalResidue) (scalar_pole_residue_zero σ)

theorem reduction_contraction (σ : GlobalForm) :
    inverseIdealReduction immersion ≫ normalContractionOfGlobal σ =
      poleMultiplication σ ≫ canonicalResidue :=
  literalInverseIdealComplex_shortExact.exact.g_desc
    (poleMultiplication σ ≫ canonicalResidue) (scalar_pole_residue_zero σ)

theorem normalContractionOfGlobal_unique (σ : GlobalForm)
    (c : normalDirectImageSheaf immersion ⟶ ResidueTarget)
    (hc : inverseIdealReduction immersion ≫ c =
      poleMultiplication σ ≫ canonicalResidue) :
    normalContractionOfGlobal σ = c := by
  apply (cancel_epi (inverseIdealReduction immersion)).mp
  exact (reduction_contraction σ).trans hc.symm

/-- In the original exterior frame, postcomposition by the global form is
multiplication by its actual local frame coordinate. -/
theorem internalHomFrame_poleMultiplication (σ : GlobalForm)
    (a : PatchIndex) (O : Surface.Opens) (hO : O ≤ surfacePatch a)
    (f : (inverseIdealSheaf immersion).val.obj (op O)) :
    (internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app O hO
        ((poleMultiplication σ).val.app (op O) f) =
      frameCoordinate (exteriorFrame 57 1 a) O hO (formRestriction σ O) • f := by
  apply localLinearHom_ext
  intro V x
  let e : CanonicalForms.val.obj (op V.left) ≃ₗ[Γ(Surface,V.left)] Γ(Surface,V.left) :=
    (exteriorFrame 57 1 a).app V.left (V.hom.le.trans hO)
  let c : Γ(Surface,V.left) := f.val.app (op V) x
  let q : Γ(Surface,V.left) := Surface.presheaf.map V.hom.op
    (frameCoordinate (exteriorFrame 57 1 a) O hO (formRestriction σ O))
  change e (c • formRestriction σ V.left) = q * c
  have he := (exteriorFrame 57 1 a).naturality V.hom.le hO (formRestriction σ O)
  change q = e (CanonicalForms.val.map V.hom.op (formRestriction σ O)) at he
  have hcoord : q = e (formRestriction σ V.left) :=
    he.trans (congrArg e (formRestriction_restrict σ V.hom.le))
  exact (e.map_smul c (formRestriction σ V.left)).trans
    ((congrArg (fun z : Γ(Surface,V.left) => c * z) hcoord.symm).trans (mul_comm c q))

/-- The residue of a multiplied inverse-ideal section is computed in the
same actual frame and by the unchanged Cartier reduction. -/
theorem pole_residue_local (σ : GlobalForm) (a : PatchIndex)
    (O : Surface.Opens) (hO : O ≤ refinedPatch a)
    (f : (inverseIdealSheaf immersion).val.obj (op O)) :
    canonicalResidue.val.app (op O) ((poleMultiplication σ).val.app (op O) f) =
      frameCoordinate (exteriorFrame 57 1 a) O
          (hO.trans (refinedPatch_le a)) (formRestriction σ O) •
        (reducedContraction (frameCubic a)).val.app (op O) f := by
  rw [canonicalResidue_local a O hO]
  change (reducedContraction (frameCubic a)).val.app (op O)
      ((internalHomFrame Surface.sheaf IdealSheaf (exteriorFrame 57 1 a)).app
        O (hO.trans (refinedPatch_le a))
        ((poleMultiplication σ).val.app (op O) f)) = _
  rw [internalHomFrame_poleMultiplication, map_smul]

section CubicIdentification

variable (σ : GlobalForm) (p : CycleQ2SurfaceCubicGluing.WeightedCubic)
  (hσ : ∀ (a : PatchIndex) (O : Surface.Opens) (hO : O ≤ refinedPatch a),
    formRestriction σ O = CycleQ2SurfaceCubicGluing.localSectionOn 57 1 p.val a O
      (hO.trans (refinedPatch_le a)))

include hσ

/-- A global form with the indicated actual cubic restrictions has exactly
the original cubic contraction. Only a neighborhood of the curve is used
in this identification; existence of the global form is not asserted. -/
theorem pole_residue_eq_cubic :
    poleMultiplication σ ≫ canonicalResidue =
      inverseIdealReduction immersion ≫ normalContraction p := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  apply (addSheaf ResidueTarget).eq_of_locally_eq'
    (fun a => O.unop ⊓ residueCover a) O.unop (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, residueCover_top, inf_top_eq])
  intro a
  change ResidueTarget.val.map
      (homOfLE (show O.unop ⊓ residueCover a ≤ O.unop from inf_le_left)).op
      (canonicalResidue.val.app O ((poleMultiplication σ).val.app O f)) =
    ResidueTarget.val.map
      (homOfLE (show O.unop ⊓ residueCover a ≤ O.unop from inf_le_left)).op
      ((normalContraction p).val.app O ((inverseIdealReduction immersion).val.app O f))
  let g := (homOfLE (show O.unop ⊓ residueCover a ≤ O.unop from inf_le_left)).op
  refine (PresheafOfModules.naturality_apply
    (poleMultiplication σ ≫ canonicalResidue).val g f).symm.trans ?_
  refine Eq.trans ?_ (PresheafOfModules.naturality_apply
    (inverseIdealReduction immersion ≫ normalContraction p).val g f)

  cases a with
  | none =>
      haveI := target_empty_of_le
        (show O.unop ⊓ residueCover none ≤ offCurve from inf_le_right)
      exact Subsingleton.elim _ _
  | some a =>
      let P : Surface.Opens := O.unop ⊓ refinedPatch a
      let fP := (inverseIdealSheaf immersion).val.map
        (homOfLE (show P ≤ O.unop from inf_le_left)).op f
      change canonicalResidue.val.app (op P)
          ((poleMultiplication σ).val.app (op P) fP) =
        (normalContraction p).val.app (op P)
          ((inverseIdealReduction immersion).val.app (op P) fP)
      rw [pole_residue_local σ a P inf_le_right, hσ a P inf_le_right]
      let n := (actualNormalPushforwardIso 57 1).inv.val.app (op P)
        ((inverseIdealReduction immersion).val.app (op P) fP)
      change immersion.app P
          (frameCoordinate (exteriorFrame 57 1 a) P
            (inf_le_right.trans (refinedPatch_le a))
            (CycleQ2SurfaceCubicGluing.localSectionOn 57 1 p.val a P
              (inf_le_right.trans (refinedPatch_le a)))) •
          (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction (frameCubic a)).val.app
            (op (immersion ⁻¹ᵁ P)) n =
        (CycleQ2GlobalCubicAdjunction.literalCubicAdjunction p).val.app
          (op (immersion ⁻¹ᵁ P)) n
      have hc := CycleQ2CubicAdjunctionFrameBinding.contraction_formula p a P
        (inf_le_right.trans (refinedPatch_le a)) (immersion ⁻¹ᵁ P)
        ((immersion.preimage_mono (show P ≤ refinedPatch a from inf_le_right)).trans
          (preimage_refinedPatch a).le) le_rfl n
      rw [Scheme.Hom.appLE_eq_app] at hc
      exact hc.symm

theorem normalContractionOfGlobal_eq_cubic :
    normalContractionOfGlobal σ = normalContraction p :=
  normalContractionOfGlobal_unique σ (normalContraction p)
    (pole_residue_eq_cubic σ p hσ).symm

end CubicIdentification

set_option maxHeartbeats 1000000 in
/-- The concrete commutative diagram of the two actual module sequences. -/
def globalFormDiagram (σ : GlobalForm) :
    literalInverseIdealComplex (57 : ℂ) 1 ⟶ canonicalResidueComplex where
  τ₁ := (show (literalInverseIdealComplex (57 : ℂ) 1).X₁ ⟶ canonicalResidueComplex.X₁ from
    formMultiplication σ)
  τ₂ := (show (literalInverseIdealComplex (57 : ℂ) 1).X₂ ⟶ canonicalResidueComplex.X₂ from
    poleMultiplication σ)
  τ₃ := (show (literalInverseIdealComplex (57 : ℂ) 1).X₃ ⟶ canonicalResidueComplex.X₃ from
    normalContractionOfGlobal σ)
  comm₁₂ := (scalar_regular_square σ).symm
  comm₂₃ := (reduction_contraction σ).symm

local instance forgetPreservesZero :
    (SheafOfModules.toSheaf.{0} (ringSheaf Surface.sheaf)).PreservesZeroMorphisms :=
  moduleSheaf_toSheaf_preservesZeroMorphisms (ringSheaf Surface.sheaf)

/-- Forget only the module structure in the actual diagram. -/
def globalFormAdditiveDiagram (σ : GlobalForm) :
    literalInverseIdealAdditiveComplex (57 : ℂ) 1 ⟶ canonicalResidueAdditiveComplex :=
  (SheafOfModules.toSheaf.{0} (ringSheaf Surface.sheaf)).mapShortComplex.map
    (globalFormDiagram σ)

local instance sheafHasExt {T : Type} [TopologicalSpace T] :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

/-- The connecting map of the constructed canonical residue sequence. -/
def canonicalOpenConnecting (U : Surface.Opens) :
    canonicalResidueAdditiveComplex.X₃.H' 1 U →+
      canonicalResidueAdditiveComplex.X₁.H' 2 U :=
  openConnecting canonicalResidueAdditiveComplex_shortExact 1 U

def formContractionH1 (σ : GlobalForm) (U : Surface.Opens) :
    (literalInverseIdealAdditiveComplex (57 : ℂ) 1).X₃.H' 1 U →+
      canonicalResidueAdditiveComplex.X₃.H' 1 U :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).map
    (globalFormAdditiveDiagram σ).τ₃).app (op U)).hom

def formMultiplicationH2 (σ : GlobalForm) (U : Surface.Opens) :
    (literalInverseIdealAdditiveComplex (57 : ℂ) 1).X₁.H' 2 U →+
      canonicalResidueAdditiveComplex.X₁.H' 2 U :=
  (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 2).map
    (globalFormAdditiveDiagram σ).τ₁).app (op U)).hom

/-- The connecting identity has the fixed original Ext sign convention. -/
theorem connecting_multiplication (σ : GlobalForm) (U : Surface.Opens)
    (x : (literalInverseIdealAdditiveComplex (57 : ℂ) 1).X₃.H' 1 U) :
    canonicalOpenConnecting U (formContractionH1 σ U x) =
      formMultiplicationH2 σ U (literalOpenConnecting U x) :=
  openConnecting_naturality literalInverseIdealAdditiveComplex_shortExact
    canonicalResidueAdditiveComplex_shortExact (globalFormAdditiveDiagram σ) 1 U x

/-- Specialization to the original reduced inverse-ideal class and its
already fixed Cartier boundary. No comparison class is substituted. -/
theorem originalClass_connecting (σ : GlobalForm) :
    canonicalOpenConnecting ⊤ (formContractionH1 σ ⊤ literalNormalClassAtTop) =
      formMultiplicationH2 σ ⊤
        CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop := by
  rw [connecting_multiplication, literalOpenConnecting_normalClass]

/-- Nonvanishing on the two sides of the actual connecting identity is
equivalent; this does not assert injectivity of the residue connecting map. -/
theorem originalClass_connecting_ne_zero_iff (σ : GlobalForm) :
    canonicalOpenConnecting ⊤ (formContractionH1 σ ⊤ literalNormalClassAtTop) ≠ 0 ↔
      formMultiplicationH2 σ ⊤
        CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop ≠ 0 := by
  rw [originalClass_connecting]

section CubicCohomology

variable (σ : GlobalForm) (p : CycleQ2SurfaceCubicGluing.WeightedCubic)
  (hσ : ∀ (a : PatchIndex) (O : Surface.Opens) (hO : O ≤ refinedPatch a),
    formRestriction σ O = CycleQ2SurfaceCubicGluing.localSectionOn 57 1 p.val a O
      (hO.trans (refinedPatch_le a)))

include hσ

theorem formContractionH1_eq_cubic
    (x : (literalInverseIdealAdditiveComplex (57 : ℂ) 1).X₃.H' 1 ⊤) :
    formContractionH1 σ ⊤ x =
      CycleQ2GlobalCubicAdjunctionCohomology.surfaceAdjunctionH1 p x := by
  change (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).map
      ((SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).map
        (normalContractionOfGlobal σ))).app (op ⊤)) x =
    (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).map
      ((SheafOfModules.toSheaf (ringSheaf Surface.sheaf)).map
        (normalContraction p))).app (op ⊤)) x
  rw [normalContractionOfGlobal_eq_cubic σ p hσ]

/-- Whenever the cubic has been extended as the indicated actual global
form, the original cubic image and Cartier boundary satisfy the canonical
residue connecting identity with no new sign convention. -/
theorem cubic_originalClass_connecting :
    canonicalOpenConnecting ⊤
        (CycleQ2GlobalCubicAdjunctionCohomology.surfaceAdjunctionH1 p
          literalNormalClassAtTop) =
      formMultiplicationH2 σ ⊤
        CycleQ2ProjectiveCartierDerived.literalDerivedClassAtTop := by
  rw [← formContractionH1_eq_cubic σ p hσ]
  exact originalClass_connecting σ

end CubicCohomology

#print axioms scalar_regular_square
#print axioms normalContractionOfGlobal
#print axioms globalFormDiagram
#print axioms normalContractionOfGlobal_eq_cubic
#print axioms connecting_multiplication
#print axioms originalClass_connecting
#print axioms cubic_originalClass_connecting

end CycleQ2CanonicalResidueDiagram

end
