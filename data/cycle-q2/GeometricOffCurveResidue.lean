import Proposal.GeometricLocalHomFrame

/-!
# The regular-form inclusion on opens disjoint from the curve

On an open with empty inverse image under the original scheme morphism,
the original kernel ideal is the unit ideal. Evaluation at its section
whose image is one identifies `Hom(I, K)` with `K`, for arbitrary module
sheaves `K`. The equivalence retains the original regular inclusion and
is natural on every subopen; no local freeness of `K` is assumed.

This is the off-curve part of the canonical residue sequence. The residue
morphism and exactness near the curve are constructed separately.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2OffCurveResidue

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricCanonicalGluing CycleQ2LocalHomFrame

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

section LocalUnitIdeal

variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
  (L K : SheafOfModules.{0} (ringSheaf R))
  (ι : L ⟶ SheafOfModules.unit (ringSheaf R)) {U : Opens T}
  (e : LocalFrame R L U)
  (he : ∀ (O : Opens T) (hO : O ≤ U) (x : L.val.obj (op O)),
    frameCoordinate e O hO x = inclusionCoefficient R L ι O x)

/-- The actual section of the ideal whose original inclusion is one. -/
def idealUnit (O : Opens T) (hO : O ≤ U) : L.val.obj (op O) :=
  frameGenerator e O hO

include he in
theorem idealUnit_inclusion (O : Opens T) (hO : O ≤ U) :
    inclusionCoefficient R L ι O (idealUnit R L e O hO) = 1 := by
  rw [← he]
  exact (e.app O hO).apply_symm_apply (1 : R.obj.obj (op O))

theorem idealUnit_restrict {O P : Opens T} (hPO : P ≤ O) (hO : O ≤ U) :
    L.val.map (homOfLE hPO).op (idealUnit R L e O hO) =
      idealUnit R L e P (hPO.trans hO) := by
  exact frameGenerator_naturality e hPO hO

include he in
theorem reconstruct_ideal (O : Opens T) (hO : O ≤ U)
    (x : L.val.obj (op O)) :
    (ι.val.app (op O) x : R.obj.obj (op O)) • idealUnit R L e O hO = x := by
  apply (e.app O hO).injective
  rw [map_smul]
  change (inclusionCoefficient R L ι O x) *
    frameCoordinate e O hO (idealUnit R L e O hO) =
      frameCoordinate e O hO x
  have hu : frameCoordinate e O hO (idealUnit R L e O hO) = 1 :=
    (e.app O hO).apply_symm_apply (1 : R.obj.obj (op O))
  rw [hu, mul_one]
  exact (he O hO x).symm

/-- Inverse to the original regular inclusion, by evaluation at its ideal unit. -/
def regularSectionEquiv (O : Opens T) (hO : O ≤ U) :
    K.val.obj (op O) ≃ₗ[R.obj.obj (op O)] LocalLinearHom R L K O where
  toFun := regularSection R L K ι O
  invFun H := localLinearHomEvaluate R L K O H (idealUnit R L e O hO)
  left_inv s := by
    change localLinearHomEvaluate R L K O
      ((regularInclusion R L K ι).val.app (op O) s) (idealUnit R L e O hO) = s
    rw [regularInclusion_evaluate]
    change inclusionCoefficient R L ι O (idealUnit R L e O hO) • s = s
    rw [idealUnit_inclusion R L ι e he, one_smul]
  right_inv H := by
    apply localLinearHom_ext
    intro V x
    change (ι.val.app (op V.left) x : R.obj.obj (op V.left)) •
      K.val.map V.hom.op
        (H.val.app (op (Over.mk (𝟙 O))) (idealUnit R L e O hO)) =
      H.val.app (op V) x
    have hn := ConcreteCategory.congr_hom
      (H.val.naturality
        (Over.homMk V.hom : V ⟶ Over.mk (𝟙 O)).op) (idealUnit R L e O hO)
    change H.val.app (op V) (L.val.map V.hom.op (idealUnit R L e O hO)) =
      K.val.map V.hom.op
        (H.val.app (op (Over.mk (𝟙 O))) (idealUnit R L e O hO)) at hn
    rw [← hn]
    have hu : L.val.map V.hom.op (idealUnit R L e O hO) =
        idealUnit R L e V.left (V.hom.le.trans hO) :=
      idealUnit_restrict R L e V.hom.le hO
    rw [hu, ← H.property V]
    exact congrArg (H.val.app (op V))
      (reconstruct_ideal R L ι e he V.left (V.hom.le.trans hO) x)
  map_add' s t := (regularSectionLinearMap R L K ι O).map_add s t
  map_smul' r s := (regularSectionLinearMap R L K ι O).map_smul r s

/-- The equivalences are an actual local module-sheaf isomorphism. -/
def regularPatchIso : PatchIso K (moduleHomSheaf R L K) U where
  app O hO := regularSectionEquiv R L K ι e he O hO
  naturality hPO hO s := regularSection_restrict R L K ι (homOfLE hPO) s

theorem regularPatchIso_apply (O : Opens T) (hO : O ≤ U)
    (s : K.val.obj (op O)) :
    (regularPatchIso R L K ι e he).app O hO s =
      (regularInclusion R L K ι).val.app (op O) s := rfl

theorem regularPatchIso_inverse (O : Opens T) (hO : O ≤ U)
    (H : LocalLinearHom R L K O) :
    ((regularPatchIso R L K ι e he).app O hO).symm H =
      localLinearHomEvaluate R L K O H (idealUnit R L e O hO) := rfl

end LocalUnitIdeal

section EmptyInverseImage

variable {X Y : Scheme.{0}} (j : X ⟶ Y) (U : Y.Opens) (hU : j ⁻¹ᵁ U = ⊥)

include hU in
theorem preimage_subopen_empty (O : Y.Opens) (hO : O ≤ U) :
    j ⁻¹ᵁ O = ⊥ :=
  le_bot_iff.mp ((j.preimage_mono hO).trans_eq hU)

include hU in
theorem section_mem_kernel (O : Y.Opens) (hO : O ≤ U) (a : Γ(Y, O)) :
    a ∈ RingHom.ker (j.app O).hom := by
  letI : Subsingleton Γ(X, j ⁻¹ᵁ O) :=
    CommRingCat.subsingleton_of_isTerminal
      (X.sheaf.isTerminalOfEqEmpty (preimage_subopen_empty j U hU O hO))
  exact Subsingleton.elim _ _

/-- The original ring-map kernel is the whole section ring on each subopen. -/
def emptyKernelEquiv (O : Y.Opens) (hO : O ≤ U) :
    RingHom.ker (j.app O).hom ≃ₗ[Γ(Y, O)] Γ(Y, O) where
  toFun := Subtype.val
  invFun a := ⟨a, section_mem_kernel j U hU O hO a⟩
  left_inv a := Subtype.ext rfl
  right_inv a := rfl
  map_add' a b := rfl
  map_smul' r a := rfl

/-- A frame of the actual categorical kernel, normalized by its original inclusion. -/
def kernelUnitFrame : LocalFrame Y.sheaf (kernelIdealSheaf j) U where
  app O hO := by
    change (kernelIdealSheaf j).val.obj (op O) ≃ₗ[Γ(Y, O)] Γ(Y, O)
    exact (kernelIdealSectionEquiv j O).trans (emptyKernelEquiv j U hU O hO)
  naturality hPO hO a :=
    (kernelIdealSectionEquiv_restrict j (homOfLE hPO) a).symm

theorem kernelUnitFrame_inclusion (O : Y.Opens) (hO : O ≤ U)
    (a : (kernelIdealSheaf j).val.obj (op O)) :
    frameCoordinate (kernelUnitFrame j U hU) O hO a =
      inclusionCoefficient Y.sheaf (kernelIdealSheaf j)
        (kernel.ι (schemeStructureMap j)) O a :=
  kernelIdealSectionEquiv_coe j O a

/-- Away from the actual inverse image, the original regular-form inclusion
is an isomorphism for every coefficient sheaf, without a frame of that sheaf. -/
def idealRegularPatchIso (K : Y.Modules) :
    PatchIso K (moduleHomSheaf Y.sheaf (kernelIdealSheaf j) K) U :=
  regularPatchIso Y.sheaf (kernelIdealSheaf j) K
    (kernel.ι (schemeStructureMap j)) (kernelUnitFrame j U hU)
      (kernelUnitFrame_inclusion j U hU)

theorem idealRegularPatchIso_apply (K : Y.Modules) (O : Y.Opens)
    (hO : O ≤ U) (s : K.val.obj (op O)) :
    (idealRegularPatchIso j U hU K).app O hO s =
      (idealRegularInclusion j K).val.app (op O) s := rfl

include hU in
theorem idealRegularInclusion_bijective (K : Y.Modules) (O : Y.Opens)
    (hO : O ≤ U) :
    Function.Bijective ((idealRegularInclusion j K).val.app (op O)) :=
  ((idealRegularPatchIso j U hU K).app O hO).bijective

end EmptyInverseImage

#print axioms regularPatchIso
#print axioms regularPatchIso_inverse
#print axioms kernelUnitFrame
#print axioms idealRegularPatchIso
#print axioms idealRegularInclusion_bijective

end CycleQ2OffCurveResidue

end
