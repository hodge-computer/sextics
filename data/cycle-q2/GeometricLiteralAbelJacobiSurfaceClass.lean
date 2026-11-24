import Proposal.GeometricLiteralAbelJacobiSheafContraction
import Proposal.GeometricSurfaceCoordinateFrames

/-!
# Surface Kodaira–Spencer contraction against the retained canonical cubic

The full augmented-Jacobian atlas gives a genuine rank-two basis of
the differential sections on every subopen of each patch. The residue
coordinate recovers the exterior representative of the global canonical
two-form on each such open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAbelJacobiSurfaceClass

open CategoryTheory Opposite AlgebraicGeometry Module
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2GeometricSurfaceCoefficients CycleQ2SurfaceCommonOpen CycleQ2ThirdSurfaceChart
  CycleQ2GeometricSurfaceResidueSections CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricExteriorLocalFrames CycleQ2GeometricExteriorSheaf
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeTangentEvaluation

abbrev Patch := CycleQ2FullSurfaceResidueCover.PatchIndex
abbrev patch := CycleQ2FullSurfaceResidueCover.patchOpen
abbrev Canonical := CycleQ2SurfaceCoordinateFrames.CanonicalForms

private theorem chartData {U : Surface.Opens} (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
    (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
    (hc : e.inv ≫ U.ι ≫ projectiveToComplex 57 1 =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))
    (W : Surface.Opens) (h : W ≤ U) :
    Nonempty (Basis (Fin 2) Γ(Surface,W) (DifferentialSheaf.val.obj (op W))) ∧
      Function.Surjective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W) := by
  refine ⟨⟨chartResidueBasis_common _ v n t e hc (Over.mk (homOfLE h))⟩, ?_⟩
  intro σ
  let c := chartResidueCoordinate (projectiveToComplex 57 1) v n t e hc (Over.mk (homOfLE h))
  let f := (chartResidueLocalFrame (projectiveToComplex 57 1) v n t e hc).app W h
  refine ⟨c.symm (f σ), ?_⟩
  apply f.injective
  exact (chartResidueLocalFrame_exteriorSection _ v n t e hc W h _).trans (c.apply_symm_apply _)

private theorem patchData (a : Patch) (W : Surface.Opens) (h : W ≤ patch a) :
    Nonempty (Basis (Fin 2) Γ(Surface,W) (DifferentialSheaf.val.obj (op W))) ∧
      Function.Surjective (exteriorSection Surface.sheaf DifferentialSheaf.val 2 W) := by
  rcases a with ⟨i,n,t⟩
  fin_cases i
  · exact chartData (firstEquations 57 1) n t (firstPatchChart 57 1 n t)
      (CycleQ2SurfaceResidueSheafOverlap.firstPatchChart_overComplex 57 1 n t) W h
  · exact chartData (secondEquations 57 1) n t (secondPatchChart 57 1 n t)
      (CycleQ2SurfaceResidueSheafOverlap.secondPatchChart_overComplex 57 1 n t) W h
  · exact chartData (thirdEquations 57 1) n t (thirdPatchChart 57 1 n t)
      (thirdPatchChart_overComplex 57 1 n t) W h

open CycleQ2LiteralAbelJacobiSurfaceWedge CycleQ2LiteralAbelJacobiSheafContraction
  CycleQ2GeometricModuleLocalIso CycleQ2GeometricIntrinsicNormal

/-- Every local two-form on the original projective surface satisfies the
rank-two wedge/contraction identity with the actual tangent-sheaf evaluation. -/
theorem wedge_interior (W : Surface.Opens) (δ : tangentSheaf.val.obj (op W))
    (γ : DifferentialSheaf.val.obj (op W)) (σ : Canonical.val.obj (op W)) :
    wedgeSection Surface.sheaf DifferentialSheaf.val 2 W ![γ, interior W δ σ] =
      evaluateTangent W δ γ • σ := by
  apply (addSheaf Canonical).eq_of_locally_eq' (fun a : Patch => W ⊓ patch a)
    W (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, CycleQ2FullSurfaceResidueCover.patchOpen_cover, inf_top_eq])
  intro a
  let V := W ⊓ patch a
  let j : V ⟶ W := homOfLE inf_le_left
  let δ' := tangentSheaf.val.map j.op δ
  let γ' := DifferentialSheaf.val.map j.op γ
  let σ' := Canonical.val.map j.op σ
  obtain ⟨⟨basis⟩, hsurj⟩ := patchData a V inf_le_right
  obtain ⟨raw, hr⟩ := hsurj σ'
  have hi : interior V δ' σ' = contract (evaluateTangent V δ') raw :=
    (congrArg (interior V δ') hr.symm).trans (interior_exterior V δ' raw)
  have he : evaluateTangent V δ' γ' = Surface.presheaf.map j.op (evaluateTangent W δ γ) :=
    localLinearHomEvaluate_restrict Surface.sheaf DifferentialSheaf structureModule j δ γ
  change Canonical.val.map j.op _ = Canonical.val.map j.op _
  calc
    _ = wedgeSection Surface.sheaf DifferentialSheaf.val 2 V
        (fun i => DifferentialSheaf.val.map j.op (![γ, interior W δ σ] i)) :=
      wedgeSection_restrict Surface.sheaf DifferentialSheaf.val 2 j _
    _ = wedgeSection Surface.sheaf DifferentialSheaf.val 2 V ![γ', contract (evaluateTangent V δ') raw] := by
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact (interior_restrict W δ (show V ≤ W from inf_le_left) σ).trans hi
    _ = exteriorSection Surface.sheaf DifferentialSheaf.val 2 V ((evaluateTangent V δ' γ') • raw) :=
      congrArg (exteriorSection Surface.sheaf DifferentialSheaf.val 2 V)
        (wedge_contract basis (evaluateTangent V δ') γ' raw)
    _ = evaluateTangent V δ' γ' • σ' := ((exteriorSection Surface.sheaf DifferentialSheaf.val 2 V).map_smul _ raw).trans
      (congrArg (fun z : Canonical.val.obj (op V) => evaluateTangent V δ' γ' • z) hr)
    _ = _ := (congrArg (fun z : Γ(Surface,V) => z • σ') he).trans
      (Canonical.val.map_smul j.op (evaluateTangent W δ γ) σ).symm

end CycleQ2LiteralAbelJacobiSurfaceClass
end

#print axioms CycleQ2LiteralAbelJacobiSurfaceClass.wedge_interior
