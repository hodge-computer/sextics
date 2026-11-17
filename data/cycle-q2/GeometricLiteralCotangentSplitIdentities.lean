import Proposal.GeometricOpenCotangentSplitting
import Proposal.GeometricLiteralCotangentShortExact

/-!
# Split identities on the native affine opens

On each native affine chart, restriction of the split cotangent sequence
provides a lift of differentials on every smaller open and a retraction
of the epsilon inclusion on the kernel of reduction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCotangentSplitIdentities

open CategoryTheory Opposite AlgebraicGeometry CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricDifferentialSheaf CycleQ2OpenCotangentSplitting

private theorem restrict_twice {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
    (M N : SheafOfModules.{0} (ringSheaf R))
    {W V U : TopologicalSpace.Opens T} (h : W ≤ V) (k : V ≤ U) (f : LocalLinearHom R M N U) :
    restrictLocalLinearHom R M N (homOfLE (h.trans k)).op f =
      restrictLocalLinearHom R M N (homOfLE h).op
        (restrictLocalLinearHom R M N (homOfLE k).op f) :=
  ConcreteCategory.congr_hom ((moduleHomAdditivePresheaf R M N).map_comp
    (homOfLE k).op (homOfLE h).op) f

private theorem sectionMap_restrict_eq_top {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
    {M N : Y.Modules} (f : M.restrict j ⟶ N.restrict j)
    {W U : Y.Opens} (h : W ≤ U) (k : U ≤ j.opensRange) (x : M.val.obj (op W)) :
    localLinearHomEvaluate Y.sheaf M N W
      (restrictLocalLinearHom Y.sheaf M N (homOfLE h).op
        (restrictLocalLinearHom Y.sheaf M N (homOfLE k).op
          ((localLinearHomOpenImmersionEquiv j M N).symm f))) x =
      sectionMap j f W (h.trans k) x :=
  (congrArg (fun H => localLinearHomEvaluate Y.sheaf M N W H x)
    (restrict_twice Y.sheaf M N h k ((localLinearHomOpenImmersionEquiv j M N).symm f)).symm).trans
    (sectionMap_eq_top j f _ _ _).symm

private theorem exists_split {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j]
    (S : ShortComplex Y.Modules) (z : (S.map (Scheme.Modules.restrictFunctor j)).Splitting)
    (U : Y.Opens) (k : U ≤ j.opensRange) :
    ∃ H : LocalLinearHom Y.sheaf S.X₃ S.X₂ U,
      ∃ r : S.X₂.val.obj (op U) →ₗ[Γ(Y,U)] S.X₁.val.obj (op U),
      (∀ (W : Y.Opens) (h : W ≤ U) (x : S.X₃.val.obj (op W)),
        S.g.val.app (op W) (localLinearHomEvaluate Y.sheaf S.X₃ S.X₂ W
          (restrictLocalLinearHom Y.sheaf S.X₃ S.X₂ (homOfLE h).op H) x) = x) ∧
      (∀ x : S.X₂.val.obj (op U), S.g.val.app (op U) x = 0 → S.f.val.app (op U) (r x) = x) := by
  refine ⟨restrictLocalLinearHom Y.sheaf S.X₃ S.X₂ (homOfLE k).op
    ((localLinearHomOpenImmersionEquiv j S.X₃ S.X₂).symm z.s),
    sectionMap (M := S.X₂) (N := S.X₁) j z.r U k, ?_, ?_⟩
  · intro W h x
    exact (congrArg (S.g.val.app (op W))
      (sectionMap_restrict_eq_top (M := S.X₃) (N := S.X₂) j z.s h k x)).trans (split_reduce j S z W (h.trans k) x)
  · intro x hx
    have e := split_identity j S z U k x
    rw [hx, map_zero, add_zero] at e
    exact e

open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralAffineCotangent CycleQ2LiteralCotangentShortExact CycleQ2LiteralCotangentAffineExact
  CycleQ2LiteralCotangentEpsilon

/-- On each actual intersection, the chart's cotangent extension has a compatible
right inverse on subopens and a left inverse on its kernel. -/
theorem chart (s : Finset Vertex) (hs : s.Nonempty) (a : Fin 4) (ha : Admissible s a) :
    ∃ H : LocalLinearHom ClosedSurface.sheaf originalDifferentialSheaf restrictedCotangentSheaf (closedOpen s),
      ∃ r : restrictedCotangentSheaf.val.obj (op (closedOpen s)) →ₗ[Γ(ClosedSurface,closedOpen s)] Γ(ClosedSurface,closedOpen s),
      (∀ (W : ClosedSurface.Opens) (h : W ≤ closedOpen s) (x : originalDifferentialSheaf.val.obj (op W)),
        cotangentReduction.val.app (op W) (localLinearHomEvaluate ClosedSurface.sheaf
          originalDifferentialSheaf restrictedCotangentSheaf W
          (restrictLocalLinearHom ClosedSurface.sheaf originalDifferentialSheaf restrictedCotangentSheaf
            (homOfLE h).op H) x) = x) ∧
      (∀ x : restrictedCotangentSheaf.val.obj (op (closedOpen s)), cotangentReduction.val.app (op (closedOpen s)) x = 0 →
        epsilonInclusion.val.app (op (closedOpen s)) (r x) = x) := by
  let z := ((nativeTildeSplitting s a ha).ofIso (chartCotangentComplexIso s hs).symm).ofIso
    (cotangentComplex.mapNatIso (Scheme.Modules.restrictFunctorIsoPullback (closedAffineMap s hs)).symm)
  have hr : (closedAffineMap s hs).opensRange = closedOpen s := Proj.opensRange_awayι _ _ _ _
  exact exists_split (closedAffineMap s hs) cotangentComplex z (closedOpen s) hr.ge

end CycleQ2LiteralCotangentSplitIdentities
end

#print axioms CycleQ2LiteralCotangentSplitIdentities.chart
