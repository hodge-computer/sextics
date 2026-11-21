import Proposal.GeometricLiteralCotangentEpsilon

/-!
# Reduction of the original global epsilon differential

On the twelve Cartier charts the dual-number structure morphism restricts
on the closed surface to the augmentation. Its epsilon parameter therefore
vanishes there. The pullback adjunction then computes the reduction of
the global differential and shows that the two cotangent arrows compose
to zero.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentEpsilonKernel

open scoped DualNumber
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomogeneousLocalization
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveComplexSplittings CycleQ2LiteralProjectiveKernel
  CycleQ2LiteralProjectiveDualFamily CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralCotangentEpsilon CycleQ2GeometricDifferentialSheaf

def augmentation : ℂ[ε] →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem chartReduction_dualCoefficient (a : Fin 4) (l : Fin 3) (z : ℂ[ε]) :
    chartReduction a l (chartDualCoefficient a l z) = closedCoefficient a l (augmentation z) := by
  change chartReduction a l (fromZeroRingHom deformationGrade _ (dualCoefficient z)) = _
  rw [dualCoefficient_apply, map_add, map_mul, map_add, map_mul]
  change chartReduction a l (thickCoefficient a l z.fst) +
    chartReduction a l (chartEpsilon a l) * chartReduction a l (thickCoefficient a l z.snd) = _
  rw [chartReduction_epsilon, zero_mul, add_zero, chartReduction_complex]
  rfl

set_option maxHeartbeats 600000 in
theorem closedFiber_firstOrderStructure :
    closedFiber ≫ firstOrderStructure =
      CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 ≫
        Spec.map (CommRingCat.ofHom augmentation) := by
  have hc : IsOpenCover (fun i : Fin 4 × Fin 3 => refinedOpen 57 1 i.1 i.2) :=
    .mk (by simpa only [iSup_prod] using literal_refinedOpen_cover)
  refine Scheme.Cover.hom_ext (ClosedSurface.openCoverOfIsOpenCover _ hc) _ _ ?_
  intro i
  apply (cancel_epi (Proj.basicOpenIsoSpec (surfaceGrade 57 1)
    (refinedDenominator 57 1 i.1 i.2) (refinedDenominator_homogeneous 57 1 i.1 i.2)
    (by omega)).inv).mp
  change Proj.awayι (surfaceGrade 57 1) (refinedDenominator 57 1 i.1 i.2)
      (refinedDenominator_homogeneous 57 1 i.1 i.2) (by omega) ≫
        closedFiber ≫ firstOrderStructure =
    Proj.awayι (surfaceGrade 57 1) (refinedDenominator 57 1 i.1 i.2)
      (refinedDenominator_homogeneous 57 1 i.1 i.2) (by omega) ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1 ≫
          Spec.map (CommRingCat.ofHom augmentation)
  rw [chartReduction_scheme_square_assoc, chart_firstOrderStructure,
    ← Category.assoc, CycleQ2GeometricSurfaceCoefficients.awayι_projectiveToComplex,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartReduction_dualCoefficient i.1 i.2)

theorem closedFiber_totalEpsilon : closedFiber.appTop totalEpsilon = 0 := by
  have h := congrArg
    (fun f : ClosedSurface ⟶ Spec (CommRingCat.of ℂ[ε]) =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ε))
    closedFiber_firstOrderStructure
  have hn := ConcreteCategory.congr_hom (C := CommRingCat)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom augmentation)).symm
    (ε : ℂ[ε])
  change (Spec.map (CommRingCat.ofHom augmentation)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ε) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv 0 at hn
  rw [map_zero] at hn
  change closedFiber.appTop totalEpsilon =
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1).appTop
      ((Spec.map (CommRingCat.ofHom augmentation)).appTop
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ε)) at h
  rw [hn, map_zero] at h
  exact h

theorem cotangentReduction_epsilon :
    cotangentReduction.val.app (op ⊤) restrictedEpsilonDifferential = 0 := by
  have h := congrArg (fun f => f.val.app (op ⊤)
    ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d totalEpsilon))
    cotangentReduction_adjunct
  exact h.trans (pushedCotangentReduction_ideal ⊤ ⟨totalEpsilon, closedFiber_totalEpsilon⟩)

theorem epsilonInclusion_cotangentReduction :
    epsilonInclusion ≫ cotangentReduction = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change cotangentReduction.val.app U (epsilonInclusion.val.app U a) = 0
  rw [epsilonInclusion_apply, map_smul, PresheafOfModules.naturality_apply,
    cotangentReduction_epsilon, map_zero, smul_zero]

end CycleQ2LiteralCotangentEpsilonKernel

end

#print axioms CycleQ2LiteralCotangentEpsilonKernel.closedFiber_firstOrderStructure
#print axioms CycleQ2LiteralCotangentEpsilonKernel.epsilonInclusion_cotangentReduction
