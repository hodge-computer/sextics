import Proposal.SegreFactorCechComplex

/-!
# Ranks of the global factor map and the incidence Jacobian
-/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SegreCechCofactorGrade.lean -/
section
/-! # The actual local cofactor differential preserves the required grade -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceFirstOrder CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedProjection
  CycleQ2SeedLocalizedClearing CycleQ2SegreGlobalObstruction

/-- The explicit bilinear cofactor differential respects any three
submodules whose multiplication has the indicated degree. -/
theorem cofactorDifferential_mem {R A : Type*} [CommRing R] [CommRing A] [Module R A]
    (P Q T : Submodule R A) (hmul : ∀ a∈P, ∀ b∈Q, a*b∈T)
    (M N : Matrix (Fin 3) (Fin 3) A) (hM : ∀ i j, M i j∈P) (hN : ∀ i j, N i j∈Q) :
    ∀ i j, cofactorDifferential M N i j∈T := by
  have hMN (i j k l : Fin 3) : M i j*N k l∈T := hmul _ (hM i j) _ (hN k l)
  have hNM (i j k l : Fin 3) : N i j*M k l∈T := by
    rw [mul_comm]
    exact hMN k l i j
  rw [cofactorDifferential_fin_three]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val_zero',Matrix.cons_val_succ',neg_mul] <;>
    repeat' first
      | apply T.add_mem
      | apply T.sub_mem
      | apply T.neg_mem
      | exact hMN _ _ _ _
      | exact hNM _ _ _ _

/-- Every entry of the actual localized seed matrix has degree fourteen
and invariant character. -/
theorem localSeedMatrix_grade (s : Finset (Fin 3)) (i j : Fin 3) :
    HasLocalGrade ℂ 57 Complex.I s (14,0)
      (localizeMatrix ℂ 57 Complex.I s SeedMatrix i j) :=
  polynomial_hasLocalGrade ℂ 57 Complex.I s (rawSeedMatrix (57:ℂ) i j) (14,0)
    (rawSeedMatrix_homogeneous (57:ℂ) i j)

/-- Degree fourteen local matrix variations produce actual degree twenty-eight
cofactor variations in the coordinate localization. -/
theorem localCofactor_grade (s : Finset (Fin 3))
    (N : Matrix (Fin 3) (Fin 3) (SeedLocal ℂ 57 Complex.I s))
    (hN : ∀ i j,HasLocalGrade ℂ 57 Complex.I s (14,0) (N i j)) :
    ∀ i j,HasLocalGrade ℂ 57 Complex.I s (28,0)
      (cofactorDifferential (localizeMatrix ℂ 57 Complex.I s SeedMatrix) N i j) := by
  refine cofactorDifferential_mem (R:=ℂ) (A:=SeedLocal ℂ 57 Complex.I s)
    (gradeSubmodule ℂ 57 Complex.I s (14,0))
    (gradeSubmodule ℂ 57 Complex.I s (14,0))
    (gradeSubmodule ℂ 57 Complex.I s (28,0)) ?_
    (localizeMatrix ℂ 57 Complex.I s SeedMatrix) N (localSeedMatrix_grade s) hN
  intro a ha b hb
  change HasLocalGrade ℂ 57 Complex.I s ((14,0)+(14,0)) (a*b)
  exact hasLocalGrade_mul ℂ 57 Complex.I s (14,0) (14,0) a b ha hb

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.localCofactor_grade
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorCechVanishing.lean -/
section
/-! # H1 vanishing for the actual graded factor module -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2SegreFactorChartExact CycleQ2SegreFactorRestrictions

/-- The direct sum of the three left and three right factor modules has
vanishing actual Čech H1 in precisely the degrees used by the seed matrix. -/
theorem factorCech_exact (F : FactorPairs) (hF : factorD1 F=0) :
    ∃ (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}),
      F=factorD0 F0 F1 F2 := by
  have hleft (i : Fin 3) :=
    CycleQ2SeedLinkageCechVanishing.left_idealCechExact
      (F.1.val.1 i) (F.2.1.val.1 i) (F.2.2.val.1 i)
      (F.1.property.1 i) (F.2.1.property.1 i) (F.2.2.property.1 i)
      (F.1.val.1 i).property (F.2.1.val.1 i).property (F.2.2.val.1 i).property
      (congrArg (fun V : GradedFactors Finset.univ => (V.val.1 i:Chart Finset.univ)) hF)
  have hright (j : Fin 3) :=
    CycleQ2SeedLinkageCechVanishing.right_idealCechExact
      (F.1.val.2 j) (F.2.1.val.2 j) (F.2.2.val.2 j)
      (F.1.property.2 j) (F.2.1.property.2 j) (F.2.2.property.2 j)
      (F.1.val.2 j).property (F.2.1.val.2 j).property (F.2.2.val.2 j).property
      (congrArg (fun V : GradedFactors Finset.univ => (V.val.2 j:Chart Finset.univ)) hF)
  choose v0 v1 v2 hv0 hv1 hv2 mv0 mv1 mv2 ev01 ev02 ev12 using hleft
  choose w0 w1 w2 hw0 hw1 hw2 mw0 mw1 mw2 ew01 ew02 ew12 using hright
  let F0 : GradedFactors {0} :=
    ⟨(fun i => ⟨v0 i,mv0 i⟩,fun j => ⟨w0 j,mw0 j⟩),hv0,hw0⟩
  let F1 : GradedFactors {1} :=
    ⟨(fun i => ⟨v1 i,mv1 i⟩,fun j => ⟨w1 j,mw1 j⟩),hv1,hw1⟩
  let F2 : GradedFactors {2} :=
    ⟨(fun i => ⟨v2 i,mv2 i⟩,fun j => ⟨w2 j,mw2 j⟩),hv2,hw2⟩
  refine ⟨F0,F1,F2,?_⟩
  apply Prod.ext
  · apply Subtype.ext
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact ev01 i
    · funext j
      apply Subtype.ext
      exact ew01 j
  · apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · funext i
        apply Subtype.ext
        exact ev02 i
      · funext j
        apply Subtype.ext
        exact ew02 j
    · apply Subtype.ext
      apply Prod.ext
      · funext i
        apply Subtype.ext
        exact ev12 i
      · funext j
        apply Subtype.ext
        exact ew12 j

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.factorCech_exact
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorTopLifts.lean -/
section
/-! # Actual lifts from cofactor-kernel cocycles to scalar top cochains -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechActualTop CycleQ2SegreCechConnecting
  CycleQ2SegreFactorChartExact CycleQ2SegreFactorGraded CycleQ2SegreFactorRestrictions

abbrev ActualKernelCocycles := kernelCocycles ℂ (57:ℂ) Complex.I
  CycleQ2SegreGlobalObstruction.SeedMatrix CycleQ2SegreGlobalObstruction.matrixGrades

abbrev ActualKernelH1 := KernelCechH1 ℂ (57:ℂ) Complex.I
  CycleQ2SegreGlobalObstruction.SeedMatrix CycleQ2SegreGlobalObstruction.matrixGrades

def FactorLifts (P : ActualKernelCocycles) (F : FactorPairs) : Prop :=
  gradedFactorMap {0,1} (by decide) F.1=P.val 0 1 ∧
  gradedFactorMap {0,2} (by decide) F.2.1=P.val 0 2 ∧
  gradedFactorMap {1,2} (by decide) F.2.2=P.val 1 2

theorem factorD1_image (P : ActualKernelCocycles) (F : FactorPairs) (hF : FactorLifts P F) :
    gradedFactorMap Finset.univ (by decide) (factorD1 F)=0 := by
  change gradedFactorMap Finset.univ _
    (gradedFactorRestriction (Finset.subset_univ {0,1}) F.1-
     gradedFactorRestriction (Finset.subset_univ {0,2}) F.2.1+
     gradedFactorRestriction (Finset.subset_univ {1,2}) F.2.2)=0
  rw [map_add (gradedFactorMap Finset.univ (by decide)),
    map_sub (gradedFactorMap Finset.univ (by decide)),
    ← gradedFactorMap_restriction (by decide) (by decide) (Finset.subset_univ {0,1}),
    ← gradedFactorMap_restriction (by decide) (by decide) (Finset.subset_univ {0,2}),
    ← gradedFactorMap_restriction (by decide) (by decide) (Finset.subset_univ {1,2}),
    hF.1,hF.2.1,hF.2.2]
  exact (kernelCocycle_properties ℂ 57 Complex.I
    CycleQ2SegreGlobalObstruction.SeedMatrix CycleQ2SegreGlobalObstruction.matrixGrades P).2.2 0 1 2

/-- Every actual graded kernel cocycle lifts to the literal factor sequence,
and its triple defect is a genuine degree-zero scalar gauge. -/
theorem exists_factor_top_lift (P : ActualKernelCocycles) :
    ∃ (F : FactorPairs) (c : ScalarSections Finset.univ),
      FactorLifts P F ∧ factorD1 F=gradedGaugeMap Finset.univ (by decide) c := by
  have hp := kernelCocycle_properties ℂ 57 Complex.I
    CycleQ2SegreGlobalObstruction.SeedMatrix CycleQ2SegreGlobalObstruction.matrixGrades P
  obtain ⟨F01,h01⟩ := graded_factor_lift {0,1} (by decide) (P.val 0 1)
    (hp.2.1 0 1) (hp.1 0 1)
  obtain ⟨F02,h02⟩ := graded_factor_lift {0,2} (by decide) (P.val 0 2)
    (hp.2.1 0 2) (hp.1 0 2)
  obtain ⟨F12,h12⟩ := graded_factor_lift {1,2} (by decide) (P.val 1 2)
    (hp.2.1 1 2) (hp.1 1 2)
  let F : FactorPairs := (F01,F02,F12)
  have hF : FactorLifts P F := ⟨h01,h02,h12⟩
  obtain ⟨c,hc⟩ := graded_zero_factor_gauge Finset.univ (by decide) (factorD1 F)
    (factorD1_image P F hF)
  exact ⟨F,c,hF,hc.symm⟩

theorem factorLifts_sub_pairGauge (P : ActualKernelCocycles) (F : FactorPairs)
    (hF : FactorLifts P F) (B : ScalarPairs) : FactorLifts P (F-pairGauge B) := by
  constructor
  · change gradedFactorMap {0,1} _ (F.1-gradedGaugeMap {0,1} _ B.1)=_
    rw [map_sub (gradedFactorMap {0,1} (by decide)),gradedFactorMap_gaugeMap,sub_zero]
    exact hF.1
  · constructor
    · change gradedFactorMap {0,2} _ (F.2.1-gradedGaugeMap {0,2} _ B.2.1)=_
      rw [map_sub (gradedFactorMap {0,2} (by decide)),gradedFactorMap_gaugeMap,sub_zero]
      exact hF.2.1
    · change gradedFactorMap {1,2} _ (F.2.2-gradedGaugeMap {1,2} _ B.2.2)=_
      rw [map_sub (gradedFactorMap {1,2} (by decide)),gradedFactorMap_gaugeMap,sub_zero]
      exact hF.2.2

/-- Any two factor lifts of the same actual cocycle differ by a genuine
graded scalar pair cochain. -/
theorem factorLifts_difference_gauge (P : ActualKernelCocycles) (F G : FactorPairs)
    (hF : FactorLifts P F) (hG : FactorLifts P G) :
    ∃ B : ScalarPairs, F-G=pairGauge B := by
  obtain ⟨b01,h01⟩ := graded_zero_factor_gauge {0,1} (by decide) (F.1-G.1) (by
    rw [map_sub (gradedFactorMap {0,1} (by decide)),hF.1,hG.1,sub_self])
  obtain ⟨b02,h02⟩ := graded_zero_factor_gauge {0,2} (by decide) (F.2.1-G.2.1) (by
    rw [map_sub (gradedFactorMap {0,2} (by decide)),hF.2.1,hG.2.1,sub_self])
  obtain ⟨b12,h12⟩ := graded_zero_factor_gauge {1,2} (by decide) (F.2.2-G.2.2) (by
    rw [map_sub (gradedFactorMap {1,2} (by decide)),hF.2.2,hG.2.2,sub_self])
  refine ⟨(b01,b02,b12),?_⟩
  exact Prod.ext h01.symm (Prod.ext h02.symm h12.symm)

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.exists_factor_top_lift
#print axioms CycleQ2SegreFactorCech.factorLifts_difference_gauge
end
end

/- Component: continuation_3/SegreGlobalRankSpaces.lean -/
section
/-! # The actual finite spaces in the global Segre rank calculation

This module fixes the literal degree-14 source and degree-28 relation
source, proves their dimensions, and records rank-nullity deductions.
The numerical kernel and obstruction bounds are supplied separately.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreGlobalRankSpaces

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceGradedBasis CycleQ2IncidenceFirstOrder
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction
  CycleQ2SegreCechConnecting CycleQ2SegreGlobalObstruction
  CycleQ2SegreRelationsLocal

abbrev Input14 := Matrix (Fin 3) (Fin 3) (SeedPiece (57:ℂ) Complex.I 14 0)

instance invariantPiece_finite (d : ℕ) :
    Module.Finite ℂ (SeedPiece (57:ℂ) Complex.I d 0) :=
  Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I d 0 (by decide))

theorem degree14Piece_finrank :
    Module.finrank ℂ (SeedPiece (57:ℂ) Complex.I 14 0)=239 := by
  change Module.finrank ℂ (quotientPiece fullGrading (smoothH Complex.I)
    (smoothF (57:ℂ) Complex.I) (14,0))=239
  rw [seed_h_normalized,seed_F_normalized]
  exact fullPiece_degree14_finrank _ _

theorem degree28Piece_finrank :
    Module.finrank ℂ (SeedPiece (57:ℂ) Complex.I 28 0)=1058 := by
  change Module.finrank ℂ (quotientPiece fullGrading (smoothH Complex.I)
    (smoothF (57:ℂ) Complex.I) (28,0))=1058
  rw [seed_h_normalized,seed_F_normalized]
  exact fullPiece_degree28_finrank _ _

theorem input14_finrank : Module.finrank ℂ Input14=2151 := by
  change Module.finrank ℂ (Fin 3 → Fin 3 → SeedPiece (57:ℂ) Complex.I 14 0)=2151
  simp only [Module.finrank_pi_fintype,degree14Piece_finrank,Finset.sum_const,Fintype.card_fin,
    Finset.card_univ,smul_eq_mul]

theorem degree28_finrank : Module.finrank ℂ Degree28Matrices=9522 := by
  change Module.finrank ℂ (Fin 3 → Fin 3 → SeedPiece (57:ℂ) Complex.I 28 0)=9522
  simp only [Module.finrank_pi_fintype,degree28Piece_finrank,Finset.sum_const,Fintype.card_fin,
    Finset.card_univ,smul_eq_mul]

def inputToGlobal : Input14 →ₗ[ℂ] GlobalMatrix ℂ (57:ℂ) Complex.I where
  toFun N i j := (N i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem inputToGlobal_injective : Function.Injective inputToGlobal := by
  intro N P h
  funext i j
  apply Subtype.ext
  exact congrArg (fun M : GlobalMatrix ℂ (57:ℂ) Complex.I => M i j) h

def entryDifferential : Input14 →ₗ[ℂ] GlobalMatrix ℂ (57:ℂ) Complex.I :=
  ((cofactorDifferentialLinear SeedMatrix).restrictScalars ℂ).comp inputToGlobal

def relationMap : Degree28Matrices →ₗ[ℂ]
    (Fin 16 → SeedRing (57:ℂ) Complex.I) :=
  ((relationsLinear SeedMatrix).restrictScalars ℂ).comp degree28ToGlobal

theorem relationMap_kernel : LinearMap.ker relationMap=relationVariations := rfl

theorem degree28ToGlobal_injective : Function.Injective degree28ToGlobal := by
  intro C D h
  funext i j
  apply Subtype.ext
  exact congrArg (fun M : GlobalMatrix ℂ (57:ℂ) Complex.I => M i j) h

theorem cofactorImage_le_preimage_range :
    globalCofactorImage≤(LinearMap.range entryDifferential).comap
      (degree28ToGlobal.comp relationVariations.subtype) := by
  apply Submodule.span_le.mpr
  intro C hC
  obtain ⟨P,_hstandard,hgrade,hD⟩ := hC
  have hPg (i j : Fin 3) : (P i j).IsWeightedHomogeneous fullGrading (14,0) :=
    (CycleQ2SeedQuotientGrading.signedHomogeneous_iff ℂ (P i j) (14,0)).mp (hgrade i j)
  let N : Input14 := fun i j => ⟨Ideal.Quotient.mk
      (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) (P i j),
    Submodule.mem_map.mpr ⟨P i j,hPg i j,rfl⟩⟩
  refine ⟨N,?_⟩
  change cofactorDifferential SeedMatrix (quotientMatrix ℂ (57:ℂ) Complex.I P)=_
  exact hD

def cofactorImageToRange : globalCofactorImage →ₗ[ℂ] LinearMap.range entryDifferential :=
  ((degree28ToGlobal.comp relationVariations.subtype).comp globalCofactorImage.subtype).codRestrict
    _ (fun C => cofactorImage_le_preimage_range C.property)

theorem cofactorImageToRange_injective : Function.Injective cofactorImageToRange := by
  intro C D h
  apply Subtype.ext
  apply Subtype.ext
  apply degree28ToGlobal_injective
  exact congrArg Subtype.val h

theorem cofactorImage_finrank_le :
    Module.finrank ℂ globalCofactorImage≤Module.finrank ℂ (LinearMap.range entryDifferential) :=
  LinearMap.finrank_le_finrank_of_injective cofactorImageToRange_injective

theorem entry_rank_le_of_kernel_bound
    (hkernel : 236≤Module.finrank ℂ (LinearMap.ker entryDifferential)) :
    Module.finrank ℂ (LinearMap.range entryDifferential)≤1915 := by
  have h := entryDifferential.finrank_range_add_finrank_ker
  rw [input14_finrank] at h
  omega

theorem relation_dimension_le_of_bounds
    (hkernel : 236≤Module.finrank ℂ (LinearMap.ker entryDifferential))
    (hobstruction : Module.finrank ℂ RelationObstruction≤7) :
    Module.finrank ℂ relationVariations≤1922 := by
  have hi := cofactorImage_finrank_le.trans (entry_rank_le_of_kernel_bound hkernel)
  have h := @Submodule.finrank_quotient_add_finrank ℂ relationVariations
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance globalCofactorImage
  change Module.finrank ℂ RelationObstruction+Module.finrank ℂ globalCofactorImage=
    Module.finrank ℂ relationVariations at h
  omega

theorem relation_rank_lower_bound_of_bounds
    (hkernel : 236≤Module.finrank ℂ (LinearMap.ker entryDifferential))
    (hobstruction : Module.finrank ℂ RelationObstruction≤7) :
    7600≤Module.finrank ℂ (LinearMap.range relationMap) := by
  have hk := relation_dimension_le_of_bounds hkernel hobstruction
  have h := relationMap.finrank_range_add_finrank_ker
  rw [relationMap_kernel,degree28_finrank] at h
  omega

end CycleQ2SegreGlobalRankSpaces

#print axioms CycleQ2SegreGlobalRankSpaces.input14_finrank
#print axioms CycleQ2SegreGlobalRankSpaces.cofactorImage_finrank_le
#print axioms CycleQ2SegreGlobalRankSpaces.relation_rank_lower_bound_of_bounds
end
end

/- Component: continuation_3/ModularGlobalFactorLift.lean -/
section
/-! Global factor pairs for every actual modular cofactor-kernel matrix.
The pairs lie in the finite curve restriction kernels, which suffices for
an upper bound on the cofactor kernel. No global orbit-ideal equality is used. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalFactorLift

open Matrix CycleQ2ModularGlobalFactorSpaces CycleQ2ModularGlobalCurveGluing
  CycleQ2ModularGlobalFactorCech CycleQ2ModularFactorCech
  CycleQ2ModularFactorChartExact CycleQ2SeedCechGlobalGluing

theorem glue_graded_factors (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2}) (hF : factorD0 F0 F1 F2=0) :
    ∃ v : Domain,
      (∀ i, chartMap {0} (leftValue v i)=(F0.val.1 i:Chart {0})) ∧
      (∀ j, chartMap {0} (rightValue v j)=(F0.val.2 j:Chart {0})) := by
  have hleft (i : Fin 3) := exists_global_curve_kernel_piece .left 10 0
    (F0.val.1 i) (F1.val.1 i) (F2.val.1 i)
    (F0.property.1 i) (F0.val.1 i).property
    (congrArg (fun B : FactorPairs => (B.1.val.1 i:Chart {0,1})) hF)
    (congrArg (fun B : FactorPairs => (B.2.1.val.1 i:Chart {0,2})) hF)
  have hright (j : Fin 3) := exists_global_curve_kernel_piece .right 8 1
    (F0.val.2 j) (F1.val.2 j) (F2.val.2 j)
    (F0.property.2 j) (F0.val.2 j).property
    (congrArg (fun B : FactorPairs => (B.1.val.2 j:Chart {0,1})) hF)
    (congrArg (fun B : FactorPairs => (B.2.1.val.2 j:Chart {0,2})) hF)
  choose v hv0 _hv1 _hv2 using hleft
  choose w hw0 _hw1 _hw2 using hright
  exact ⟨(v,w),hv0,hw0⟩

theorem exists_global_factor_pair (N : Input14) (hN : entryDifferential N=0) :
    ∃ v : Domain, ∀ i j,
      CycleQ2ModularGlobalFactorSpaces.linkage*(N i j).val=
        leftValue v i*right j + left i*rightValue v j := by
  obtain ⟨F0,F1,F2,hF,hF0⟩ := exists_compatible_local_factors N hN
  obtain ⟨v,hv,hw⟩ := glue_graded_factors F0 F1 F2 hF
  refine ⟨v,?_⟩
  intro i j
  apply localization_injective K (57:K) 33 {0}
  change chartMap {0} (CycleQ2ModularGlobalFactorSpaces.linkage*(N i j).val)=
    chartMap {0} (leftValue v i*right j+left i*rightValue v j)
  rw [map_mul,map_add,map_mul,map_mul,hv,hw]
  change CycleQ2ModularFactorChartExact.linkage {0}*(localMatrix N {0}) i j=
    (F0.val.1 i:Chart {0})*rightSection {0} j+leftSection {0} i*(F0.val.2 j:Chart {0})
  rw [←hF0]
  exact chartFactorMap_formula {0} (by decide) F0.val i j

end CycleQ2ModularGlobalFactorLift

#print axioms CycleQ2ModularGlobalFactorLift.exists_global_factor_pair
end
end

/- Component: continuation_3/SeedGlobalFactorRank.lean -/
section
/-! At least 236 actual degree-14 invariant matrix sections lie in the
cofactor differential kernel. The source has dimension 3*56+3*23=237;
its only possible ambiguity is the proved constant scalar gauge. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalFactorRank

open CycleQ2IncidenceFirstOrder CycleQ2SeedGlobalFactorMap
  CycleQ2SeedGlobalFactorGauge CycleQ2SegreGlobalRankSpaces

theorem factor_image_finrank_lower_bound :
    236≤Module.finrank ℂ (LinearMap.range gradedFactorMap) := by
  letI : Module.Finite ℂ (Fin 3 → LeftPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite ℂ (Fin 3 → RightPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => RightPiece)
  letI : Module.Finite ℂ Domain := Module.Finite.prod
  have h := @LinearMap.finrank_range_add_finrank_ker ℂ Domain
    (inferInstance : DivisionRing ℂ) (inferInstance : AddCommGroup Domain)
    (inferInstance : Module ℂ Domain) MatrixPiece (inferInstance : AddCommGroup MatrixPiece)
    (inferInstance : Module ℂ MatrixPiece) (inferInstance : FiniteDimensional ℂ Domain) gradedFactorMap
  rw [domain_finrank] at h
  have hk := gradedFactorMap_kernel_finrank_le_one
  omega

theorem entryDifferential_gradedFactorMap (v : Domain) :
    entryDifferential (gradedFactorMap v)=0 := by
  change cofactorDifferential CycleQ2SegreComplexBasepoint.matrix (factorMap v)=0
  exact factorMap_cofactor_zero v

theorem factor_image_le_entryKernel :
    LinearMap.range gradedFactorMap≤LinearMap.ker entryDifferential := by
  rintro N ⟨v,rfl⟩
  exact entryDifferential_gradedFactorMap v

theorem entry_kernel_finrank_lower_bound :
    236≤Module.finrank ℂ (LinearMap.ker entryDifferential) :=
  factor_image_finrank_lower_bound.trans (Submodule.finrank_mono factor_image_le_entryKernel)

theorem entry_rank_upper_bound :
    Module.finrank ℂ (LinearMap.range entryDifferential)≤1915 :=
  entry_rank_le_of_kernel_bound entry_kernel_finrank_lower_bound

end CycleQ2SeedGlobalFactorRank

#print axioms CycleQ2SeedGlobalFactorRank.entry_kernel_finrank_lower_bound
#print axioms CycleQ2SeedGlobalFactorRank.entry_rank_upper_bound
end
end

/- Component: continuation_3/cylinder_bridge/SegreCechGlobalLift.lean -/
section
/-! # Global relation vectors realizing every actual kernel cocycle

Ambient matrix Čech H1 exactness gives local matrices. Their cofactor
images agree, so actual homogeneous section gluing gives a degree-28
relation vector. Faithfulness of the coordinate localization proves the
literal global relation equations.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreGlobalObstruction

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SegreRelationsLocal
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedProjection
  CycleQ2SegreCechConnecting CycleQ2SegreFactorCech CycleQ2SegreGradedChartExact

theorem cofactor_locals_compatible (P : ActualKernelCocycles)
    (N : localGraded ℂ 57 Complex.I matrixGrades)
    (hNP : overlapDifference ℂ 57 Complex.I N.val=P.val) (i j : Fin 3) :
    (pairRestriction ℂ 57 Complex.I i j).mapMatrix
      (cofactorDifferential (localizeMatrix ℂ 57 Complex.I {i} SeedMatrix) (N.val i))=
    (secondPairRestriction ℂ 57 Complex.I i j).mapMatrix
      (cofactorDifferential (localizeMatrix ℂ 57 Complex.I {j} SeedMatrix) (N.val j)) := by
  have hp := kernelCocycle_properties ℂ 57 Complex.I SeedMatrix matrixGrades P
  have hz : cofactorDifferential (localizeMatrix ℂ 57 Complex.I {i,j} SeedMatrix)
      (overlapDifference ℂ 57 Complex.I N.val i j)=0 := by
    rw [hNP]
    exact hp.2.1 i j
  have hi := map_cofactorDifferential (B:=SeedLocal ℂ 57 Complex.I {i,j})
    (pairRestriction ℂ 57 Complex.I i j)
    (localizeMatrix ℂ 57 Complex.I {i} SeedMatrix) (N.val i)
  have hj := map_cofactorDifferential (B:=SeedLocal ℂ 57 Complex.I {i,j})
    (secondPairRestriction ℂ 57 Complex.I i j)
    (localizeMatrix ℂ 57 Complex.I {j} SeedMatrix) (N.val j)
  simp only [pairRestriction,secondPairRestriction,restrict_localizeMatrix] at hi hj
  simp only [overlapDifference,cofactorDifferential_sub,pairRestriction,secondPairRestriction] at hz
  rw [←hj,←hi] at hz
  exact (sub_eq_zero.mp hz).symm

/-- The actual sixteen relation equations descend from one faithful chart. -/
theorem globalRelations_of_local_preimage (C : GlobalMatrix ℂ 57 Complex.I)
    (N : Matrix (Fin 3) (Fin 3) (SeedLocal ℂ 57 Complex.I {0}))
    (hC : localizeMatrix ℂ 57 Complex.I {0} C=
      cofactorDifferential (localizeMatrix ℂ 57 Complex.I {0} SeedMatrix) N) :
    CycleQ2SegreRelations.relations SeedMatrix *ᵥ vector C=0 := by
  have hr : CycleQ2SegreRelations.relations
      (localizeMatrix ℂ 57 Complex.I {0} SeedMatrix) *ᵥ
      vector (localizeMatrix ℂ 57 Complex.I {0} C)=0 := by
    rw [hC]
    exact relations_cofactorDifferential _ N
      (CycleQ2SegreComplexChartExact.chartMatrix_cofactors {0})
  have hm := map_relations_action (A:=SeedRing (57:ℂ) Complex.I)
    (B:=SeedLocal ℂ 57 Complex.I {0})
    (algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I {0})) SeedMatrix C
  change (fun k => algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I {0})
      ((CycleQ2SegreRelations.relations SeedMatrix *ᵥ vector C) k))=
    CycleQ2SegreRelations.relations (localizeMatrix ℂ 57 Complex.I {0} SeedMatrix) *ᵥ
      vector (localizeMatrix ℂ 57 Complex.I {0} C) at hm
  rw [hr] at hm
  funext k
  apply localization_injective ℂ 57 Complex.I {0}
  change algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I {0})
      ((CycleQ2SegreRelations.relations SeedMatrix *ᵥ vector C) k)=
    algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I {0}) 0
  rw [map_zero (algebraMap (SeedRing (57:ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I {0}))]
  exact congrFun hm k

/-- Every actual kernel Čech cocycle is represented by local lifts of an
actual degree-28 invariant global relation vector. -/
theorem kernelCocycle_has_global_relation (P : ActualKernelCocycles) :
    ∃ (C : relationVariations) (N : localGraded ℂ 57 Complex.I matrixGrades),
      HasLocalLift ℂ 57 Complex.I SeedMatrix (degree28ToGlobal C.val) N.val ∧
      overlapDifference ℂ 57 Complex.I N.val=P.val := by
  obtain ⟨N,hNP⟩ := kernelCech_ambient_preimage ℂ 57 Complex.I SeedMatrix matrixGrades P
  let Q : LocalMatrices ℂ 57 Complex.I := fun i =>
    cofactorDifferential (localizeMatrix ℂ 57 Complex.I {i} SeedMatrix) (N.val i)
  have hQg : LocalHasGrades ℂ 57 Complex.I (fun _ _ => (28,0)) Q := by
    intro i
    exact localCofactor_grade {i} (N.val i) (N.property i)
  obtain ⟨A,hA,hAg,hAQ⟩ := exists_homogeneous_matrix_gluing ℂ 57 Complex.I
    (fun _ _ => (28,0)) Q (cofactor_locals_compatible P N hNP) hQg
  let Cq := quotientMatrix ℂ 57 Complex.I A
  have hrel : CycleQ2SegreRelations.relations SeedMatrix *ᵥ vector Cq=0 :=
    globalRelations_of_local_preimage Cq (N.val 0) (hAQ 0)
  have hAh (i j : Fin 3) : (A i j).IsWeightedHomogeneous fullGrading (28,0) :=
    (signedHomogeneous_iff ℂ (A i j) (28,0)).mp (hAg i j)
  let C0 : Degree28Matrices := fun i j => ⟨Cq i j,
    Submodule.mem_map.mpr ⟨A i j,hAh i j,rfl⟩⟩
  let C : relationVariations := ⟨C0,hrel⟩
  refine ⟨C,N,?_,hNP⟩
  intro i
  exact (hAQ i).symm

end CycleQ2SegreGlobalObstruction

#print axioms CycleQ2SegreGlobalObstruction.globalRelations_of_local_preimage
#print axioms CycleQ2SegreGlobalObstruction.kernelCocycle_has_global_relation
end
end

/- Component: continuation_3/SegreCoefficientRankBinding.lean -/
section
/-! # The literal coefficient relation matrix has the actual quotient-map rank -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreCoefficientRankBinding

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceJacobian
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidenceJacobianNaturality
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SegreRelationsLocal
  CycleQ2SegreGlobalObstruction CycleQ2SegreGlobalRankSpaces

abbrev Seed := SeedRing (57:ℂ) Complex.I

def nf : Poly ℂ →ₗ[ℂ] Poly ℂ :=
  fullRemainderLinear (seedCubicCoefficients Complex.I) (seedSexticCoefficients (57:ℂ) Complex.I)
    (seedCubicCoefficients_unit Complex.I) (seedSexticCoefficients_unit (57:ℂ) Complex.I)

theorem nf_standard (p : Poly ℂ) : FullStandard (nf p) :=
  (fullRemainder_spec (seedCubicCoefficients Complex.I) (seedSexticCoefficients (57:ℂ) Complex.I)
    (seedCubicCoefficients_unit Complex.I) (seedSexticCoefficients_unit (57:ℂ) Complex.I) p).1

theorem nf_grade (d : ℕ) (p : Poly ℂ) (hp : HG p (d,0)) : HG (nf p) (d,0) :=
  fullRemainder_preserves_grading (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (seedCubicCoefficients_unit Complex.I)
    (seedSexticCoefficients_unit (57:ℂ) Complex.I) hp

theorem nf_quotient (p : Poly ℂ) :
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) (nf p)=
      Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) p := by
  apply Ideal.Quotient.eq.mpr
  change fullRemainder (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (seedCubicCoefficients_unit Complex.I)
    (seedSexticCoefficients_unit (57:ℂ) Complex.I) p-p∈_
  have h := sub_fullRemainder_mem (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (seedCubicCoefficients_unit Complex.I)
    (seedSexticCoefficients_unit (57:ℂ) Complex.I) p
  rw [seedCubicCoefficients_polynomial,seedSexticCoefficients_polynomial] at h
  simpa only [neg_sub] using (equationsIdeal (smoothH Complex.I)
    (smoothF (57:ℂ) Complex.I)).neg_mem h

theorem nf_zero_iff (p : Poly ℂ) : nf p=0 ↔
    Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) p=0 := by
  change fullRemainder (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (seedCubicCoefficients_unit Complex.I)
    (seedSexticCoefficients_unit (57:ℂ) Complex.I) p=0 ↔ _
  rw [fullRemainder_eq_zero_iff,seedCubicCoefficients_polynomial,
    seedSexticCoefficients_polynomial,Ideal.Quotient.eq_zero_iff_mem]

def expansion (d : ℕ) (v : StandardIndex d → ℂ) : Poly ℂ :=
  ∑ e, v e • monomial (standardExponent e) 1

theorem expansion_grade (d : ℕ) (v : StandardIndex d → ℂ) : HG (expansion d v) (d,0) := by
  apply (weightedHomogeneousSubmodule ℂ fullGrading (d,0)).sum_mem
  intro e _
  exact (weightedHomogeneousSubmodule ℂ fullGrading (d,0)).smul_mem (v e)
    (isWeightedHomogeneous_monomial fullGrading (standardExponent e) (1:ℂ) (standardExponent_grade e))

theorem expansion_coefficients (d : ℕ) (p : Poly ℂ) (hs : FullStandard p) (hg : HG p (d,0)) :
    expansion d (fun e => p.coeff (standardExponent e))=p :=
  standardExpansion_eq d p hs hg

def decode : (ColumnIndex → ℂ) →ₗ[ℂ] Degree28Matrices where
  toFun v i j := ⟨Ideal.Quotient.mk
      (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I))
        (expansion 28 (fun e => v (cofactorPosition.symm (i,j),e))),
    Submodule.mem_map.mpr ⟨_,expansion_grade _ _,rfl⟩⟩
  map_add' v w := by
    funext i j
    apply Subtype.ext
    simp [expansion,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by
    funext i j
    apply Subtype.ext
    change Ideal.Quotient.mk _ (expansion 28
      (fun e => c*v (cofactorPosition.symm (i,j),e)))=
      c • Ideal.Quotient.mk _ (expansion 28 (fun e => v (cofactorPosition.symm (i,j),e)))
    have he : expansion 28 (fun e => c*v (cofactorPosition.symm (i,j),e))=
        c • expansion 28 (fun e => v (cofactorPosition.symm (i,j),e)) := by
      simp only [expansion,Finset.smul_sum,smul_smul]
    rw [he]
    exact map_smul (Ideal.Quotient.mkₐ ℂ (equationsIdeal (smoothH Complex.I)
      (smoothF (57:ℂ) Complex.I))).toLinearMap c _

theorem vector_decode (v : ColumnIndex → ℂ) (k : Fin 9) :
    vector (degree28ToGlobal (decode v)) k=
      Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I))
        (expansion 28 (fun e => v (k,e))) := by
  fin_cases k <;> rfl

theorem decode_surjective : Function.Surjective decode := by
  intro C
  choose P hP hPC using fun i j => Submodule.mem_map.mp (C i j).property
  let v : ColumnIndex → ℂ := fun ke =>
    (nf (P (cofactorPosition ke.1).1 (cofactorPosition ke.1).2)).coeff (standardExponent ke.2)
  refine ⟨v,?_⟩
  funext i j
  apply Subtype.ext
  change Ideal.Quotient.mk _ (expansion 28
    (fun e => v (cofactorPosition.symm (i,j),e)))=(C i j).val
  have hv : (fun e => v (cofactorPosition.symm (i,j),e))=
      (fun e => (nf (P i j)).coeff (standardExponent e)) := by
    simp only [v,Equiv.apply_symm_apply]
  rw [hv,expansion_coefficients 28 _ (nf_standard _) (nf_grade _ _ (hP i j)),nf_quotient]
  exact hPC i j

def rowPolynomial (v : ColumnIndex → ℂ) (k : Fin 16) : Poly ℂ :=
  ∑ j : Fin 9, CycleQ2SegreRelations.relations (rawSeedMatrix (57:ℂ)) k j *
    expansion 28 (fun e => v (j,e))

theorem relation_entry_grade (M : Matrix (Fin 3) (Fin 3) (Poly ℂ))
    (hM : ∀ i j,HG (M i j) (14,0)) (k : Fin 16) (j : Fin 9) :
    HG (CycleQ2SegreRelations.relations M k j) (14,0) := by
  fin_cases k <;> fin_cases j <;>
    simp only [CycleQ2SegreRelations.relations,Matrix.of_apply,
      Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.cons_val_zero,Matrix.cons_val_succ]
  all_goals first
    | exact isWeightedHomogeneous_zero _ _ _
    | exact hM _ _
    | exact (hM _ _).neg

theorem rowPolynomial_grade (v : ColumnIndex → ℂ) (k : Fin 16) : HG (rowPolynomial v k) (42,0) := by
  apply (weightedHomogeneousSubmodule ℂ fullGrading (42,0)).sum_mem
  intro j _
  simpa using (relation_entry_grade (rawSeedMatrix (57:ℂ)) (rawSeedMatrix_homogeneous 57) k j).mul
    (expansion_grade 28 (fun e => v (j,e)))

theorem relationMap_decode (v : ColumnIndex → ℂ) (k : Fin 16) :
    relationMap (decode v) k=Ideal.Quotient.mk
      (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) (rowPolynomial v k) := by
  change (∑ j : Fin 9,CycleQ2SegreRelations.relations SeedMatrix k j *
      vector (degree28ToGlobal (decode v)) j)=_
  simp only [rowPolynomial,map_sum,map_mul,segreRelations_map,vector_decode]
  rfl

def coefficientMap : (ColumnIndex → ℂ) →ₗ[ℂ] (RelationIndex → ℂ) :=
  Matrix.mulVecLin (seedCoefficientRelations (57:ℂ) Complex.I)

theorem coefficientMap_apply (v : ColumnIndex → ℂ) (k : Fin 16) (e : StandardIndex 42) :
    coefficientMap v (k,e)=(nf (rowPolynomial v k)).coeff (standardExponent e) := by
  have hterm (j : Fin 9) : nf
      (CycleQ2SegreRelations.relations (rawSeedMatrix (57:ℂ)) k j *
        expansion 28 (fun f => v (j,f)))=
      ∑ f : StandardIndex 28,v (j,f) • nf
        (CycleQ2SegreRelations.relations (rawSeedMatrix (57:ℂ)) k j *
          monomial (standardExponent f) 1) := by
    rw [expansion,Finset.mul_sum,map_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [mul_smul_comm,map_smul]
  rw [rowPolynomial,map_sum]
  simp_rw [hterm]
  simp only [coeff_sum,coeff_smul,smul_eq_mul]
  change (∑ q : ColumnIndex,seedCoefficientRelations (57:ℂ) Complex.I (k,e) q*v q)=_
  simp only [Fintype.sum_prod_type,seedCoefficientRelations,coefficientRelations]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro f _
  exact mul_comm _ _

theorem coefficient_zero_iff (v : ColumnIndex → ℂ) :
    coefficientMap v=0 ↔ relationMap (decode v)=0 := by
  constructor
  · intro h
    funext k
    rw [relationMap_decode]
    apply (nf_zero_iff _).mp
    apply standard_eq_zero_of_coefficients (nf_standard _) (nf_grade _ _ (rowPolynomial_grade v k))
    intro e
    rw [←coefficientMap_apply,h]
    rfl
  · intro h
    funext ke
    rw [coefficientMap_apply]
    have hk := congrFun h ke.1
    rw [relationMap_decode] at hk
    have hz := (nf_zero_iff _).mpr hk
    rw [hz,coeff_zero]
    rfl

theorem coefficient_kernel :
    LinearMap.ker coefficientMap=LinearMap.ker (relationMap.comp decode) := by
  ext v
  exact coefficient_zero_iff v

theorem relation_comp_range :
    LinearMap.range (relationMap.comp decode)=LinearMap.range relationMap := by
  ext z
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨decode v,rfl⟩
  · rintro ⟨C,rfl⟩
    obtain ⟨v,rfl⟩ := decode_surjective C
    exact ⟨v,rfl⟩

/-- This is the original 39440-by-9522 coefficient matrix, with exactly
the same rank as the actual quotient relation map used in the Čech proof. -/
theorem coefficient_rank_eq :
    Module.finrank ℂ (LinearMap.range coefficientMap)=
      Module.finrank ℂ (LinearMap.range relationMap) := by
  have h1 := coefficientMap.finrank_range_add_finrank_ker
  have h2 := (relationMap.comp decode).finrank_range_add_finrank_ker
  rw [coefficient_kernel] at h1
  rw [relation_comp_range] at h2
  omega

end CycleQ2SegreCoefficientRankBinding

#print axioms CycleQ2SegreCoefficientRankBinding.coefficient_rank_eq
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorTopCriterion.lean -/
section
/-! # The actual top connecting class detects precisely kernel boundaries -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechActualTop CycleQ2SegreCechConnecting
  CycleQ2SegreFactorChartExact CycleQ2SegreFactorGraded CycleQ2SegreFactorRestrictions

abbrev ActualKernelBoundaries := kernelBoundaries ℂ (57:ℂ) Complex.I
  CycleQ2SegreGlobalObstruction.SeedMatrix CycleQ2SegreGlobalObstruction.matrixGrades

def singletonMatrices (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2}) : LocalMatrices ℂ 57 Complex.I :=
  Fin.cons (gradedFactorMap {0} (by decide) F0)
    (Fin.cons (gradedFactorMap {1} (by decide) F1)
      (Fin.cons (gradedFactorMap {2} (by decide) F2) (fun i => Fin.elim0 i)))

def singletonGraded (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}) :
    localGraded ℂ 57 Complex.I CycleQ2SegreGlobalObstruction.matrixGrades :=
  ⟨singletonMatrices F0 F1 F2,by
    intro i
    fin_cases i
    · change MatrixGrade {0} (gradedFactorMap {0} (by decide) F0)
      exact gradedFactorMap_grade {0} (by decide) F0
    · change MatrixGrade {1} (gradedFactorMap {1} (by decide) F1)
      exact gradedFactorMap_grade {1} (by decide) F1
    · change MatrixGrade {2} (gradedFactorMap {2} (by decide) F2)
      exact gradedFactorMap_grade {2} (by decide) F2⟩

def singletonKernel (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}) :
    LinearMap.ker (localD ℂ 57 Complex.I CycleQ2SegreGlobalObstruction.SeedMatrix
      CycleQ2SegreGlobalObstruction.matrixGrades) :=
  ⟨singletonGraded F0 F1 F2,by
    change localD ℂ 57 Complex.I _ _ (singletonGraded F0 F1 F2)=0
    funext i
    fin_cases i
    · change cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix {0})
        (gradedFactorMap {0} (by decide) F0)=0
      exact gradedFactorMap_kernel {0} (by decide) F0
    · change cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix {1})
        (gradedFactorMap {1} (by decide) F1)=0
      exact gradedFactorMap_kernel {1} (by decide) F1
    · change cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix {2})
        (gradedFactorMap {2} (by decide) F2)=0
      exact gradedFactorMap_kernel {2} (by decide) F2⟩

theorem factorD0_isBoundary (P : ActualKernelCocycles)
    (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2})
    (hF : FactorLifts P (factorD0 F0 F1 F2)) : P∈ActualKernelBoundaries := by
  let K := singletonKernel F0 F1 F2
  refine ⟨K,?_⟩
  apply Subtype.ext
  apply cocycle_eq_of_three ℂ 57 Complex.I
  · exact overlap_pairCocycle ℂ 57 Complex.I _ (singletonGraded F0 F1 F2)
  · exact (kernelCocycle_properties ℂ 57 Complex.I _ _ P).2.2
  · change (res (by decide : ({1}:Finset (Fin 3))⊆{0,1})).mapMatrix
        (gradedFactorMap {1} (by decide) F1)-
      (res (by decide : ({0}:Finset (Fin 3))⊆{0,1})).mapMatrix
        (gradedFactorMap {0} (by decide) F0)=P.val 0 1
    rw [gradedFactorMap_restriction (by decide) (by decide),
      gradedFactorMap_restriction (by decide) (by decide),
      ← map_sub (gradedFactorMap {0,1} (by decide))]
    exact hF.1
  · change (res (by decide : ({2}:Finset (Fin 3))⊆{0,2})).mapMatrix
        (gradedFactorMap {2} (by decide) F2)-
      (res (by decide : ({0}:Finset (Fin 3))⊆{0,2})).mapMatrix
        (gradedFactorMap {0} (by decide) F0)=P.val 0 2
    rw [gradedFactorMap_restriction (by decide) (by decide),
      gradedFactorMap_restriction (by decide) (by decide),
      ← map_sub (gradedFactorMap {0,2} (by decide))]
    exact hF.2.1
  · change (res (by decide : ({2}:Finset (Fin 3))⊆{1,2})).mapMatrix
        (gradedFactorMap {2} (by decide) F2)-
      (res (by decide : ({1}:Finset (Fin 3))⊆{1,2})).mapMatrix
        (gradedFactorMap {1} (by decide) F1)=P.val 1 2
    rw [gradedFactorMap_restriction (by decide) (by decide),
      gradedFactorMap_restriction (by decide) (by decide),
      ← map_sub (gradedFactorMap {1,2} (by decide))]
    exact hF.2.2

/-- A true graded kernel boundary admits factor lifts with zero triple defect. -/
theorem boundary_factor_lift (P : ActualKernelCocycles) (hP : P∈ActualKernelBoundaries) :
    ∃ F : FactorPairs, FactorLifts P F ∧ factorD1 F=0 := by
  obtain ⟨K,hK⟩ := hP
  have hk0 : localD ℂ 57 Complex.I CycleQ2SegreGlobalObstruction.SeedMatrix
      CycleQ2SegreGlobalObstruction.matrixGrades K.val=0 := K.property
  obtain ⟨F0,h0⟩ := graded_factor_lift {0} (by decide) (K.val.val 0)
    (congrFun hk0 0) (K.val.property 0)
  obtain ⟨F1,h1⟩ := graded_factor_lift {1} (by decide) (K.val.val 1)
    (congrFun hk0 1) (K.val.property 1)
  obtain ⟨F2,h2⟩ := graded_factor_lift {2} (by decide) (K.val.val 2)
    (congrFun hk0 2) (K.val.property 2)
  refine ⟨factorD0 F0 F1 F2,?_,factorD1_factorD0 F0 F1 F2⟩
  constructor
  · change gradedFactorMap {0,1} _
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1-
       gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0)=_
    rw [map_sub (gradedFactorMap {0,1} (by decide)),← gradedFactorMap_restriction (by decide) (by decide),
      ← gradedFactorMap_restriction (by decide) (by decide),h1,h0]
    exact congrArg (fun Q : ActualKernelCocycles => Q.val 0 1) hK
  · constructor
    · change gradedFactorMap {0,2} _
        (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2-
         gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0)=_
      rw [map_sub (gradedFactorMap {0,2} (by decide)),← gradedFactorMap_restriction (by decide) (by decide),
        ← gradedFactorMap_restriction (by decide) (by decide),h2,h0]
      exact congrArg (fun Q : ActualKernelCocycles => Q.val 0 2) hK
    · change gradedFactorMap {1,2} _
        (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2-
         gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)=_
      rw [map_sub (gradedFactorMap {1,2} (by decide)),← gradedFactorMap_restriction (by decide) (by decide),
        ← gradedFactorMap_restriction (by decide) (by decide),h2,h1]
      exact congrArg (fun Q : ActualKernelCocycles => Q.val 1 2) hK

/-- The actual top Čech class vanishes exactly when the original cofactor-
kernel cocycle is an actual graded kernel boundary. The positive factor H1
vanishing is already discharged by its literal curve restriction proof. -/
theorem top_boundary_iff_kernel_boundary (P : ActualKernelCocycles)
    (F : FactorPairs) (c : ScalarSections Finset.univ) (hF : FactorLifts P F)
    (hd : factorD1 F=gradedGaugeMap Finset.univ (by decide) c) :
    c∈actualBoundary ℂ (57:ℂ) Complex.I ↔ P∈ActualKernelBoundaries := by
  constructor
  · intro hc
    rw [← scalarD1_range] at hc
    obtain ⟨B,hB⟩ := hc
    have hz : factorD1 (F-pairGauge B)=0 := by
      rw [map_sub factorD1,hd,factorD1_pairGauge,hB,sub_self]
    obtain ⟨F0,F1,F2,h0⟩ := factorCech_exact (F-pairGauge B) hz
    have hF' := factorLifts_sub_pairGauge P F hF B
    rw [h0] at hF'
    exact factorD0_isBoundary P F0 F1 F2 hF'
  · intro hp
    obtain ⟨G,hG,hG0⟩ := boundary_factor_lift P hp
    obtain ⟨B,hB⟩ := factorLifts_difference_gauge P F G hF hG
    have hh := congrArg factorD1 hB
    rw [map_sub factorD1,hd,hG0,
      sub_zero (gradedGaugeMap Finset.univ (by decide) c),factorD1_pairGauge] at hh
    have he : c=scalarD1 B := gradedGaugeMap_injective Finset.univ (by decide) hh
    rw [he,← scalarD1_range]
    exact ⟨B,rfl⟩

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.boundary_factor_lift
#print axioms CycleQ2SegreFactorCech.top_boundary_iff_kernel_boundary
end
end

/- Component: continuation_3/ModularGlobalFactorRank.lean -/
section
/-! A graph of actual factor equations bounds the modular cofactor kernel.
Only the finite curve restriction kernels are used as ambient factor spaces;
no assertion that every ambient pair is globally divisible by the linkage
element is made or needed. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 1024
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalFactorRank

open Matrix CycleQ2ModularGlobalFactorSpaces CycleQ2ModularGlobalFactorLift
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechGlobalGluing
  CycleQ2ModularFactorChartExact CycleQ2SegreFactorExact

abbrev EntryKernel := LinearMap.ker entryDifferential

instance domainAddCommGroup : AddCommGroup Domain := inferInstance
instance domainModule : Module K Domain := inferInstance
instance inputAddCommGroup : AddCommGroup Input14 := inferInstance
instance inputModule : Module K Input14 := inferInstance
instance kernelAddCommGroup : AddCommGroup EntryKernel := Submodule.addCommGroup _
instance kernelModule : Module K EntryKernel := Submodule.module _

private theorem scalar_factor_identity (p a b v w n : A) (c : K) :
    p*(c • n)-((c • v)*b+a*(c • w))=c • (p*n-(v*b+a*w)) := by
  simp only [smul_sub,smul_add,smul_mul_assoc,mul_smul_comm]

def factorEquation : Domain × EntryKernel →ₗ[K] Matrix (Fin 3) (Fin 3) A where
  toFun z i j := CycleQ2ModularGlobalFactorSpaces.linkage*(z.2.val i j).val-
    (leftValue z.1 i*right j+left i*rightValue z.1 j)
  map_add' z w := by
    funext i j
    change CycleQ2ModularGlobalFactorSpaces.linkage*((z.2.val i j).val+(w.2.val i j).val)-
      ((leftValue z.1 i+leftValue w.1 i)*right j+left i*(rightValue z.1 j+rightValue w.1 j))=_
    change _=(CycleQ2ModularGlobalFactorSpaces.linkage*(z.2.val i j).val-
      (leftValue z.1 i*right j+left i*rightValue z.1 j))+
      (CycleQ2ModularGlobalFactorSpaces.linkage*(w.2.val i j).val-
      (leftValue w.1 i*right j+left i*rightValue w.1 j))
    ring
  map_smul' c z := by
    funext i j
    exact scalar_factor_identity CycleQ2ModularGlobalFactorSpaces.linkage
      (left i) (right j) (leftValue z.1 i) (rightValue z.1 j) (z.2.val i j).val c

abbrev FactorGraph := LinearMap.ker factorEquation

instance graphAddCommGroup : AddCommGroup FactorGraph := Submodule.addCommGroup _
instance graphModule : Module K FactorGraph := Submodule.module _

theorem mem_factorGraph (v : Domain) (N : EntryKernel) :
    (v,N)∈FactorGraph ↔ ∀ i j,
      CycleQ2ModularGlobalFactorSpaces.linkage*(N.val i j).val=
        leftValue v i*right j+left i*rightValue v j := by
  change factorEquation (v,N)=0 ↔ _
  constructor
  · intro h i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) A => M i j) h
    change CycleQ2ModularGlobalFactorSpaces.linkage*(N.val i j).val-
      (leftValue v i*right j+left i*rightValue v j)=0 at hh
    exact sub_eq_zero.mp hh
  · intro h
    funext i j
    exact sub_eq_zero.mpr (h i j)

def graphToDomain : FactorGraph →ₗ[K] Domain :=
  (LinearMap.fst K Domain EntryKernel).comp FactorGraph.subtype

def graphToKernel : FactorGraph →ₗ[K] EntryKernel :=
  (LinearMap.snd K Domain EntryKernel).comp FactorGraph.subtype

theorem graphToDomain_injective : Function.Injective graphToDomain := by
  intro x y h
  apply Subtype.ext
  apply Prod.ext
  · exact h
  · apply Subtype.ext
    funext i j
    apply Subtype.ext
    apply CycleQ2ModularGlobalFactorSpaces.linkage_regular
    have hx := (mem_factorGraph x.val.1 x.val.2).mp x.property i j
    have hy := (mem_factorGraph y.val.1 y.val.2).mp y.property i j
    change x.val.1=y.val.1 at h
    rw [h] at hx
    exact hx.trans hy.symm

instance factorGraph_finite : Module.Finite K FactorGraph := by
  letI : Module.Finite K Domain := domain_finite
  letI : IsNoetherian K Domain := isNoetherian_of_isNoetherianRing_of_finite K Domain
  exact Module.Finite.of_injective graphToDomain graphToDomain_injective

theorem factorGraph_finrank_le : Module.finrank K FactorGraph≤237 :=
  (LinearMap.finrank_le_finrank_of_injective graphToDomain_injective).trans_eq domain_finrank

theorem graphToKernel_surjective : Function.Surjective graphToKernel := by
  intro N
  obtain ⟨v,hv⟩ := exists_global_factor_pair N.val N.property
  exact ⟨⟨(v,N),(mem_factorGraph v N).mpr hv⟩,rfl⟩

def graphGauge : FactorGraph := ⟨(gaugeVector,0),by
  apply (mem_factorGraph gaugeVector 0).mpr
  intro i j
  change CycleQ2ModularGlobalFactorSpaces.linkage*0=left i*right j+left i*(-right j)
  ring⟩

theorem gaugeVector_ne_zero : gaugeVector≠0 := by
  have hb : seedBasis K (57:K) 33 ((0:Fin 3),(0:Fin 3))≠0 :=
    (seedBasis K (57:K) 33).ne_zero _
  letI : Nontrivial A := ⟨⟨_,0,hb⟩⟩
  letI : Nontrivial (Chart {0}) :=
    (localization_injective K (57:K) 33 {0}).nontrivial
  intro hz
  have hl (i : Fin 3) : left i=0 :=
    congrArg (fun v : Domain => leftValue v i) hz
  let F := factorData {0} (by simp)
  have h10 : (1:Chart {0})=0 := gauge_scalar_unique F.linkage F.regular F.matrix
    F.left F.right F.product F.entries_generate 1 0 (by
      intro i
      change (1:Chart {0})*chartMap {0} (left i)=0*chartMap {0} (left i)
      rw [hl i,map_zero]
      simp)
  exact one_ne_zero h10

theorem graphGauge_ne_zero : graphGauge≠0 := by
  intro hz
  exact gaugeVector_ne_zero (congrArg graphToDomain hz)

theorem graphGauge_mem_kernel : graphGauge∈LinearMap.ker graphToKernel := by
  rfl

theorem graphToKernel_kernel_finrank_pos :
    1≤Module.finrank K (LinearMap.ker graphToKernel) := by
  have hle : Submodule.span K {graphGauge}≤LinearMap.ker graphToKernel := by
    apply Submodule.span_le.mpr
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact graphGauge_mem_kernel
  have h := Submodule.finrank_mono hle
  have hs : Module.finrank K (Submodule.span K {graphGauge})=1 :=
    @finrank_span_singleton K FactorGraph (inferInstance : DivisionRing K)
      (inferInstance : AddCommGroup FactorGraph) (inferInstance : Module K FactorGraph)
      graphGauge graphGauge_ne_zero
  rw [hs] at h
  exact h

theorem entry_kernel_finrank_upper_bound :
    Module.finrank K (LinearMap.ker entryDifferential)≤236 := by
  have h := graphToKernel.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr graphToKernel_surjective,finrank_top] at h
  have hdim := factorGraph_finrank_le
  have hgauge := graphToKernel_kernel_finrank_pos
  change Module.finrank K EntryKernel+Module.finrank K (LinearMap.ker graphToKernel)=
    Module.finrank K FactorGraph at h
  change Module.finrank K EntryKernel≤236
  omega

theorem entry_rank_lower_bound :
    1915≤Module.finrank K (LinearMap.range entryDifferential) := by
  have h := entryDifferential.finrank_range_add_finrank_ker
  rw [input14_finrank] at h
  have hk := entry_kernel_finrank_upper_bound
  omega

theorem entryJacobianBlock_rank_lower_bound :
    1915≤Module.finrank K (LinearMap.range (Matrix.mulVecLin
      (CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock (57:K) 33))) := by
  rw [CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock_rank_eq (57:K) 33]
  exact entry_rank_lower_bound

end CycleQ2ModularGlobalFactorRank

#print axioms CycleQ2ModularGlobalFactorRank.entry_kernel_finrank_upper_bound
#print axioms CycleQ2ModularGlobalFactorRank.entry_rank_lower_bound

#print axioms CycleQ2ModularGlobalFactorRank.entryJacobianBlock_rank_lower_bound
end
end

/- Component: continuation_3/SeedGlobalGaugeLine.lean -/
section
/-! The actual scalar gauge is nonzero, so the global factor image has
exact dimension236. This statement concerns the factor image; equality
with the whole cofactor kernel is established separately. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalGaugeLine

open CycleQ2SeedGlobalFactorMap CycleQ2SeedGlobalFactorGauge
  CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechGlobalGluing CycleQ2SegreFactorExact

instance domain_finite : Module.Finite ℂ Domain := by
  letI : Module.Finite ℂ (Fin 3 → LeftPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite ℂ (Fin 3 → RightPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => RightPiece)
  exact Module.Finite.prod

theorem gaugeVector_ne_zero : gaugeVector≠0 := by
  have hb : seedBasis ℂ (57:ℂ) Complex.I ((0:Fin 3),(0:Fin 3))≠0 :=
    (seedBasis ℂ (57:ℂ) Complex.I).ne_zero _
  letI : Nontrivial A := ⟨⟨_,0,hb⟩⟩
  letI : Nontrivial (Chart {0}) :=
    (localization_injective ℂ (57:ℂ) Complex.I {0}).nontrivial
  intro hz
  have hl (i : Fin 3) : left i=0 :=
    congrArg (fun v : Domain => leftValue v i) hz
  let F := CycleQ2SegreFactorChartExact.factorData {0} (by simp)
  have h10 : (1:Chart {0})=0 := gauge_scalar_unique F.linkage F.regular F.matrix
    F.left F.right F.product F.entries_generate 1 0 (by
      intro i
      change (1:Chart {0})*chartMap {0} (left i)=0*chartMap {0} (left i)
      rw [hl i,map_zero]
      simp)
  exact one_ne_zero h10

theorem gradedFactorMap_gaugeVector : gradedFactorMap gaugeVector=0 := by
  funext i j
  apply Subtype.ext
  apply linkage_regular
  change linkage*factorMap gaugeVector i j=linkage*0
  rw [factorMap_formula]
  change left i*right j+left i*(-right j)=linkage*0
  ring

theorem gradedFactorMap_kernel_eq_gauge :
    LinearMap.ker gradedFactorMap=Submodule.span ℂ {gaugeVector} := by
  apply le_antisymm gradedFactorMap_kernel_le_gauge
  apply Submodule.span_le.mpr
  intro v hv
  rw [Set.mem_singleton_iff.mp hv]
  exact gradedFactorMap_gaugeVector

theorem gradedFactorMap_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker gradedFactorMap)=1 := by
  rw [gradedFactorMap_kernel_eq_gauge]
  exact @finrank_span_singleton ℂ Domain (inferInstance : DivisionRing ℂ)
    (inferInstance : AddCommGroup Domain) (inferInstance : Module ℂ Domain) gaugeVector gaugeVector_ne_zero

theorem factor_image_finrank : Module.finrank ℂ (LinearMap.range gradedFactorMap)=236 := by
  letI : Module.Finite ℂ (Fin 3 → LeftPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => LeftPiece)
  letI : Module.Finite ℂ (Fin 3 → RightPiece) :=
    Module.Finite.pi (R:=ℂ) (M:=fun _ : Fin 3 => RightPiece)
  letI : Module.Finite ℂ Domain := Module.Finite.prod
  have h := @LinearMap.finrank_range_add_finrank_ker ℂ Domain
    (inferInstance : DivisionRing ℂ) (inferInstance : AddCommGroup Domain)
    (inferInstance : Module ℂ Domain) MatrixPiece (inferInstance : AddCommGroup MatrixPiece)
    (inferInstance : Module ℂ MatrixPiece) (inferInstance : FiniteDimensional ℂ Domain) gradedFactorMap
  rw [domain_finrank,gradedFactorMap_kernel_finrank] at h
  omega

end CycleQ2SeedGlobalGaugeLine

#print axioms CycleQ2SeedGlobalGaugeLine.gaugeVector_ne_zero
#print axioms CycleQ2SeedGlobalGaugeLine.factor_image_finrank
end
end

/- Component: continuation_3/cylinder_bridge/SegreCechGlobalSurjective.lean -/
section
/-! # The actual global obstruction is the actual kernel Čech H1

Ambient matrix H1 exactness and homogeneous global gluing discharge the
surjectivity direction of the already checked connecting injection.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreGlobalObstruction

open CycleQ2SegreCechConnecting CycleQ2SegreFactorCech

theorem relationConnecting_eq_class (C : relationVariations)
    (N : localGraded ℂ 57 Complex.I matrixGrades)
    (hN : HasLocalLift ℂ 57 Complex.I SeedMatrix (degree28ToGlobal C.val) N.val)
    (P : ActualKernelCocycles) (hNP : overlapDifference ℂ 57 Complex.I N.val=P.val) :
    relationConnecting C=ActualKernelBoundaries.mkQ P := by
  let L : liftPairs ℂ 57 Complex.I SeedMatrix matrixGrades :=
    ⟨(degree28ToGlobal C.val,N),hN⟩
  have he : relationToLiftable C=
      ⟨liftProjection ℂ 57 Complex.I SeedMatrix matrixGrades L,⟨L,rfl⟩⟩ :=
    Subtype.ext rfl
  change connectingToH1 ℂ 57 Complex.I SeedMatrix matrixGrades (relationToLiftable C)=_
  rw [he,connectingToH1_apply_lift]
  change ActualKernelBoundaries.mkQ (liftCocycle ℂ 57 Complex.I SeedMatrix matrixGrades L)=_
  apply congrArg ActualKernelBoundaries.mkQ
  exact Subtype.ext hNP

theorem relationConnecting_realizes (P : ActualKernelCocycles) :
    ∃ C : relationVariations, relationConnecting C=ActualKernelBoundaries.mkQ P := by
  obtain ⟨C,N,hN,hNP⟩ := kernelCocycle_has_global_relation P
  exact ⟨C,relationConnecting_eq_class C N hN P hNP⟩

theorem relationConnecting_surjective : Function.Surjective relationConnecting := by
  intro q
  obtain ⟨P,hP⟩ := ActualKernelBoundaries.mkQ_surjective q
  obtain ⟨C,hC⟩ := relationConnecting_realizes P
  exact ⟨C,hC.trans hP⟩

/-- No ambient H1 or global-gluing hypothesis remains: the literal global
relation obstruction surjects onto the actual kernel Čech cohomology. -/
theorem relationObstructionInjection_surjective : Function.Surjective relationObstructionInjection :=
  @CycleQ2LinearRangeDescent.kernelQuotientInjection_surjective ℂ relationVariations
    ActualKernelH1 inferInstance inferInstance inferInstance inferInstance inferInstance
    relationConnecting globalCofactorImage ker_relationConnecting relationConnecting_surjective

def relationObstructionEquivKernelH1 : RelationObstruction ≃ₗ[ℂ] ActualKernelH1 :=
  LinearEquiv.ofBijective relationObstructionInjection
    ⟨relationObstructionInjection_injective,relationObstructionInjection_surjective⟩

end CycleQ2SegreGlobalObstruction

#print axioms CycleQ2SegreGlobalObstruction.relationConnecting_eq_class
#print axioms CycleQ2SegreGlobalObstruction.relationObstructionInjection_surjective
#print axioms CycleQ2SegreGlobalObstruction.relationObstructionEquivKernelH1
end
end

/- Component: continuation_3/SegreEntryCoefficientBinding.lean -/
section
/-! # The literal matrix-entry Jacobian block and its actual quotient rank -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreEntryCoefficientBinding

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder CycleQ2IncidenceJacobian
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceJacobianNaturality
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SegreGlobalObstruction
  CycleQ2SegreGlobalRankSpaces CycleQ2SegreCoefficientRankBinding

abbrev PolynomialMatrices := Matrix (Fin 3) (Fin 3) (Poly ℂ)

def rawInput : (MatrixParameter → ℂ) →ₗ[ℂ] PolynomialMatrices where
  toFun v i j := expansion 14 (fun e => v ((i,j),e))
  map_add' v w := by
    funext i j
    simp [expansion,Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' c v := by
    funext i j
    simp [expansion,Pi.smul_apply,Finset.smul_sum,smul_smul]

theorem rawInput_eq_perturbation (v : MatrixParameter → ℂ) :
    rawInput v=perturbation (fun i j e => v ((i,j),e)) := by
  funext i j
  simp only [rawInput,LinearMap.coe_mk,AddHom.coe_mk,expansion,perturbation,
    smul_monomial,smul_eq_mul,mul_one]

def decodeInput : (MatrixParameter → ℂ) →ₗ[ℂ] Input14 where
  toFun v i j := ⟨Ideal.Quotient.mk
      (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) (rawInput v i j),
    Submodule.mem_map.mpr ⟨_,expansion_grade _ _,rfl⟩⟩
  map_add' v w := by
    funext i j
    apply Subtype.ext
    change Ideal.Quotient.mk _ (rawInput (v+w) i j)=_
    rw [map_add]
    exact map_add _ _ _
  map_smul' c v := by
    funext i j
    apply Subtype.ext
    change Ideal.Quotient.mk _ (rawInput (c • v) i j)=_
    rw [map_smul]
    exact map_smul (Ideal.Quotient.mkₐ ℂ (equationsIdeal (smoothH Complex.I)
      (smoothF (57:ℂ) Complex.I))).toLinearMap c _

theorem decodeInput_surjective : Function.Surjective decodeInput := by
  intro N
  choose P hP hPN using fun i j => Submodule.mem_map.mp (N i j).property
  let v : MatrixParameter → ℂ := fun ie => (nf (P ie.1.1 ie.1.2)).coeff (standardExponent ie.2)
  refine ⟨v,?_⟩
  funext i j
  apply Subtype.ext
  change Ideal.Quotient.mk _ (expansion 14
    (fun e => (nf (P i j)).coeff (standardExponent e)))=(N i j).val
  rw [expansion_coefficients 14 _ (nf_standard _) (nf_grade _ _ (hP i j)),nf_quotient]
  exact hPN i j

def rawDifferential : (MatrixParameter → ℂ) →ₗ[ℂ] PolynomialMatrices :=
  ((cofactorDifferentialLinear (rawSeedMatrix (57:ℂ))).restrictScalars ℂ).comp rawInput

def extractCoefficients : PolynomialMatrices →ₗ[ℂ] (EquationIndex → ℂ) where
  toFun P q := (nf (P q.1.1 q.1.2)).coeff (standardExponent q.2)
  map_add' P Q := by
    funext q
    simp only [Matrix.add_apply,map_add,coeff_add,Pi.add_apply]
  map_smul' c P := by
    funext q
    simp only [Matrix.smul_apply,map_smul,coeff_smul,Pi.smul_apply,RingHom.id_apply]

def entryCoefficients : (MatrixParameter → ℂ) →ₗ[ℂ] (EquationIndex → ℂ) :=
  extractCoefficients.comp rawDifferential

theorem entryCoefficients_apply (v : MatrixParameter → ℂ) (q : EquationIndex) :
    entryCoefficients v q=(nf (cofactorDifferential (rawSeedMatrix (57:ℂ))
      (rawInput v) q.1.1 q.1.2)).coeff (standardExponent q.2) := rfl

theorem entryCoefficients_eq_linearized (v : MatrixParameter → ℂ) (q : EquationIndex) :
    entryCoefficients v q=linearizedEquations (57:ℂ) Complex.I
      (fun _ => 0) (fun _ => 0) (fun i j e => v ((i,j),e)) q := by
  rw [entryCoefficients_apply,rawInput_eq_perturbation]
  simp only [linearizedEquations,fullInvariantPolynomial,monomial_zero,Finset.sum_const_zero,
    fullFirstOrderResidual,firstOrderResidual,zero_mul,add_zero,sub_zero]
  rfl

/-- Exactly the 2151 columns belonging to the matrix-entry parameters in
 the existing universal incidence Jacobian. -/
def entryJacobianBlock : Matrix EquationIndex MatrixParameter ℂ :=
  fun q j => linearizedMatrix (57:ℂ) Complex.I q (Sum.inr (Sum.inr j))

theorem entryCoefficients_matrix : LinearMap.toMatrix' entryCoefficients=entryJacobianBlock := by
  classical
  ext q j
  rw [LinearMap.toMatrix'_apply,entryCoefficients_eq_linearized]
  unfold entryJacobianBlock linearizedMatrix
  congr 1 <;> simp [funext_iff,Pi.single_apply,eq_comm]

theorem entryJacobianBlock_map : Matrix.mulVecLin entryJacobianBlock=entryCoefficients := by
  rw [←entryCoefficients_matrix]
  exact Matrix.toLin'_toMatrix' entryCoefficients

theorem rawDifferential_grade (v : MatrixParameter → ℂ) (i j : Fin 3) :
    HG (rawDifferential v i j) (28,0) := by
  have hm := rawSeedMatrix_homogeneous (57:ℂ)
  have hn : ∀ i j,HG (rawInput v i j) (14,0) := fun i j => expansion_grade _ _
  exact ((cofactors_homogeneous _ (fun i j => (hm i j).add (hn i j)) i j).sub
    (cofactors_homogeneous _ hm i j)).sub (cofactors_homogeneous _ hn i j)

theorem entryDifferential_decode (v : MatrixParameter → ℂ) (i j : Fin 3) :
    entryDifferential (decodeInput v) i j=Ideal.Quotient.mk
      (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I))
      (rawDifferential v i j) := by
  have h := CycleQ2SegreTangentLocal.map_cofactorDifferential
    (Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)))
    (rawSeedMatrix (57:ℂ)) (rawInput v)
  exact (congrArg (fun P : Matrix (Fin 3) (Fin 3) (SeedRing (57:ℂ) Complex.I) => P i j) h).symm

theorem entryCoefficients_zero_iff (v : MatrixParameter → ℂ) :
    entryCoefficients v=0 ↔ entryDifferential (decodeInput v)=0 := by
  constructor
  · intro h
    funext i j
    rw [entryDifferential_decode]
    apply (nf_zero_iff _).mp
    apply standard_eq_zero_of_coefficients (nf_standard _)
      (nf_grade _ _ (rawDifferential_grade v i j))
    intro e
    exact congrFun h ((i,j),e)
  · intro h
    funext q
    have hz : nf (rawDifferential v q.1.1 q.1.2)=0 := by
      apply (nf_zero_iff _).mpr
      rw [←entryDifferential_decode,h]
      rfl
    change (nf (rawDifferential v q.1.1 q.1.2)).coeff (standardExponent q.2)=0
    rw [hz,coeff_zero]

theorem entryCoefficients_kernel : LinearMap.ker entryCoefficients=
    LinearMap.ker (entryDifferential.comp decodeInput) := by
  ext v
  exact entryCoefficients_zero_iff v

theorem entryDifferential_comp_range : LinearMap.range (entryDifferential.comp decodeInput)=
    LinearMap.range entryDifferential := by
  ext y
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨decodeInput v,rfl⟩
  · rintro ⟨N,rfl⟩
    obtain ⟨v,rfl⟩ := decodeInput_surjective N
    exact ⟨v,rfl⟩

/-- No abstract dimension model: the rank is that of the literal original
9522-by-2151 matrix-entry block of the incidence Jacobian. -/
theorem entryJacobianBlock_rank_eq :
    Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin entryJacobianBlock))=
      Module.finrank ℂ (LinearMap.range entryDifferential) := by
  rw [entryJacobianBlock_map]
  have h1 := entryCoefficients.finrank_range_add_finrank_ker
  have h2 := (entryDifferential.comp decodeInput).finrank_range_add_finrank_ker
  rw [entryCoefficients_kernel] at h1
  rw [entryDifferential_comp_range] at h2
  omega

end CycleQ2SegreEntryCoefficientBinding

#print axioms CycleQ2SegreEntryCoefficientBinding.entryCoefficients_matrix
#print axioms CycleQ2SegreEntryCoefficientBinding.entryJacobianBlock_rank_eq
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorTopInjection.lean -/
section
/-! # The actual kernel Čech H1 embeds in scalar H2

The linear lift relation uses the actual cofactor-kernel cocycles, actual
ideal-valued factor sections and actual scalar gauge. Its checked boundary
criterion makes descent independent of the noncanonical local lifts.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2SeedCechActualTop CycleQ2SegreFactorChartExact

abbrev FactorPairMatrices :=
  Matrix (Fin 3) (Fin 3) (Chart {0,1}) ×
  Matrix (Fin 3) (Fin 3) (Chart {0,2}) ×
  Matrix (Fin 3) (Fin 3) (Chart {1,2})

def cocycleEntries : ActualKernelCocycles →ₗ[ℂ] FactorPairMatrices where
  toFun P := (P.val 0 1,P.val 0 2,P.val 1 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def factorEntries : FactorPairs →ₗ[ℂ] FactorPairMatrices :=
  (gradedFactorMap {0,1} (by decide)).prodMap
    ((gradedFactorMap {0,2} (by decide)).prodMap (gradedFactorMap {1,2} (by decide)))

theorem factorLifts_iff_entries (P : ActualKernelCocycles) (F : FactorPairs) :
    FactorLifts P F ↔ factorEntries F=cocycleEntries P := by
  constructor
  · intro h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  · intro h
    exact ⟨congrArg Prod.fst h,congrArg (fun X : FactorPairMatrices => X.2.1) h,
      congrArg (fun X : FactorPairMatrices => X.2.2) h⟩

theorem exists_top_relation (P : ActualKernelCocycles) :
    ∃ (F : FactorPairs) (c : ScalarSections Finset.univ),
      factorEntries F=cocycleEntries P ∧
      factorD1 F=gradedGaugeMap Finset.univ (by decide) c := by
  obtain ⟨F,c,hF,hc⟩ := exists_factor_top_lift P
  exact ⟨F,c,(factorLifts_iff_entries P F).mp hF,hc⟩

theorem top_relation_boundary_iff (P : ActualKernelCocycles)
    (F : FactorPairs) (c : ScalarSections Finset.univ)
    (hF : factorEntries F=cocycleEntries P)
    (hd : factorD1 F=gradedGaugeMap Finset.univ (by decide) c) :
    c∈actualBoundary ℂ (57:ℂ) Complex.I ↔ P∈ActualKernelBoundaries :=
  top_boundary_iff_kernel_boundary P F c ((factorLifts_iff_entries P F).mpr hF) hd

def kernelH1ToH2 : ActualKernelH1 →ₗ[ℂ] ActualTopCechQuotient ℂ (57:ℂ) Complex.I :=
  @CycleQ2CechLiftRelation.quotientInjection ℂ ActualKernelCocycles FactorPairs
    (ScalarSections Finset.univ) FactorPairMatrices (GradedFactors Finset.univ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    cocycleEntries factorEntries factorD1 (gradedGaugeMap Finset.univ (by decide))
    ActualKernelBoundaries (actualBoundary ℂ (57:ℂ) Complex.I)
    exists_top_relation top_relation_boundary_iff

/-- The actual scalar top Čech quotient controls the cofactor-kernel H1,
with all local exactness, grading and positive factor H1 inputs discharged. -/
theorem kernelH1ToH2_injective : Function.Injective kernelH1ToH2 :=
  @CycleQ2CechLiftRelation.quotientInjection_injective ℂ ActualKernelCocycles FactorPairs
    (ScalarSections Finset.univ) FactorPairMatrices (GradedFactors Finset.univ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    cocycleEntries factorEntries factorD1 (gradedGaugeMap Finset.univ (by decide))
    ActualKernelBoundaries (actualBoundary ℂ (57:ℂ) Complex.I)
    exists_top_relation top_relation_boundary_iff

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.kernelH1ToH2_injective
end
end

/- Component: continuation_3/SeedGlobalFactorExact.lean -/
section
/-! The full actual degree-14 cofactor kernel is the global factor image.
All local factor lifts are constructed, their scalar overlap cocycle is
contracted, and the corrected factors glue into the proved global ideal
pieces. Consequently the actual entry differential has rank exactly 1915. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalFactorExact

open Matrix CycleQ2SeedGlobalFactorMap CycleQ2SeedGlobalIdealGluing
  CycleQ2SeedGlobalFactorCech CycleQ2SeedGlobalFactorRank CycleQ2SeedGlobalGaugeLine
  CycleQ2SeedLinkageIdealRanks CycleQ2SegreGlobalRankSpaces
  CycleQ2SegreFactorCech CycleQ2SeedCechGlobalGluing

theorem glue_graded_factors (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2}) (hF : factorD0 F0 F1 F2=0) :
    ∃ v : Domain, chartSections {0} v=F0.val := by
  have hleft (i : Fin 3) := exists_global_ideal_piece .left 10 0
    left_linkagePiece_eq_restrictionKernel (F0.val.1 i) (F1.val.1 i) (F2.val.1 i)
    (F0.property.1 i) (F0.val.1 i).property
    (congrArg (fun B : FactorPairs => (B.1.val.1 i:Chart {0,1})) hF)
    (congrArg (fun B : FactorPairs => (B.2.1.val.1 i:Chart {0,2})) hF)
  have hright (j : Fin 3) := exists_global_ideal_piece .right 8 1
    right_linkagePiece_eq_restrictionKernel (F0.val.2 j) (F1.val.2 j) (F2.val.2 j)
    (F0.property.2 j) (F0.val.2 j).property
    (congrArg (fun B : FactorPairs => (B.1.val.2 j:Chart {0,1})) hF)
    (congrArg (fun B : FactorPairs => (B.2.1.val.2 j:Chart {0,2})) hF)
  choose v hv0 _hv1 _hv2 using hleft
  choose w hw0 _hw1 _hw2 using hright
  refine ⟨(v,w),?_⟩
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact hv0 i
  · funext j
    apply Subtype.ext
    exact hw0 j

theorem exists_global_factor_lift (N : Input14) (hN : entryDifferential N=0) :
    ∃ v : Domain, CycleQ2SeedGlobalFactorMap.gradedFactorMap v=N := by
  obtain ⟨F0,F1,F2,hF,hF0⟩ := exists_compatible_local_factors N hN
  obtain ⟨v,hv⟩ := glue_graded_factors F0 F1 F2 hF
  refine ⟨v,?_⟩
  funext i j
  apply Subtype.ext
  apply localization_injective ℂ 57 Complex.I {0}
  change chartMap {0} (factorMap v i j)=chartMap {0} (N i j).val
  rw [factorMap_localize {0} (by decide) v i j,hv]
  exact congrArg (fun M : Matrix (Fin 3) (Fin 3) (Chart {0}) => M i j) hF0

theorem entry_kernel_eq_factor_image :
    LinearMap.ker entryDifferential=LinearMap.range CycleQ2SeedGlobalFactorMap.gradedFactorMap := by
  apply le_antisymm
  · intro N hN
    exact exists_global_factor_lift N hN
  · exact factor_image_le_entryKernel

theorem entry_kernel_finrank : Module.finrank ℂ (LinearMap.ker entryDifferential)=236 := by
  rw [entry_kernel_eq_factor_image]
  exact factor_image_finrank

theorem entry_rank : Module.finrank ℂ (LinearMap.range entryDifferential)=1915 := by
  have h := entryDifferential.finrank_range_add_finrank_ker
  rw [input14_finrank,entry_kernel_finrank] at h
  omega

/-- The literal 9522-by-2151 matrix-entry block of the original incidence
Jacobian has this same exact rank. -/
theorem entryJacobianBlock_rank :
    Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin
      CycleQ2SegreEntryCoefficientBinding.entryJacobianBlock))=1915 :=
  CycleQ2SegreEntryCoefficientBinding.entryJacobianBlock_rank_eq.trans entry_rank

end CycleQ2SeedGlobalFactorExact

#print axioms CycleQ2SeedGlobalFactorExact.entry_kernel_eq_factor_image
#print axioms CycleQ2SeedGlobalFactorExact.entry_rank

#print axioms CycleQ2SeedGlobalFactorExact.entryJacobianBlock_rank
end
end

/- Component: continuation_3/cylinder_bridge/SegreGlobalObstructionBound.lean -/
section
/-! # The actual global cofactor obstruction has dimension at most seven

This is the composite of the actual graded local-to-global injection and
the actual factor Čech connecting injection. The target is the independently
computed seven-dimensional quotient of scalar localization sections.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreGlobalObstruction

open CycleQ2SeedCechActualTop CycleQ2SegreFactorCech

abbrev ScalarH2 := ActualTopCechQuotient ℂ (57:ℂ) Complex.I

def relationObstructionToH2 : RelationObstruction →ₗ[ℂ] ScalarH2 :=
  kernelH1ToH2.comp relationObstructionInjection

theorem relationObstructionToH2_injective : Function.Injective relationObstructionToH2 :=
  kernelH1ToH2_injective.comp relationObstructionInjection_injective

/-- The actual quotient of degree-28 relation vectors by global degree-14
cofactor variations has dimension at most seven. No rank or cohomology
vanishing hypothesis remains in this specialized theorem. -/
theorem relationObstruction_finrank_le_seven :
    Module.finrank ℂ RelationObstruction≤7 := by
  letI : Module.Finite ℂ ScalarH2 :=
    Module.Finite.of_basis (actualTopBasis ℂ (57:ℂ) Complex.I)
  have h : Module.finrank ℂ RelationObstruction≤Module.finrank ℂ ScalarH2 :=
    LinearMap.finrank_le_finrank_of_injective relationObstructionToH2_injective
  exact h.trans_eq (actualTop_rank_seven ℂ (57:ℂ) Complex.I)

end CycleQ2SegreGlobalObstruction

#print axioms CycleQ2SegreGlobalObstruction.relationObstructionToH2_injective
#print axioms CycleQ2SegreGlobalObstruction.relationObstruction_finrank_le_seven
end
end

/- Component: continuation_3/SegreActualRelationRank.lean -/
section
/-! # An unconditional rank bound for the literal seed relation matrix

The positive linkage-ideal Cech vanishing and global factor gauge have
both been proved for the actual seed. This combines those results with
the original coefficient-matrix identification; no numerical rank premise
or geometric comparison is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreActualRelationRank

open CycleQ2SegreGlobalObstruction CycleQ2SegreGlobalRankSpaces
  CycleQ2SeedGlobalFactorRank CycleQ2SegreCoefficientRankBinding

theorem actual_relation_kernel_finrank_le :
    Module.finrank ℂ relationVariations≤1922 :=
  relation_dimension_le_of_bounds entry_kernel_finrank_lower_bound
    relationObstruction_finrank_le_seven

theorem actual_relation_rank_lower_bound :
    7600≤Module.finrank ℂ (LinearMap.range relationMap) :=
  relation_rank_lower_bound_of_bounds entry_kernel_finrank_lower_bound
    relationObstruction_finrank_le_seven

/-- The original 39440-by-9522 complex matrix has rank at least7600. -/
theorem literal_coefficient_matrix_rank_lower_bound :
    7600≤Module.finrank ℂ (LinearMap.range
      (Matrix.mulVecLin (CycleQ2IncidenceJacobianNaturality.seedCoefficientRelations
        (57:ℂ) Complex.I))) := by
  change 7600≤Module.finrank ℂ (LinearMap.range coefficientMap)
  rw [coefficient_rank_eq]
  exact actual_relation_rank_lower_bound

end CycleQ2SegreActualRelationRank

#print axioms CycleQ2SegreActualRelationRank.actual_relation_kernel_finrank_le
#print axioms CycleQ2SegreActualRelationRank.literal_coefficient_matrix_rank_lower_bound
end
end

/- Component: continuation_3/cylinder_bridge/SegreTopConnectingFormula.lean -/
section
/-! # Evaluation of the canonical top connecting map on actual lifts

The formula applies to any verified local matrix and factor lifts. It does
not choose lifts linearly or identify the result with an unproved geometric
residue pairing.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2CechLiftRelation

variable {R P F C X G : Type*} [CommRing R]
  [AddCommGroup P] [Module R P] [AddCommGroup F] [Module R F]
  [AddCommGroup C] [Module R C] [AddCommGroup X] [Module R X]
  [AddCommGroup G] [Module R G]

theorem quotientInjection_apply_mk
    (u : P →ₗ[R] X) (v : F →ₗ[R] X) (d : F →ₗ[R] G) (g : C →ₗ[R] G)
    (K : Submodule R P) (H : Submodule R C)
    (hex : ∀ p : P, ∃ f c, v f=u p ∧ d f=g c)
    (hzero : ∀ p f c, v f=u p → d f=g c → (c∈H ↔ p∈K))
    (p : P) (f : F) (c : C) (hf : v f=u p) (hc : d f=g c) :
    quotientInjection u v d g K H hex hzero (K.mkQ p)=H.mkQ c :=
  connecting_apply u v d g K H hex hzero p f c hf hc

end CycleQ2CechLiftRelation

namespace CycleQ2SegreFactorCech

open CycleQ2SeedCechActualTop

theorem kernelH1ToH2_eq_class (P : ActualKernelCocycles) (F : FactorPairs)
    (c : ScalarSections Finset.univ) (hF : FactorLifts P F)
    (hd : factorD1 F=gradedGaugeMap Finset.univ (by decide) c) :
    kernelH1ToH2 (ActualKernelBoundaries.mkQ P)=
      (actualBoundary ℂ (57:ℂ) Complex.I).mkQ c :=
  @CycleQ2CechLiftRelation.quotientInjection_apply_mk ℂ ActualKernelCocycles FactorPairs
    (ScalarSections Finset.univ) FactorPairMatrices (GradedFactors Finset.univ)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    cocycleEntries factorEntries factorD1 (gradedGaugeMap Finset.univ (by decide))
    ActualKernelBoundaries (actualBoundary ℂ (57:ℂ) Complex.I)
    exists_top_relation top_relation_boundary_iff P F c
    ((factorLifts_iff_entries P F).mp hF) hd

end CycleQ2SegreFactorCech

namespace CycleQ2SegreGlobalObstruction

open CycleQ2SeedCechActualTop CycleQ2SegreCechConnecting CycleQ2SegreFactorCech

def relationClass : relationVariations →ₗ[ℂ] RelationObstruction :=
  @Submodule.mkQ ℂ relationVariations inferInstance inferInstance inferInstance
    globalCofactorImage

/-- The global obstruction's canonical scalar H2 class is the class of
any actual scalar triple defect obtained from verified local lifts. -/
theorem relationObstructionToH2_eq_class (C : relationVariations)
    (N : localGraded ℂ 57 Complex.I matrixGrades)
    (hN : HasLocalLift ℂ 57 Complex.I SeedMatrix (degree28ToGlobal C.val) N.val)
    (P : ActualKernelCocycles) (hNP : overlapDifference ℂ 57 Complex.I N.val=P.val)
    (F : FactorPairs) (c : ScalarSections Finset.univ) (hF : FactorLifts P F)
    (hd : factorD1 F=gradedGaugeMap Finset.univ (by decide) c) :
    relationObstructionToH2 (relationClass C)=
      (actualBoundary ℂ (57:ℂ) Complex.I).mkQ c := by
  change kernelH1ToH2 (relationConnecting C)=_
  rw [relationConnecting_eq_class C N hN P hNP]
  exact kernelH1ToH2_eq_class P F c hF hd

end CycleQ2SegreGlobalObstruction

#print axioms CycleQ2SegreFactorCech.kernelH1ToH2_eq_class
#print axioms CycleQ2SegreGlobalObstruction.relationObstructionToH2_eq_class
end
end

/- Component: continuation_3/SegreFullJacobianBounds.lean -/
section
/-! # Bounds for the literal full incidence Jacobian

All upper bounds use the actual polynomial relation-times-Jacobian identity.
The exact matrix-entry block supplies the lower bound. This leaves precisely
the seven additional cubic directions to establish rank1922.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreFullJacobianBounds

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidenceJacobianNaturality
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreCoefficientRankBinding
  CycleQ2SegreActualRelationRank CycleQ2SegreEntryCoefficientBinding
  CycleQ2SeedGlobalFactorExact

def fullJacobian : Matrix EquationIndex ParameterIndex ℂ :=
  linearizedMatrix (57:ℂ) Complex.I

def orderedJacobian : Matrix ColumnIndex ParameterIndex ℂ :=
  fullJacobian.submatrix columnEquiv (Equiv.refl _)

theorem orderedJacobian_rank : orderedJacobian.rank=fullJacobian.rank :=
  Matrix.rank_submatrix fullJacobian columnEquiv (Equiv.refl _)

theorem full_range_le_relation_kernel :
    LinearMap.range (Matrix.mulVecLin orderedJacobian)≤LinearMap.ker coefficientMap := by
  rintro y ⟨x,rfl⟩
  change (Matrix.mulVecLin (seedCoefficientRelations (57:ℂ) Complex.I))
    (Matrix.mulVecLin orderedJacobian x)=0
  rw [←LinearMap.comp_apply,←Matrix.mulVecLin_mul]
  have h : seedCoefficientRelations (57:ℂ) Complex.I*orderedJacobian=0 :=
    actual_coefficientRelations_linearizedMatrix (57:ℂ) Complex.I
  rw [h]
  simp

theorem coefficient_kernel_finrank_le :
    Module.finrank ℂ (LinearMap.ker coefficientMap)≤1922 := by
  have h := coefficientMap.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card,columnIndex_count] at h
  have hr := literal_coefficient_matrix_rank_lower_bound
  change 7600≤Module.finrank ℂ (LinearMap.range coefficientMap) at hr
  omega

/-- The complete cubic/sextic/matrix incidence Jacobian has rank at most1922. -/
theorem fullJacobian_rank_upper_bound : fullJacobian.rank≤1922 := by
  rw [←orderedJacobian_rank]
  exact (Submodule.finrank_mono full_range_le_relation_kernel).trans coefficient_kernel_finrank_le

theorem fullJacobian_rank_lower_bound : 1915≤fullJacobian.rank := by
  have h := Matrix.rank_submatrix_le fullJacobian id
    (fun j : MatrixParameter => Sum.inr (Sum.inr j))
  change entryJacobianBlock.rank≤fullJacobian.rank at h
  have he : entryJacobianBlock.rank=1915 := entryJacobianBlock_rank
  rwa [he] at h

abbrev FixedSexticParameters := FullInvariantIndex 3 ⊕ MatrixParameter

def fixedSexticColumn : FixedSexticParameters → ParameterIndex :=
  Sum.elim Sum.inl (fun j => Sum.inr (Sum.inr j))

def fixedSexticJacobian : Matrix EquationIndex FixedSexticParameters ℂ :=
  fullJacobian.submatrix id fixedSexticColumn

theorem fixedSexticJacobian_rank_upper_bound : fixedSexticJacobian.rank≤1922 :=
  (Matrix.rank_submatrix_le fullJacobian id fixedSexticColumn).trans fullJacobian_rank_upper_bound

theorem fixedSexticJacobian_rank_lower_bound : 1915≤fixedSexticJacobian.rank := by
  have h := Matrix.rank_submatrix_le fixedSexticJacobian id
    (Sum.inr : MatrixParameter → FixedSexticParameters)
  change entryJacobianBlock.rank≤fixedSexticJacobian.rank at h
  have he : entryJacobianBlock.rank=1915 := entryJacobianBlock_rank
  rwa [he] at h

end CycleQ2SegreFullJacobianBounds

#print axioms CycleQ2SegreFullJacobianBounds.fullJacobian_rank_upper_bound
#print axioms CycleQ2SegreFullJacobianBounds.fixedSexticJacobian_rank_upper_bound
#print axioms CycleQ2SegreFullJacobianBounds.fixedSexticJacobian_rank_lower_bound
end
end

/- Component: continuation_3/SegreCubicAnnihilator.lean -/
section
/-! # The precise finite detector criterion for the seven cubic directions

This criterion is instantiated on the literal original Jacobian blocks.
The detector identities are explicit remaining data obligations; this file
does not assert that such a detector has already been checked.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreCubicAnnihilator

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2SegreEntryCoefficientBinding
  CycleQ2SeedGlobalFactorExact CycleQ2SegreFullJacobianBounds

def cubicJacobianBlock : Matrix EquationIndex (FullInvariantIndex 3) ℂ :=
  fullJacobian.submatrix id Sum.inl

theorem fixedSextic_rank_eq_of_annihilator (L : Matrix (Fin 7) EquationIndex ℂ)
    (hL : L*entryJacobianBlock=0) (hrank : (L*cubicJacobianBlock).rank=7) :
    fixedSexticJacobian.rank=1922 := by
  have h := CycleQ2LinearAnnihilatorRank.selected_column_rank_add_le fixedSexticJacobian
    (Sum.inr : MatrixParameter → FixedSexticParameters)
    (Sum.inl : FullInvariantIndex 3 → FixedSexticParameters) L hL
  change entryJacobianBlock.rank+(L*cubicJacobianBlock).rank≤fixedSexticJacobian.rank at h
  have he : entryJacobianBlock.rank=1915 := entryJacobianBlock_rank
  rw [he,hrank] at h
  exact le_antisymm fixedSexticJacobian_rank_upper_bound h

theorem fullJacobian_rank_eq_of_annihilator (L : Matrix (Fin 7) EquationIndex ℂ)
    (hL : L*entryJacobianBlock=0) (hrank : (L*cubicJacobianBlock).rank=7) :
    fullJacobian.rank=1922 := by
  have h := Matrix.rank_submatrix_le fullJacobian id fixedSexticColumn
  change fixedSexticJacobian.rank≤fullJacobian.rank at h
  rw [fixedSextic_rank_eq_of_annihilator L hL hrank] at h
  exact le_antisymm fullJacobian_rank_upper_bound h

end CycleQ2SegreCubicAnnihilator

#print axioms CycleQ2SegreCubicAnnihilator.fixedSextic_rank_eq_of_annihilator
#print axioms CycleQ2SegreCubicAnnihilator.fullJacobian_rank_eq_of_annihilator
end
end

/- Component: continuation_3/SegreJacobianRankTransfer.lean -/
section
/-! # Rank transfer for the literal fixed-sextic incidence Jacobian

The integral matrix is the already defined Gaussian incidence Jacobian,
restricted to exactly the cubic and matrix-entry parameters.  The modular
and complex sides are identified by the proved coefficient naturality.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreJacobianRankTransfer

open Matrix CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceJacobianNaturality CycleQ2IncidenceGaussianArithmetic
  CycleQ2SegreFullJacobianBounds

def modularFixedSexticJacobian : Matrix EquationIndex FixedSexticParameters F109 :=
  (linearizedMatrix (57:F109) 33).submatrix id fixedSexticColumn

/-- The exact modular fixed-sextic rank is bounded by the rank of the
same literal matrix over the complex numbers. -/
theorem fixedSextic_rank_transfer :
    modularFixedSexticJacobian.rank ≤ fixedSexticJacobian.rank := by
  have h := CycleQ2ArithmeticRankTransfer.gaussian_rank_transfer
    (integralJacobian.submatrix id fixedSexticColumn)
  change ((integralJacobian.map reduction).submatrix id fixedSexticColumn).rank ≤
    ((integralJacobian.map GaussianInt.toComplex).submatrix id fixedSexticColumn).rank at h
  rw [integralJacobian_modular,integralJacobian_complex] at h
  exact h

theorem fullJacobian_rank_transfer :
    (linearizedMatrix (57:F109) 33).rank ≤ fullJacobian.rank := by
  have h := CycleQ2ArithmeticRankTransfer.gaussian_rank_transfer integralJacobian
  rw [integralJacobian_modular,integralJacobian_complex] at h
  exact h

end CycleQ2SegreJacobianRankTransfer

#print axioms CycleQ2SegreJacobianRankTransfer.fixedSextic_rank_transfer
#print axioms CycleQ2SegreJacobianRankTransfer.fullJacobian_rank_transfer
end
end

/- Component: continuation_3/SegreTangentProjectionSpace.lean -/
section
/-! # All45 sextic directions lift to the actual incidence tangent kernel

Equal ranks of the fixed-sextic and complete Jacobians imply equality of
their images. Thus every sextic coefficient variation admits a compensating
cubic and matrix variation. The final module supplies this rank equality
from the checked exact-rank theorems.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreTangentProjectionSpace

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidencePolynomialJacobianBinding

abbrev SexticCoefficients := FullInvariantIndex 6 → ℂ
abbrev TangentSpace := LinearMap.ker (Matrix.mulVecLin fullJacobian)

def fixedInsertion : (FixedSexticParameters → ℂ) →ₗ[ℂ] (ParameterIndex → ℂ) where
  toFun v := Sum.elim (fun e => v (Sum.inl e))
    (Sum.elim (fun _ => 0) (fun e => v (Sum.inr e)))
  map_add' _ _ := by ext j; rcases j with j | j | j <;> simp
  map_smul' _ _ := by ext j; rcases j with j | j | j <;> simp

def sexticProjection : (ParameterIndex → ℂ) →ₗ[ℂ] SexticCoefficients where
  toFun v e := v (Sum.inr (Sum.inl e))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def sexticInsertion : SexticCoefficients →ₗ[ℂ] (ParameterIndex → ℂ) where
  toFun v := Sum.elim (fun _ => 0) (Sum.elim v (fun _ => 0))
  map_add' _ _ := by ext j; rcases j with j | j | j <;> simp
  map_smul' _ _ := by ext j; rcases j with j | j | j <;> simp

theorem projection_fixedInsertion : sexticProjection.comp fixedInsertion=0 := by
  ext v e
  rfl

theorem projection_sexticInsertion :
    sexticProjection.comp sexticInsertion=LinearMap.id := by
  ext v e
  rfl

theorem sexticProjection_surjective : Function.Surjective sexticProjection := by
  intro v
  exact ⟨sexticInsertion v,rfl⟩

theorem fullJacobian_fixedInsertion (v : FixedSexticParameters → ℂ) :
    fullJacobian *ᵥ fixedInsertion v=fixedSexticJacobian *ᵥ v := by
  funext q
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
    fixedInsertion,LinearMap.coe_mk,AddHom.coe_mk,
    fixedSexticJacobian,fixedSexticColumn,Matrix.submatrix_apply,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add,id_eq]

theorem full_comp_fixedInsertion :
    (Matrix.mulVecLin fullJacobian).comp fixedInsertion=
      Matrix.mulVecLin fixedSexticJacobian := by
  ext v q
  exact congrFun (fullJacobian_fixedInsertion v) q

theorem fixed_range_eq_full_range
    (hrank : fixedSexticJacobian.rank=fullJacobian.rank) :
    LinearMap.range (Matrix.mulVecLin fixedSexticJacobian)=
      LinearMap.range (Matrix.mulVecLin fullJacobian) := by
  apply Submodule.eq_of_le_of_finrank_eq
  · rintro y ⟨v,rfl⟩
    exact ⟨fixedInsertion v,fullJacobian_fixedInsertion v⟩
  · change fixedSexticJacobian.rank=fullJacobian.rank
    exact hrank

def tangentProjection : TangentSpace →ₗ[ℂ] SexticCoefficients :=
  sexticProjection.comp (LinearMap.ker (Matrix.mulVecLin fullJacobian)).subtype

theorem tangentProjection_surjective
    (hrank : fixedSexticJacobian.rank=fullJacobian.rank) :
    Function.Surjective tangentProjection := by
  apply CycleQ2LinearKernelProjection.kernel_projection_surjective
    (Matrix.mulVecLin fullJacobian) fixedInsertion sexticProjection
    projection_fixedInsertion
  · rw [full_comp_fixedInsertion,fixed_range_eq_full_range hrank]
  · exact sexticProjection_surjective

theorem sexticCoefficients_finrank : Module.finrank ℂ SexticCoefficients=45 := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact CycleQ2IncidenceFullIndexCounts.sextic_count

/-- A nonconstructively chosen linear lift exists for all45 coefficient
directions at once, rather than a separate unbound lift for each coordinate. -/
theorem exists_linear_tangent_lift
    (hrank : fixedSexticJacobian.rank=fullJacobian.rank) :
    ∃s : SexticCoefficients →ₗ[ℂ] TangentSpace,
      tangentProjection.comp s=LinearMap.id :=
  tangentProjection.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (tangentProjection_surjective hrank))

theorem exists_cubic_matrix_compensation
    (hrank : fixedSexticJacobian.rank=fullJacobian.rank) (ζ : SexticCoefficients) :
    ∃v : ParameterIndex → ℂ,
      fullJacobian *ᵥ v=0 ∧ (∀e,v (Sum.inr (Sum.inl e))=ζ e) := by
  obtain ⟨v,hv⟩ := tangentProjection_surjective hrank ζ
  refine ⟨v.val,v.property,?_⟩
  exact fun e => congrFun hv e

/-- The same lift annihilates the Jacobian of the literal cleared9522
polynomial equations, using the checked derivative identification. -/
theorem exists_polynomial_tangent_lift
    (hrank : fixedSexticJacobian.rank=fullJacobian.rank) (ζ : SexticCoefficients) :
    ∃v : ParameterIndex → ℂ,
      seedJacobian ℂ 57 Complex.I *ᵥ v=0 ∧
        (∀e,v (Sum.inr (Sum.inl e))=ζ e) := by
  obtain ⟨v,hv,hζ⟩ := exists_cubic_matrix_compensation hrank ζ
  refine ⟨v,?_,hζ⟩
  funext q
  have h := congrFun hv (columnEquiv q)
  simpa only [Matrix.mulVec,dotProduct,seedJacobian_eq_linearizedMatrix,
    fullJacobian,Pi.zero_apply] using h

end CycleQ2SegreTangentProjectionSpace

#print axioms CycleQ2SegreTangentProjectionSpace.tangentProjection_surjective
#print axioms CycleQ2SegreTangentProjectionSpace.exists_polynomial_tangent_lift
end
end
