import Proposal.GeometricSurfaceBindings
import Proposal.SolutionSupport06Part01

/-! Components extracted from SolutionSupport06.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

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


/- Component: continuation_3/cylinder_bridge/IncidenceSexticFamily.lean -/
section
/-! The actual incidence presentation over independent sextic coefficients.
The already chosen complex polynomial presentation is coefficient-mapped,
so no naturality of a nonconstructively chosen denominator presentation is
assumed.  Affine directions change precisely cubic and matrix parameters. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceSexticFamily
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice

abbrev FamilyRing := MvPolynomial (FullInvariantIndex 6) ℂ

def familyEval : FamilyRing →+* ℂ := eval (seedSexticCoefficients (57:ℂ) Complex.I)

def centre : ParameterIndex → FamilyRing :=
  coefficientPoint (fun i => C (seedCubicCoefficients Complex.I i)) X (fun _ _ _ => 0)

def familyEquations (q : ColumnIndex) : MvPolynomial ParameterIndex FamilyRing :=
  MvPolynomial.map C ((presentation ℂ 57).equation q)

def familyRelations : Matrix RelationIndex ColumnIndex (MvPolynomial ParameterIndex FamilyRing) :=
  ((presentation ℂ 57).relation).map (MvPolynomial.map C)

def familyOpen : MvPolynomial ParameterIndex FamilyRing :=
  MvPolynomial.map C (leadingProduct ℂ)

theorem familyEval_comp_C : familyEval.comp (C : ℂ →+* FamilyRing)=RingHom.id ℂ := by
  ext z
  simp only [RingHom.comp_apply,familyEval,eval_C,RingHom.id_apply]

theorem centre_seed : familyEval ∘ centre=seedPoint (57:ℂ) Complex.I := by
  funext j
  rcases j with j | j
  · simp [centre,familyEval,seedPoint,coefficientPoint]
  · rcases j with j | j
    · simp [centre,familyEval,seedPoint,coefficientPoint]
    · simp [centre,familyEval,seedPoint,coefficientPoint]

theorem eval_familyMap (p : ParameterPolynomial ℂ) :
    eval₂Hom familyEval (familyEval ∘ centre) (MvPolynomial.map C p) =
      eval (seedPoint (57:ℂ) Complex.I) p := by
  rw [eval₂Hom_map_hom,familyEval_comp_C,centre_seed]
  rfl

theorem family_relation_identity : familyRelations *ᵥ familyEquations=0 := by
  have h := (presentation ℂ 57).relation_identity
  funext k
  have hk := congrArg (MvPolynomial.map (C : ℂ →+* FamilyRing)) (congrFun h k)
  simpa only [familyRelations,familyEquations,Matrix.mulVec,dotProduct,Matrix.map_apply,
    map_sum,map_mul,Pi.zero_apply,map_zero] using hk

theorem family_seed_zero (q : ColumnIndex) :
    eval₂Hom familyEval (familyEval ∘ centre) (familyEquations q)=0 := by
  rw [familyEquations,eval_familyMap]
  exact seed_equations_zero ℂ (57:ℂ) Complex.I q

theorem family_seed_relation : familyRelations.map
    (eval₂Hom familyEval (familyEval ∘ centre)) = seedRelationMatrix ℂ (57:ℂ) Complex.I := by
  funext k q
  change eval₂Hom familyEval (familyEval ∘ centre)
    (MvPolynomial.map C ((presentation ℂ 57).relation k q)) = _
  rw [eval_familyMap]
  rfl

theorem family_seed_jacobian :
    jacobian familyEval (familyEval ∘ centre) familyEquations =
      seedJacobian ℂ (57:ℂ) Complex.I := by
  funext q j
  change eval₂Hom familyEval (familyEval ∘ centre)
    (pderiv j (MvPolynomial.map C ((presentation ℂ 57).equation q))) = _
  rw [pderiv_map,eval_familyMap]
  rfl

theorem family_seed_open : eval₂Hom familyEval (familyEval ∘ centre) familyOpen=1 := by
  rw [familyOpen,eval_familyMap]
  change polynomialSpecialization (seedCubicCoefficients Complex.I)
    (seedSexticCoefficients (57:ℂ) Complex.I) (fun _ _ _ => 0) (leadingProduct ℂ)=1
  rw [polynomialSpecialization_leadingProduct]
  simp only [seedCubicCoefficients,seedSexticCoefficients,fullCubicLeadingIndex_exponent,
    fullSexticLeadingIndex_exponent,smoothH_leading_coefficient,smoothF_leading_coefficient,
    one_mul]

variable {ι : Type*}

def extendDirections (B : Matrix FixedSexticParameters ι ℂ) : Matrix ParameterIndex ι ℂ :=
  fun j i => Sum.elim (fun h => B (Sum.inl h) i)
    (Sum.elim (fun _ => 0) (fun δ => B (Sum.inr δ) i)) j

def familyDirections (B : Matrix FixedSexticParameters ι ℂ) : Matrix ParameterIndex ι FamilyRing :=
  (extendDirections B).map C

theorem familyDirections_seed (B : Matrix FixedSexticParameters ι ℂ) :
    (familyDirections B).map familyEval=extendDirections B := by
  funext j i
  simp only [familyDirections,Matrix.map_apply,familyEval,eval_C]

theorem jacobian_extendDirections [Fintype ι]
    (J : Matrix ColumnIndex ParameterIndex ℂ) (B : Matrix FixedSexticParameters ι ℂ) :
    J * extendDirections B=J.submatrix id fixedSexticColumn * B := by
  funext q i
  simp only [Matrix.mul_apply,Fintype.sum_sum_type,extendDirections,Sum.elim_inl,Sum.elim_inr,
    mul_zero,Finset.sum_const_zero,zero_add,Matrix.submatrix_apply,fixedSexticColumn,id_eq]

theorem sextic_coordinate_fixed {S : Type*} [CommRing S] [Algebra FamilyRing S]
    [Fintype ι] (B : Matrix FixedSexticParameters ι ℂ) (x : ι → S)
    (j : FullInvariantIndex 6) :
    pointValue (algebraMap FamilyRing S) centre (familyDirections B) x (Sum.inr (Sum.inl j)) =
      algebraMap FamilyRing S (X j) := by
  rw [pointValue_of_zero_row (algebraMap FamilyRing S) centre (familyDirections B) x
    (Sum.inr (Sum.inl j)) (by intro i; exact map_zero C)]
  rfl

end CycleQ2IncidenceSexticFamily

#print axioms CycleQ2IncidenceSexticFamily.family_relation_identity
#print axioms CycleQ2IncidenceSexticFamily.family_seed_jacobian
#print axioms CycleQ2IncidenceSexticFamily.family_seed_open
#print axioms CycleQ2IncidenceSexticFamily.sextic_coordinate_fixed
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


/- Component: continuation_3/cylinder_bridge/IncidenceCompatibleGenericPoint.lean -/
section
/-! The literal fixed-sextic incidence sequence is the only remaining
finite linear input to the actual generic family point.  All polynomial
relations, seed values, affine coordinate compatibility, and fixed sextic
coordinates are discharged here. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceCompatibleGenericPoint
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2IncidenceJacobianNaturality
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2CompatibleEquationCoordinates CycleQ2CompatibleAffineGenericLifting
  CycleQ2IncidenceSexticFamily

def fixedJacobian : Matrix ColumnIndex FixedSexticParameters ℂ :=
  (seedJacobian ℂ (57:ℂ) Complex.I).submatrix id fixedSexticColumn

def literalRelations : Matrix RelationIndex ColumnIndex ℂ :=
  seedRelationMatrix ℂ (57:ℂ) Complex.I

theorem fixedJacobian_eq_ordered : fixedJacobian=
    fixedSexticJacobian.submatrix columnEquiv (Equiv.refl _) := by
  funext q j
  exact seedJacobian_eq_linearizedMatrix (57:ℂ) Complex.I q (fixedSexticColumn j)

theorem literalRelations_eq : literalRelations=seedCoefficientRelations (57:ℂ) Complex.I :=
  seedRelationMatrix_eq_coefficientRelations (57:ℂ) Complex.I

abbrev SquareIndex := Fin fixedJacobian.rank
abbrev ComplementIndex := Fin literalRelations.rank
abbrev GenericField := FractionRing FamilyRing

abbrev GenericFamilyAlgebra
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (V : Matrix ColumnIndex ComplementIndex ℂ)
    (T₀ : Matrix ComplementIndex RelationIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) :=
  GenericAlgebra GenericField centre (familyDirections B) (P.map C)
    (T₀.map C) familyRelations (V.map C) familyEquations familyOpen

theorem constantMatrix_seed {α β : Type*} (M : Matrix α β ℂ) :
    (M.map (C : ℂ →+* FamilyRing)).map familyEval=M := by
  funext i j
  simp only [Matrix.map_apply,familyEval,eval_C]

def IsFamilyPoint {S : Type*} [CommRing S] [Algebra FamilyRing S]
    (y : ParameterIndex → S) : Prop :=
  (∀ q, aeval y (familyEquations q)=0) ∧ IsUnit (aeval y familyOpen) ∧
    (∀ q : FullInvariantIndex 6,
      y (Sum.inr (Sum.inl q))=algebraMap FamilyRing S (X q : FamilyRing))

/-- An actual finite separable point over the field of independent sextic
coefficients.  The hypothesis is exactly the literal fixed-sextic linear
exactness, not an independent polynomial lifting or minor assumption. -/
theorem finite_generic_point_of_exactness
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations)) :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericFamilyAlgebra P V T₀ B)),
      I.IsMaximal ∧
      Module.Finite GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      Algebra.IsSeparable GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      ∃ y : ParameterIndex → ((GenericFamilyAlgebra P V T₀ B) ⧸ I),
        IsFamilyPoint y := by
  obtain ⟨P,Q,V,W,T₀,B,hdecomp,hjac,hcomplement,_,_⟩ :=
    CycleQ2LinearExactSequenceSplit.exists_matrix_split fixedJacobian literalRelations hexact
  letI : Algebra FamilyRing ℂ := familyEval.toAlgebra
  have hjac' : (P.map C).map familyEval *
      jacobian familyEval (familyEval ∘ centre) familyEquations *
      (familyDirections B).map familyEval=1 := by
    rw [constantMatrix_seed,family_seed_jacobian,familyDirections_seed,
      Matrix.mul_assoc,jacobian_extendDirections,← Matrix.mul_assoc]
    exact hjac
  have hcomplement' : (T₀.map C).map familyEval *
      familyRelations.map (eval₂Hom familyEval (familyEval ∘ centre)) *
      (V.map C).map familyEval=1 := by
    rw [constantMatrix_seed,constantMatrix_seed,family_seed_relation]
    exact hcomplement
  have hc : IsUnit (eval₂Hom familyEval (familyEval ∘ centre) familyOpen) := by
    rw [family_seed_open]
    exact isUnit_one
  obtain ⟨I,hI,hfinite,hseparable,x,he,hopen⟩ :=
    lift_all_on_compatible_affine_slice (T := ℂ) (K := GenericField)
      centre (familyDirections B) (P.map C) (Q.map C) (V.map C) (W.map C)
      (T₀.map C) familyRelations familyEquations familyOpen
      (mapped_decomposition C P Q V W hdecomp) family_relation_identity
      family_seed_zero hjac' hcomplement' hc
      (IsFractionRing.injective FamilyRing GenericField)
  refine ⟨P,V,T₀,B,I,hI,hfinite,hseparable,
    pointValue (algebraMap FamilyRing _) centre (familyDirections B) x,he,hopen,?_⟩
  intro q
  exact sextic_coordinate_fixed B x q

end CycleQ2IncidenceCompatibleGenericPoint

#print axioms CycleQ2IncidenceCompatibleGenericPoint.fixedJacobian_eq_ordered
#print axioms CycleQ2IncidenceCompatibleGenericPoint.finite_generic_point_of_exactness
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceGenericPointSemantics.lean -/
section
/-! Vanishing of the literal coefficient-mapped equations, on their proved
leading-coefficient open, is exactly the original cofactor incidence. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceGenericPointSemantics
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidencePolynomialRelations CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidenceSexticFamily

variable {S : Type*} [CommRing S]


def pointMatrix (y : ParameterIndex → S) : Fin 3 → Fin 3 → StandardIndex 14 → S :=
  fun i j q => y (Sum.inr (Sum.inr ((i,j),q)))

theorem coefficientPoint_components (y : ParameterIndex → S) :
    coefficientPoint (pointCubic y) (pointSextic y) (pointMatrix y)=y := by
  funext j
  rcases j with j | j
  · rfl
  · rcases j with j | j <;> rfl

variable [Algebra FamilyRing S]

def genericSextic : FullInvariantIndex 6 → S := fun q => algebraMap FamilyRing S (X q)

theorem eval_familyOpen (y : ParameterIndex → S) :
    aeval y familyOpen = pointCubic y fullCubicLeadingIndex *
      pointSextic y fullSexticLeadingIndex := by
  simp only [familyOpen,leadingProduct,map_mul,map_X,aeval_X,pointCubic,pointSextic]

theorem point_leading_units (y : ParameterIndex → S) (hu : IsUnit (aeval y familyOpen)) :
    IsUnit (pointCubic y fullCubicLeadingIndex) ∧
      IsUnit (pointSextic y fullSexticLeadingIndex) := by
  rw [eval_familyOpen] at hu
  exact ⟨isUnit_of_mul_isUnit_left hu,isUnit_of_mul_isUnit_right hu⟩

/-- This conclusion uses the actual incidence matrix and the actual
homogeneous cubic/sextic ideal, not just the cleared polynomial system. -/
theorem point_satisfies_incidence [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y (familyEquations q)=0)
    (hu : IsUnit (aeval y familyOpen)) :
    ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (57:S) (pointMatrix y)) i j ∈
      equationsIdeal (fullInvariantPolynomial 3 (pointCubic y))
        (fullInvariantPolynomial 6 (pointSextic y)) := by
  letI : Algebra ℂ S := ((algebraMap FamilyRing S).comp (C : ℂ →+* FamilyRing)).toAlgebra
  have he' (q : ColumnIndex) : polynomialSpecialization (pointCubic y) (pointSextic y)
      (pointMatrix y) ((presentation ℂ 57).equation q)=0 := by
    have hq := he q
    change eval₂Hom (algebraMap FamilyRing S) y
      (MvPolynomial.map C ((presentation ℂ 57).equation q))=0 at hq
    rw [eval₂Hom_map_hom] at hq
    change eval₂Hom ((algebraMap FamilyRing S).comp C)
      (coefficientPoint (pointCubic y) (pointSextic y) (pointMatrix y))
      ((presentation ℂ 57).equation q)=0
    rw [coefficientPoint_components]
    exact hq
  obtain ⟨hc,hF⟩ := point_leading_units y hu
  have hi := (equations_zero_iff (pointCubic y) (pointSextic y) hc hF (pointMatrix y)
    (57:ℂ)).mp he'
  simpa only [map_ofNat] using hi

theorem point_satisfies_generic_incidence [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y (familyEquations q)=0)
    (hu : IsUnit (aeval y familyOpen))
    (hF : ∀ q, y (Sum.inr (Sum.inl q))=algebraMap FamilyRing S (X q)) :
    ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (57:S) (pointMatrix y)) i j ∈
      equationsIdeal (fullInvariantPolynomial 3 (pointCubic y))
        (fullInvariantPolynomial 6 (genericSextic (S := S))) := by
  have hcoeff : pointSextic y=genericSextic (S := S) := funext hF
  simpa only [hcoeff] using point_satisfies_incidence y he hu

end CycleQ2IncidenceGenericPointSemantics

#print axioms CycleQ2IncidenceGenericPointSemantics.point_satisfies_incidence
#print axioms CycleQ2IncidenceGenericPointSemantics.point_satisfies_generic_incidence
end
end


/- Component: continuation_3/IncidenceTraceRow.lean -/
section
/-! The unscaled two-coefficient seed trace is an integral Gaussian row.
Appending this row to the literal fixed-sextic Jacobian gives a second
rank-transfer statement, without lifting a modular kernel vector. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceTraceRow
open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceGaussianArithmetic
  CycleQ2SegreFullJacobianBounds CycleQ2SegreJacobianRankTransfer
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2MatrixTraceAugment

def traceRow {R : Type*} [CommRing R] (i : R) : FixedSexticParameters → R := by
  classical
  exact Pi.single (Sum.inl (cubicIndex 1)) i+
    Pi.single (Sum.inl (cubicIndex 8)) (-(1+i))

theorem traceRow_formula {R : Type*} [CommRing R] (i : R)
    (v : FixedSexticParameters → R) :
    rowLinear (traceRow i) v=i*v (Sum.inl (cubicIndex 1))-
      (1+i)*v (Sum.inl (cubicIndex 8)) := by
  classical
  change traceRow i ⬝ᵥ v=_
  simp only [traceRow,add_dotProduct,single_dotProduct]
  ring

theorem traceRow_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (i : R) : φ ∘ traceRow i=traceRow (φ i) := by
  classical
  funext j
  simp only [Function.comp_apply,traceRow,Pi.add_apply,Pi.single_apply,map_add]
  split_ifs <;> simp only [map_zero,map_neg,map_add,map_one]

def integralAugmented : Matrix (EquationIndex ⊕ Unit) FixedSexticParameters GaussianInt :=
  augment (integralJacobian.submatrix id fixedSexticColumn) (traceRow gaussianI)

theorem integralAugmented_modular :
    integralAugmented.map reduction=
      augment modularFixedSexticJacobian (traceRow (33:F109)) := by
  rw [integralAugmented,augment_map,traceRow_map,reduction_I]
  change augment ((integralJacobian.map reduction).submatrix id fixedSexticColumn) _=_
  rw [integralJacobian_modular]
  rfl

theorem integralAugmented_complex :
    integralAugmented.map GaussianInt.toComplex=
      augment fixedSexticJacobian (traceRow Complex.I) := by
  rw [integralAugmented,augment_map,traceRow_map,complex_I]
  change augment ((integralJacobian.map GaussianInt.toComplex).submatrix id fixedSexticColumn) _=_
  rw [integralJacobian_complex]
  rfl

theorem augmented_rank_transfer :
    (augment modularFixedSexticJacobian (traceRow (33:F109))).rank≤
      (augment fixedSexticJacobian (traceRow Complex.I)).rank := by
  have h := CycleQ2ArithmeticRankTransfer.gaussian_rank_transfer integralAugmented
  rwa [integralAugmented_modular,integralAugmented_complex] at h

end CycleQ2IncidenceTraceRow

#print axioms CycleQ2IncidenceTraceRow.augmented_rank_transfer
end
end


/- Component: continuation_3/SegreModularRankCertificate.lean -/
section
/-! # The literal fixed-sextic modular Jacobian has rank at least1922

The structural entry-block bound and seven checked coefficient functionals
are combined on the actual columns. The nine selected cubic exponents need
no assumed enumeration or ordering property.
-/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularRankCertificate

open Matrix CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGaussianArithmetic CycleQ2SegreFullJacobianBounds
  CycleQ2SegreJacobianRankTransfer CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2SegreModularDetectorCertificate

theorem cubic_detected_rank : (L*selectedCubicBlock).rank=7 := by
  have h := Matrix.rank_mul_le_left (L*selectedCubicBlock) rightInverse
  rw [cubic_right_inverse,Matrix.rank_one,Fintype.card_fin] at h
  exact le_antisymm (by simpa using Matrix.rank_le_card_height (L*selectedCubicBlock)) h

/-- The complete lower bound for the literal9522-by2160 fixed-sextic
Jacobian. Every arithmetic and structural premise is discharged. -/
theorem fixedSextic_rank_lower_bound : 1922≤modularFixedSexticJacobian.rank := by
  have h := CycleQ2LinearAnnihilatorRank.selected_column_rank_add_le
    modularFixedSexticJacobian
    (Sum.inr : MatrixParameter → FixedSexticParameters)
    (fun k : Fin 9 => Sum.inl (cubicIndex k)) L annihilates_entry
  change (CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock (57:F109) 33).rank+
    (L*selectedCubicBlock).rank≤modularFixedSexticJacobian.rank at h
  rw [cubic_detected_rank] at h
  have he := CycleQ2ModularGlobalFactorRank.entryJacobianBlock_rank_lower_bound
  change 1915≤(CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock (57:F109) 33).rank at he
  omega

end CycleQ2SegreModularRankCertificate

#print axioms CycleQ2SegreModularRankCertificate.cubic_detected_rank
#print axioms CycleQ2SegreModularRankCertificate.fixedSextic_rank_lower_bound
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceFiniteGenericSolution.lean -/
section
/-! The finite generic point satisfies the actual homogeneous cofactor
incidence with the generic sextic, with both leading coefficients units. -/

noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceFiniteGenericSolution
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceSexticFamily CycleQ2IncidenceCompatibleGenericPoint
  CycleQ2IncidenceGenericPointSemantics

def IsGenericIncidence {S : Type*} [CommRing S] [Algebra FamilyRing S]
    (h : FullInvariantIndex 3 → S)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → S) : Prop :=
  IsUnit (h fullCubicLeadingIndex) ∧
    IsUnit (genericSextic (S := S) fullSexticLeadingIndex) ∧
    ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (57:S) δ) i j ∈
      equationsIdeal (fullInvariantPolynomial 3 h)
        (fullInvariantPolynomial 6 (genericSextic (S := S)))

theorem generic_incidence_of_family_point {S : Type*} [CommRing S] [Nontrivial S]
    [Algebra FamilyRing S] (y : ParameterIndex → S) (hy : IsFamilyPoint y) :
    IsGenericIncidence (pointCubic y) (pointMatrix y) := by
  obtain ⟨he,hu,hF⟩ := hy
  obtain ⟨hc,hFunit⟩ := point_leading_units y hu
  have hcoeff : pointSextic y=genericSextic (S := S) := funext hF
  rw [hcoeff] at hFunit
  exact ⟨hc,hFunit,point_satisfies_generic_incidence y he hu hF⟩

theorem finite_generic_incidence_of_exactness
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations)) :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericFamilyAlgebra P V T₀ B)),
      I.IsMaximal ∧
      Module.Finite GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      Algebra.IsSeparable GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      ∃ (h : FullInvariantIndex 3 → ((GenericFamilyAlgebra P V T₀ B) ⧸ I))
        (δ : Fin 3 → Fin 3 → StandardIndex 14 → ((GenericFamilyAlgebra P V T₀ B) ⧸ I)),
        IsGenericIncidence h δ := by
  obtain ⟨P,V,T₀,B,I,hI,hfinite,hseparable,y,hy⟩ := finite_generic_point_of_exactness hexact
  letI : I.IsMaximal := hI
  letI : Field ((GenericFamilyAlgebra P V T₀ B) ⧸ I) := Ideal.Quotient.field I
  exact ⟨P,V,T₀,B,I,hI,hfinite,hseparable,pointCubic y,pointMatrix y,
    generic_incidence_of_family_point y hy⟩

end CycleQ2IncidenceFiniteGenericSolution

#print axioms CycleQ2IncidenceFiniteGenericSolution.finite_generic_incidence_of_exactness
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceImageLine.lean -/
section
/-! The actual moving incidence matrix defines a free image line at every
relevant prime on the proved basepoint open.  Its cofactor equations are
deduced from the cleared incidence equations, not assumed as a line-bundle
property.  This statement concerns the actual prime-localized matrix image;
regularity of a chosen section is a separate Cartier-divisor question. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceImageLine
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceBasepointOpen CycleQ2IncidenceGenericPointSemantics

variable {S : Type} [CommRing S] [Algebra ℂ S]


theorem pointMap_familyMatrix (y : ParameterIndex → S) :
    familyMatrix.map (MvPolynomial.map (pointMap y))=
      incidenceMatrix (57:S) (pointMatrix y) := by
  rw [familyMatrix]
  change (MvPolynomial.map (pointMap y)).mapMatrix
    (incidenceMatrix 57 rawMatrixCoefficient)=_
  rw [map_incidenceMatrix]
  simp only [map_ofNat,pointMap,rawMatrixCoefficient,AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe,aeval_X]
  rfl

theorem point_leading_units (y : ParameterIndex → S)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) :
    IsUnit (pointCubic y fullCubicLeadingIndex) ∧
      IsUnit (pointSextic y fullSexticLeadingIndex) := by
  have h : IsUnit (pointCubic y fullCubicLeadingIndex *
      pointSextic y fullSexticLeadingIndex) := by
    simpa only [leadingProduct,map_mul,aeval_X,pointCubic,pointSextic] using hu
  exact ⟨isUnit_of_mul_isUnit_left h,isUnit_of_mul_isUnit_right h⟩

theorem cofactor_memberships [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q)=0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) :
    ∀ i j, CycleQ2SegreLocal.cofactors (incidenceMatrix (57:S) (pointMatrix y)) i j∈
      equationsIdeal (map (pointMap y) familyH) (map (pointMap y) familyF) := by
  obtain ⟨hc,hF⟩ := point_leading_units y hu
  have he' (q : ColumnIndex) : polynomialSpecialization (pointCubic y) (pointSextic y)
      (pointMatrix y) ((presentation ℂ 57).equation q)=0 := by
    rw [polynomialSpecialization,coefficientPoint_components]
    exact he q
  have h := (equations_zero_iff (pointCubic y) (pointSextic y) hc hF
    (pointMatrix y) (57:ℂ)).mp he'
  simpa only [pointMap_familyH,pointMap_familyF,map_ofNat] using h

theorem curveMatrix_cofactors [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q)=0)
    (hu : IsUnit (aeval y (leadingProduct ℂ))) :
    CycleQ2SegreLocal.cofactors (curveMatrix (pointMap y))=0 := by
  have hm : curveMatrix (pointMap y)=
      (curveQuotient (pointMap y)).mapMatrix (incidenceMatrix (57:S) (pointMatrix y)) := by
    funext i j
    exact congrArg (curveQuotient (pointMap y))
      (congrArg (fun M : Matrix (Fin 3) (Fin 3) (Poly S) => M i j) (pointMap_familyMatrix y))
  rw [hm,←CycleQ2SegreTangentLocal.map_cofactors]
  funext i j
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (cofactor_memberships y he hu i j)

abbrev PointPrimeRing (y : ParameterIndex → S) (P : Ideal (PointSurface y)) [P.IsPrime] :=
  Localization.AtPrime P

def primeMatrix (y : ParameterIndex → S) (P : Ideal (PointSurface y)) [P.IsPrime] :
    Matrix (Fin 3) (Fin 3) (PointPrimeRing y P) :=
  (algebraMap (PointSurface y) (PointPrimeRing y P)).mapMatrix (curveMatrix (pointMap y))

theorem prime_image_line [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q)=0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y basepointPolynomial))
    (P : Ideal (PointSurface y)) [P.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap y) j∉P) :
    Nonempty (PointPrimeRing y P ≃ₗ[PointPrimeRing y P]
      LinearMap.range (primeMatrix y P).mulVecLin) := by
  obtain ⟨i,j,hij⟩ := specialized_prime_pivot_cover (pointMap y) hb P hx
  have hpivot : IsUnit (primeMatrix y P i j) :=
    IsLocalization.map_units (M := P.primeCompl) (PointPrimeRing y P)
      ⟨curveMatrix (pointMap y) i j,hij⟩
  have hcof := @CycleQ2SegreCech.cofactors_map_zero
    (PointSurface y) (inferInstance : CommRing (PointSurface y))
    (PointPrimeRing y P) (inferInstance : CommRing (PointPrimeRing y P))
    (algebraMap (PointSurface y) (PointPrimeRing y P))
    (curveMatrix (pointMap y)) (curveMatrix_cofactors y he hu)
  exact CycleQ2SegreImage.image_linearEquiv (primeMatrix y P) hcof i j hpivot

/-- The local line is the localization of the literal global image
submodule, rather than a separately introduced local model. -/
theorem localized_global_image_line [Nontrivial S] (y : ParameterIndex → S)
    (he : ∀ q, aeval y ((presentation ℂ 57).equation q)=0)
    (hu : IsUnit (aeval y (leadingProduct ℂ)))
    (hb : IsUnit (aeval y basepointPolynomial))
    (P : Ideal (PointSurface y)) [P.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap y) j∉P) :
    Nonempty (PointPrimeRing y P ≃ₗ[PointPrimeRing y P]
      (LinearMap.range (curveMatrix (pointMap y)).mulVecLin).localized'
        (PointPrimeRing y P) P.primeCompl
        (CycleQ2MatrixImageLocalization.vectorMap
          (R := PointSurface y) (S := PointPrimeRing y P))) := by
  obtain ⟨e⟩ := prime_image_line y he hu hb P hx
  have h := CycleQ2MatrixImageLocalization.localized_image
    (S := PointPrimeRing y P) P.primeCompl (curveMatrix (pointMap y))
  exact ⟨e.trans (LinearEquiv.ofEq _ _ h.symm)⟩

end CycleQ2IncidenceImageLine

#print axioms CycleQ2IncidenceImageLine.curveMatrix_cofactors
#print axioms CycleQ2IncidenceImageLine.prime_image_line
#print axioms CycleQ2IncidenceImageLine.localized_global_image_line
end
end


/- Component: continuation_3/SegreDetectedTangent.lean -/
section
/-! A cubic in the kernel of the seven actual detectors lifts to an
actual modular incidence tangent by dimension, without a saved correction
vector. All hypotheses below are the small detector identities. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreDetectedTangent
open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceJacobianNaturality
  CycleQ2IncidenceGaussianArithmetic CycleQ2SegreFullJacobianBounds
  CycleQ2SegreJacobianRankTransfer CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2IncidenceTraceRow CycleQ2MatrixTraceAugment
  CycleQ2IncidenceCubicCechTrace

abbrev E := CycleQ2GenericEntryCoefficientBinding.entryJacobianBlock (57:F109) 33
abbrev J := modularFixedSexticJacobian

def cubicLift (v : Fin 9 → F109) : FixedSexticParameters → F109 :=
  Sum.elim (v ∘ cubicEquiv.symm) (fun _ => 0)

def entryLift (v : MatrixParameter → F109) : FixedSexticParameters → F109 :=
  Sum.elim (fun _ => 0) v

theorem cubicLift_index (v : Fin 9 → F109) (k : Fin 9) :
    cubicLift v (Sum.inl (cubicIndex k))=v k := by
  change v (cubicEquiv.symm (cubicEquiv k))=v k
  rw [Equiv.symm_apply_apply]

theorem cubicLift_jacobian (v : Fin 9 → F109) :
    J*ᵥcubicLift v=selectedCubicBlock*ᵥv := by
  funext q
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,cubicLift,
    Sum.elim_inl,Sum.elim_inr,Function.comp_apply,mul_zero,
    Finset.sum_const_zero,add_zero]
  change (∑ e : FullInvariantIndex 3,
      J q (Sum.inl e)*v (cubicEquiv.symm e))=
    ∑ k : Fin 9,J q (Sum.inl (cubicIndex k))*v k
  rw [←Equiv.sum_comp cubicEquiv
    (fun e => J q (Sum.inl e)*v (cubicEquiv.symm e))]
  simp only [Equiv.symm_apply_apply]
  rfl

theorem entryLift_jacobian (v : MatrixParameter → F109) :
    J*ᵥentryLift v=E*ᵥv := by
  funext q
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,entryLift,
    Sum.elim_inl,Sum.elim_inr,mul_zero,Finset.sum_const_zero,zero_add]
  rfl

theorem trace_cubicLift (v : Fin 9 → F109) :
    rowLinear (traceRow (33:F109)) (cubicLift v)=33*v 1-(1+33)*v 8 := by
  rw [traceRow_formula,cubicLift_index,cubicLift_index]

theorem trace_entryLift (v : MatrixParameter → F109) :
    rowLinear (traceRow (33:F109)) (entryLift v)=0 := by
  rw [traceRow_formula]
  simp only [entryLift,Sum.elim_inl,mul_zero,sub_zero]

theorem entry_range_le :
    LinearMap.range (Matrix.mulVecLin E)≤LinearMap.range (Matrix.mulVecLin J) :=
  CycleQ2LinearAnnihilatorRank.selected_columns_range_le J
    (Sum.inr : MatrixParameter → FixedSexticParameters)

theorem cubic_range_le :
    LinearMap.range (Matrix.mulVecLin selectedCubicBlock)≤
      LinearMap.range (Matrix.mulVecLin J) :=
  CycleQ2LinearAnnihilatorRank.selected_columns_range_le J
    (fun k : Fin 9 => Sum.inl (cubicIndex k))

theorem detector_surjective_on_image (B : Matrix (Fin 9) (Fin 7) F109)
    (hB : (detectorMatrix*selectedCubicBlock)*B=1) :
    Function.Surjective ((Matrix.mulVecLin detectorMatrix).domRestrict
      (LinearMap.range (Matrix.mulVecLin J))) := by
  intro z
  let v := B*ᵥz
  refine ⟨⟨selectedCubicBlock*ᵥv,cubic_range_le ⟨v,rfl⟩⟩,?_⟩
  change detectorMatrix*ᵥ(selectedCubicBlock*ᵥ(B*ᵥz))=z
  rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]

theorem exists_modular_trace_one_of_detector
    (hE : detectorMatrix*E=0)
    (B : Matrix (Fin 9) (Fin 7) F109)
    (hB : (detectorMatrix*selectedCubicBlock)*B=1)
    (v : Fin 9 → F109) (hv : (detectorMatrix*selectedCubicBlock)*ᵥv=0)
    (ht : (33:F109)*v 1-(1+33)*v 8=1) :
    ∃ x : FixedSexticParameters → F109,
      J*ᵥx=0 ∧ rowLinear (traceRow (33:F109)) x=1 := by
  have hJ : Module.finrank F109 (LinearMap.range (Matrix.mulVecLin J))≤1915+7 :=
    fixedSextic_rank_transfer.trans fixedSexticJacobian_rank_upper_bound
  have he : 1915≤Module.finrank F109 (LinearMap.range (Matrix.mulVecLin E)) :=
    CycleQ2ModularGlobalFactorRank.entryJacobianBlock_rank_lower_bound
  have hzero : (Matrix.mulVecLin detectorMatrix).comp (Matrix.mulVecLin E)=0 := by
    rw [←Matrix.mulVecLin_mul,hE]
    ext x
    simp
  have hcv : Matrix.mulVecLin detectorMatrix (selectedCubicBlock*ᵥv)=0 := by
    change detectorMatrix*ᵥ(selectedCubicBlock*ᵥv)=0
    rwa [Matrix.mulVec_mulVec]
  obtain ⟨w,hw⟩ := CycleQ2LinearAnnihilatorKernel.exists_entry_correction
    (Matrix.mulVecLin E) (Matrix.mulVecLin J) 1915 7 (Matrix.mulVecLin detectorMatrix)
    entry_range_le hJ he hzero (detector_surjective_on_image B hB)
    (selectedCubicBlock*ᵥv) (cubic_range_le ⟨v,rfl⟩) hcv
  refine ⟨cubicLift v-entryLift w,?_,?_⟩
  · change Matrix.mulVecLin J (cubicLift v-entryLift w)=0
    rw [map_sub]
    change J*ᵥcubicLift v-J*ᵥentryLift w=0
    rw [cubicLift_jacobian,entryLift_jacobian]
    change selectedCubicBlock*ᵥv-Matrix.mulVecLin E w=0
    rw [hw,sub_self]
  · rw [map_sub,trace_cubicLift,trace_entryLift,sub_zero,ht]

end CycleQ2SegreDetectedTangent

#print axioms CycleQ2SegreDetectedTangent.exists_modular_trace_one_of_detector
end
end


/- Component: continuation_3/SegreExactRanks.lean -/
section
/-! # Exact ranks and exactness for the literal complex incidence sequence

The seven modular detectors and the independently proved modular entry rank
supply the lower bound. Faithful Gaussian specialization transfers it to the
original complex matrix. The actual relation bound supplies the opposite
inequality. All statements below concern the original maps at r=57, i=I.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreExactRanks

open Matrix CycleQ2IncidenceMonomials CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidenceJacobianNaturality CycleQ2SegreFullJacobianBounds
  CycleQ2SegreJacobianRankTransfer CycleQ2SegreCoefficientRankBinding
  CycleQ2SegreGlobalObstruction CycleQ2SegreGlobalRankSpaces

theorem fixedSexticJacobian_rank : fixedSexticJacobian.rank=1922 :=
  le_antisymm fixedSexticJacobian_rank_upper_bound
    (CycleQ2SegreModularRankCertificate.fixedSextic_rank_lower_bound.trans
      fixedSextic_rank_transfer)

theorem fullJacobian_rank : fullJacobian.rank=1922 := by
  have h := Matrix.rank_submatrix_le fullJacobian id fixedSexticColumn
  change fixedSexticJacobian.rank≤fullJacobian.rank at h
  rw [fixedSexticJacobian_rank] at h
  exact le_antisymm fullJacobian_rank_upper_bound h

theorem coefficient_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker coefficientMap)=1922 := by
  have h := Submodule.finrank_mono full_range_le_relation_kernel
  change orderedJacobian.rank≤Module.finrank ℂ (LinearMap.ker coefficientMap) at h
  rw [orderedJacobian_rank,fullJacobian_rank] at h
  exact le_antisymm coefficient_kernel_finrank_le h

theorem coefficient_rank : Module.finrank ℂ (LinearMap.range coefficientMap)=7600 := by
  have h := coefficientMap.finrank_range_add_finrank_ker
  rw [coefficient_kernel_finrank,Module.finrank_fintype_fun_eq_card,columnIndex_count] at h
  omega

/-- The original 39440-by-9522 relation matrix has rank exactly7600. -/
theorem literal_coefficient_matrix_rank :
    (seedCoefficientRelations (57:ℂ) Complex.I).rank=7600 := coefficient_rank

theorem full_range_eq_relation_kernel :
    LinearMap.range (Matrix.mulVecLin orderedJacobian)=LinearMap.ker coefficientMap := by
  apply Submodule.eq_of_le_of_finrank_eq full_range_le_relation_kernel
  change orderedJacobian.rank=Module.finrank ℂ (LinearMap.ker coefficientMap)
  rw [orderedJacobian_rank,fullJacobian_rank,coefficient_kernel_finrank]

def orderedFixedSexticJacobian :=
  fixedSexticJacobian.submatrix columnEquiv (Equiv.refl _)

theorem orderedFixedSexticJacobian_rank : orderedFixedSexticJacobian.rank=1922 := by
  rw [orderedFixedSexticJacobian,Matrix.rank_submatrix,fixedSexticJacobian_rank]

theorem fixed_range_le_relation_kernel :
    LinearMap.range (Matrix.mulVecLin orderedFixedSexticJacobian)≤
      LinearMap.ker coefficientMap :=
  (CycleQ2LinearAnnihilatorRank.selected_columns_range_le
    orderedJacobian fixedSexticColumn).trans full_range_le_relation_kernel

theorem fixed_range_eq_relation_kernel :
    LinearMap.range (Matrix.mulVecLin orderedFixedSexticJacobian)=LinearMap.ker coefficientMap := by
  apply Submodule.eq_of_le_of_finrank_eq fixed_range_le_relation_kernel
  change orderedFixedSexticJacobian.rank=Module.finrank ℂ (LinearMap.ker coefficientMap)
  rw [orderedFixedSexticJacobian_rank,coefficient_kernel_finrank]

theorem relationMap_rank : Module.finrank ℂ (LinearMap.range relationMap)=7600 := by
  have h := coefficient_rank
  rwa [coefficient_rank_eq] at h

theorem relationVariations_finrank : Module.finrank ℂ relationVariations=1922 := by
  have h := relationMap.finrank_range_add_finrank_ker
  rw [relationMap_rank,relationMap_kernel,degree28_finrank] at h
  omega

theorem relationObstruction_finrank : Module.finrank ℂ RelationObstruction=7 := by
  have h := @Submodule.finrank_quotient_add_finrank ℂ relationVariations
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance globalCofactorImage
  change Module.finrank ℂ RelationObstruction+Module.finrank ℂ globalCofactorImage=
    Module.finrank ℂ relationVariations at h
  have hi := cofactorImage_finrank_le
  rw [CycleQ2SeedGlobalFactorExact.entry_rank] at hi
  rw [relationVariations_finrank] at h
  have hu := relationObstruction_finrank_le_seven
  omega

theorem globalCofactorImage_finrank : Module.finrank ℂ globalCofactorImage=1915 := by
  have h := @Submodule.finrank_quotient_add_finrank ℂ relationVariations
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance globalCofactorImage
  change Module.finrank ℂ RelationObstruction+Module.finrank ℂ globalCofactorImage=
    Module.finrank ℂ relationVariations at h
  rw [relationObstruction_finrank,relationVariations_finrank] at h
  omega

theorem actualKernelH1_finrank :
    Module.finrank ℂ CycleQ2SegreFactorCech.ActualKernelH1=7 := by
  rw [←relationObstructionEquivKernelH1.finrank_eq,relationObstruction_finrank]

/-- The already constructed actual connecting injection is surjective as
well; this identifies the actual seven-dimensional obstruction, not an
abstract vector space of the same dimension. -/
theorem relationObstructionToH2_surjective : Function.Surjective relationObstructionToH2 := by
  letI : Module.Finite ℂ ScalarH2 :=
    Module.Finite.of_basis (CycleQ2SeedCechActualTop.actualTopBasis ℂ (57:ℂ) Complex.I)
  apply LinearMap.range_eq_top.mp
  apply Submodule.eq_top_of_finrank_eq
  rw [LinearMap.finrank_range_of_inj relationObstructionToH2_injective,
    relationObstruction_finrank]
  exact (CycleQ2SeedCechActualTop.actualTop_rank_seven ℂ (57:ℂ) Complex.I).symm

def relationObstructionEquivH2 : RelationObstruction ≃ₗ[ℂ] ScalarH2 :=
  LinearEquiv.ofBijective relationObstructionToH2
    ⟨relationObstructionToH2_injective,relationObstructionToH2_surjective⟩

/-- Compatible square Jacobian and complementary relation blocks exist
for the literal fixed-sextic incidence system. -/
theorem exists_compatible_square_blocks :
    ∃ (P : Matrix (Fin orderedFixedSexticJacobian.rank) ColumnIndex ℂ)
      (Q : Matrix ColumnIndex (Fin orderedFixedSexticJacobian.rank) ℂ)
      (V : Matrix ColumnIndex (Fin (seedCoefficientRelations (57:ℂ) Complex.I).rank) ℂ)
      (W : Matrix (Fin (seedCoefficientRelations (57:ℂ) Complex.I).rank) ColumnIndex ℂ)
      (T : Matrix (Fin (seedCoefficientRelations (57:ℂ) Complex.I).rank) RelationIndex ℂ)
      (B : Matrix FixedSexticParameters (Fin orderedFixedSexticJacobian.rank) ℂ),
      Q*P+V*W=1 ∧ P*orderedFixedSexticJacobian*B=1 ∧
      T*seedCoefficientRelations (57:ℂ) Complex.I*V=1 ∧
      seedCoefficientRelations (57:ℂ) Complex.I*Q=0 ∧ P*V=0 :=
  CycleQ2LinearExactSequenceSplit.exists_matrix_split orderedFixedSexticJacobian
    (seedCoefficientRelations (57:ℂ) Complex.I) fixed_range_eq_relation_kernel

end CycleQ2SegreExactRanks

#print axioms CycleQ2SegreExactRanks.fixedSexticJacobian_rank
#print axioms CycleQ2SegreExactRanks.full_range_eq_relation_kernel
#print axioms CycleQ2SegreExactRanks.literal_coefficient_matrix_rank
#print axioms CycleQ2SegreExactRanks.relationObstruction_finrank
#print axioms CycleQ2SegreExactRanks.relationObstructionEquivH2
#print axioms CycleQ2SegreExactRanks.exists_compatible_square_blocks
end
end


/- Component: continuation_3/SegreNonconstructiveTangent.lean -/
section
/-! A characteristic-zero trace-one tangent exists by rank transfer.
The seven checked detector rows first supply a modular tangent by dimension.
An augmented Gaussian matrix then forces a nonzero trace on the complex
kernel. Scaling and classical choice need no explicit complex correction. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreNonconstructiveTangent
open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceGaussianArithmetic CycleQ2SegreFullJacobianBounds
  CycleQ2SegreJacobianRankTransfer CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2SegreModularDetectorCertificate CycleQ2IncidenceTraceRow
  CycleQ2MatrixTraceAugment

theorem exists_modular_trace_one : ∃ x : FixedSexticParameters → F109,
    modularFixedSexticJacobian*ᵥx=0 ∧ rowLinear (traceRow (33:F109)) x=1 :=
  CycleQ2SegreDetectedTangent.exists_modular_trace_one_of_detector
    annihilates_entry rightInverse cubic_right_inverse kernelCubic
    detected_kernelCubic kernelCubic_trace

theorem modular_augmented_rank_lower_bound :
    1923≤(augment modularFixedSexticJacobian (traceRow (33:F109))).rank := by
  have h := CycleQ2LinearKernelTrace.rank_add_one_le_of_kernel_trace_one
    (Matrix.mulVecLin modularFixedSexticJacobian) (rowLinear (traceRow (33:F109)))
    exists_modular_trace_one
  rw [←augment_rank] at h
  change modularFixedSexticJacobian.rank+1≤_ at h
  have hj := CycleQ2SegreModularRankCertificate.fixedSextic_rank_lower_bound
  omega

/-- Existence of an actual complex fixed-sextic kernel direction with
unscaled trace six. No numerical kernel vector is lifted or assumed. -/
theorem exists_fixed_trace_six : ∃ x : FixedSexticParameters → ℂ,
    fixedSexticJacobian*ᵥx=0 ∧ rowLinear (traceRow Complex.I) x=6 := by
  have haug := modular_augmented_rank_lower_bound.trans augmented_rank_transfer
  have hJ := fixedSexticJacobian_rank_upper_bound
  have hlt : Module.finrank ℂ (LinearMap.range (Matrix.mulVecLin fixedSexticJacobian))<
      Module.finrank ℂ (LinearMap.range
        ((Matrix.mulVecLin fixedSexticJacobian).prod (rowLinear (traceRow Complex.I)))) := by
    rw [←augment_rank]
    change fixedSexticJacobian.rank<_
    omega
  exact CycleQ2LinearKernelTrace.exists_kernel_trace_value_of_rank_lt
    (Matrix.mulVecLin fixedSexticJacobian) (rowLinear (traceRow Complex.I)) hlt 6

theorem exists_actual_trace_one_tangent : ∃ x : FixedSexticParameters → ℂ,
    fixedSexticJacobian*ᵥx=0 ∧
      (Complex.I*x (Sum.inl (cubicIndex 1))-
        (1+Complex.I)*x (Sum.inl (cubicIndex 8)))/6=1 := by
  obtain ⟨x,hx,ht⟩ := exists_fixed_trace_six
  refine ⟨x,hx,?_⟩
  rw [traceRow_formula] at ht
  rw [ht]
  norm_num

end CycleQ2SegreNonconstructiveTangent

#print axioms CycleQ2SegreNonconstructiveTangent.exists_modular_trace_one
#print axioms CycleQ2SegreNonconstructiveTangent.exists_fixed_trace_six
#print axioms CycleQ2SegreNonconstructiveTangent.exists_actual_trace_one_tangent
end
end


/- Component: continuation_3/SegreTangentProjection.lean -/
section
/-! All45 literal sextic coefficient directions lift to the actual incidence
Jacobian kernel, with no additional hypothesis. This is a tangent statement;
no nonlinear integration is asserted here. -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreTangentProjection

open Matrix CycleQ2IncidenceUniversalChart CycleQ2SegreFullJacobianBounds
  CycleQ2IncidencePolynomialRelations CycleQ2SegreTangentProjectionSpace

private theorem ranks_equal : fixedSexticJacobian.rank=fullJacobian.rank := by
  rw [CycleQ2SegreExactRanks.fixedSexticJacobian_rank,
    CycleQ2SegreExactRanks.fullJacobian_rank]

theorem tangentProjection_surjective : Function.Surjective tangentProjection :=
  CycleQ2SegreTangentProjectionSpace.tangentProjection_surjective ranks_equal

theorem parameter_count : Fintype.card ParameterIndex=2205 := by
  norm_num [ParameterIndex,MatrixParameter,Fintype.card_sum,Fintype.card_prod,
    CycleQ2IncidenceFullIndexCounts.cubic_count,CycleQ2IncidenceFullIndexCounts.sextic_count,
    CycleQ2IncidenceMonomials.standard_degree14_count]

theorem fixedSexticParameter_count : Fintype.card FixedSexticParameters=2160 := by
  norm_num [FixedSexticParameters,MatrixParameter,Fintype.card_sum,Fintype.card_prod,
    CycleQ2IncidenceFullIndexCounts.cubic_count,
    CycleQ2IncidenceMonomials.standard_degree14_count]

theorem tangentSpace_finrank : Module.finrank ℂ TangentSpace=283 := by
  have h := (Matrix.mulVecLin fullJacobian).finrank_range_add_finrank_ker
  change fullJacobian.rank+Module.finrank ℂ TangentSpace=
    Module.finrank ℂ (ParameterIndex → ℂ) at h
  rw [CycleQ2SegreExactRanks.fullJacobian_rank,
    Module.finrank_fintype_fun_eq_card,parameter_count] at h
  omega

theorem fixedSexticTangent_finrank :
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin fixedSexticJacobian))=238 := by
  have h := (Matrix.mulVecLin fixedSexticJacobian).finrank_range_add_finrank_ker
  change fixedSexticJacobian.rank+
    Module.finrank ℂ (LinearMap.ker (Matrix.mulVecLin fixedSexticJacobian))=
      Module.finrank ℂ (FixedSexticParameters → ℂ) at h
  rw [CycleQ2SegreExactRanks.fixedSexticJacobian_rank,
    Module.finrank_fintype_fun_eq_card,fixedSexticParameter_count] at h
  omega

theorem projection_kernel_finrank :
    Module.finrank ℂ (LinearMap.ker tangentProjection)=238 := by
  have h := tangentProjection.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr tangentProjection_surjective,finrank_top,
    sexticCoefficients_finrank,tangentSpace_finrank] at h
  omega

theorem exists_linear_tangent_lift :
    ∃s : SexticCoefficients →ₗ[ℂ] TangentSpace,
      tangentProjection.comp s=LinearMap.id :=
  CycleQ2SegreTangentProjectionSpace.exists_linear_tangent_lift ranks_equal

theorem exists_cubic_matrix_compensation (ζ : SexticCoefficients) :
    ∃v : ParameterIndex → ℂ,
      fullJacobian *ᵥ v=0 ∧ (∀e,v (Sum.inr (Sum.inl e))=ζ e) :=
  CycleQ2SegreTangentProjectionSpace.exists_cubic_matrix_compensation ranks_equal ζ

theorem exists_polynomial_tangent_lift (ζ : SexticCoefficients) :
    ∃v : ParameterIndex → ℂ,
      seedJacobian ℂ 57 Complex.I *ᵥ v=0 ∧
        (∀e,v (Sum.inr (Sum.inl e))=ζ e) :=
  CycleQ2SegreTangentProjectionSpace.exists_polynomial_tangent_lift ranks_equal ζ

end CycleQ2SegreTangentProjection

#print axioms CycleQ2SegreTangentProjection.tangentProjection_surjective
#print axioms CycleQ2SegreTangentProjection.exists_polynomial_tangent_lift
#print axioms CycleQ2SegreTangentProjection.tangentSpace_finrank
#print axioms CycleQ2SegreTangentProjection.projection_kernel_finrank
end
end


