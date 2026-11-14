import Proposal.SolutionSupport05Part02

/-! Components extracted from SolutionSupport05.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SegreFactorCechSpaces.lean -/
section
/-! # The graded factor and scalar modules on the actual Čech opens -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedLocalizedProjection CycleQ2SeedCechActualTop
  CycleQ2SegreFactorChartExact CycleQ2SegreFactorGraded CycleQ2SegreFactorRestrictions

abbrev ScalarSections (s : Finset (Fin 3)) := gradedLocal ℂ (57:ℂ) Complex.I s

def factorGrades (s : Finset (Fin 3)) : Submodule ℂ (FactorSections s) where
  carrier := {V | LeftGrade s (fun i => (V.1 i:Chart s)) ∧ RightGrade s (fun j => (V.2 j:Chart s))}
  zero_mem' := ⟨fun i => hasLocalGrade_zero ℂ 57 Complex.I s (10,0),
    fun j => hasLocalGrade_zero ℂ 57 Complex.I s (8,1)⟩
  add_mem' hV hW := ⟨fun i => hasLocalGrade_add ℂ 57 Complex.I s (10,0) _ _ (hV.1 i) (hW.1 i),
    fun j => hasLocalGrade_add ℂ 57 Complex.I s (8,1) _ _ (hV.2 j) (hW.2 j)⟩
  smul_mem' c _ hV := ⟨fun i => hasLocalGrade_R_smul ℂ 57 Complex.I s (10,0) c _ (hV.1 i),
    fun j => hasLocalGrade_R_smul ℂ 57 Complex.I s (8,1) c _ (hV.2 j)⟩

abbrev GradedFactors (s : Finset (Fin 3)) := factorGrades s

def gradedFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    GradedFactors s →ₗ[ℂ] Matrix (Fin 3) (Fin 3) (Chart s) :=
  ((chartFactorMap s hs).restrictScalars ℂ).comp (factorGrades s).subtype

def gradedGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ScalarSections s →ₗ[ℂ] GradedFactors s :=
  (((chartGaugeMap s hs).restrictScalars ℂ).comp (ScalarSections s).subtype).codRestrict _
    (fun c => gaugeMap_grade s hs c.val c.property)

def gradedFactorRestriction {s t : Finset (Fin 3)} (hst : s⊆t) :
    GradedFactors s →ₗ[ℂ] GradedFactors t :=
  ((factorRestriction hst).comp (factorGrades s).subtype).codRestrict _
    (fun V => factorRestriction_grade hst V.val V.property.1 V.property.2)

theorem gradedFactorMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty) (V : GradedFactors s) :
    MatrixGrade s (gradedFactorMap s hs V) :=
  chartFactorMap_grade s hs V.val V.property.1 V.property.2

theorem gradedFactorMap_kernel (s : Finset (Fin 3)) (hs : s.Nonempty) (V : GradedFactors s) :
    cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) (gradedFactorMap s hs V)=0 := by
  have hh : chartFactorMap s hs V.val ∈ LinearMap.range (chartFactorMap s hs) := ⟨V.val,rfl⟩
  rw [(actual_factor_sequence s hs).2.2] at hh
  exact hh

theorem gradedGaugeMap_injective (s : Finset (Fin 3)) (hs : s.Nonempty) :
    Function.Injective (gradedGaugeMap s hs) := by
  intro c d h
  apply Subtype.ext
  apply (actual_factor_sequence s hs).1
  exact congrArg (fun V : GradedFactors s => V.val) h

theorem gradedFactorMap_gaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) (c : ScalarSections s) :
    gradedFactorMap s hs (gradedGaugeMap s hs c)=0 :=
  CycleQ2SegreFactorSequence.factorMap_gaugeMap (factorData s hs) c.val

/-- Exactness at the actual graded factor module, including the degree-zero
nature of the unique scalar gauge. -/
theorem graded_zero_factor_gauge (s : Finset (Fin 3)) (hs : s.Nonempty)
    (V : GradedFactors s) (hV : gradedFactorMap s hs V=0) :
    ∃ c : ScalarSections s, gradedGaugeMap s hs c=V := by
  have hv : V.val ∈ LinearMap.ker (chartFactorMap s hs) := hV
  rw [(actual_factor_sequence s hs).2.1] at hv
  obtain ⟨c,hc⟩ := hv
  have hcg : HasLocalGrade ℂ 57 Complex.I s (0,0) c := by
    apply gauge_scalar_grade s hs c
    intro i
    have hi := congrArg (fun W : FactorSections s => (W.1 i:Chart s)) hc
    change c*leftSection s i=(V.val.1 i:Chart s) at hi
    change HasLocalGrade ℂ 57 Complex.I s (10,0) (c*leftSection s i)
    rw [hi]
    exact V.property.1 i
  refine ⟨⟨c,hcg⟩,?_⟩
  exact Subtype.ext hc

/-- Surjectivity onto the actual graded cofactor kernel. -/
theorem graded_factor_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (N : Matrix (Fin 3) (Fin 3) (Chart s))
    (hN : cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) N=0)
    (hNg : MatrixGrade s N) : ∃ V : GradedFactors s, gradedFactorMap s hs V=N := by
  obtain ⟨v,w,hv,hw,hvg,hwg,he⟩ := exists_graded_factor_lift s hs N hN hNg
  let V : GradedFactors s := ⟨(fun i => ⟨v i,hv i⟩,fun j => ⟨w j,hw j⟩),hvg,hwg⟩
  refine ⟨V,?_⟩
  funext i j
  apply linkage_regular s
  calc
    linkage s*gradedFactorMap s hs V i j=
        (V.val.1 i:Chart s)*rightSection s j+leftSection s i*(V.val.2 j:Chart s) :=
      chartFactorMap_formula s hs V.val i j
    _ = linkage s*N i j := he i j

theorem gradedFactorRestriction_comp {s t u : Finset (Fin 3)} (hst : s⊆t) (htu : t⊆u)
    (V : GradedFactors s) :
    gradedFactorRestriction htu (gradedFactorRestriction hst V)=
      gradedFactorRestriction (hst.trans htu) V := by
  apply Subtype.ext
  exact factorRestriction_comp hst htu V.val

theorem gradedFactorMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (V : GradedFactors s) :
    (res hst).mapMatrix (gradedFactorMap s hs V)=
      gradedFactorMap t ht (gradedFactorRestriction hst V) :=
  chartFactorMap_restriction hs ht hst V.val

theorem gradedGaugeMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (c : ScalarSections s) :
    gradedFactorRestriction hst (gradedGaugeMap s hs c)=
      gradedGaugeMap t ht (gradedRestriction ℂ 57 Complex.I hst c) := by
  apply Subtype.ext
  exact chartGaugeMap_restriction hs ht hst c.val

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.graded_zero_factor_gauge
#print axioms CycleQ2SegreFactorCech.graded_factor_lift
#print axioms CycleQ2SegreFactorCech.gradedFactorMap_restriction
end
end


/- Component: continuation_3/cylinder_bridge/SegreSeedLinkageDuality.lean -/
section
/-! The actual smooth seed factor ideals, their duality, and the actual
matrix image.  All regular-linkage and unit-ideal hypotheses are supplied
by the checked coordinate-chart construction.  The displayed grading is
the shift underlying I_left^∨(4) and I_right(8). -/

noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreSeedLinkageDuality
open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SeedLocalizedProjection CycleQ2SeedFactorHomogeneous
  CycleQ2SegreFactorSequence CycleQ2SegreFactorChartExact
  CycleQ2SegreFactorGraded CycleQ2SegreFactorRestrictions
  CycleQ2SegreLinkageDuality CycleQ2SegreLinkageImage

def actualDuality (s : Finset (Fin 3)) (hs : s.Nonempty) :=
  rightEquivLeftDual (factorData s hs)

def actualImage (s : Finset (Fin 3)) (hs : s.Nonempty) :
    rightIdeal s ≃ₗ[Chart s]
      LinearMap.range (CycleQ2SegreComplexChartExact.chartMatrix s).mulVecLin :=
  rightEquivImage (factorData s hs)

theorem actualDuality_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (x : leftIdeal s) (y : rightIdeal s) :
    linkage s*actualDuality s hs y x=(x:Chart s)*(y:Chart s) :=
  linkage_pair (factorData s hs) x y

theorem actualImage_formula (s : Finset (Fin 3)) (hs : s.Nonempty)
    (y : rightIdeal s) (i : Fin 3) :
    linkage s*(actualImage s hs y).val i=leftSection s i*(y:Chart s) :=
  linkage_pair (factorData s hs) (leftElement (factorData s hs) i) y

theorem actualImage_selected (s : Finset (Fin 3)) (hs : s.Nonempty) (j : Fin 3) :
    (actualImage s hs (rightElement (factorData s hs) j)).val=
      (CycleQ2SegreComplexChartExact.chartMatrix s).col j :=
  rightEquivImage_selected (factorData s hs) j

/-- A right section of grade (8,1) gives a dual functional of degree (4,0).
This is proved in the actual homogeneous localization, not inferred from
an ungraded module equivalence. -/
theorem actualDuality_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (y : rightIdeal s) (hy : HasLocalGrade ℂ 57 Complex.I s (8,1) (y:Chart s))
    (d : Grade) (x : leftIdeal s)
    (hx : HasLocalGrade ℂ 57 Complex.I s d (x:Chart s)) :
    HasLocalGrade ℂ 57 Complex.I s (d+(4,0)) (actualDuality s hs y x) := by
  apply regular_division_hasLocalGrade ℂ 57 Complex.I s (polynomialLinkage 57)
    (4,1) (d+(4,0)) (polynomialLinkage_homogeneous 57) (linkage_regular s)
  change HasLocalGrade ℂ 57 Complex.I s ((d+(4,0))+(4,1))
    (linkage s*actualDuality s hs y x)
  rw [actualDuality_formula s hs x y]
  have hd : (d+(4,0))+(4,1)=d+(8,1) := by
    rw [add_assoc]
    rfl
  rw [hd]
  exact hasLocalGrade_mul ℂ 57 Complex.I s d (8,1) _ _ hx hy

theorem actualImage_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (y : rightIdeal s) (hy : HasLocalGrade ℂ 57 Complex.I s (8,1) (y:Chart s))
    (i : Fin 3) :
    HasLocalGrade ℂ 57 Complex.I s (14,0) ((actualImage s hs y).val i) := by
  change HasLocalGrade ℂ 57 Complex.I s (14,0)
    (pairing (factorData s hs) y (leftElement (factorData s hs) i))
  exact actualDuality_grade s hs y hy (10,0) (leftElement (factorData s hs) i)
    (leftSection_grade s i)

def leftRestriction {s t : Finset (Fin 3)} (hst : s⊆t) (x : leftIdeal s) : leftIdeal t :=
  ⟨res hst (x:Chart s),restriction_ideal_mem .left hst _ x.property⟩

def rightRestriction {s t : Finset (Fin 3)} (hst : s⊆t) (y : rightIdeal s) : rightIdeal t :=
  ⟨res hst (y:Chart s),restriction_ideal_mem .right hst _ y.property⟩

theorem actualDuality_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t)
    (x : leftIdeal s) (y : rightIdeal s) :
    res hst (actualDuality s hs y x)=
      actualDuality t ht (rightRestriction hst y) (leftRestriction hst x) := by
  apply linkage_regular t
  calc
    linkage t*res hst (actualDuality s hs y x)=
        res hst (linkage s*actualDuality s hs y x) := by
      rw [map_mul,restriction_linkage]
    _=res hst ((x:Chart s)*(y:Chart s)) :=
      congrArg (res hst) (actualDuality_formula s hs x y)
    _=linkage t*actualDuality t ht (rightRestriction hst y) (leftRestriction hst x) := by
      rw [actualDuality_formula t ht (leftRestriction hst x) (rightRestriction hst y),map_mul]
      rfl

end CycleQ2SegreSeedLinkageDuality

#print axioms CycleQ2SegreSeedLinkageDuality.actualDuality
#print axioms CycleQ2SegreSeedLinkageDuality.actualImage
#print axioms CycleQ2SegreSeedLinkageDuality.actualDuality_grade
#print axioms CycleQ2SegreSeedLinkageDuality.actualDuality_restriction
end
end


/- Component: continuation_3/cylinder_bridge/ModularFactorCechDifferentials.lean -/
section
/-! # Actual factor and scalar differentials on the three-open cover -/

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxSize 1024
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2ModularFactorCech

open CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2SeedCechActualTop CycleQ2ModularFactorChartExact
  CycleQ2ModularFactorRestrictions

abbrev FactorPairs := GradedFactors {0,1} × GradedFactors {0,2} × GradedFactors {1,2}
abbrev ScalarPairs := ScalarSections {0,1} × ScalarSections {0,2} × ScalarSections {1,2}

instance factorPairsModule : Module F109 FactorPairs := by infer_instance

def factorD1 : FactorPairs →ₗ[F109] GradedFactors Finset.univ :=
  CycleQ2CechLinearAlgebra.signedThree
    (R:=F109) (A:=GradedFactors {0,1}) (B:=GradedFactors {0,2})
    (C:=GradedFactors {1,2}) (T:=GradedFactors Finset.univ)
    (gradedFactorRestriction (Finset.subset_univ {0,1}))
    (gradedFactorRestriction (Finset.subset_univ {0,2}))
    (gradedFactorRestriction (Finset.subset_univ {1,2}))

def scalarD1 : ScalarPairs →ₗ[F109] ScalarSections Finset.univ :=
  CycleQ2CechLinearAlgebra.signedThree
    (R:=F109) (A:=ScalarSections {0,1}) (B:=ScalarSections {0,2})
    (C:=ScalarSections {1,2}) (T:=ScalarSections Finset.univ)
    (gradedRestriction F109 57 33 (Finset.subset_univ {0,1}))
    (gradedRestriction F109 57 33 (Finset.subset_univ {0,2}))
    (gradedRestriction F109 57 33 (Finset.subset_univ {1,2}))

def pairGauge : ScalarPairs →ₗ[F109] FactorPairs :=
  (gradedGaugeMap {0,1} (by decide)).prodMap
    ((gradedGaugeMap {0,2} (by decide)).prodMap (gradedGaugeMap {1,2} (by decide)))

theorem factorD1_pairGauge (B : ScalarPairs) :
    factorD1 (pairGauge B)=gradedGaugeMap Finset.univ (by decide) (scalarD1 B) := by
  change gradedFactorRestriction _ (gradedGaugeMap {0,1} _ B.1)-
    gradedFactorRestriction _ (gradedGaugeMap {0,2} _ B.2.1)+
    gradedFactorRestriction _ (gradedGaugeMap {1,2} _ B.2.2)=_
  rw [gradedGaugeMap_restriction (by decide) (by decide),
    gradedGaugeMap_restriction (by decide) (by decide),
    gradedGaugeMap_restriction (by decide) (by decide)]
  change gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction F109 57 33 (Finset.subset_univ {0,1}) B.1)-
    gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction F109 57 33 (Finset.subset_univ {0,2}) B.2.1)+
    gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction F109 57 33 (Finset.subset_univ {1,2}) B.2.2)=_
  rw [← map_sub (gradedGaugeMap Finset.univ (by decide)),
    ← map_add (gradedGaugeMap Finset.univ (by decide))]
  rfl

/-- The signed three-term scalar differential has exactly the actual
boundary submodule used by the checked rank-seven H2 quotient. -/
theorem scalarD1_range : LinearMap.range scalarD1=actualBoundary F109 (57:F109) 33 := by
  apply le_antisymm
  · rintro c ⟨B,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨gradedRestriction F109 57 33 (Finset.subset_univ {0,1}) B.1-
      gradedRestriction F109 57 33 (Finset.subset_univ {0,2}) B.2.1,?_,
      gradedRestriction F109 57 33 (Finset.subset_univ {1,2}) B.2.2,⟨B.2.2,rfl⟩,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨gradedRestriction F109 57 33 (Finset.subset_univ {0,1}) B.1,⟨B.1,rfl⟩,
      -(gradedRestriction F109 57 33 (Finset.subset_univ {0,2}) B.2.1),?_,?_⟩
    · exact (LinearMap.range (gradedRestriction F109 57 33
        (Finset.subset_univ {0,2}))).neg_mem ⟨B.2.1,rfl⟩
    · exact (sub_eq_add_neg _ _).symm
  · intro c hc
    obtain ⟨u,hu,z,hz,huz⟩ := Submodule.mem_sup.mp hc
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hu
    obtain ⟨b01,h01⟩ := hx
    obtain ⟨b02,h02⟩ := hy
    obtain ⟨b12,h12⟩ := hz
    refine ⟨(b01,-b02,b12),?_⟩
    change gradedRestriction F109 57 33 _ b01-
      gradedRestriction F109 57 33 _ (-b02)+
      gradedRestriction F109 57 33 _ b12=c
    rw [map_neg,sub_neg_eq_add,h01,h02,h12,hxy,huz]

def factorD0 (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}) : FactorPairs :=
  (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1-
    gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0,
   gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2-
    gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0,
   gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2-
    gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)

theorem factorD1_factorD0 (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2}) : factorD1 (factorD0 F0 F1 F2)=0 := by
  change gradedFactorRestriction (Finset.subset_univ {0,1})
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1-
       gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0)-
    gradedFactorRestriction (Finset.subset_univ {0,2})
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2-
       gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0)+
    gradedFactorRestriction (Finset.subset_univ {1,2})
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2-
       gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)=0
  have hd01 := map_sub (gradedFactorRestriction (Finset.subset_univ {0,1}))
    (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1)
    (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0)
  have hd02 := map_sub (gradedFactorRestriction (Finset.subset_univ {0,2}))
    (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2)
    (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0)
  have hd12 := map_sub (gradedFactorRestriction (Finset.subset_univ {1,2}))
    (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2)
    (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)
  have h10 := gradedFactorRestriction_comp
    (by decide : ({1}:Finset (Fin 3))⊆{0,1}) (Finset.subset_univ {0,1}) F1
  have h00 := gradedFactorRestriction_comp
    (by decide : ({0}:Finset (Fin 3))⊆{0,1}) (Finset.subset_univ {0,1}) F0
  have h21 := gradedFactorRestriction_comp
    (by decide : ({2}:Finset (Fin 3))⊆{0,2}) (Finset.subset_univ {0,2}) F2
  have h01 := gradedFactorRestriction_comp
    (by decide : ({0}:Finset (Fin 3))⊆{0,2}) (Finset.subset_univ {0,2}) F0
  have h22 := gradedFactorRestriction_comp
    (by decide : ({2}:Finset (Fin 3))⊆{1,2}) (Finset.subset_univ {1,2}) F2
  have h12 := gradedFactorRestriction_comp
    (by decide : ({1}:Finset (Fin 3))⊆{1,2}) (Finset.subset_univ {1,2}) F1
  calc
    _ = (gradedFactorRestriction (Finset.subset_univ {0,1})
          (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1)-
        gradedFactorRestriction (Finset.subset_univ {0,1})
          (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0))-
      (gradedFactorRestriction (Finset.subset_univ {0,2})
          (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2)-
        gradedFactorRestriction (Finset.subset_univ {0,2})
          (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0))+
      (gradedFactorRestriction (Finset.subset_univ {1,2})
          (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2)-
        gradedFactorRestriction (Finset.subset_univ {1,2})
          (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)) :=
      congrArg₂ (fun x y : GradedFactors Finset.univ => x+y)
        (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) hd01 hd02) hd12
    _ = (gradedFactorRestriction (Finset.subset_univ {1}) F1-
          gradedFactorRestriction (Finset.subset_univ {0}) F0)-
        (gradedFactorRestriction (Finset.subset_univ {2}) F2-
          gradedFactorRestriction (Finset.subset_univ {0}) F0)+
        (gradedFactorRestriction (Finset.subset_univ {2}) F2-
          gradedFactorRestriction (Finset.subset_univ {1}) F1) :=
      congrArg₂ (fun x y : GradedFactors Finset.univ => x+y)
        (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y)
          (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h10 h00)
          (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h21 h01))
        (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h22 h12)
    _ = 0 := by abel

end CycleQ2ModularFactorCech

#print axioms CycleQ2ModularFactorCech.scalarD1_range
#print axioms CycleQ2ModularFactorCech.factorD1_factorD0
end
end


/- Component: continuation_3/SeedLinkageCechVanishing.lean -/
section
/-! # Positive graded Čech vanishing for the two actual linkage ideals

The proof uses the actual seed H1 contraction, the actual curve restriction,
curve H0 gluing, and the checked characteristic-zero restriction surjectivity.
The orbit ideal is identified with the chosen component only for genuinely
homogeneous localized sections, using the separately checked cyclic action.
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageCechVanishing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLinkageComponents

abbrev Local (t : Finset (Fin 3)) := SeedLocal ℂ (57:ℂ) Complex.I t
abbrev Seed := SeedRing (57:ℂ) Complex.I

def localGrade (t : Finset (Fin 3)) (g : LaurentGrade) (q : Local t) : Prop :=
  ∀ ab,HasGrade ab g (localizedCoordinates ℂ (57:ℂ) Complex.I t q ab)

def localIdeal (side : Side) (t : Finset (Fin 3)) : Ideal (Local t) :=
  localLinkageIdeal side (57:ℂ) Complex.I t

abbrev res {s t : Finset (Fin 3)} (h : s⊆t) : Local s →+* Local t :=
  CycleQ2SeedCechRestrictions.restriction ℂ (57:ℂ) Complex.I h

abbrev restrictCurve (side : Side) (t : Finset (Fin 3)) :=
  CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ side (57:ℂ) Complex.I t

theorem mem_iff_restriction_zero (side : Side) (t : Finset (Fin 3)) (ht : t.Nonempty)
    (q : Local t) (g : LaurentGrade) (hq : localGrade t g q) :
    q∈localIdeal side t ↔ restrictCurve side t q=0 := by
  apply CycleQ2SeedLinkageRestrictionKernel.homogeneous_mem_linkage_iff_restriction_zero
    side (57:ℂ) Complex.I (by norm_num) Complex.I_ne_zero _ t ht q g hq
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

theorem polynomial_grade (d ch : ℕ) (p : Poly ℂ)
    (hp : p.IsWeightedHomogeneous fullGrading (d,(ch:ZMod 3))) (t : Finset (Fin 3)) :
    localGrade t ((d:ℤ),(ch:ZMod 3))
      (algebraMap Seed (Local t) (Ideal.Quotient.mk
        (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) p)) :=
  CycleQ2SeedQuotientGrading.localized_polynomial_homogeneous ℂ (57:ℂ) Complex.I t p
    (d,(ch:ZMod 3)) hp

theorem localGrade_sub (t : Finset (Fin 3)) (g : LaurentGrade) (q p : Local t)
    (hq : localGrade t g q) (hp : localGrade t g p) : localGrade t g (q-p) := by
  intro ab
  rw [map_sub,Pi.sub_apply]
  exact hasGrade_sub ab g (hq ab) (hp ab)

def IdealCechExact (side : Side) (d ch : ℕ) : Prop :=
  ∀ (p01 : Local {0,1}) (p02 : Local {0,2}) (p12 : Local {1,2}),
    localGrade {0,1} ((d:ℤ),(ch:ZMod 3)) p01 →
    localGrade {0,2} ((d:ℤ),(ch:ZMod 3)) p02 →
    localGrade {1,2} ((d:ℤ),(ch:ZMod 3)) p12 →
    p01∈localIdeal side {0,1} → p02∈localIdeal side {0,2} → p12∈localIdeal side {1,2} →
    res (show ({0,1}:Finset (Fin 3))⊆Finset.univ by decide) p01-
      res (show ({0,2}:Finset (Fin 3))⊆Finset.univ by decide) p02+
      res (show ({1,2}:Finset (Fin 3))⊆Finset.univ by decide) p12=0 →
    ∃ (q0 : Local {0}) (q1 : Local {1}) (q2 : Local {2}),
      localGrade {0} ((d:ℤ),(ch:ZMod 3)) q0 ∧
      localGrade {1} ((d:ℤ),(ch:ZMod 3)) q1 ∧
      localGrade {2} ((d:ℤ),(ch:ZMod 3)) q2 ∧
      q0∈localIdeal side {0} ∧ q1∈localIdeal side {1} ∧ q2∈localIdeal side {2} ∧
      p01=res (show ({1}:Finset (Fin 3))⊆{0,1} by decide) q1-
        res (show ({0}:Finset (Fin 3))⊆{0,1} by decide) q0 ∧
      p02=res (show ({2}:Finset (Fin 3))⊆{0,2} by decide) q2-
        res (show ({0}:Finset (Fin 3))⊆{0,2} by decide) q0 ∧
      p12=res (show ({2}:Finset (Fin 3))⊆{1,2} by decide) q2-
        res (show ({1}:Finset (Fin 3))⊆{1,2} by decide) q1

theorem idealCechExact_of_surjective (side : Side) (d ch : ℕ)
    (hsurj : Function.Surjective (seedRestrictionPiece side (57:ℂ) Complex.I d ch)) :
    IdealCechExact side d ch := by
  intro p01 p02 p12 hg01 hg02 hg12 hi01 hi02 hi12 hc
  obtain ⟨q0,q1,q2,hg0,hg1,hg2,he01,he02,he12⟩ :=
    CycleQ2SeedCechRestrictions.coordinateCech_exact ℂ (57:ℂ) Complex.I
      ((d:ℤ),(ch:ZMod 3)) p01 p02 p12 hg01 hg02 hg12 hc
  have hz02 := (mem_iff_restriction_zero side {0,2} (by decide) p02 _ hg02).mp hi02
  have hz12 := (mem_iff_restriction_zero side {1,2} (by decide) p12 _ hg12).mp hi12
  rw [he02,map_sub] at hz02
  rw [he12,map_sub] at hz12
  obtain ⟨P,hP,hPg,hP0,hP1,hP2⟩ := CycleQ2CurveRestrictionGluing.exists_homogeneous_gluing
    side (57:ℂ) Complex.I q0 q1 q2 ((d:ℤ),(ch:ZMod 3)) hg0
      (sub_eq_zero.mp hz02).symm (sub_eq_zero.mp hz12).symm
  have hPh : P.IsHomogeneous d :=
    (CycleQ2CurveQuotientGrading.signedHomogeneous_iff ℂ P d).mp hPg
  let c : CurvePiece side (57:ℂ) Complex.I d :=
    ⟨Ideal.Quotient.mk (curveIdeal side (57:ℂ) Complex.I) P,
      Submodule.mem_map.mpr ⟨P,hPh,rfl⟩⟩
  obtain ⟨a,ha⟩ := hsurj c
  have har : seedRestriction side (57:ℂ) Complex.I a.val=
      Ideal.Quotient.mk (curveIdeal side (57:ℂ) Complex.I) P := congrArg Subtype.val ha
  obtain ⟨A,hA,hAa⟩ := Submodule.mem_map.mp a.property
  have hag (t : Finset (Fin 3)) : localGrade t ((d:ℤ),(ch:ZMod 3))
      (algebraMap Seed (Local t) a.val) := by
    rw [←hAa]
    exact polynomial_grade d ch A hA t
  let u0 := q0-algebraMap Seed (Local {0}) a.val
  let u1 := q1-algebraMap Seed (Local {1}) a.val
  let u2 := q2-algebraMap Seed (Local {2}) a.val
  have hu0 := localGrade_sub {0} ((d:ℤ),(ch:ZMod 3)) q0 _ hg0 (hag {0})
  have hu1 := localGrade_sub {1} ((d:ℤ),(ch:ZMod 3)) q1 _ hg1 (hag {1})
  have hu2 := localGrade_sub {2} ((d:ℤ),(ch:ZMod 3)) q2 _ hg2 (hag {2})
  refine ⟨u0,u1,u2,hu0,hu1,hu2,?_,?_,?_,?_,?_,?_⟩
  · apply (mem_iff_restriction_zero side {0} (by decide) u0 _ hu0).mpr
    change restrictCurve side {0} (q0-algebraMap Seed (Local {0}) a.val)=0
    rw [map_sub,CycleQ2CurveLocalizedRestriction.localRestrictionMap_algebraMap,har]
    exact sub_eq_zero.mpr hP0.symm
  · apply (mem_iff_restriction_zero side {1} (by decide) u1 _ hu1).mpr
    change restrictCurve side {1} (q1-algebraMap Seed (Local {1}) a.val)=0
    rw [map_sub,CycleQ2CurveLocalizedRestriction.localRestrictionMap_algebraMap,har]
    exact sub_eq_zero.mpr hP1.symm
  · apply (mem_iff_restriction_zero side {2} (by decide) u2 _ hu2).mpr
    change restrictCurve side {2} (q2-algebraMap Seed (Local {2}) a.val)=0
    rw [map_sub,CycleQ2CurveLocalizedRestriction.localRestrictionMap_algebraMap,har]
    exact sub_eq_zero.mpr hP2.symm
  · dsimp only [u0,u1]
    simp only [map_sub,CycleQ2SeedCechRestrictions.restriction_algebraMap]
    rw [he01]
    abel
  · dsimp only [u0,u2]
    simp only [map_sub,CycleQ2SeedCechRestrictions.restriction_algebraMap]
    rw [he02]
    abel
  · dsimp only [u1,u2]
    simp only [map_sub,CycleQ2SeedCechRestrictions.restriction_algebraMap]
    rw [he12]
    abel

/-- The actual left degree-ten invariant factor has vanishing H1. -/
theorem left_idealCechExact : IdealCechExact .left 10 0 :=
  idealCechExact_of_surjective .left 10 0 left_restriction_surjective

/-- The actual right degree-eight character-one factor has vanishing H1. -/
theorem right_idealCechExact : IdealCechExact .right 8 1 :=
  idealCechExact_of_surjective .right 8 1 right_restriction_surjective

end CycleQ2SeedLinkageCechVanishing

#print axioms CycleQ2SeedLinkageCechVanishing.left_idealCechExact
#print axioms CycleQ2SeedLinkageCechVanishing.right_idealCechExact
end
end


/- Component: continuation_3/cylinder_bridge/SegreFactorCechDifferentials.lean -/
section
/-! # Actual factor and scalar differentials on the three-open cover -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreFactorCech

open Matrix CycleQ2SeedCechActualTop CycleQ2SegreFactorChartExact
  CycleQ2SegreFactorRestrictions

abbrev FactorPairs := GradedFactors {0,1} × GradedFactors {0,2} × GradedFactors {1,2}
abbrev ScalarPairs := ScalarSections {0,1} × ScalarSections {0,2} × ScalarSections {1,2}

def factorD1 : FactorPairs →ₗ[ℂ] GradedFactors Finset.univ :=
  CycleQ2CechLinearAlgebra.signedThree
    (R:=ℂ) (A:=GradedFactors {0,1}) (B:=GradedFactors {0,2})
    (C:=GradedFactors {1,2}) (T:=GradedFactors Finset.univ)
    (gradedFactorRestriction (Finset.subset_univ {0,1}))
    (gradedFactorRestriction (Finset.subset_univ {0,2}))
    (gradedFactorRestriction (Finset.subset_univ {1,2}))

def scalarD1 : ScalarPairs →ₗ[ℂ] ScalarSections Finset.univ :=
  CycleQ2CechLinearAlgebra.signedThree
    (R:=ℂ) (A:=ScalarSections {0,1}) (B:=ScalarSections {0,2})
    (C:=ScalarSections {1,2}) (T:=ScalarSections Finset.univ)
    (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,1}))
    (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,2}))
    (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {1,2}))

def pairGauge : ScalarPairs →ₗ[ℂ] FactorPairs :=
  (gradedGaugeMap {0,1} (by decide)).prodMap
    ((gradedGaugeMap {0,2} (by decide)).prodMap (gradedGaugeMap {1,2} (by decide)))

theorem factorD1_pairGauge (B : ScalarPairs) :
    factorD1 (pairGauge B)=gradedGaugeMap Finset.univ (by decide) (scalarD1 B) := by
  change gradedFactorRestriction _ (gradedGaugeMap {0,1} _ B.1)-
    gradedFactorRestriction _ (gradedGaugeMap {0,2} _ B.2.1)+
    gradedFactorRestriction _ (gradedGaugeMap {1,2} _ B.2.2)=_
  rw [gradedGaugeMap_restriction (by decide) (by decide),
    gradedGaugeMap_restriction (by decide) (by decide),
    gradedGaugeMap_restriction (by decide) (by decide)]
  change gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,1}) B.1)-
    gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,2}) B.2.1)+
    gradedGaugeMap Finset.univ (by decide)
      (gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {1,2}) B.2.2)=_
  rw [← map_sub (gradedGaugeMap Finset.univ (by decide)),
    ← map_add (gradedGaugeMap Finset.univ (by decide))]
  rfl

/-- The signed three-term scalar differential has exactly the actual
boundary submodule used by the checked rank-seven H2 quotient. -/
theorem scalarD1_range : LinearMap.range scalarD1=actualBoundary ℂ (57:ℂ) Complex.I := by
  apply le_antisymm
  · rintro c ⟨B,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,1}) B.1-
      gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,2}) B.2.1,?_,
      gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {1,2}) B.2.2,⟨B.2.2,rfl⟩,rfl⟩
    apply Submodule.mem_sup.mpr
    refine ⟨gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,1}) B.1,⟨B.1,rfl⟩,
      -(gradedRestriction ℂ 57 Complex.I (Finset.subset_univ {0,2}) B.2.1),?_,?_⟩
    · exact (LinearMap.range (gradedRestriction ℂ 57 Complex.I
        (Finset.subset_univ {0,2}))).neg_mem ⟨B.2.1,rfl⟩
    · exact (sub_eq_add_neg _ _).symm
  · intro c hc
    obtain ⟨u,hu,z,hz,huz⟩ := Submodule.mem_sup.mp hc
    obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hu
    obtain ⟨b01,h01⟩ := hx
    obtain ⟨b02,h02⟩ := hy
    obtain ⟨b12,h12⟩ := hz
    refine ⟨(b01,-b02,b12),?_⟩
    change gradedRestriction ℂ 57 Complex.I _ b01-
      gradedRestriction ℂ 57 Complex.I _ (-b02)+
      gradedRestriction ℂ 57 Complex.I _ b12=c
    rw [map_neg,sub_neg_eq_add,h01,h02,h12,hxy,huz]

def factorD0 (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}) : FactorPairs :=
  (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1-
    gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0,
   gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2-
    gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0,
   gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2-
    gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)

theorem factorD1_factorD0 (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2}) : factorD1 (factorD0 F0 F1 F2)=0 := by
  change gradedFactorRestriction (Finset.subset_univ {0,1})
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F1-
       gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1}) F0)-
    gradedFactorRestriction (Finset.subset_univ {0,2})
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F2-
       gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2}) F0)+
    gradedFactorRestriction (Finset.subset_univ {1,2})
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F2-
       gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2}) F1)=0
  rw [map_sub (gradedFactorRestriction (Finset.subset_univ {0,1})),
    map_sub (gradedFactorRestriction (Finset.subset_univ {0,2})),
    map_sub (gradedFactorRestriction (Finset.subset_univ {1,2}))]
  have h10 := gradedFactorRestriction_comp
    (by decide : ({1}:Finset (Fin 3))⊆{0,1}) (Finset.subset_univ {0,1}) F1
  have h00 := gradedFactorRestriction_comp
    (by decide : ({0}:Finset (Fin 3))⊆{0,1}) (Finset.subset_univ {0,1}) F0
  have h21 := gradedFactorRestriction_comp
    (by decide : ({2}:Finset (Fin 3))⊆{0,2}) (Finset.subset_univ {0,2}) F2
  have h01 := gradedFactorRestriction_comp
    (by decide : ({0}:Finset (Fin 3))⊆{0,2}) (Finset.subset_univ {0,2}) F0
  have h22 := gradedFactorRestriction_comp
    (by decide : ({2}:Finset (Fin 3))⊆{1,2}) (Finset.subset_univ {1,2}) F2
  have h12 := gradedFactorRestriction_comp
    (by decide : ({1}:Finset (Fin 3))⊆{1,2}) (Finset.subset_univ {1,2}) F1
  calc
    _ = (gradedFactorRestriction (Finset.subset_univ {1}) F1-
          gradedFactorRestriction (Finset.subset_univ {0}) F0)-
        (gradedFactorRestriction (Finset.subset_univ {2}) F2-
          gradedFactorRestriction (Finset.subset_univ {0}) F0)+
        (gradedFactorRestriction (Finset.subset_univ {2}) F2-
          gradedFactorRestriction (Finset.subset_univ {1}) F1) :=
      congrArg₂ (fun x y : GradedFactors Finset.univ => x+y)
        (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y)
          (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h10 h00)
          (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h21 h01))
        (congrArg₂ (fun x y : GradedFactors Finset.univ => x-y) h22 h12)
    _ = 0 := by abel

end CycleQ2SegreFactorCech

#print axioms CycleQ2SegreFactorCech.scalarD1_range
#print axioms CycleQ2SegreFactorCech.factorD1_factorD0
end
end


/- Component: continuation_3/cylinder_bridge/SegreGlobalObstruction.lean -/
section
/-! # The literal complex relation-kernel obstruction

The source is the relation kernel inside matrices over the actual degree-28,
character-zero seed quotient piece. The checked graded local exactness theorem
discharges local liftability. Quotienting by the literal degree-14 global
cofactor image therefore gives an injection into actual kernel Čech H1.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreGlobalObstruction

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SegreRelationsLocal
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedQuotientGrading
  CycleQ2SeedLocalizedClearing CycleQ2SeedCechGlobalGluing
  CycleQ2SegreCechConnecting CycleQ2CurveRestriction

abbrev SeedMatrix := seedQuotientMatrix (57:ℂ) Complex.I

def matrixGrades : MatrixGrades := fun _ _ => (14,0)

abbrev Degree28Matrices := Matrix (Fin 3) (Fin 3) (SeedPiece (57:ℂ) Complex.I 28 0)

def degree28ToGlobal : Degree28Matrices →ₗ[ℂ] GlobalMatrix ℂ 57 Complex.I where
  toFun C i j := (C i j).val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def relationVariations : Submodule ℂ Degree28Matrices :=
  LinearMap.ker (((relationsLinear SeedMatrix).restrictScalars ℂ).comp degree28ToGlobal)

/-- Every literal homogeneous relation vector has actual graded local lifts. -/
theorem polynomial_relation_locally_liftable
    (C : Matrix (Fin 3) (Fin 3) (Poly ℂ))
    (hC : ∀ i j, HG (C i j) (28,0))
    (hrel : CycleQ2SegreRelations.relations SeedMatrix *ᵥ
      vector (quotientMatrix ℂ 57 Complex.I C)=0) :
    quotientMatrix ℂ 57 Complex.I C ∈
      LocallyLiftableVariations ℂ 57 Complex.I SeedMatrix matrixGrades := by
  choose N hNg hN using fun i : Fin 3 =>
    CycleQ2SegreGradedChartExact.complex_graded_lift {i} (by simp) C hC hrel
  let Ng : localGraded ℂ 57 Complex.I matrixGrades := ⟨N,hNg⟩
  have hp : (quotientMatrix ℂ 57 Complex.I C,Ng) ∈
      liftPairs ℂ 57 Complex.I SeedMatrix matrixGrades := by
    intro i
    exact hN i
  exact ⟨⟨(quotientMatrix ℂ 57 Complex.I C,Ng),hp⟩,rfl⟩

theorem relation_variation_locally_liftable (C : relationVariations) :
    degree28ToGlobal C.val ∈
      LocallyLiftableVariations ℂ 57 Complex.I SeedMatrix matrixGrades := by
  choose P hP hPC using fun i j => Submodule.mem_map.mp (C.val i j).property
  have he : quotientMatrix ℂ 57 Complex.I P=degree28ToGlobal C.val := by
    funext i j
    exact hPC i j
  have hr : CycleQ2SegreRelations.relations SeedMatrix *ᵥ
      vector (quotientMatrix ℂ 57 Complex.I P)=0 := by
    rw [he]
    exact C.property
  rw [← he]
  exact polynomial_relation_locally_liftable P hP hr

def relationToLiftable : relationVariations →ₗ[ℂ]
    LocallyLiftableVariations ℂ 57 Complex.I SeedMatrix matrixGrades :=
  (degree28ToGlobal.comp relationVariations.subtype).codRestrict _
    relation_variation_locally_liftable

def relationConnecting : relationVariations →ₗ[ℂ]
    KernelCechH1 ℂ 57 Complex.I SeedMatrix matrixGrades :=
  (connectingToH1 ℂ 57 Complex.I SeedMatrix matrixGrades).comp relationToLiftable

theorem relationConnecting_zero_iff (C : relationVariations) :
    relationConnecting C=0 ↔
      ∃ P : Matrix (Fin 3) (Fin 3) (Poly ℂ),
        (∀ i j, FullStandard (P i j)) ∧
        (∀ i j, SignedHomogeneous ℂ (P i j) (14,0)) ∧
        cofactorDifferential SeedMatrix (quotientMatrix ℂ 57 Complex.I P)=degree28ToGlobal C.val :=
  connectingToH1_zero_iff ℂ 57 Complex.I SeedMatrix matrixGrades (relationToLiftable C)

def globalCofactorImage : Submodule ℂ relationVariations :=
  Submodule.span ℂ {C | ∃ P : Matrix (Fin 3) (Fin 3) (Poly ℂ),
    (∀ i j, FullStandard (P i j)) ∧
    (∀ i j, SignedHomogeneous ℂ (P i j) (14,0)) ∧
    cofactorDifferential SeedMatrix (quotientMatrix ℂ 57 Complex.I P)=degree28ToGlobal C.val}

theorem ker_relationConnecting : LinearMap.ker relationConnecting=globalCofactorImage := by
  apply le_antisymm
  · intro C hC
    exact Submodule.subset_span ((relationConnecting_zero_iff C).mp hC)
  · apply Submodule.span_le.mpr
    intro C hC
    exact (relationConnecting_zero_iff C).mpr hC

abbrev RelationObstruction :=
  @HasQuotient.Quotient relationVariations (Submodule ℂ relationVariations)
    (@Submodule.hasQuotient ℂ relationVariations inferInstance inferInstance inferInstance)
    globalCofactorImage

def relationObstructionInjection : RelationObstruction →ₗ[ℂ]
    KernelCechH1 ℂ 57 Complex.I SeedMatrix matrixGrades :=
  @CycleQ2LinearRangeDescent.kernelQuotientInjection ℂ relationVariations
    (KernelCechH1 ℂ 57 Complex.I SeedMatrix matrixGrades)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    relationConnecting globalCofactorImage ker_relationConnecting

/-- This injection has the literal relation kernel as its source; no
local-liftability, local-exactness or basepoint hypothesis remains. -/
theorem relationObstructionInjection_injective :
    Function.Injective relationObstructionInjection :=
  @CycleQ2LinearRangeDescent.kernelQuotientInjection_injective ℂ relationVariations
    (KernelCechH1 ℂ 57 Complex.I SeedMatrix matrixGrades)
    inferInstance inferInstance inferInstance inferInstance inferInstance
    relationConnecting globalCofactorImage ker_relationConnecting

end CycleQ2SegreGlobalObstruction

#print axioms CycleQ2SegreGlobalObstruction.relation_variation_locally_liftable
#print axioms CycleQ2SegreGlobalObstruction.relationConnecting_zero_iff
#print axioms CycleQ2SegreGlobalObstruction.relationObstructionInjection_injective
end
end


