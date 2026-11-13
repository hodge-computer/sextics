import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport05

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/ModularGlobalFactorCech.lean -/
section
/-! Actual H1(O) removes the scalar overlap ambiguity of local factor
lifts. The corrected graded factor sections agree on all three overlaps. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 1024
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalFactorCech

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2ModularGlobalFactorSpaces CycleQ2SeedLocalizedProjection
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2CurveRestriction
  CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechActualTop CycleQ2SeedCechRestrictions
  CycleQ2ModularFactorCech CycleQ2ModularFactorChartExact CycleQ2ModularFactorGraded
  CycleQ2ModularFactorRestrictions

abbrev MatrixPiece := CycleQ2ModularGlobalFactorSpaces.Input14

def scalarD0 (q0 : ScalarSections {0}) (q1 : ScalarSections {1})
    (q2 : ScalarSections {2}) : ScalarPairs :=
  (gradedRestriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
    gradedRestriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0,
   gradedRestriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
    gradedRestriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0,
   gradedRestriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{1,2}) q2-
    gradedRestriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{1,2}) q1)

theorem scalarCech_exact (B : ScalarPairs) (hB : scalarD1 B=0) :
    ∃ (q0 : ScalarSections {0}) (q1 : ScalarSections {1}) (q2 : ScalarSections {2}),
      B=scalarD0 q0 q1 q2 := by
  have hc := congrArg Subtype.val hB
  obtain ⟨q0,q1,q2,hg0,hg1,hg2,h01,h02,h12⟩ :=
    coordinateCech_exact K (57:K) 33 0 B.1.val B.2.1.val B.2.2.val
      B.1.property B.2.1.property B.2.2.property hc
  refine ⟨⟨q0,hg0⟩,⟨q1,hg1⟩,⟨q2,hg2⟩,?_⟩
  exact Prod.ext (Subtype.ext h01) (Prod.ext (Subtype.ext h02) (Subtype.ext h12))

private theorem linear_sub_four {U V W : Type*}
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W]
    (f : U →ₗ[K] W) (g : V →ₗ[K] W) (u u' : U) (v v' : V) :
    f (u-u')-g (v-v')=(f u-g v)-(f u'-g v') := by
  rw [map_sub,map_sub]
  abel

theorem factorD0_sub (F0 G0 : GradedFactors {0}) (F1 G1 : GradedFactors {1})
    (F2 G2 : GradedFactors {2}) :
    factorD0 (F0-G0) (F1-G1) (F2-G2)=factorD0 F0 F1 F2-factorD0 G0 G1 G2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact @linear_sub_four (GradedFactors {1}) (GradedFactors {0}) (GradedFactors {0,1})
      (inferInstance : AddCommGroup (GradedFactors {1}))
      (inferInstance : Module K (GradedFactors {1}))
      (inferInstance : AddCommGroup (GradedFactors {0}))
      (inferInstance : Module K (GradedFactors {0}))
      (inferInstance : AddCommGroup (GradedFactors {0,1}))
      (inferInstance : Module K (GradedFactors {0,1}))
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}))
      (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1})) F1 G1 F0 G0
  · exact @linear_sub_four (GradedFactors {2}) (GradedFactors {0}) (GradedFactors {0,2})
      (inferInstance : AddCommGroup (GradedFactors {2}))
      (inferInstance : Module K (GradedFactors {2}))
      (inferInstance : AddCommGroup (GradedFactors {0}))
      (inferInstance : Module K (GradedFactors {0}))
      (inferInstance : AddCommGroup (GradedFactors {0,2}))
      (inferInstance : Module K (GradedFactors {0,2}))
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}))
      (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2})) F2 G2 F0 G0
  · exact @linear_sub_four (GradedFactors {2}) (GradedFactors {1}) (GradedFactors {1,2})
      (inferInstance : AddCommGroup (GradedFactors {2}))
      (inferInstance : Module K (GradedFactors {2}))
      (inferInstance : AddCommGroup (GradedFactors {1}))
      (inferInstance : Module K (GradedFactors {1}))
      (inferInstance : AddCommGroup (GradedFactors {1,2}))
      (inferInstance : Module K (GradedFactors {1,2}))
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}))
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2})) F2 G2 F1 G1

private theorem gauge_difference {s t u : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (hsu : s⊆u) (htu : t⊆u) (q : ScalarSections s) (q' : ScalarSections t) :
    gradedFactorRestriction htu (gradedGaugeMap t ht q')-
      gradedFactorRestriction hsu (gradedGaugeMap s hs q)=
    gradedGaugeMap u hu (gradedRestriction K 57 33 htu q'-
      gradedRestriction K 57 33 hsu q) := by
  exact (congrArg₂ (fun x y : GradedFactors u => x-y)
    (gradedGaugeMap_restriction ht hu htu q')
    (gradedGaugeMap_restriction hs hu hsu q)).trans
    (map_sub (gradedGaugeMap u hu) _ _).symm

theorem factorD0_gauge (q0 : ScalarSections {0}) (q1 : ScalarSections {1})
    (q2 : ScalarSections {2}) :
    factorD0 (gradedGaugeMap {0} (by decide) q0) (gradedGaugeMap {1} (by decide) q1)
      (gradedGaugeMap {2} (by decide) q2)=pairGauge (scalarD0 q0 q1 q2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({0}:Finset (Fin 3))⊆{0,1})
      (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q0 q1
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({0}:Finset (Fin 3))⊆{0,2})
      (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q0 q2
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({1}:Finset (Fin 3))⊆{1,2})
      (by decide : ({2}:Finset (Fin 3))⊆{1,2}) q1 q2

private theorem factorMap_sub_gauge (s : Finset (Fin 3)) (hs : s.Nonempty)
    (F : GradedFactors s) (q : ScalarSections s) :
    gradedFactorMap s hs (F-gradedGaugeMap s hs q)=gradedFactorMap s hs F := by
  exact (map_sub (gradedFactorMap s hs) F (gradedGaugeMap s hs q)).trans
    ((congrArg (fun x : Matrix (Fin 3) (Fin 3) (Chart s) => gradedFactorMap s hs F-x)
      (gradedFactorMap_gaugeMap s hs q)).trans (sub_zero _))

set_option maxHeartbeats 1000000 in
theorem correct_local_factors (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2})
    (h01 : gradedFactorMap {0,1} (by decide) (factorD0 F0 F1 F2).1=0)
    (h02 : gradedFactorMap {0,2} (by decide) (factorD0 F0 F1 F2).2.1=0)
    (h12 : gradedFactorMap {1,2} (by decide) (factorD0 F0 F1 F2).2.2=0) :
    ∃ (G0 : GradedFactors {0}) (G1 : GradedFactors {1}) (G2 : GradedFactors {2}),
      factorD0 G0 G1 G2=0 ∧
      gradedFactorMap {0} (by decide) G0=gradedFactorMap {0} (by decide) F0 ∧
      gradedFactorMap {1} (by decide) G1=gradedFactorMap {1} (by decide) F1 ∧
      gradedFactorMap {2} (by decide) G2=gradedFactorMap {2} (by decide) F2 := by
  obtain ⟨b01,hb01⟩ := graded_zero_factor_gauge {0,1} (by decide) (factorD0 F0 F1 F2).1 h01
  obtain ⟨b02,hb02⟩ := graded_zero_factor_gauge {0,2} (by decide) (factorD0 F0 F1 F2).2.1 h02
  obtain ⟨b12,hb12⟩ := graded_zero_factor_gauge {1,2} (by decide) (factorD0 F0 F1 F2).2.2 h12
  let B : ScalarPairs := (b01,b02,b12)
  have hB : pairGauge B=factorD0 F0 F1 F2 := Prod.ext hb01 (Prod.ext hb02 hb12)
  have hc : scalarD1 B=0 := by
    apply gradedGaugeMap_injective Finset.univ (by decide)
    rw [map_zero,←factorD1_pairGauge,hB,factorD1_factorD0]
  obtain ⟨q0,q1,q2,hq⟩ := scalarCech_exact B hc
  let G0 := F0-gradedGaugeMap {0} (by decide) q0
  let G1 := F1-gradedGaugeMap {1} (by decide) q1
  let G2 := F2-gradedGaugeMap {2} (by decide) q2
  refine ⟨G0,G1,G2,?_,?_,?_,?_⟩
  · calc
      factorD0 G0 G1 G2 = factorD0 F0 F1 F2-
          factorD0 (gradedGaugeMap {0} (by decide) q0)
            (gradedGaugeMap {1} (by decide) q1) (gradedGaugeMap {2} (by decide) q2) :=
        factorD0_sub F0 _ F1 _ F2 _
      _ = factorD0 F0 F1 F2-pairGauge (scalarD0 q0 q1 q2) :=
        congrArg (fun H : FactorPairs => factorD0 F0 F1 F2-H) (factorD0_gauge q0 q1 q2)
      _ = factorD0 F0 F1 F2-pairGauge B :=
        congrArg (fun H : ScalarPairs => factorD0 F0 F1 F2-pairGauge H) hq.symm
      _ = 0 := sub_eq_zero.mpr hB.symm
  · exact factorMap_sub_gauge {0} (by decide) F0 q0
  · exact factorMap_sub_gauge {1} (by decide) F1 q1
  · exact factorMap_sub_gauge {2} (by decide) F2 q2

theorem seedPiece_local_grade (r ι : K) (d ch : ℕ) (q : SeedPiece r ι d ch)
    (s : Finset (Fin 3)) :
    HasLocalGrade K r ι s (d,(ch:ZMod 3))
      (algebraMap (SeedRing r ι) (SeedLocal K r ι s) q.val) := by
  obtain ⟨p,hp,hpq⟩ := Submodule.mem_map.mp q.property
  change HG p (d,(ch:ZMod 3)) at hp
  change Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p=q.val at hpq
  rw [←hpq]
  exact polynomial_hasLocalGrade K r ι s p (d,(ch:ZMod 3)) hp

def localMatrix (N : MatrixPiece) (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Chart s) :=
  (chartMap s).mapMatrix (fun i j => (N i j).val)

theorem localMatrix_grade (N : MatrixPiece) (s : Finset (Fin 3)) : MatrixGrade s (localMatrix N s) := by
  intro i j
  exact seedPiece_local_grade 57 33 14 0 (N i j) s

theorem localMatrix_kernel (N : MatrixPiece)
    (hN : cofactorDifferential (seedQuotientMatrix (57:K) 33) (fun i j => (N i j).val)=0)
    (s : Finset (Fin 3)) :
    cofactorDifferential (CycleQ2SegreModularChartExact.chartMatrix (R:=K) s) (localMatrix N s)=0 := by
  have h := @map_cofactorDifferential CycleQ2ModularGlobalFactorSpaces.A inferInstance
    (Chart s) inferInstance (chartMap s) (seedQuotientMatrix (57:K) 33) (fun i j => (N i j).val)
  rw [hN] at h
  have hz : (chartMap s).mapMatrix (0:Matrix (Fin 3) (Fin 3) CycleQ2ModularGlobalFactorSpaces.A)=0 := by
    ext i j
    exact map_zero (chartMap s)
  rw [hz] at h
  exact h.symm

theorem localMatrix_restriction (N : MatrixPiece) {s t : Finset (Fin 3)} (hst : s⊆t) :
    (res hst).mapMatrix (localMatrix N s)=localMatrix N t := by
  ext i j
  exact restriction_chartMap hst _

theorem local_lifts_difference_kernel (N : MatrixPiece)
    {s t u : Finset (Fin 3)} (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (hsu : s⊆u) (htu : t⊆u) (F : GradedFactors s) (G : GradedFactors t)
    (hF : gradedFactorMap s hs F=localMatrix N s)
    (hG : gradedFactorMap t ht G=localMatrix N t) :
    gradedFactorMap u hu (gradedFactorRestriction htu G-gradedFactorRestriction hsu F)=0 := by
  rw [map_sub (gradedFactorMap u hu),←gradedFactorMap_restriction ht hu htu,←gradedFactorMap_restriction hs hu hsu,
    hF,hG,localMatrix_restriction,localMatrix_restriction,sub_self]

theorem exists_compatible_local_factors (N : MatrixPiece)
    (hN : cofactorDifferential (seedQuotientMatrix (57:K) 33) (fun i j => (N i j).val)=0) :
    ∃ (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}),
      factorD0 F0 F1 F2=0 ∧ gradedFactorMap {0} (by decide) F0=localMatrix N {0} := by
  obtain ⟨F0,hF0⟩ := graded_factor_lift {0} (by decide) (localMatrix N {0})
    (localMatrix_kernel N hN {0}) (localMatrix_grade N {0})
  obtain ⟨F1,hF1⟩ := graded_factor_lift {1} (by decide) (localMatrix N {1})
    (localMatrix_kernel N hN {1}) (localMatrix_grade N {1})
  obtain ⟨F2,hF2⟩ := graded_factor_lift {2} (by decide) (localMatrix N {2})
    (localMatrix_kernel N hN {2}) (localMatrix_grade N {2})
  have h01 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({0}:Finset (Fin 3))⊆{0,1}) (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F0 F1 hF0 hF1
  have h02 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({0}:Finset (Fin 3))⊆{0,2}) (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F0 F2 hF0 hF2
  have h12 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({1}:Finset (Fin 3))⊆{1,2}) (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F1 F2 hF1 hF2
  obtain ⟨G0,G1,G2,hG,hG0,_hG1,_hG2⟩ := correct_local_factors F0 F1 F2 h01 h02 h12
  exact ⟨G0,G1,G2,hG,hG0.trans hF0⟩

end CycleQ2ModularGlobalFactorCech

#print axioms CycleQ2ModularGlobalFactorCech.scalarCech_exact
#print axioms CycleQ2ModularGlobalFactorCech.exists_compatible_local_factors
end
end


/- Component: continuation_3/SeedGlobalFactorCech.lean -/
section
/-! Actual H1(O) removes the scalar overlap ambiguity of local factor
lifts. The corrected graded factor sections agree on all three overlaps. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalFactorCech

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechActualTop CycleQ2SeedCechRestrictions
  CycleQ2SegreFactorCech CycleQ2SegreFactorChartExact CycleQ2SegreFactorGraded
  CycleQ2SegreFactorRestrictions

abbrev MatrixPiece := CycleQ2SeedGlobalFactorMap.MatrixPiece

def scalarD0 (q0 : ScalarSections {0}) (q1 : ScalarSections {1})
    (q2 : ScalarSections {2}) : ScalarPairs :=
  (gradedRestriction ℂ 57 Complex.I (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
    gradedRestriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0,
   gradedRestriction ℂ 57 Complex.I (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
    gradedRestriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0,
   gradedRestriction ℂ 57 Complex.I (by decide : ({2}:Finset (Fin 3))⊆{1,2}) q2-
    gradedRestriction ℂ 57 Complex.I (by decide : ({1}:Finset (Fin 3))⊆{1,2}) q1)

theorem scalarCech_exact (B : ScalarPairs) (hB : scalarD1 B=0) :
    ∃ (q0 : ScalarSections {0}) (q1 : ScalarSections {1}) (q2 : ScalarSections {2}),
      B=scalarD0 q0 q1 q2 := by
  have hc := congrArg Subtype.val hB
  obtain ⟨q0,q1,q2,hg0,hg1,hg2,h01,h02,h12⟩ :=
    coordinateCech_exact ℂ (57:ℂ) Complex.I 0 B.1.val B.2.1.val B.2.2.val
      B.1.property B.2.1.property B.2.2.property hc
  refine ⟨⟨q0,hg0⟩,⟨q1,hg1⟩,⟨q2,hg2⟩,?_⟩
  exact Prod.ext (Subtype.ext h01) (Prod.ext (Subtype.ext h02) (Subtype.ext h12))

private theorem linear_sub_four {U V W : Type*}
    [AddCommGroup U] [Module ℂ U] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (f : U →ₗ[ℂ] W) (g : V →ₗ[ℂ] W) (u u' : U) (v v' : V) :
    f (u-u')-g (v-v')=(f u-g v)-(f u'-g v') := by
  rw [map_sub,map_sub]
  abel

theorem factorD0_sub (F0 G0 : GradedFactors {0}) (F1 G1 : GradedFactors {1})
    (F2 G2 : GradedFactors {2}) :
    factorD0 (F0-G0) (F1-G1) (F2-G2)=factorD0 F0 F1 F2-factorD0 G0 G1 G2 := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact @linear_sub_four (GradedFactors {1}) (GradedFactors {0}) (GradedFactors {0,1})
      (inferInstance : AddCommGroup (GradedFactors {1}))
      (inferInstance : Module ℂ (GradedFactors {1}))
      (inferInstance : AddCommGroup (GradedFactors {0}))
      (inferInstance : Module ℂ (GradedFactors {0}))
      (inferInstance : AddCommGroup (GradedFactors {0,1}))
      (inferInstance : Module ℂ (GradedFactors {0,1}))
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{0,1}))
      (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,1})) F1 G1 F0 G0
  · exact @linear_sub_four (GradedFactors {2}) (GradedFactors {0}) (GradedFactors {0,2})
      (inferInstance : AddCommGroup (GradedFactors {2}))
      (inferInstance : Module ℂ (GradedFactors {2}))
      (inferInstance : AddCommGroup (GradedFactors {0}))
      (inferInstance : Module ℂ (GradedFactors {0}))
      (inferInstance : AddCommGroup (GradedFactors {0,2}))
      (inferInstance : Module ℂ (GradedFactors {0,2}))
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{0,2}))
      (gradedFactorRestriction (by decide : ({0}:Finset (Fin 3))⊆{0,2})) F2 G2 F0 G0
  · exact @linear_sub_four (GradedFactors {2}) (GradedFactors {1}) (GradedFactors {1,2})
      (inferInstance : AddCommGroup (GradedFactors {2}))
      (inferInstance : Module ℂ (GradedFactors {2}))
      (inferInstance : AddCommGroup (GradedFactors {1}))
      (inferInstance : Module ℂ (GradedFactors {1}))
      (inferInstance : AddCommGroup (GradedFactors {1,2}))
      (inferInstance : Module ℂ (GradedFactors {1,2}))
      (gradedFactorRestriction (by decide : ({2}:Finset (Fin 3))⊆{1,2}))
      (gradedFactorRestriction (by decide : ({1}:Finset (Fin 3))⊆{1,2})) F2 G2 F1 G1

private theorem gauge_difference {s t u : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (hsu : s⊆u) (htu : t⊆u) (q : ScalarSections s) (q' : ScalarSections t) :
    gradedFactorRestriction htu (gradedGaugeMap t ht q')-
      gradedFactorRestriction hsu (gradedGaugeMap s hs q)=
    gradedGaugeMap u hu (gradedRestriction ℂ 57 Complex.I htu q'-
      gradedRestriction ℂ 57 Complex.I hsu q) := by
  exact (congrArg₂ (fun x y : GradedFactors u => x-y)
    (gradedGaugeMap_restriction ht hu htu q')
    (gradedGaugeMap_restriction hs hu hsu q)).trans
    (map_sub (gradedGaugeMap u hu) _ _).symm

theorem factorD0_gauge (q0 : ScalarSections {0}) (q1 : ScalarSections {1})
    (q2 : ScalarSections {2}) :
    factorD0 (gradedGaugeMap {0} (by decide) q0) (gradedGaugeMap {1} (by decide) q1)
      (gradedGaugeMap {2} (by decide) q2)=pairGauge (scalarD0 q0 q1 q2) := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({0}:Finset (Fin 3))⊆{0,1})
      (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q0 q1
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({0}:Finset (Fin 3))⊆{0,2})
      (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q0 q2
  · exact gauge_difference (by decide) (by decide) (by decide)
      (by decide : ({1}:Finset (Fin 3))⊆{1,2})
      (by decide : ({2}:Finset (Fin 3))⊆{1,2}) q1 q2

private theorem factorMap_sub_gauge (s : Finset (Fin 3)) (hs : s.Nonempty)
    (F : GradedFactors s) (q : ScalarSections s) :
    gradedFactorMap s hs (F-gradedGaugeMap s hs q)=gradedFactorMap s hs F := by
  exact (map_sub (gradedFactorMap s hs) F (gradedGaugeMap s hs q)).trans
    ((congrArg (fun x : Matrix (Fin 3) (Fin 3) (Chart s) => gradedFactorMap s hs F-x)
      (gradedFactorMap_gaugeMap s hs q)).trans (sub_zero _))

set_option maxHeartbeats 1000000 in
theorem correct_local_factors (F0 : GradedFactors {0}) (F1 : GradedFactors {1})
    (F2 : GradedFactors {2})
    (h01 : gradedFactorMap {0,1} (by decide) (factorD0 F0 F1 F2).1=0)
    (h02 : gradedFactorMap {0,2} (by decide) (factorD0 F0 F1 F2).2.1=0)
    (h12 : gradedFactorMap {1,2} (by decide) (factorD0 F0 F1 F2).2.2=0) :
    ∃ (G0 : GradedFactors {0}) (G1 : GradedFactors {1}) (G2 : GradedFactors {2}),
      factorD0 G0 G1 G2=0 ∧
      gradedFactorMap {0} (by decide) G0=gradedFactorMap {0} (by decide) F0 ∧
      gradedFactorMap {1} (by decide) G1=gradedFactorMap {1} (by decide) F1 ∧
      gradedFactorMap {2} (by decide) G2=gradedFactorMap {2} (by decide) F2 := by
  obtain ⟨b01,hb01⟩ := graded_zero_factor_gauge {0,1} (by decide) (factorD0 F0 F1 F2).1 h01
  obtain ⟨b02,hb02⟩ := graded_zero_factor_gauge {0,2} (by decide) (factorD0 F0 F1 F2).2.1 h02
  obtain ⟨b12,hb12⟩ := graded_zero_factor_gauge {1,2} (by decide) (factorD0 F0 F1 F2).2.2 h12
  let B : ScalarPairs := (b01,b02,b12)
  have hB : pairGauge B=factorD0 F0 F1 F2 := Prod.ext hb01 (Prod.ext hb02 hb12)
  have hc : scalarD1 B=0 := by
    apply gradedGaugeMap_injective Finset.univ (by decide)
    rw [map_zero,←factorD1_pairGauge,hB,factorD1_factorD0]
  obtain ⟨q0,q1,q2,hq⟩ := scalarCech_exact B hc
  let G0 := F0-gradedGaugeMap {0} (by decide) q0
  let G1 := F1-gradedGaugeMap {1} (by decide) q1
  let G2 := F2-gradedGaugeMap {2} (by decide) q2
  refine ⟨G0,G1,G2,?_,?_,?_,?_⟩
  · calc
      factorD0 G0 G1 G2 = factorD0 F0 F1 F2-
          factorD0 (gradedGaugeMap {0} (by decide) q0)
            (gradedGaugeMap {1} (by decide) q1) (gradedGaugeMap {2} (by decide) q2) :=
        factorD0_sub F0 _ F1 _ F2 _
      _ = factorD0 F0 F1 F2-pairGauge (scalarD0 q0 q1 q2) :=
        congrArg (fun H : FactorPairs => factorD0 F0 F1 F2-H) (factorD0_gauge q0 q1 q2)
      _ = factorD0 F0 F1 F2-pairGauge B :=
        congrArg (fun H : ScalarPairs => factorD0 F0 F1 F2-pairGauge H) hq.symm
      _ = 0 := sub_eq_zero.mpr hB.symm
  · exact factorMap_sub_gauge {0} (by decide) F0 q0
  · exact factorMap_sub_gauge {1} (by decide) F1 q1
  · exact factorMap_sub_gauge {2} (by decide) F2 q2

def localMatrix (N : MatrixPiece) (s : Finset (Fin 3)) : Matrix (Fin 3) (Fin 3) (Chart s) :=
  (chartMap s).mapMatrix (fun i j => (N i j).val)

theorem localMatrix_grade (N : MatrixPiece) (s : Finset (Fin 3)) : MatrixGrade s (localMatrix N s) := by
  intro i j
  exact CycleQ2SeedGlobalFactorMap.seedPiece_local_grade 57 Complex.I 14 0 (N i j) s

theorem localMatrix_kernel (N : MatrixPiece)
    (hN : cofactorDifferential CycleQ2SegreComplexBasepoint.matrix (fun i j => (N i j).val)=0)
    (s : Finset (Fin 3)) :
    cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) (localMatrix N s)=0 := by
  have h := @map_cofactorDifferential CycleQ2SeedGlobalFactorMap.A inferInstance
    (Chart s) inferInstance (chartMap s) CycleQ2SegreComplexBasepoint.matrix (fun i j => (N i j).val)
  rw [hN] at h
  have hz : (chartMap s).mapMatrix (0:Matrix (Fin 3) (Fin 3) CycleQ2SeedGlobalFactorMap.A)=0 := by
    ext i j
    exact map_zero (chartMap s)
  rw [hz] at h
  exact h.symm

theorem localMatrix_restriction (N : MatrixPiece) {s t : Finset (Fin 3)} (hst : s⊆t) :
    (res hst).mapMatrix (localMatrix N s)=localMatrix N t := by
  ext i j
  exact restriction_chartMap hst _

theorem local_lifts_difference_kernel (N : MatrixPiece)
    {s t u : Finset (Fin 3)} (hs : s.Nonempty) (ht : t.Nonempty) (hu : u.Nonempty)
    (hsu : s⊆u) (htu : t⊆u) (F : GradedFactors s) (G : GradedFactors t)
    (hF : gradedFactorMap s hs F=localMatrix N s)
    (hG : gradedFactorMap t ht G=localMatrix N t) :
    gradedFactorMap u hu (gradedFactorRestriction htu G-gradedFactorRestriction hsu F)=0 := by
  rw [map_sub (gradedFactorMap u hu),←gradedFactorMap_restriction ht hu htu,←gradedFactorMap_restriction hs hu hsu,
    hF,hG,localMatrix_restriction,localMatrix_restriction,sub_self]

theorem exists_compatible_local_factors (N : MatrixPiece)
    (hN : cofactorDifferential CycleQ2SegreComplexBasepoint.matrix (fun i j => (N i j).val)=0) :
    ∃ (F0 : GradedFactors {0}) (F1 : GradedFactors {1}) (F2 : GradedFactors {2}),
      factorD0 F0 F1 F2=0 ∧ gradedFactorMap {0} (by decide) F0=localMatrix N {0} := by
  obtain ⟨F0,hF0⟩ := graded_factor_lift {0} (by decide) (localMatrix N {0})
    (localMatrix_kernel N hN {0}) (localMatrix_grade N {0})
  obtain ⟨F1,hF1⟩ := graded_factor_lift {1} (by decide) (localMatrix N {1})
    (localMatrix_kernel N hN {1}) (localMatrix_grade N {1})
  obtain ⟨F2,hF2⟩ := graded_factor_lift {2} (by decide) (localMatrix N {2})
    (localMatrix_kernel N hN {2}) (localMatrix_grade N {2})
  have h01 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({0}:Finset (Fin 3))⊆{0,1}) (by decide : ({1}:Finset (Fin 3))⊆{0,1}) F0 F1 hF0 hF1
  have h02 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({0}:Finset (Fin 3))⊆{0,2}) (by decide : ({2}:Finset (Fin 3))⊆{0,2}) F0 F2 hF0 hF2
  have h12 := local_lifts_difference_kernel N (by decide) (by decide) (by decide)
    (by decide : ({1}:Finset (Fin 3))⊆{1,2}) (by decide : ({2}:Finset (Fin 3))⊆{1,2}) F1 F2 hF1 hF2
  obtain ⟨G0,G1,G2,hG,hG0,_hG1,_hG2⟩ := correct_local_factors F0 F1 F2 h01 h02 h12
  exact ⟨G0,G1,G2,hG,hG0.trans hF0⟩

end CycleQ2SeedGlobalFactorCech

#print axioms CycleQ2SeedGlobalFactorCech.scalarCech_exact
#print axioms CycleQ2SeedGlobalFactorCech.exists_compatible_local_factors
end
end


/- Component: continuation_3/SeedGlobalIdealGluing.lean -/
section
/-! Graded local ideal sections glue into the actual finite global linkage
pieces. Global ideal membership uses the checked finite-piece restriction
kernel and faithfulness of the actual curve base-coordinate localization. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalIdealGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading
  CycleQ2SeedLinkageCechVanishing CycleQ2SeedGlobalFactorMap

def threeSections {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    (i : Fin 3) → P i := Fin.cases q0 (Fin.cases q1 (Fin.cases q2 (fun i => Fin.elim0 i)))

@[simp] theorem threeSections_zero {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 0=q0 := rfl
@[simp] theorem threeSections_one {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 1=q1 := rfl
@[simp] theorem threeSections_two {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 2=q2 := rfl

theorem compatible_of_two_differences (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (h01 : restriction ℂ 57 Complex.I (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction ℂ 57 Complex.I (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    Compatible ℂ 57 Complex.I (threeSections (P:=fun i => Chart {i}) q0 q1 q2) := by
  have hc01 (ab) : localizedCoordinates ℂ 57 Complex.I {1} q1 ab=
      localizedCoordinates ℂ 57 Complex.I {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates ℂ 57 Complex.I {0,1} q ab) h01
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hc02 (ab) : localizedCoordinates ℂ 57 Complex.I {2} q2 ab=
      localizedCoordinates ℂ 57 Complex.I {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates ℂ 57 Complex.I {0,2} q ab) h02
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hcoord (i : Fin 3) (ab) :
      localizedCoordinates ℂ 57 Complex.I {i} (threeSections (P:=fun i => Chart {i}) q0 q1 q2 i) ab=
      localizedCoordinates ℂ 57 Complex.I {0} q0 ab := by
    fin_cases i
    · rfl
    · exact hc01 ab
    · exact hc02 ab
  intro i j
  apply localizedCoordinates_injective ℂ 57 Complex.I {i,j}
  funext ab
  simp only [pairRestriction,secondPairRestriction,coordinates_restriction]
  exact (hcoord i ab).trans (hcoord j ab).symm

theorem seedRestriction_zero_of_first_local_zero (side : Side) (q : A)
    (hq : CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ side 57 Complex.I {0}
      (chartMap {0} q)=0) : seedRestriction side (57:ℂ) Complex.I q=0 := by
  let e := CycleQ2CurveLocalizedRestriction.baseOpenEquiv ℂ side 57 Complex.I {0}
    (CycleQ2CurveLocalizedRestriction.complex_scale_unit side)
  have h := congrArg e hq
  have hb : CycleQ2CurveLocalizedRestriction.baseOpenMap ℂ side 57 Complex.I {0}
      (CycleQ2CurveLocalizedRestriction.complex_scale_unit side) (chartMap {0} q)=0 := by
    exact h.trans (map_zero e)
  apply CycleQ2CurveCechGlobalGluing.localization_injective ℂ side 57 Complex.I {0}
  rw [map_zero]
  rw [←CycleQ2CurveLocalizedRestriction.baseOpenMap_algebraMap ℂ side 57 Complex.I {0}
    (CycleQ2CurveLocalizedRestriction.complex_scale_unit side) q]
  exact hb

theorem exists_global_ideal_piece (side : Side) (d ch : ℕ)
    (hpiece : linkagePiece side (57:ℂ) Complex.I d ch=
      LinearMap.ker (seedRestrictionPiece side (57:ℂ) Complex.I d ch))
    (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (hq0 : localGrade {0} ((d:ℤ),(ch:ZMod 3)) q0)
    (hi0 : q0∈localIdeal side {0})
    (h01 : restriction ℂ 57 Complex.I (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction ℂ 57 Complex.I (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction ℂ 57 Complex.I (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    ∃ q : linkagePiece side (57:ℂ) Complex.I d ch,
      chartMap {0} q.val.val=q0 ∧ chartMap {1} q.val.val=q1 ∧ chartMap {2} q.val.val=q2 := by
  let qs := threeSections (P:=fun i => Chart {i}) q0 q1 q2
  have hcomp := compatible_of_two_differences q0 q1 q2 h01 h02
  obtain ⟨p,_hstd,hp,hglue⟩ := exists_homogeneous_polynomial_gluing ℂ 57 Complex.I qs hcomp
    ((d:ℤ),(ch:ZMod 3)) hq0
  have hpg : HG p (d,(ch:ZMod 3)) := (signedHomogeneous_iff ℂ p _).mp hp
  let q : SeedPiece (57:ℂ) Complex.I d ch :=
    ⟨Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF (57:ℂ) Complex.I)) p,
      Submodule.mem_map.mpr ⟨p,hpg,rfl⟩⟩
  have hqzero : seedRestriction side (57:ℂ) Complex.I q.val=0 := by
    apply seedRestriction_zero_of_first_local_zero side q.val
    have hzero := (mem_iff_restriction_zero side {0} (by decide) q0
      ((d:ℤ),(ch:ZMod 3)) hq0).mp hi0
    have he : chartMap {0} q.val=q0 := hglue 0
    rw [he]
    exact hzero
  have hmem : q∈linkagePiece side (57:ℂ) Complex.I d ch := by
    rw [hpiece]
    change seedRestrictionPiece side (57:ℂ) Complex.I d ch q=0
    apply Subtype.ext
    exact hqzero
  exact ⟨⟨q,hmem⟩,hglue 0,hglue 1,hglue 2⟩

end CycleQ2SeedGlobalIdealGluing

#print axioms CycleQ2SeedGlobalIdealGluing.exists_global_ideal_piece
end
end


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

def pointCubic (y : ParameterIndex → S) : FullInvariantIndex 3 → S :=
  fun j => y (Sum.inl j)

def pointSextic (y : ParameterIndex → S) : FullInvariantIndex 6 → S :=
  fun j => y (Sum.inr (Sum.inl j))

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

def pointMap (y : ParameterIndex → S) : Coeff →+* S := (aeval y).toRingHom

theorem pointMap_familyH (y : ParameterIndex → S) :
    map (pointMap y) familyH=fullInvariantPolynomial 3 (pointCubic y) := by
  rw [familyH,map_fullInvariantPolynomial]
  congr 1
  funext j
  simp only [Function.comp_apply,pointMap,rawCubicCoefficient,AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe,aeval_X,pointCubic]

theorem pointMap_familyF (y : ParameterIndex → S) :
    map (pointMap y) familyF=fullInvariantPolynomial 6 (pointSextic y) := by
  rw [familyF,map_fullInvariantPolynomial]
  congr 1
  funext j
  simp only [Function.comp_apply,pointMap,rawSexticCoefficient,AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe,aeval_X,pointSextic]

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

abbrev PointSurface (y : ParameterIndex → S) := CurveRing (pointMap y)
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


/- Component: continuation_3/cylinder_bridge/IncidenceTraceDirection.lean -/
section
/-! The actual trace-one incidence direction is chosen from the proved
characteristic-zero kernel.  Its residue is bound to the actual smooth
curve calculation; no saved matrix correction is needed. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceDirection
open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2PolynomialAffineSlice CycleQ2PolynomialImplicitTrace
  CycleQ2SegreFullJacobianBounds CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2IncidenceTraceRow CycleQ2MatrixTraceAugment
  CycleQ2IncidenceCubicCechTrace

def fixedDirection : FixedSexticParameters → ℂ :=
  CycleQ2SegreNonconstructiveTangent.exists_fixed_trace_six.choose

theorem fixedDirection_kernel : fixedSexticJacobian*ᵥfixedDirection=0 :=
  CycleQ2SegreNonconstructiveTangent.exists_fixed_trace_six.choose_spec.1

theorem fixedDirection_trace_six : rowLinear (traceRow Complex.I) fixedDirection=6 :=
  CycleQ2SegreNonconstructiveTangent.exists_fixed_trace_six.choose_spec.2

def parameterDirection : ParameterIndex → ℂ :=
  fun j => CycleQ2IncidenceSexticFamily.extendDirections
    (fun k (_ : Unit) => fixedDirection k) j ()

theorem parameterDirection_kernel :
    seedJacobian ℂ (57:ℂ) Complex.I*ᵥparameterDirection=0 := by
  let B : Matrix FixedSexticParameters Unit ℂ := fun k _ => fixedDirection k
  have h := CycleQ2IncidenceSexticFamily.jacobian_extendDirections
    (seedJacobian ℂ (57:ℂ) Complex.I) B
  funext q
  calc
    _=(seedJacobian ℂ (57:ℂ) Complex.I*
        CycleQ2IncidenceSexticFamily.extendDirections B) q () := rfl
    _=((seedJacobian ℂ (57:ℂ) Complex.I).submatrix id fixedSexticColumn*B) q () :=
      congrArg (fun M : Matrix ColumnIndex Unit ℂ => M q ()) h
    _=(fixedSexticJacobian*ᵥfixedDirection) (columnEquiv q) := by
      simp only [Matrix.mul_apply,Matrix.submatrix_apply,id_eq,Matrix.mulVec,dotProduct,B]
      apply Finset.sum_congr rfl
      intro j _
      rw [seedJacobian_eq_linearizedMatrix]
      rfl
    _=0 := congrFun fixedDirection_kernel (columnEquiv q)

theorem parameterDirection_sextic (j : FullInvariantIndex 6) :
    parameterDirection (Sum.inr (Sum.inl j))=0 := rfl

def traceWeights : ParameterIndex → ℂ := by
  classical
  exact Pi.single (Sum.inl (cubicIndex 1)) (Complex.I/6)+
    Pi.single (Sum.inl (cubicIndex 8)) (-(1+Complex.I)/6)

theorem traceWeights_formula (v : ParameterIndex → ℂ) :
    traceWeights ⬝ᵥ v=(Complex.I*v (Sum.inl (cubicIndex 1))-
      (1+Complex.I)*v (Sum.inl (cubicIndex 8)))/6 := by
  classical
  simp only [traceWeights,add_dotProduct,single_dotProduct]
  ring

theorem parameterDirection_trace_six :
    unscaledTrace (fun j => parameterDirection (Sum.inl j))=6 := by
  have h := fixedDirection_trace_six
  rw [traceRow_formula] at h
  exact h

theorem traceWeights_parameterDirection : traceWeights ⬝ᵥparameterDirection=1 := by
  rw [traceWeights_formula]
  change unscaledTrace (fun j => parameterDirection (Sum.inl j))/6=1
  rw [parameterDirection_trace_six]
  norm_num

theorem traceWeights_eq_checked_seed_trace : traceWeights ⬝ᵥparameterDirection=
    CycleQ2SeedCechTheta.derivativeTrace 1
      (fun j => parameterDirection (Sum.inl (cubicIndex j))) := by
  rw [traceWeights_formula,CycleQ2SeedCechTheta.smooth_derivativeTrace_explicit]

theorem parameterCubic_not_boundary :
    ¬ CycleQ2SeedCechTheta.CechBoundary 57 1
      (CycleQ2SeedCechTheta.derivativeNumerator
        (CycleQ2SeedTrace.substitute
          (fullInvariantPolynomial 3 (fun j => parameterDirection (Sum.inl j))))) 2 4 :=
  cubic_trace_one_not_boundary 57 (by norm_num) _ parameterDirection_trace_six

theorem parameterCubic_normal_trace :
    CycleQ2NormalConnecting.pairedNormalTrace 57 1 (by norm_num)
      (CycleQ2SeedTrace.substitute
        (fullInvariantPolynomial 3 (fun j => parameterDirection (Sum.inl j))))= -1/171 := by
  rw [cubic_trace_one_normal_trace 57 (by norm_num) _ parameterDirection_trace_six]
  norm_num

theorem actual_tracePolynomial_seed_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix ParameterIndex ι ℂ)
    (hJ : P*seedJacobian ℂ (57:ℂ) Complex.I*B=1) :
    eval (seedPoint (57:ℂ) Complex.I)
      (tracePolynomial P B (presentation ℂ 57).equation traceWeights parameterDirection)=1 := by
  exact seed_tracePolynomial_one (RingHom.id ℂ) (seedPoint (57:ℂ) Complex.I)
    P B (presentation ℂ 57).equation traceWeights parameterDirection
    hJ parameterDirection_kernel traceWeights_parameterDirection

end CycleQ2IncidenceTraceDirection

#print axioms CycleQ2IncidenceTraceDirection.parameterDirection_kernel
#print axioms CycleQ2IncidenceTraceDirection.parameterCubic_not_boundary
#print axioms CycleQ2IncidenceTraceDirection.parameterCubic_normal_trace
#print axioms CycleQ2IncidenceTraceDirection.actual_tracePolynomial_seed_one
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceProjectiveTrace.lean -/
section
/-! The actual seed trace annihilates the seed cubic, while its leading
coefficient is one.  The projective implicit numerator therefore equals
one at the seed and detects motion modulo rescaling of the cubic. -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceProjectiveTrace
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreModularDetectorMatrixBinding
  CycleQ2IncidenceCubicCechTrace CycleQ2IncidenceTraceDirection
  CycleQ2PolynomialProjectiveTrace

def leadingWeights : ParameterIndex → ℂ := by
  classical
  exact Pi.single (Sum.inl fullCubicLeadingIndex) 1

theorem leadingWeights_formula (v : ParameterIndex → ℂ) :
    leadingWeights ⬝ᵥ v=v (Sum.inl fullCubicLeadingIndex) := by
  classical
  rw [leadingWeights,single_dotProduct,one_mul]

theorem mapped_leadingWeights_formula {S : Type*} [CommRing S]
    (φ : ℂ →+* S) (v : ParameterIndex → S) :
    (φ ∘ leadingWeights) ⬝ᵥ v=v (Sum.inl fullCubicLeadingIndex) := by
  classical
  have h : φ ∘ leadingWeights=Pi.single (Sum.inl fullCubicLeadingIndex) 1 := by
    funext j
    simp only [Function.comp_apply,leadingWeights,Pi.single_apply]
    split_ifs <;> simp only [map_one,map_zero]
  rw [h,single_dotProduct,one_mul]

theorem mapped_traceWeights_formula {S : Type*} [CommRing S]
    (φ : ℂ →+* S) (v : ParameterIndex → S) :
    (φ ∘ traceWeights) ⬝ᵥ v=
      φ (Complex.I/6)*v (Sum.inl (cubicIndex 1))+
      φ (-(1+Complex.I)/6)*v (Sum.inl (cubicIndex 8)) := by
  classical
  have hsingle (j : ParameterIndex) (a : ℂ) :
      φ ∘ Pi.single j a=Pi.single j (φ a) := by
    funext k
    simp only [Function.comp_apply,Pi.single_apply]
    split_ifs <;> simp only [map_zero]
  have h : φ ∘ traceWeights=
      Pi.single (Sum.inl (cubicIndex 1)) (φ (Complex.I/6))+
        Pi.single (Sum.inl (cubicIndex 8)) (φ (-(1+Complex.I)/6)) := by
    change (fun k => φ ((Pi.single (Sum.inl (cubicIndex 1)) (Complex.I/6) : ParameterIndex → ℂ) k+
      (Pi.single (Sum.inl (cubicIndex 8)) (-(1+Complex.I)/6) : ParameterIndex → ℂ) k))=_
    simp only [map_add]
    exact congrArg₂ (fun a b : ParameterIndex → S => a+b)
      (hsingle _ _) (hsingle _ _)
  rw [h,add_dotProduct,single_dotProduct,single_dotProduct]

theorem seed_cubic_coefficient_one (ι : ℂ) :
    seedCubicCoefficients ι (cubicIndex 1)=1-ι := by
  have he : fullExponentOf (cubicIndex 1).val=Finsupp.single (3:Fin 5) 3 := by
    rw [cubicIndex_exponent]
    ext j
    fin_cases j <;>
      simp [CycleQ2SparseGaussianPolynomial.tupleExponent,
        CycleQ2SparseGaussianPolynomial.tupleFun,CycleQ2SegreModularDetectorData.cubicExponents,
        Finsupp.single_apply,Fin.reduceFinMk]
  simp only [seedCubicCoefficients,he,smoothH,smoothB,smoothA,coeff_sub,coeff_add,
    coeff_C_mul,X_pow_eq_monomial]
  simp only [X,monomial_mul,coeff_monomial]
  have hne (e : FullExponent) (he : e 3 ≠ 3) :
      e ≠ Finsupp.single (3 : Fin 5) 3 := by
    intro h
    apply he
    simpa only [Finsupp.single_eq_same] using (congrArg (fun f : FullExponent => f 3) h)
  have h2 : (Finsupp.single (2 : Fin 5) 3 : FullExponent) ≠
      Finsupp.single 3 3 := hne _ (by simp [Finsupp.single_apply])
  have h123 : (Finsupp.single (1 : Fin 5) 1 + Finsupp.single 2 1 +
      Finsupp.single 3 1 : FullExponent) ≠ Finsupp.single 3 3 :=
    hne _ (by simp [Finsupp.single_apply])
  have h023 : (Finsupp.single (0 : Fin 5) 1 + Finsupp.single 2 1 +
      Finsupp.single 3 1 : FullExponent) ≠ Finsupp.single 3 3 :=
    hne _ (by simp [Finsupp.single_apply])
  have h012 : (Finsupp.single (0 : Fin 5) 1 + Finsupp.single 1 2 : FullExponent) ≠
      Finsupp.single 3 3 := hne _ (by simp [Finsupp.single_apply])
  have h0 : (Finsupp.single (0 : Fin 5) 3 : FullExponent) ≠
      Finsupp.single 3 3 := hne _ (by simp [Finsupp.single_apply])
  have h1 : (Finsupp.single (1 : Fin 5) 3 : FullExponent) ≠
      Finsupp.single 3 3 := hne _ (by simp [Finsupp.single_apply])
  simp only [ite_true, if_neg h2, if_neg h123, if_neg h023, if_neg h012,
    if_neg h0, if_neg h1, one_mul, zero_add, add_zero, mul_one]

theorem seed_cubic_leading (ι : ℂ) :
    seedCubicCoefficients ι fullCubicLeadingIndex=1 := by
  rw [seedCubicCoefficients,fullCubicLeadingIndex_exponent,smoothH_leading_coefficient]

theorem seed_leading_value :
    leadingWeights ⬝ᵥ seedPoint (57:ℂ) Complex.I=1 := by
  rw [leadingWeights_formula]
  exact seed_cubic_leading Complex.I

theorem seed_trace_value :
    traceWeights ⬝ᵥ seedPoint (57:ℂ) Complex.I=0 := by
  rw [traceWeights_formula]
  change (Complex.I*seedCubicCoefficients Complex.I (cubicIndex 1)-
    (1+Complex.I)*seedCubicCoefficients Complex.I (cubicIndex 8))/6=0
  rw [seed_cubic_coefficient_one,cubicIndex8_eq_leading,seed_cubic_leading]
  ring_nf
  simp only [Complex.I_sq]
  norm_num

theorem actual_projectiveTracePolynomial_seed_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix ParameterIndex ι ℂ)
    (hJ : P*seedJacobian ℂ (57:ℂ) Complex.I*B=1) :
    eval (seedPoint (57:ℂ) Complex.I)
      (projectiveTracePolynomial P B (presentation ℂ 57).equation
        traceWeights leadingWeights parameterDirection)=1 := by
  exact seed_projectiveTracePolynomial_one (RingHom.id ℂ)
    (seedPoint (57:ℂ) Complex.I) P B (presentation ℂ 57).equation
    traceWeights leadingWeights parameterDirection hJ parameterDirection_kernel
    traceWeights_parameterDirection seed_leading_value seed_trace_value

end CycleQ2IncidenceProjectiveTrace

#print axioms CycleQ2IncidenceProjectiveTrace.seed_trace_value
#print axioms CycleQ2IncidenceProjectiveTrace.actual_projectiveTracePolynomial_seed_one
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceTraceFamily.lean -/
section
/-! The independent sextic family with one additional external parameter
along the proved trace-one tangent. Its original-parameter open contains
both the ordinary and projective implicit trace numerators and the retained
Jacobian determinant. -/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceFamily
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice CycleQ2PolynomialImplicitTrace
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceProjectiveTrace
  CycleQ2PolynomialProjectiveTrace

abbrev TraceRing := MvPolynomial (Unit ⊕ FullInvariantIndex 6) ℂ

def traceParameter : TraceRing := X (Sum.inl ())
def sexticParameter (j : FullInvariantIndex 6) : TraceRing := X (Sum.inr j)

def baseSeed : Unit ⊕ FullInvariantIndex 6 → ℂ :=
  Sum.elim (fun _ => 0) (seedSexticCoefficients (57:ℂ) Complex.I)

def seedEvaluation : TraceRing →+* ℂ := eval baseSeed

def centre : ParameterIndex → TraceRing :=
  coefficientPoint
    (fun h => C (seedCubicCoefficients Complex.I h) +
      traceParameter * C (parameterDirection (Sum.inl h)))
    sexticParameter
    (fun i j e => traceParameter * C (parameterDirection (Sum.inr (Sum.inr ((i,j),e)))))

def equations (q : ColumnIndex) : MvPolynomial ParameterIndex TraceRing :=
  MvPolynomial.map C ((presentation ℂ 57).equation q)

def relations : Matrix RelationIndex ColumnIndex (MvPolynomial ParameterIndex TraceRing) :=
  ((presentation ℂ 57).relation).map (MvPolynomial.map C)

def directions {ι : Type*} (B : Matrix FixedSexticParameters ι ℂ) :
    Matrix ParameterIndex ι TraceRing := (CycleQ2IncidenceSexticFamily.extendDirections B).map C

def protectedOpen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix ParameterIndex ι ℂ) :
    MvPolynomial ParameterIndex TraceRing :=
  MvPolynomial.map C (leadingProduct ℂ *
    tracePolynomial P B (presentation ℂ 57).equation traceWeights parameterDirection *
    projectiveTracePolynomial P B (presentation ℂ 57).equation
      traceWeights leadingWeights parameterDirection *
    (retainedJacobian P B (presentation ℂ 57).equation).det)

theorem seedEvaluation_comp_C : seedEvaluation.comp (C : ℂ →+* TraceRing)=RingHom.id ℂ := by
  ext z
  simp only [RingHom.comp_apply,seedEvaluation,eval_C,RingHom.id_apply]

theorem centre_seed : seedEvaluation ∘ centre=seedPoint (57:ℂ) Complex.I := by
  funext j
  rcases j with j | j
  · simp [centre,seedEvaluation,baseSeed,traceParameter,seedPoint,coefficientPoint]
  · rcases j with j | j
    · simp [centre,seedEvaluation,baseSeed,sexticParameter,seedPoint,coefficientPoint]
    · simp [centre,seedEvaluation,baseSeed,traceParameter,seedPoint,coefficientPoint]

theorem eval_coefficientMap (p : ParameterPolynomial ℂ) :
    eval₂Hom seedEvaluation (seedEvaluation ∘ centre) (MvPolynomial.map C p) =
      eval (seedPoint (57:ℂ) Complex.I) p := by
  rw [eval₂Hom_map_hom,seedEvaluation_comp_C,centre_seed]
  rfl

theorem relation_identity : relations *ᵥ equations=0 := by
  have h := (presentation ℂ 57).relation_identity
  funext k
  have hk := congrArg (MvPolynomial.map (C : ℂ →+* TraceRing)) (congrFun h k)
  simpa only [relations,equations,Matrix.mulVec,dotProduct,Matrix.map_apply,
    map_sum,map_mul,Pi.zero_apply,map_zero] using hk

theorem seed_zero (q : ColumnIndex) :
    eval₂Hom seedEvaluation (seedEvaluation ∘ centre) (equations q)=0 := by
  rw [equations,eval_coefficientMap]
  exact seed_equations_zero ℂ (57:ℂ) Complex.I q

theorem seed_relation : relations.map (eval₂Hom seedEvaluation (seedEvaluation ∘ centre)) =
    seedRelationMatrix ℂ (57:ℂ) Complex.I := by
  funext k q
  change eval₂Hom seedEvaluation (seedEvaluation ∘ centre)
    (MvPolynomial.map C ((presentation ℂ 57).relation k q)) = _
  rw [eval_coefficientMap]
  rfl

theorem seed_jacobian : jacobian seedEvaluation (seedEvaluation ∘ centre) equations =
    seedJacobian ℂ (57:ℂ) Complex.I := by
  funext q j
  change eval₂Hom seedEvaluation (seedEvaluation ∘ centre)
    (pderiv j (MvPolynomial.map C ((presentation ℂ 57).equation q))) = _
  rw [pderiv_map,eval_coefficientMap]
  rfl

theorem constantMatrix_seed {α β : Type*} (M : Matrix α β ℂ) :
    (M.map (C : ℂ →+* TraceRing)).map seedEvaluation=M := by
  funext i j
  simp only [Matrix.map_apply,seedEvaluation,eval_C]

theorem directions_seed {ι : Type*} (B : Matrix FixedSexticParameters ι ℂ) :
    (directions B).map seedEvaluation=CycleQ2IncidenceSexticFamily.extendDirections B :=
  constantMatrix_seed _

theorem protectedOpen_seed {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix ParameterIndex ι ℂ)
    (hJ : P * seedJacobian ℂ (57:ℂ) Complex.I * B=1) :
    eval₂Hom seedEvaluation (seedEvaluation ∘ centre) (protectedOpen P B)=1 := by
  have hlead : eval (seedPoint (57:ℂ) Complex.I) (leadingProduct ℂ)=1 := by
    have h := CycleQ2IncidenceSexticFamily.family_seed_open
    rw [CycleQ2IncidenceSexticFamily.familyOpen,CycleQ2IncidenceSexticFamily.eval_familyMap] at h
    exact h
  have hdet : eval (seedPoint (57:ℂ) Complex.I)
      (retainedJacobian P B (presentation ℂ 57).equation).det=1 := by
    rw [RingHom.map_det]
    change ((retainedJacobian P B (presentation ℂ 57).equation).map
      (eval₂Hom (RingHom.id ℂ) (seedPoint (57:ℂ) Complex.I))).det=1
    rw [eval_retainedJacobian]
    change (P * seedJacobian ℂ (57:ℂ) Complex.I * B).det=1
    rw [hJ,Matrix.det_one]
  rw [protectedOpen,eval_coefficientMap,map_mul,map_mul,map_mul,hlead,
    actual_tracePolynomial_seed_one P B hJ,actual_projectiveTracePolynomial_seed_one P B hJ,
    hdet,one_mul,one_mul,one_mul]

theorem sextic_coordinate_fixed {S ι : Type*} [CommRing S] [Algebra TraceRing S]
    [Fintype ι] (B : Matrix FixedSexticParameters ι ℂ) (z : ι → S)
    (j : FullInvariantIndex 6) :
    pointValue (algebraMap TraceRing S) centre (directions B) z (Sum.inr (Sum.inl j)) =
      algebraMap TraceRing S (sexticParameter j) := by
  rw [pointValue_of_zero_row (algebraMap TraceRing S) centre (directions B) z
    (Sum.inr (Sum.inl j)) (by intro i; exact map_zero C)]
  rfl

end CycleQ2IncidenceTraceFamily

#print axioms CycleQ2IncidenceTraceFamily.protectedOpen_seed
#print axioms CycleQ2IncidenceTraceFamily.sextic_coordinate_fixed
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceTraceDerivative.lean -/
section
/-! The actual affine incidence family differentiates in the proved
trace-one direction when its external parameter has derivative one and
the sextic coefficients are fixed. The protected projective numerator
also excludes mere rescaling of the cubic. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceDerivative
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialRelations
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2PolynomialDerivationChainRule CycleQ2PolynomialImplicitTrace
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceProjectiveTrace
  CycleQ2PolynomialProjectiveTrace CycleQ2IncidenceTraceFamily

variable {S ι : Type*} [CommRing S] [Algebra TraceRing S]
  [Algebra ℂ S] [IsScalarTower ℂ TraceRing S]

theorem coefficient_scalar (c : ℂ) :
    algebraMap TraceRing S (C c)=algebraMap ℂ S c :=
  (IsScalarTower.algebraMap_apply ℂ TraceRing S c).symm

theorem coefficient_comp :
    (algebraMap TraceRing S).comp (C : ℂ →+* TraceRing)=algebraMap ℂ S := by
  ext c
  exact coefficient_scalar c

theorem eval_coefficient_map (y : ParameterIndex → S) (p : ParameterPolynomial ℂ) :
    aeval y (MvPolynomial.map (C : ℂ →+* TraceRing) p)=aeval y p := by
  change eval₂Hom (algebraMap TraceRing S) y (MvPolynomial.map C p)=
    eval₂Hom (algebraMap ℂ S) y p
  rw [eval₂Hom_map_hom,coefficient_comp]

theorem derivative_centre (D : Derivation ℂ S S)
    (ht : D (algebraMap TraceRing S traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing S (sexticParameter j))=0)
    (k : ParameterIndex) :
    D (algebraMap TraceRing S (centre k))=algebraMap ℂ S (parameterDirection k) := by
  rcases k with h | k
  · change D (algebraMap TraceRing S
      (C (seedCubicCoefficients Complex.I h)+traceParameter*C (parameterDirection (Sum.inl h))))=
        algebraMap ℂ S (parameterDirection (Sum.inl h))
    simp only [map_add,map_mul,coefficient_scalar,Derivation.leibniz,
      Derivation.map_algebraMap,ht,smul_eq_mul,mul_zero,mul_one,zero_add]
  · rcases k with f | ⟨⟨i,j⟩,e⟩
    · change D (algebraMap TraceRing S (sexticParameter f))=
        algebraMap ℂ S (parameterDirection (Sum.inr (Sum.inl f)))
      rw [parameterDirection_sextic,hF,map_zero]
    · change D (algebraMap TraceRing S
        (traceParameter*C (parameterDirection (Sum.inr (Sum.inr ((i,j),e))))))=
          algebraMap ℂ S (parameterDirection (Sum.inr (Sum.inr ((i,j),e))))
      simp only [map_mul,coefficient_scalar,Derivation.leibniz,
        Derivation.map_algebraMap,ht,smul_eq_mul,mul_zero,mul_one,zero_add]

theorem directions_scalar (B : Matrix FixedSexticParameters ι ℂ)
    (k : ParameterIndex) (j : ι) :
    algebraMap TraceRing S (directions B k j)=
      algebraMap ℂ S (CycleQ2IncidenceSexticFamily.extendDirections B k j) :=
  coefficient_scalar _

theorem derivative_point [Fintype ι] (D : Derivation ℂ S S)
    (ht : D (algebraMap TraceRing S traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing S (sexticParameter j))=0)
    (B : Matrix FixedSexticParameters ι ℂ) (z : ι → S) (k : ParameterIndex) :
    D (pointValue (algebraMap TraceRing S) centre (directions B) z k)=
      algebraMap ℂ S (parameterDirection k)+
        ((CycleQ2IncidenceSexticFamily.extendDirections B).map (algebraMap ℂ S) *ᵥ
          (fun j => D (z j))) k := by
  simp only [pointValue,directions_scalar,map_add,map_sum,Derivation.leibniz,
    Derivation.map_algebraMap,smul_eq_mul,mul_zero,add_zero,
    derivative_centre D ht hF,Matrix.mulVec,dotProduct,Matrix.map_apply]

theorem protectedOpen_components [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix ParameterIndex ι ℂ)
    (y : ParameterIndex → S)
    (ho : IsUnit (aeval y (protectedOpen P B))) :
    IsUnit (aeval y (leadingProduct ℂ)) ∧
      IsUnit (aeval y (tracePolynomial P B (presentation ℂ 57).equation
        traceWeights parameterDirection)) ∧
      IsUnit (aeval y (projectiveTracePolynomial P B (presentation ℂ 57).equation
        traceWeights leadingWeights parameterDirection)) ∧
      IsUnit (aeval y (retainedJacobian P B (presentation ℂ 57).equation).det) := by
  change IsUnit (aeval y (MvPolynomial.map C _)) at ho
  rw [eval_coefficient_map,map_mul,map_mul,map_mul] at ho
  have habc := isUnit_of_mul_isUnit_left ho
  have hab := isUnit_of_mul_isUnit_left habc
  exact ⟨isUnit_of_mul_isUnit_left hab,isUnit_of_mul_isUnit_right hab,
    isUnit_of_mul_isUnit_right habc,isUnit_of_mul_isUnit_right ho⟩

theorem actual_derivative_trace_isUnit [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ S S)
    (ht : D (algebraMap TraceRing S traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing S (sexticParameter j))=0)
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix FixedSexticParameters ι ℂ) (z : ι → S)
    (he : ∀ q, aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (equations q)=0)
    (ho : IsUnit (aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B)))) :
    IsUnit ((algebraMap ℂ S ∘ traceWeights) ⬝ᵥ
      (fun k => D (pointValue (algebraMap TraceRing S) centre (directions B) z k))) := by
  let y := pointValue (algebraMap TraceRing S) centre (directions B) z
  have he' (q : ColumnIndex) : aeval y ((presentation ℂ 57).equation q)=0 := by
    rw [← eval_coefficient_map]
    exact he q
  have hN := (protectedOpen_components P
    (CycleQ2IncidenceSexticFamily.extendDirections B) y ho).2.1
  exact derivative_trace_isUnit D y z P
    (CycleQ2IncidenceSexticFamily.extendDirections B) (presentation ℂ 57).equation
    traceWeights parameterDirection he' (derivative_point D ht hF B z) hN

theorem actual_derivative_projective_trace_isUnit [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ S S)
    (ht : D (algebraMap TraceRing S traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing S (sexticParameter j))=0)
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix FixedSexticParameters ι ℂ) (z : ι → S)
    (he : ∀ q, aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (equations q)=0)
    (ho : IsUnit (aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B)))) :
    let y := pointValue (algebraMap TraceRing S) centre (directions B) z
    IsUnit (y (Sum.inl fullCubicLeadingIndex)*
      D ((algebraMap ℂ S ∘ traceWeights) ⬝ᵥ y)-
      ((algebraMap ℂ S ∘ traceWeights) ⬝ᵥ y)*D (y (Sum.inl fullCubicLeadingIndex))) := by
  let y := pointValue (algebraMap TraceRing S) centre (directions B) z
  have he' (q : ColumnIndex) : aeval y ((presentation ℂ 57).equation q)=0 := by
    rw [←eval_coefficient_map]
    exact he q
  have hN := (protectedOpen_components P
    (CycleQ2IncidenceSexticFamily.extendDirections B) y ho).2.2.1
  simpa only [mapped_leadingWeights_formula] using
    derivative_projective_trace_isUnit D y z P
      (CycleQ2IncidenceSexticFamily.extendDirections B) (presentation ℂ 57).equation
      traceWeights leadingWeights parameterDirection he' (derivative_point D ht hF B z) hN

theorem actual_cubic_derivative_not_rescaling [Nontrivial S] [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ S S)
    (ht : D (algebraMap TraceRing S traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing S (sexticParameter j))=0)
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix FixedSexticParameters ι ℂ) (z : ι → S)
    (he : ∀ q, aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (equations q)=0)
    (ho : IsUnit (aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B)))) :
    ¬ ∃ a : S, ∀ j : FullInvariantIndex 3,
      D (pointValue (algebraMap TraceRing S) centre (directions B) z (Sum.inl j))=
        a*pointValue (algebraMap TraceRing S) centre (directions B) z (Sum.inl j) := by
  have hU := actual_derivative_projective_trace_isUnit D ht hF P B z he ho
  rintro ⟨a,ha⟩
  apply hU.ne_zero
  rw [derivation_linear_value,mapped_traceWeights_formula,mapped_traceWeights_formula,
    ha _,ha _,ha _]
  ring

theorem actual_normalized_trace_derivative_isUnit
    {K : Type*} [Field K] [Algebra TraceRing K]
    [Algebra ℂ K] [IsScalarTower ℂ TraceRing K] [Fintype ι] [DecidableEq ι]
    (D : Derivation ℂ K K)
    (ht : D (algebraMap TraceRing K traceParameter)=1)
    (hF : ∀ j, D (algebraMap TraceRing K (sexticParameter j))=0)
    (P : Matrix ι ColumnIndex ℂ) (B : Matrix FixedSexticParameters ι ℂ) (z : ι → K)
    (he : ∀ q, aeval (pointValue (algebraMap TraceRing K) centre (directions B) z)
      (equations q)=0)
    (ho : IsUnit (aeval (pointValue (algebraMap TraceRing K) centre (directions B) z)
      (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B)))) :
    let y := pointValue (algebraMap TraceRing K) centre (directions B) z
    IsUnit (D (((algebraMap ℂ K ∘ traceWeights) ⬝ᵥ y)/y (Sum.inl fullCubicLeadingIndex))) := by
  let y := pointValue (algebraMap TraceRing K) centre (directions B) z
  have hU := actual_derivative_projective_trace_isUnit D ht hF P B z he ho
  have hlead := (protectedOpen_components P
    (CycleQ2IncidenceSexticFamily.extendDirections B) y ho).1
  have hproduct : IsUnit (y (Sum.inl fullCubicLeadingIndex)*
      y (Sum.inr (Sum.inl fullSexticLeadingIndex))) := by
    simpa only [leadingProduct,map_mul,aeval_X] using hlead
  have hleading := isUnit_of_mul_isUnit_left hproduct
  change IsUnit (D (((algebraMap ℂ K ∘ traceWeights) ⬝ᵥ y)/_))
  rw [Derivation.leibniz_div]
  change IsUnit ((y (Sum.inl fullCubicLeadingIndex))⁻¹^2*
    (y (Sum.inl fullCubicLeadingIndex)*D ((algebraMap ℂ K ∘ traceWeights) ⬝ᵥ y)-
      ((algebraMap ℂ K ∘ traceWeights) ⬝ᵥ y)*D (y (Sum.inl fullCubicLeadingIndex))))
  apply isUnit_iff_ne_zero.mpr
  exact mul_ne_zero (pow_ne_zero 2 (inv_ne_zero hleading.ne_zero)) hU.ne_zero

end CycleQ2IncidenceTraceDerivative

#print axioms CycleQ2IncidenceTraceDerivative.derivative_centre
#print axioms CycleQ2IncidenceTraceDerivative.actual_derivative_trace_isUnit
#print axioms CycleQ2IncidenceTraceDerivative.actual_cubic_derivative_not_rescaling
#print axioms CycleQ2IncidenceTraceDerivative.actual_normalized_trace_derivative_isUnit
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceTraceFieldDerivation.lean -/
section
/-! The external parameter derivative is constructed through the actual
fraction field and every finite field extension.  No derivative on the
finite field, or compatibility assumption for it, is supplied as input. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceFieldDerivation
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDerivative

abbrev TraceField := FractionRing TraceRing

local instance : Algebra ℤ TraceRing := Ring.toIntAlgebra _
local instance : Algebra ℤ TraceField := Ring.toIntAlgebra _

def polynomialTime : Derivation ℤ TraceRing TraceRing :=
  (pderiv (Sum.inl ()) : Derivation ℂ TraceRing TraceRing).restrictScalars ℤ

def fractionTime : Derivation ℤ TraceField TraceField :=
  HoldoutConstruction.extendRingDerivation (P := TraceRing) (L := TraceField) polynomialTime

section FiniteField

variable {L : Type*} [Field L] [Algebra TraceField L]
  [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
  [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]

def finiteTime : Derivation ℤ L L :=
  HoldoutConstruction.extendFiniteDerivation (K := TraceField) (L := L) fractionTime

omit [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] in
theorem finiteTime_polynomial (p : TraceRing) :
    finiteTime (algebraMap TraceRing L p)=
      algebraMap TraceRing L (pderiv (Sum.inl ()) p) := by
  rw [IsScalarTower.algebraMap_apply TraceRing TraceField L,finiteTime,
    HoldoutConstruction.extendFiniteDerivation_apply,fractionTime,
    HoldoutConstruction.extendRingDerivation_apply]
  exact (IsScalarTower.algebraMap_apply TraceRing TraceField L _).symm

theorem finiteTime_constant (c : ℂ) : finiteTime (algebraMap ℂ L c)=0 := by
  rw [←coefficient_scalar,finiteTime_polynomial,pderiv_C,map_zero]

/-- The finite extension derivative is complex-linear because it fixes
the original complex constants. -/
def timeDerivation : Derivation ℂ L L where
  toFun := finiteTime
  map_add' := finiteTime.map_add
  map_smul' c x := by
    simp only [Algebra.smul_def,Derivation.leibniz,finiteTime_constant,
      mul_zero,add_zero,Algebra.algebraMap_self,RingHom.id_apply]
  map_one_eq_zero' := finiteTime.map_one_eq_zero
  leibniz' := finiteTime.leibniz

theorem timeDerivation_polynomial (p : TraceRing) :
    timeDerivation (algebraMap TraceRing L p)=
      algebraMap TraceRing L (pderiv (Sum.inl ()) p) :=
  finiteTime_polynomial p

theorem timeDerivation_traceParameter :
    timeDerivation (algebraMap TraceRing L traceParameter)=1 := by
  rw [timeDerivation_polynomial,traceParameter,pderiv_X_self,map_one]

theorem timeDerivation_sexticParameter (j : FullInvariantIndex 6) :
    timeDerivation (algebraMap TraceRing L (sexticParameter j))=0 := by
  rw [timeDerivation_polynomial,sexticParameter,pderiv_X_of_ne (by simp),map_zero]

end FiniteField
end CycleQ2IncidenceTraceFieldDerivation

#print axioms CycleQ2IncidenceTraceFieldDerivation.timeDerivation_polynomial
#print axioms CycleQ2IncidenceTraceFieldDerivation.timeDerivation_traceParameter
#print axioms CycleQ2IncidenceTraceFieldDerivation.timeDerivation_sexticParameter
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceTraceGenericPoint.lean -/
section
/-! A finite generic incidence point with an actual nonzero parameter
derivative.  The external parameter follows the proved trace-one tangent;
all independent sextic coefficients remain fixed under that derivative.
An arbitrary additional original-parameter open may be preserved, so the
actual basepoint-free open can be included without repeating the lifting. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace CycleQ2IncidenceTraceGenericPoint
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2CompatibleEquationCoordinates CycleQ2CompatibleAffineGenericLifting
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceDirection
  CycleQ2IncidenceTraceDerivative CycleQ2IncidenceTraceFieldDerivation
open CycleQ2IncidenceCompatibleGenericPoint (fixedJacobian literalRelations SquareIndex ComplementIndex)

def totalOpen (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ) :=
  protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B) * MvPolynomial.map (C : ℂ →+* TraceRing) c

def GenericTraceAlgebra
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (V : Matrix ColumnIndex ComplementIndex ℂ)
    (T₀ : Matrix ComplementIndex RelationIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ) : Type :=
  GenericAlgebra TraceField centre (directions B) (P.map (C : ℂ →+* TraceRing))
    (T₀.map (C : ℂ →+* TraceRing)) relations (V.map (C : ℂ →+* TraceRing)) equations (totalOpen P B c)

section AlgebraInstances
variable (P : Matrix SquareIndex ColumnIndex ℂ)
  (V : Matrix ColumnIndex ComplementIndex ℂ)
  (T₀ : Matrix ComplementIndex RelationIndex ℂ)
  (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)

instance genericTraceCommRing : CommRing (GenericTraceAlgebra P V T₀ B c) :=
  inferInstanceAs (CommRing (GenericAlgebra TraceField centre (directions B)
    (P.map (C : ℂ →+* TraceRing)) (T₀.map (C : ℂ →+* TraceRing)) relations
    (V.map (C : ℂ →+* TraceRing)) equations (totalOpen P B c)))

instance genericTraceFieldAlgebra : Algebra TraceField (GenericTraceAlgebra P V T₀ B c) :=
  inferInstanceAs (Algebra TraceField (GenericAlgebra TraceField centre (directions B)
    (P.map (C : ℂ →+* TraceRing)) (T₀.map (C : ℂ →+* TraceRing)) relations
    (V.map (C : ℂ →+* TraceRing)) equations (totalOpen P B c)))

instance genericTraceRingAlgebra : Algebra TraceRing (GenericTraceAlgebra P V T₀ B c) :=
  inferInstanceAs (Algebra TraceRing (GenericAlgebra TraceField centre (directions B)
    (P.map (C : ℂ →+* TraceRing)) (T₀.map (C : ℂ →+* TraceRing)) relations
    (V.map (C : ℂ →+* TraceRing)) equations (totalOpen P B c)))

instance genericTraceScalarTower :
    IsScalarTower TraceRing TraceField (GenericTraceAlgebra P V T₀ B c) :=
  inferInstanceAs (IsScalarTower TraceRing TraceField
    (GenericAlgebra TraceField centre (directions B)
      (P.map (C : ℂ →+* TraceRing)) (T₀.map (C : ℂ →+* TraceRing)) relations
      (V.map (C : ℂ →+* TraceRing)) equations (totalOpen P B c)))

end AlgebraInstances

def IsTracePoint {S : Type*} [CommRing S] [Algebra TraceRing S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) : Prop :=
  let y := pointValue (algebraMap TraceRing S) centre (directions B) z
  (∀ q, aeval y (equations q)=0) ∧
  IsUnit (aeval y (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B))) ∧
  IsUnit (aeval y (MvPolynomial.map (C : ℂ →+* TraceRing) c)) ∧
  ∀ q : FullInvariantIndex 6,
    y (Sum.inr (Sum.inl q))=algebraMap TraceRing S (sexticParameter q)

/-- The selected generic component specializes to the actual seed.  This
is expressed on the original polynomial parameter ring; it does not assert
a field homomorphism from the generic field to the special field. -/
def IsPointedTracePoint {S : Type*} [CommRing S] [Algebra TraceRing S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) : Prop :=
  IsTracePoint P B c z ∧
    ∀ p : MvPolynomial ParameterIndex TraceRing,
      aeval (pointValue (algebraMap TraceRing S) centre (directions B) z) p=0 →
        eval₂Hom seedEvaluation (seedEvaluation ∘ centre) p=0

theorem isTracePoint_of_lift {S : Type*} [CommRing S] [Algebra TraceRing S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S)
    (he : ∀ q, aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (equations q)=0)
    (ho : IsUnit (aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
      (totalOpen P B c))) : IsTracePoint P B c z := by
  let φ : MvPolynomial ParameterIndex TraceRing →ₐ[TraceRing] S :=
    aeval (pointValue (algebraMap TraceRing S) centre (directions B) z)
  have ho' := (congrArg IsUnit (φ.map_mul
    (protectedOpen P (CycleQ2IncidenceSexticFamily.extendDirections B))
    (MvPolynomial.map (C : ℂ →+* TraceRing) c))).mp ho
  exact ⟨he,isUnit_of_mul_isUnit_left ho',isUnit_of_mul_isUnit_right ho',
    sextic_coordinate_fixed B z⟩

/-- Choosing the finite splitting separately prevents dependent elimination
from unfolding the later tensor-product and maximal-ideal quotient. -/
private structure SeedSplit where
  P : Matrix SquareIndex ColumnIndex ℂ
  Q : Matrix ColumnIndex SquareIndex ℂ
  V : Matrix ColumnIndex ComplementIndex ℂ
  W : Matrix ComplementIndex ColumnIndex ℂ
  T₀ : Matrix ComplementIndex RelationIndex ℂ
  B : Matrix FixedSexticParameters SquareIndex ℂ
  decomposition : Q*P+V*W=1
  jacobian : P*fixedJacobian*B=1
  complement : T₀*literalRelations*V=1

private theorem nonemptySeedSplit
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations)) : Nonempty SeedSplit := by
  obtain ⟨P,Q,V,W,T₀,B,hdecomp,hjac,hcomplement,_,_⟩ :=
    CycleQ2LinearExactSequenceSplit.exists_matrix_split fixedJacobian literalRelations hexact
  exact ⟨⟨P,Q,V,W,T₀,B,hdecomp,hjac,hcomplement⟩⟩

private def chooseSeedSplit
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations)) : SeedSplit :=
  Classical.choice (nonemptySeedSplit hexact)

theorem finite_pointed_trace_point_of_exactness
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations))
    (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57:ℂ) Complex.I) c=1) :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B c)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B c) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B c) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B c) ⧸ I),
        IsPointedTracePoint P B c z := by
  let s := chooseSeedSplit hexact
  let P := s.P
  let Q := s.Q
  let V := s.V
  let W := s.W
  let T₀ := s.T₀
  let B := s.B
  have hdecomp : Q*P+V*W=1 := s.decomposition
  have hjac : P*fixedJacobian*B=1 := s.jacobian
  have hcomplement : T₀*literalRelations*V=1 := s.complement
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  have hjacFull : P * seedJacobian ℂ (57:ℂ) Complex.I *
      CycleQ2IncidenceSexticFamily.extendDirections B=1 := by
    rw [Matrix.mul_assoc,CycleQ2IncidenceSexticFamily.jacobian_extendDirections,
      ←Matrix.mul_assoc]
    exact hjac
  have hjac' : (P.map (C : ℂ →+* TraceRing)).map seedEvaluation *
      jacobian seedEvaluation (seedEvaluation ∘ centre) equations *
      (directions B).map seedEvaluation=1 := by
    rw [constantMatrix_seed,seed_jacobian,directions_seed]
    exact hjacFull
  have hcomplement' : (T₀.map (C : ℂ →+* TraceRing)).map seedEvaluation *
      relations.map (eval₂Hom seedEvaluation (seedEvaluation ∘ centre)) *
      (V.map (C : ℂ →+* TraceRing)).map seedEvaluation=1 := by
    rw [constantMatrix_seed,constantMatrix_seed,seed_relation]
    exact hcomplement
  have hopen : IsUnit (eval₂Hom seedEvaluation (seedEvaluation ∘ centre) (totalOpen P B c)) := by
    rw [totalOpen,map_mul,protectedOpen_seed P _ hjacFull,eval_coefficientMap,hc,one_mul]
    exact isUnit_one
  obtain ⟨I,hI,hfinite,hseparable,z,he,ho,hspecializes⟩ :=
    CycleQ2PointedCompatibleAffineLifting.pointed_lift_all_on_compatible_affine_slice (R := TraceRing) (T := ℂ) (K := TraceField)
      (σ := ParameterIndex) (ι := SquareIndex) (m := ColumnIndex)
      (κ := ComplementIndex) (l := RelationIndex)
      centre (directions B) (P.map (C : ℂ →+* TraceRing)) (Q.map (C : ℂ →+* TraceRing)) (V.map (C : ℂ →+* TraceRing)) (W.map (C : ℂ →+* TraceRing))
      (T₀.map (C : ℂ →+* TraceRing)) relations equations (totalOpen P B c)
      (mapped_decomposition (C : ℂ →+* TraceRing) P Q V W hdecomp) relation_identity
      seed_zero hjac' hcomplement' hopen
  exact ⟨P,V,T₀,B,I,hI,hfinite,hseparable,z,
    isTracePoint_of_lift P B c z he ho,hspecializes⟩

theorem finite_trace_point_of_exactness
    (hexact : LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations))
    (c : ParameterPolynomial ℂ)
    (hc : eval (seedPoint (57:ℂ) Complex.I) c=1) :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B c)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B c) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B c) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B c) ⧸ I),
        IsTracePoint P B c z := by
  obtain ⟨P,V,T₀,B,I,hI,hfinite,hseparable,z,hz⟩ :=
    finite_pointed_trace_point_of_exactness hexact c hc
  exact ⟨P,V,T₀,B,I,hI,hfinite,hseparable,z,hz.1⟩

/-- On every finite field realization of the actual trace point, the
canonically extended external derivative has nonzero fixed linear trace. -/
theorem tracePoint_derivative_isUnit {L : Type*} [Field L] [Algebra TraceField L]
    [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
    [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → L) (hz : IsTracePoint P B c z) :
    IsUnit ((algebraMap ℂ L ∘ traceWeights) ⬝ᵥ
      (fun k => timeDerivation
        (pointValue (algebraMap TraceRing L) centre (directions B) z k))) :=
  actual_derivative_trace_isUnit timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter P B z hz.1 hz.2.1


/-- The canonical external derivation changes the cubic modulo its scalar
rescaling direction.  This is an algebraic motion statement; it does not
identify an Abel--Jacobi or cylinder map. -/
theorem tracePoint_cubic_derivative_not_rescaling
    {L : Type*} [Field L] [Algebra TraceField L]
    [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
    [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → L) (hz : IsTracePoint P B c z) :
    ¬ ∃ a : L, ∀ j : FullInvariantIndex 3,
      timeDerivation
        (pointValue (algebraMap TraceRing L) centre (directions B) z (Sum.inl j))=
      a*pointValue (algebraMap TraceRing L) centre (directions B) z (Sum.inl j) :=
  actual_cubic_derivative_not_rescaling timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter P B z hz.1 hz.2.1

/-- Dividing by the nonzero leading cubic coefficient gives an actual
coefficient function with nonzero canonical derivative. -/
theorem tracePoint_normalized_derivative_isUnit
    {L : Type*} [Field L] [Algebra TraceField L]
    [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
    [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → L) (hz : IsTracePoint P B c z) :
    let y := pointValue (algebraMap TraceRing L) centre (directions B) z
    IsUnit (timeDerivation
      (((algebraMap ℂ L ∘ traceWeights) ⬝ᵥ y)/y (Sum.inl fullCubicLeadingIndex))) :=
  actual_normalized_trace_derivative_isUnit timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter P B z hz.1 hz.2.1

end CycleQ2IncidenceTraceGenericPoint

#print axioms CycleQ2IncidenceTraceGenericPoint.finite_trace_point_of_exactness
#print axioms CycleQ2IncidenceTraceGenericPoint.tracePoint_derivative_isUnit

#print axioms CycleQ2IncidenceTraceGenericPoint.tracePoint_cubic_derivative_not_rescaling
#print axioms CycleQ2IncidenceTraceGenericPoint.tracePoint_normalized_derivative_isUnit

#print axioms CycleQ2IncidenceTraceGenericPoint.finite_pointed_trace_point_of_exactness
end
end


