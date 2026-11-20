import Proposal.GradedCurveRestriction
import Proposal.SegreGradedCechComplex

/-!
# Čech spaces and differentials for the Segre factor sequence
-/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/ModularFactorGraded.lean -/
section
/-! # Graded factor lifts on the literal modular seed

Every degree-14 invariant cofactor-kernel section has factor lifts of
left degree 10, character 0, and right degree 8, character 1. The proof
clears denominators, projects the original polynomial grading, and uses
the proved homogeneous closure of the actual linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2ModularFactorGraded

open CycleQ2IncidenceGaussianArithmetic

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SeedLocalizedProjection CycleQ2SeedFactorHomogeneous
  CycleQ2SegreFactorExact CycleQ2SegreFactorSequence CycleQ2ModularFactorChartExact

abbrev LeftGrade (s : Finset (Fin 3)) (v : Fin 3 → Chart s) : Prop :=
  ∀ i, HasLocalGrade F109 57 33 s (10,0) (v i)

abbrev RightGrade (s : Finset (Fin 3)) (w : Fin 3 → Chart s) : Prop :=
  ∀ j, HasLocalGrade F109 57 33 s (8,1) (w j)

abbrev MatrixGrade (s : Finset (Fin 3)) (N : Matrix (Fin 3) (Fin 3) (Chart s)) : Prop :=
  ∀ i j, HasLocalGrade F109 57 33 s (14,0) (N i j)

theorem leftSection_grade (s : Finset (Fin 3)) (i : Fin 3) :
    HasLocalGrade F109 57 33 s (10,0) (leftSection s i) :=
  polynomial_hasLocalGrade F109 57 33 s (polynomialLeft 57 i) (10,0)
    (polynomialLeft_homogeneous 57 i)

theorem rightSection_grade (s : Finset (Fin 3)) (j : Fin 3) :
    HasLocalGrade F109 57 33 s (8,1) (rightSection s j) :=
  polynomial_hasLocalGrade F109 57 33 s (polynomialRight 57 j) (8,1)
    (polynomialRight_homogeneous 57 j)

theorem linkage_grade (s : Finset (Fin 3)) :
    HasLocalGrade F109 57 33 s (4,1) (linkage s) :=
  polynomial_hasLocalGrade F109 57 33 s (polynomialLinkage 57) (4,1)
    (polynomialLinkage_homogeneous 57)

/-- The actual factor map sends the required factor grades to degree-14
invariant matrix sections. -/
theorem chartFactorMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (hv : LeftGrade s (fun i => (v.1 i:Chart s)))
    (hw : RightGrade s (fun j => (v.2 j:Chart s))) :
    MatrixGrade s (chartFactorMap s hs v) := by
  intro i j
  apply regular_division_hasLocalGrade F109 57 33 s (polynomialLinkage 57)
    (4,1) (14,0) (polynomialLinkage_homogeneous 57) (linkage_regular s)
  change HasLocalGrade F109 57 33 s (18,1)
    (linkage s*chartFactorMap s hs v i j)
  rw [chartFactorMap_formula]
  apply hasLocalGrade_add F109 57 33 s (18,1)
  · exact hasLocalGrade_mul F109 57 33 s (10,0) (8,1)
      _ _ (hv i) (rightSection_grade s j)
  · exact hasLocalGrade_mul F109 57 33 s (10,0) (8,1)
      _ _ (leftSection_grade s i) (hw j)

/-- Actual graded local factor exactness. Only membership in the cofactor
kernel and the target grade are supplied; ideal-valued graded lifts are
constructed from the literal seed equations. -/
theorem exists_graded_factor_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (N : Matrix (Fin 3) (Fin 3) (Chart s))
    (hN : cofactorDifferential (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s) N=0)
    (hNg : MatrixGrade s N) :
    ∃ v w : Fin 3 → Chart s,
      (∀ i, v i∈leftIdeal s) ∧ (∀ j, w j∈rightIdeal s) ∧
      LeftGrade s v ∧ RightGrade s w ∧
      ∀ i j, v i*rightSection s j+leftSection s i*w j=linkage s*N i j := by
  let F := factorData s hs
  obtain ⟨v,w,hv,hw,he⟩ := exists_factor_lift F.leftIdeal F.rightIdeal F.linkage
    F.matrix N F.left F.right F.left_mem F.right_mem F.product
    F.cofactors_zero hN F.entries_generate
  change ∀ i j, v i*rightSection s j+leftSection s i*w j=linkage s*N i j at he
  let f := polynomialMap F109 57 33 s
  let T : Matrix (Fin 3) (Fin 3) (Chart s) := fun i j => if i=0 then v j else w j
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator F109 57 33 s T
  let a := f (openPolynomial F109 s^n)
  let V : Fin 3 → Poly F109 := fun i => P 0 i
  let W : Fin 3 → Poly F109 := fun j => P 1 j
  have hV (i : Fin 3) : f (V i)=a*v i := by simpa only [T,ite_true] using hP 0 i
  have hW (j : Fin 3) : f (W j)=a*w j := by
    have hh := hP 1 j
    change f (W j)=a*(if (1:Fin 3)=0 then v j else w j) at hh
    rw [if_neg (by decide)] at hh
    exact hh
  have hVmem (i : Fin 3) : f (V i)∈leftIdeal s := by
    rw [hV]
    exact (leftIdeal s).mul_mem_left a (hv i)
  have hWmem (j : Fin 3) : f (W j)∈rightIdeal s := by
    rw [hW]
    exact (rightIdeal s).mul_mem_left a (hw j)
  let d : Grade := n • openGrade s
  let V' : Fin 3 → Poly F109 := fun i => weightedHomogeneousComponent fullGrading (d+(10,0)) (V i)
  let W' : Fin 3 → Poly F109 := fun j => weightedHomogeneousComponent fullGrading (d+(8,1)) (W j)
  have hnum (i j : Fin 3) :
      f (V i*polynomialRight 57 j+polynomialLeft 57 i*W j)=a*(linkage s*N i j) := by
    calc
      _ = f (V i)*rightSection s j+leftSection s i*f (W j) := by
        rw [map_add,map_mul,map_mul]
        rfl
      _ = a*(v i*rightSection s j+leftSection s i*w j) := by rw [hV,hW]; ring
      _ = a*(linkage s*N i j) := by rw [he i j]
  have hnumGrade (i j : Fin 3) : HasLocalGrade F109 57 33 s (d+(18,1))
      (f (V i*polynomialRight 57 j+polynomialLeft 57 i*W j)) := by
    rw [hnum]
    apply hasLocalGrade_mul F109 57 33 s d (18,1)
    · exact polynomial_hasLocalGrade F109 57 33 s _ _
        ((openPolynomial_homogeneous F109 s).pow n)
    · exact hasLocalGrade_mul F109 57 33 s (4,1) (14,0)
        _ _ (linkage_grade s) (hNg i j)
  have hproj (i j : Fin 3) :
      f (V' i)*rightSection s j+leftSection s i*f (W' j)=a*(linkage s*N i j) := by
    have hc := component_eq_of_homogeneous_image F109 57 33 s
      (V i*polynomialRight 57 j+polynomialLeft 57 i*W j) (d+(18,1)) (hnumGrade i j)
    rw [numerator_component] at hc
    have hh := hc.trans (hnum i j)
    rw [map_add,map_mul,map_mul] at hh
    exact hh
  have hV'mem (i : Fin 3) : f (V' i)∈leftIdeal s :=
    CycleQ2SeedLinkageGrading.localized_component_mem .left 57 33 s
      (V i) (d+(10,0)) (hVmem i)
  have hW'mem (j : Fin 3) : f (W' j)∈rightIdeal s :=
    CycleQ2SeedLinkageGrading.localized_component_mem .right 57 33 s
      (W j) (d+(8,1)) (hWmem j)
  have ha : IsUnit a := by
    simpa only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Chart s)
        (algebraMap (CycleQ2SeedQuotientFiniteFree.Base F109) (SeedRing (57:F109) 33)
          (CycleQ2SeedCechLocalization.baseProduct F109 s)) n)
  obtain ⟨u,hu⟩ := ha
  let v' : Fin 3 → Chart s := fun i => (↑(u⁻¹):Chart s)*f (V' i)
  let w' : Fin 3 → Chart s := fun j => (↑(u⁻¹):Chart s)*f (W' j)
  have hVden (i : Fin 3) : f (V' i)=a*v' i := by
    change f (V' i)=a*((↑(u⁻¹):Chart s)*f (V' i))
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]
  have hWden (j : Fin 3) : f (W' j)=a*w' j := by
    change f (W' j)=a*((↑(u⁻¹):Chart s)*f (W' j))
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]
  refine ⟨v',w',?_,?_,?_,?_,?_⟩
  · intro i
    exact (leftIdeal s).mul_mem_left _ (hV'mem i)
  · intro j
    exact (rightIdeal s).mul_mem_left _ (hW'mem j)
  · intro i
    exact fraction_hasLocalGrade F109 57 33 s (v' i) (10,0) n (V' i)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hVden i)
  · intro j
    exact fraction_hasLocalGrade F109 57 33 s (w' j) (8,1) n (W' j)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWden j)
  · intro i j
    calc
      v' i*rightSection s j+leftSection s i*w' j=
          (↑(u⁻¹):Chart s)*(f (V' i)*rightSection s j+leftSection s i*f (W' j)) := by
        dsimp only [v',w']
        ring
      _ = (↑(u⁻¹):Chart s)*(a*(linkage s*N i j)) := by rw [hproj]
      _ = linkage s*N i j := by rw [← hu,← mul_assoc,u.inv_mul,one_mul]

end CycleQ2ModularFactorGraded

#print axioms CycleQ2ModularFactorGraded.chartFactorMap_grade
#print axioms CycleQ2ModularFactorGraded.exists_graded_factor_lift
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorGraded.lean -/
section
/-! # Graded factor lifts on the literal complex seed

Every degree-14 invariant cofactor-kernel section has factor lifts of
left degree 10, character 0, and right degree 8, character 1. The proof
clears denominators, projects the original polynomial grading, and uses
the proved homogeneous closure of the actual linkage ideals.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2SegreFactorGraded

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SeedLocalizedProjection CycleQ2SeedFactorHomogeneous
  CycleQ2SegreFactorExact CycleQ2SegreFactorSequence CycleQ2SegreFactorChartExact

abbrev LeftGrade (s : Finset (Fin 3)) (v : Fin 3 → Chart s) : Prop :=
  ∀ i, HasLocalGrade ℂ 57 Complex.I s (10,0) (v i)

abbrev RightGrade (s : Finset (Fin 3)) (w : Fin 3 → Chart s) : Prop :=
  ∀ j, HasLocalGrade ℂ 57 Complex.I s (8,1) (w j)

abbrev MatrixGrade (s : Finset (Fin 3)) (N : Matrix (Fin 3) (Fin 3) (Chart s)) : Prop :=
  ∀ i j, HasLocalGrade ℂ 57 Complex.I s (14,0) (N i j)

theorem leftSection_grade (s : Finset (Fin 3)) (i : Fin 3) :
    HasLocalGrade ℂ 57 Complex.I s (10,0) (leftSection s i) :=
  polynomial_hasLocalGrade ℂ 57 Complex.I s (polynomialLeft 57 i) (10,0)
    (polynomialLeft_homogeneous 57 i)

theorem rightSection_grade (s : Finset (Fin 3)) (j : Fin 3) :
    HasLocalGrade ℂ 57 Complex.I s (8,1) (rightSection s j) :=
  polynomial_hasLocalGrade ℂ 57 Complex.I s (polynomialRight 57 j) (8,1)
    (polynomialRight_homogeneous 57 j)

theorem linkage_grade (s : Finset (Fin 3)) :
    HasLocalGrade ℂ 57 Complex.I s (4,1) (linkage s) :=
  polynomial_hasLocalGrade ℂ 57 Complex.I s (polynomialLinkage 57) (4,1)
    (polynomialLinkage_homogeneous 57)

/-- The actual factor map sends the required factor grades to degree-14
invariant matrix sections. -/
theorem chartFactorMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : FactorSections s) (hv : LeftGrade s (fun i => (v.1 i:Chart s)))
    (hw : RightGrade s (fun j => (v.2 j:Chart s))) :
    MatrixGrade s (chartFactorMap s hs v) := by
  intro i j
  apply regular_division_hasLocalGrade ℂ 57 Complex.I s (polynomialLinkage 57)
    (4,1) (14,0) (polynomialLinkage_homogeneous 57) (linkage_regular s)
  change HasLocalGrade ℂ 57 Complex.I s (18,1)
    (linkage s*chartFactorMap s hs v i j)
  rw [chartFactorMap_formula]
  apply hasLocalGrade_add ℂ 57 Complex.I s (18,1)
  · exact hasLocalGrade_mul ℂ 57 Complex.I s (10,0) (8,1)
      _ _ (hv i) (rightSection_grade s j)
  · exact hasLocalGrade_mul ℂ 57 Complex.I s (10,0) (8,1)
      _ _ (leftSection_grade s i) (hw j)

/-- Actual graded local factor exactness. Only membership in the cofactor
kernel and the target grade are supplied; ideal-valued graded lifts are
constructed from the literal seed equations. -/
theorem exists_graded_factor_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (N : Matrix (Fin 3) (Fin 3) (Chart s))
    (hN : cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) N=0)
    (hNg : MatrixGrade s N) :
    ∃ v w : Fin 3 → Chart s,
      (∀ i, v i∈leftIdeal s) ∧ (∀ j, w j∈rightIdeal s) ∧
      LeftGrade s v ∧ RightGrade s w ∧
      ∀ i j, v i*rightSection s j+leftSection s i*w j=linkage s*N i j := by
  let F := factorData s hs
  obtain ⟨v,w,hv,hw,he⟩ := exists_factor_lift F.leftIdeal F.rightIdeal F.linkage
    F.matrix N F.left F.right F.left_mem F.right_mem F.product
    F.cofactors_zero hN F.entries_generate
  change ∀ i j, v i*rightSection s j+leftSection s i*w j=linkage s*N i j at he
  let f := polynomialMap ℂ 57 Complex.I s
  let T : Matrix (Fin 3) (Fin 3) (Chart s) := fun i j => if i=0 then v j else w j
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator ℂ 57 Complex.I s T
  let a := f (openPolynomial ℂ s^n)
  let V : Fin 3 → Poly ℂ := fun i => P 0 i
  let W : Fin 3 → Poly ℂ := fun j => P 1 j
  have hV (i : Fin 3) : f (V i)=a*v i := by simpa only [T,ite_true] using hP 0 i
  have hW (j : Fin 3) : f (W j)=a*w j := by
    have hh := hP 1 j
    change f (W j)=a*(if (1:Fin 3)=0 then v j else w j) at hh
    rw [if_neg (by decide)] at hh
    exact hh
  have hVmem (i : Fin 3) : f (V i)∈leftIdeal s := by
    rw [hV]
    exact (leftIdeal s).mul_mem_left a (hv i)
  have hWmem (j : Fin 3) : f (W j)∈rightIdeal s := by
    rw [hW]
    exact (rightIdeal s).mul_mem_left a (hw j)
  let d : Grade := n • openGrade s
  let V' : Fin 3 → Poly ℂ := fun i => weightedHomogeneousComponent fullGrading (d+(10,0)) (V i)
  let W' : Fin 3 → Poly ℂ := fun j => weightedHomogeneousComponent fullGrading (d+(8,1)) (W j)
  have hnum (i j : Fin 3) :
      f (V i*polynomialRight 57 j+polynomialLeft 57 i*W j)=a*(linkage s*N i j) := by
    calc
      _ = f (V i)*rightSection s j+leftSection s i*f (W j) := by
        rw [map_add,map_mul,map_mul]
        rfl
      _ = a*(v i*rightSection s j+leftSection s i*w j) := by rw [hV,hW]; ring
      _ = a*(linkage s*N i j) := by rw [he i j]
  have hnumGrade (i j : Fin 3) : HasLocalGrade ℂ 57 Complex.I s (d+(18,1))
      (f (V i*polynomialRight 57 j+polynomialLeft 57 i*W j)) := by
    rw [hnum]
    apply hasLocalGrade_mul ℂ 57 Complex.I s d (18,1)
    · exact polynomial_hasLocalGrade ℂ 57 Complex.I s _ _
        ((openPolynomial_homogeneous ℂ s).pow n)
    · exact hasLocalGrade_mul ℂ 57 Complex.I s (4,1) (14,0)
        _ _ (linkage_grade s) (hNg i j)
  have hproj (i j : Fin 3) :
      f (V' i)*rightSection s j+leftSection s i*f (W' j)=a*(linkage s*N i j) := by
    have hc := component_eq_of_homogeneous_image ℂ 57 Complex.I s
      (V i*polynomialRight 57 j+polynomialLeft 57 i*W j) (d+(18,1)) (hnumGrade i j)
    rw [numerator_component] at hc
    have hh := hc.trans (hnum i j)
    rw [map_add,map_mul,map_mul] at hh
    exact hh
  have hV'mem (i : Fin 3) : f (V' i)∈leftIdeal s :=
    CycleQ2SeedLinkageGrading.localized_component_mem .left 57 Complex.I s
      (V i) (d+(10,0)) (hVmem i)
  have hW'mem (j : Fin 3) : f (W' j)∈rightIdeal s :=
    CycleQ2SeedLinkageGrading.localized_component_mem .right 57 Complex.I s
      (W j) (d+(8,1)) (hWmem j)
  have ha : IsUnit a := by
    simpa only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Chart s)
        (algebraMap (CycleQ2SeedQuotientFiniteFree.Base ℂ) (SeedRing (57:ℂ) Complex.I)
          (CycleQ2SeedCechLocalization.baseProduct ℂ s)) n)
  obtain ⟨u,hu⟩ := ha
  let v' : Fin 3 → Chart s := fun i => (↑(u⁻¹):Chart s)*f (V' i)
  let w' : Fin 3 → Chart s := fun j => (↑(u⁻¹):Chart s)*f (W' j)
  have hVden (i : Fin 3) : f (V' i)=a*v' i := by
    change f (V' i)=a*((↑(u⁻¹):Chart s)*f (V' i))
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]
  have hWden (j : Fin 3) : f (W' j)=a*w' j := by
    change f (W' j)=a*((↑(u⁻¹):Chart s)*f (W' j))
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]
  refine ⟨v',w',?_,?_,?_,?_,?_⟩
  · intro i
    exact (leftIdeal s).mul_mem_left _ (hV'mem i)
  · intro j
    exact (rightIdeal s).mul_mem_left _ (hW'mem j)
  · intro i
    exact fraction_hasLocalGrade ℂ 57 Complex.I s (v' i) (10,0) n (V' i)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hVden i)
  · intro j
    exact fraction_hasLocalGrade ℂ 57 Complex.I s (w' j) (8,1) n (W' j)
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _) (hWden j)
  · intro i j
    calc
      v' i*rightSection s j+leftSection s i*w' j=
          (↑(u⁻¹):Chart s)*(f (V' i)*rightSection s j+leftSection s i*f (W' j)) := by
        dsimp only [v',w']
        ring
      _ = (↑(u⁻¹):Chart s)*(a*(linkage s*N i j)) := by rw [hproj]
      _ = linkage s*N i j := by rw [← hu,← mul_assoc,u.inv_mul,one_mul]

end CycleQ2SegreFactorGraded

#print axioms CycleQ2SegreFactorGraded.chartFactorMap_grade
#print axioms CycleQ2SegreFactorGraded.exists_graded_factor_lift
end
end

/- Component: continuation_3/cylinder_bridge/ModularFactorGauge.lean -/
section
/-! # The scalar gauge has the actual degree-zero grade -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2ModularFactorGraded

open CycleQ2IncidenceGaussianArithmetic

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SeedLocalizedProjection CycleQ2SeedFactorHomogeneous CycleQ2WeightedComponent
  CycleQ2SegreFactorExact CycleQ2SegreFactorSequence CycleQ2ModularFactorChartExact

/-- If all three selected left products have their prescribed grades, the
actual scalar itself has degree zero and trivial cubic character. -/
theorem gauge_scalar_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (c : Chart s) (hc : LeftGrade s (fun i => c*leftSection s i)) :
    HasLocalGrade F109 57 33 s (0,0) c := by
  let f := polynomialMap F109 57 33 s
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator F109 57 33 s (fun _ _ => c)
  let Q := P 0 0
  let a := f (openPolynomial F109 s^n)
  have hQ : f Q=a*c := hP 0 0
  let d : Grade := n • openGrade s
  let Q' := weightedHomogeneousComponent fullGrading d Q
  have hprod (i : Fin 3) : f (Q*polynomialLeft 57 i)=a*(c*leftSection s i) := by
    rw [map_mul,hQ,mul_assoc]
    rfl
  have hprodGrade (i : Fin 3) : HasLocalGrade F109 57 33 s (d+(10,0))
      (f (Q*polynomialLeft 57 i)) := by
    rw [hprod]
    exact hasLocalGrade_mul F109 57 33 s d (10,0) _ _
      (polynomial_hasLocalGrade F109 57 33 s _ _
        ((openPolynomial_homogeneous F109 s).pow n)) (hc i)
  have hproj (i : Fin 3) : f Q'*leftSection s i=a*(c*leftSection s i) := by
    have hh := component_eq_of_homogeneous_image F109 57 33 s
      (Q*polynomialLeft 57 i) (d+(10,0)) (hprodGrade i)
    rw [component_mul fullGrading Q (polynomialLeft 57 i) d (10,0)
      (polynomialLeft_homogeneous 57 i)] at hh
    have he := hh.trans (hprod i)
    rw [map_mul] at he
    exact he
  have ha : IsUnit a := by
    simpa only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Chart s)
        (algebraMap (CycleQ2SeedQuotientFiniteFree.Base F109) (SeedRing (57:F109) 33)
          (CycleQ2SeedCechLocalization.baseProduct F109 s)) n)
  obtain ⟨u,hu⟩ := ha
  let c' : Chart s := (↑(u⁻¹):Chart s)*f Q'
  have he (i : Fin 3) : c'*leftSection s i=c*leftSection s i := by
    calc
      c'*leftSection s i=(↑(u⁻¹):Chart s)*(f Q'*leftSection s i) := by dsimp only [c']; ring
      _ = (↑(u⁻¹):Chart s)*(a*(c*leftSection s i)) := by rw [hproj]
      _ = c*leftSection s i := by rw [← hu,← mul_assoc,u.inv_mul,one_mul]
  have hceq : c'=c := gauge_scalar_unique (linkage s) (linkage_regular s)
    (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s) (leftSection s) (rightSection s)
    (factorData s hs).product (factorData s hs).entries_generate c' c he
  rw [← hceq]
  apply fraction_hasLocalGrade F109 57 33 s c' (0,0) n Q'
  · have hh : HG Q' d := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    change HG Q' (d+0)
    simpa only [add_zero] using hh
  · change f Q'=a*((↑(u⁻¹):Chart s)*f Q')
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]

theorem gaugeMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (c : Chart s) (hc : HasLocalGrade F109 57 33 s (0,0) c) :
    LeftGrade s (fun i => ((chartGaugeMap s hs c).1 i:Chart s)) ∧
    RightGrade s (fun j => ((chartGaugeMap s hs c).2 j:Chart s)) := by
  constructor
  · intro i
    exact hasLocalGrade_mul F109 57 33 s (0,0) (10,0)
      c (leftSection s i) hc (leftSection_grade s i)
  · intro j
    apply hasLocalGrade_neg F109 57 33 s (8,1)
    exact hasLocalGrade_mul F109 57 33 s (0,0) (8,1)
      c (rightSection s j) hc (rightSection_grade s j)

end CycleQ2ModularFactorGraded

#print axioms CycleQ2ModularFactorGraded.gauge_scalar_grade
#print axioms CycleQ2ModularFactorGraded.gaugeMap_grade
end
end

/- Component: continuation_3/cylinder_bridge/ModularFactorRestrictions.lean -/
section
/-! # Canonical restrictions of the actual factor sequence -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2ModularFactorRestrictions

open CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedLinkageIdeals CycleQ2CurveRestriction CycleQ2SeedLocalizedProjection
  CycleQ2ModularFactorChartExact CycleQ2ModularFactorGraded CycleQ2SegreCechConnecting

abbrev res {s t : Finset (Fin 3)} (hst : s⊆t) : Chart s →+* Chart t :=
  restriction F109 57 33 hst

theorem restriction_chartMap {s t : Finset (Fin 3)} (hst : s⊆t)
    (x : SeedRing (57:F109) 33) : res hst (chartMap s x)=chartMap t x :=
  restriction_algebraMap F109 57 33 hst x

theorem restriction_leftSection {s t : Finset (Fin 3)} (hst : s⊆t) (i : Fin 3) :
    res hst (leftSection s i)=leftSection t i := restriction_chartMap hst _

theorem restriction_rightSection {s t : Finset (Fin 3)} (hst : s⊆t) (j : Fin 3) :
    res hst (rightSection s j)=rightSection t j := restriction_chartMap hst _

theorem restriction_linkage {s t : Finset (Fin 3)} (hst : s⊆t) :
    res hst (linkage s)=linkage t := restriction_chartMap hst _

theorem restriction_ideal_mem (side : Side) {s t : Finset (Fin 3)} (hst : s⊆t)
    (x : Chart s) (hx : x∈(linkageIdeal side (57:F109) 33).map (chartMap s)) :
    res hst x ∈ (linkageIdeal side (57:F109) 33).map (chartMap t) := by
  have hcomp : (res hst).comp (chartMap s)=chartMap t := by
    apply RingHom.ext
    exact restriction_chartMap hst
  have hh := Ideal.mem_map_of_mem (res hst) hx
  rw [Ideal.map_map,hcomp] at hh
  exact hh

def factorRestriction {s t : Finset (Fin 3)} (hst : s⊆t) :
    FactorSections s →ₗ[F109] FactorSections t where
  toFun V := (fun i => ⟨res hst (V.1 i),restriction_ideal_mem .left hst _ (V.1 i).property⟩,
    fun j => ⟨res hst (V.2 j),restriction_ideal_mem .right hst _ (V.2 j).property⟩)
  map_add' V W := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact map_add (res hst) (V.1 i:Chart s) (W.1 i:Chart s)
    · funext j
      apply Subtype.ext
      exact map_add (res hst) (V.2 j:Chart s) (W.2 j:Chart s)
  map_smul' c V := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact map_smul (restrictionLinear F109 57 33 hst) c (V.1 i:Chart s)
    · funext j
      apply Subtype.ext
      exact map_smul (restrictionLinear F109 57 33 hst) c (V.2 j:Chart s)

theorem factorRestriction_comp {s t u : Finset (Fin 3)} (hst : s⊆t) (htu : t⊆u)
    (V : FactorSections s) :
    factorRestriction htu (factorRestriction hst V)=factorRestriction (hst.trans htu) V := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact restriction_comp F109 57 33 hst htu (V.1 i:Chart s)
  · funext j
    apply Subtype.ext
    exact restriction_comp F109 57 33 hst htu (V.2 j:Chart s)

theorem factorRestriction_grade {s t : Finset (Fin 3)} (hst : s⊆t)
    (V : FactorSections s) (hL : LeftGrade s (fun i => (V.1 i:Chart s)))
    (hR : RightGrade s (fun j => (V.2 j:Chart s))) :
    LeftGrade t (fun i => ((factorRestriction hst V).1 i:Chart t)) ∧
    RightGrade t (fun j => ((factorRestriction hst V).2 j:Chart t)) := by
  exact ⟨fun i => hasLocalGrade_restriction F109 57 33 hst (10,0) _ (hL i),
    fun j => hasLocalGrade_restriction F109 57 33 hst (8,1) _ (hR j)⟩

/-- The canonical factor map commutes with every actual coordinate restriction. -/
theorem chartFactorMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (V : FactorSections s) :
    (res hst).mapMatrix (chartFactorMap s hs V)=
      chartFactorMap t ht (factorRestriction hst V) := by
  funext i j
  apply linkage_regular t
  change linkage t*res hst (chartFactorMap s hs V i j)=
    linkage t*chartFactorMap t ht (factorRestriction hst V) i j
  calc
    _ = res hst (linkage s*chartFactorMap s hs V i j) := by
      rw [map_mul,restriction_linkage]
    _ = res hst ((V.1 i:Chart s)*rightSection s j+leftSection s i*(V.2 j:Chart s)) :=
      congrArg (res hst) (chartFactorMap_formula s hs V i j)
    _ = ((factorRestriction hst V).1 i:Chart t)*rightSection t j+
        leftSection t i*((factorRestriction hst V).2 j:Chart t) := by
      rw [map_add,map_mul,map_mul,restriction_leftSection,restriction_rightSection]
      rfl
    _ = linkage t*chartFactorMap t ht (factorRestriction hst V) i j :=
      (chartFactorMap_formula t ht (factorRestriction hst V) i j).symm

theorem chartGaugeMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (c : Chart s) :
    factorRestriction hst (chartGaugeMap s hs c)=chartGaugeMap t ht (res hst c) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    change res hst (c*leftSection s i)=res hst c*leftSection t i
    rw [map_mul,restriction_leftSection]
  · funext j
    apply Subtype.ext
    change res hst (-(c*rightSection s j))=-(res hst c*rightSection t j)
    rw [map_neg,map_mul,restriction_rightSection]

end CycleQ2ModularFactorRestrictions

#print axioms CycleQ2ModularFactorRestrictions.factorRestriction_comp
#print axioms CycleQ2ModularFactorRestrictions.chartFactorMap_restriction
#print axioms CycleQ2ModularFactorRestrictions.chartGaugeMap_restriction
end
end

/- Component: continuation_3/SeedGlobalFactorMap.lean -/
section
/-! The literal global factor map on the two finite graded linkage pieces.
Divisibility and regularity define the quotient globally; no unit-entry
hypothesis at the affine origin is used. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalFactorMap

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2CurveRestriction
  CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageIdealRanks CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechThreeOpen CycleQ2SeedQuotientGrading
  CycleQ2SeedLocalizedProjection CycleQ2SeedLocalizedClearing

abbrev A := SeedRing (57:ℂ) Complex.I
abbrev LeftPiece := linkagePiece .left (57:ℂ) Complex.I 10 0
abbrev RightPiece := linkagePiece .right (57:ℂ) Complex.I 8 1
abbrev Domain := (Fin 3 → LeftPiece) × (Fin 3 → RightPiece)
abbrev MatrixPiece := Matrix (Fin 3) (Fin 3) (SeedPiece (57:ℂ) Complex.I 14 0)

instance leftPiece_finite : Module.Finite ℂ LeftPiece := by
  letI : Module.Finite ℂ (SeedPiece (57:ℂ) Complex.I 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 10 0 (by decide))
  infer_instance

instance rightPiece_finite : Module.Finite ℂ RightPiece := by
  letI : Module.Finite ℂ (SeedPiece (57:ℂ) Complex.I 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 8 1 (by decide))
  infer_instance

instance matrixPiece_finite : Module.Finite ℂ MatrixPiece := by
  letI : Module.Finite ℂ (SeedPiece (57:ℂ) Complex.I 14 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 14 0 (by decide))
  infer_instance

theorem domain_finrank : Module.finrank ℂ Domain=237 := by
  letI : Module.Free ℂ LeftPiece := Module.Free.of_divisionRing ℂ LeftPiece
  letI : Module.Free ℂ RightPiece := Module.Free.of_divisionRing ℂ RightPiece
  letI : Module.Free ℂ (Fin 3 → LeftPiece) := Module.Free.of_divisionRing ℂ (Fin 3 → LeftPiece)
  letI : Module.Free ℂ (Fin 3 → RightPiece) := Module.Free.of_divisionRing ℂ (Fin 3 → RightPiece)
  rw [Module.finrank_prod,Module.finrank_pi_fintype,Module.finrank_pi_fintype]
  simp only [left_linkagePiece_rank,right_linkagePiece_rank,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  norm_num

def leftValue (v : Domain) (i : Fin 3) : A := (v.1 i).val.val
def rightValue (v : Domain) (j : Fin 3) : A := (v.2 j).val.val

def left (i : Fin 3) : A := CycleQ2SeedLinkagePrincipal.leftSection (57:ℂ) Complex.I i
def right (j : Fin 3) : A := CycleQ2SeedLinkagePrincipal.rightSection (57:ℂ) Complex.I j
def linkage : A := CycleQ2SeedLinkagePrincipal.linkage (57:ℂ) Complex.I

theorem leftValue_mem (v : Domain) (i : Fin 3) :
    leftValue v i∈linkageIdeal .left (57:ℂ) Complex.I := (v.1 i).property

theorem rightValue_mem (v : Domain) (j : Fin 3) :
    rightValue v j∈linkageIdeal .right (57:ℂ) Complex.I := (v.2 j).property

theorem linkage_regular : Function.Injective (fun z : A => linkage*z) := by
  apply CycleQ2SeedLinkageRegular.linkage_mul_injective
  intro h
  have hh := congrArg Complex.im h
  norm_num at hh

theorem numerator_divisible (v : Domain) (i j : Fin 3) :
    linkage ∣ leftValue v i*right j+left i*rightValue v j := by
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.span {linkage}).add_mem
  · exact CycleQ2SeedLinkagePrincipal.ideals_pairing (57:ℂ) Complex.I
      (Ideal.mul_mem_mul (leftValue_mem v i)
        (CycleQ2SeedLinkagePrincipal.rightSection_mem (57:ℂ) Complex.I j))
  · exact CycleQ2SeedLinkagePrincipal.ideals_pairing (57:ℂ) Complex.I
      (Ideal.mul_mem_mul (CycleQ2SeedLinkagePrincipal.leftSection_mem (57:ℂ) Complex.I i)
        (rightValue_mem v j))

def factorValue (v : Domain) : Matrix (Fin 3) (Fin 3) A :=
  fun i j => Classical.choose (numerator_divisible v i j)

theorem factorValue_formula (v : Domain) (i j : Fin 3) :
    linkage*factorValue v i j=leftValue v i*right j+left i*rightValue v j :=
  (Classical.choose_spec (numerator_divisible v i j)).symm

def factorMap : Domain →ₗ[ℂ] Matrix (Fin 3) (Fin 3) A where
  toFun := factorValue
  map_add' v w := by
    funext i j
    apply linkage_regular
    change linkage*factorValue (v+w) i j=linkage*(factorValue v i j+factorValue w i j)
    rw [mul_add,factorValue_formula,factorValue_formula,factorValue_formula]
    change (leftValue v i+leftValue w i)*right j+left i*(rightValue v j+rightValue w j)=
      (leftValue v i*right j+left i*rightValue v j)+
      (leftValue w i*right j+left i*rightValue w j)
    ring
  map_smul' c v := by
    funext i j
    apply linkage_regular
    change linkage*factorValue (c • v) i j=linkage*(c • factorValue v i j)
    rw [Algebra.smul_def c (factorValue v i j)]
    rw [show linkage*(algebraMap ℂ A c*factorValue v i j)=
      algebraMap ℂ A c*(linkage*factorValue v i j) by ring]
    rw [factorValue_formula,factorValue_formula]
    change (c • leftValue v i)*right j+left i*(c • rightValue v j)=
      algebraMap ℂ A c*(leftValue v i*right j+left i*rightValue v j)
    rw [Algebra.smul_def c (leftValue v i),Algebra.smul_def c (rightValue v j)]
    ring

theorem factorMap_formula (v : Domain) (i j : Fin 3) :
    linkage*factorMap v i j=leftValue v i*right j+left i*rightValue v j :=
  factorValue_formula v i j

abbrev Chart := CycleQ2SegreFactorChartExact.Chart
abbrev chartMap := CycleQ2SegreFactorChartExact.chartMap

def chartSections (s : Finset (Fin 3)) (v : Domain) :
    CycleQ2SegreFactorChartExact.FactorSections s :=
  (fun i => ⟨chartMap s (leftValue v i),Ideal.mem_map_of_mem (chartMap s) (leftValue_mem v i)⟩,
    fun j => ⟨chartMap s (rightValue v j),Ideal.mem_map_of_mem (chartMap s) (rightValue_mem v j)⟩)

theorem factorMap_localize (s : Finset (Fin 3)) (hs : s.Nonempty)
    (v : Domain) (i j : Fin 3) :
    chartMap s (factorMap v i j)=
      CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v) i j := by
  apply CycleQ2SegreFactorChartExact.linkage_regular s
  change CycleQ2SegreFactorChartExact.linkage s*chartMap s (factorMap v i j)=
    CycleQ2SegreFactorChartExact.linkage s*
      CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v) i j
  rw [CycleQ2SegreFactorChartExact.chartFactorMap_formula s hs (chartSections s v) i j]
  have h := congrArg (chartMap s) (factorMap_formula v i j)
  simpa only [map_mul,map_add,CycleQ2SegreFactorChartExact.linkage,
    CycleQ2SegreFactorChartExact.leftSection,CycleQ2SegreFactorChartExact.rightSection,
    left,right,linkage,chartSections] using h

theorem seedPiece_local_grade (r ι : ℂ) (d ch : ℕ) (q : SeedPiece r ι d ch)
    (s : Finset (Fin 3)) :
    HasLocalGrade ℂ r ι s (d,(ch:ZMod 3))
      (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s) q.val) := by
  obtain ⟨p,hp,hpq⟩ := Submodule.mem_map.mp q.property
  change HG p (d,(ch:ZMod 3)) at hp
  change Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p=q.val at hpq
  rw [←hpq]
  exact polynomial_hasLocalGrade ℂ r ι s p (d,(ch:ZMod 3)) hp

theorem seedPiece_of_local_grade (r ι : ℂ) (d ch : ℕ) (q : SeedRing r ι)
    (s : Finset (Fin 3))
    (hq : HasLocalGrade ℂ r ι s (d,(ch:ZMod 3))
      (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι s) q)) :
    q∈SeedPiece r ι d ch := by
  have hh : ∀ ab, HasGrade ab (signedGrade (d,(ch:ZMod 3)))
      (CycleQ2SeedCechLocalization.baseToLaurent ℂ ((seedBasis ℂ r ι).repr q ab)) := by
    intro ab
    simpa only [localizedCoordinates_algebraMap] using hq ab
  obtain ⟨p,_hstd,hp,hpq⟩ := exists_signed_homogeneous_representative ℂ r ι q
    (signedGrade (d,(ch:ZMod 3))) hh
  apply Submodule.mem_map.mpr
  refine ⟨p,?_,hpq⟩
  exact (signedHomogeneous_iff ℂ p (d,(ch:ZMod 3))).mp hp

theorem factorMap_mem_piece (v : Domain) (i j : Fin 3) :
    factorMap v i j∈SeedPiece (57:ℂ) Complex.I 14 0 := by
  apply seedPiece_of_local_grade 57 Complex.I 14 0 _ {0}
  change HasLocalGrade ℂ 57 Complex.I {0} (14,0) (chartMap {0} (factorMap v i j))
  rw [factorMap_localize {0} (by simp) v i j]
  apply CycleQ2SegreFactorGraded.chartFactorMap_grade {0} (by simp) (chartSections {0} v)
  · intro k
    exact seedPiece_local_grade 57 Complex.I 10 0 (v.1 k).val {0}
  · intro k
    exact seedPiece_local_grade 57 Complex.I 8 1 (v.2 k).val {0}

def gradedFactorMap : Domain →ₗ[ℂ] MatrixPiece where
  toFun v i j := ⟨factorMap v i j,factorMap_mem_piece v i j⟩
  map_add' v w := by
    funext i j
    apply Subtype.ext
    exact congrArg (fun N : Matrix (Fin 3) (Fin 3) A => N i j) (map_add factorMap v w)
  map_smul' c v := by
    funext i j
    apply Subtype.ext
    exact congrArg (fun N : Matrix (Fin 3) (Fin 3) A => N i j) (map_smul factorMap c v)

 theorem factorMap_cofactor_zero (v : Domain) :
    cofactorDifferential CycleQ2SegreComplexBasepoint.matrix (factorMap v)=0 := by
  let s : Finset (Fin 3) := {0}
  have hs : s.Nonempty := by simp [s]
  have hn : CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v) ∈
      LinearMap.ker (cofactorDifferentialLinear (CycleQ2SegreComplexChartExact.chartMatrix s)) := by
    rw [← (CycleQ2SegreFactorChartExact.actual_factor_sequence s hs).2.2]
    exact ⟨chartSections s v,rfl⟩
  have hz : cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s)
      (CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v))=0 := hn
  have hloc : (chartMap s).mapMatrix (factorMap v)=
      CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v) := by
    ext i j
    exact factorMap_localize s hs v i j
  have he := @map_cofactorDifferential A (inferInstance : CommRing A)
    (Chart s) (inferInstance : CommRing (Chart s)) (chartMap s)
    CycleQ2SegreComplexBasepoint.matrix (factorMap v)
  rw [hloc] at he
  change (chartMap s).mapMatrix (cofactorDifferential CycleQ2SegreComplexBasepoint.matrix (factorMap v))=
    cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) _ at he
  rw [hz] at he
  funext i j
  apply CycleQ2SeedCechGlobalGluing.localization_injective ℂ 57 Complex.I s
  have hij := congrArg (fun N : Matrix (Fin 3) (Fin 3) (Chart s) => N i j) he
  simpa only [chartMap,CycleQ2SegreFactorChartExact.chartMap,RingHom.mapMatrix_apply,
    Matrix.map_apply,Matrix.zero_apply,Pi.zero_apply,map_zero] using hij

end CycleQ2SeedGlobalFactorMap

#print axioms CycleQ2SeedGlobalFactorMap.domain_finrank
#print axioms CycleQ2SeedGlobalFactorMap.factorMap_cofactor_zero
end
end

/- Component: continuation_3/cylinder_bridge/SegreFactorRestrictions.lean -/
section
/-! # Canonical restrictions of the actual factor sequence -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2SegreFactorRestrictions

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedLinkageIdeals CycleQ2CurveRestriction CycleQ2SeedLocalizedProjection
  CycleQ2SegreFactorChartExact CycleQ2SegreFactorGraded CycleQ2SegreCechConnecting

abbrev res {s t : Finset (Fin 3)} (hst : s⊆t) : Chart s →+* Chart t :=
  restriction ℂ 57 Complex.I hst

theorem restriction_chartMap {s t : Finset (Fin 3)} (hst : s⊆t)
    (x : SeedRing (57:ℂ) Complex.I) : res hst (chartMap s x)=chartMap t x :=
  restriction_algebraMap ℂ 57 Complex.I hst x

theorem restriction_leftSection {s t : Finset (Fin 3)} (hst : s⊆t) (i : Fin 3) :
    res hst (leftSection s i)=leftSection t i := restriction_chartMap hst _

theorem restriction_rightSection {s t : Finset (Fin 3)} (hst : s⊆t) (j : Fin 3) :
    res hst (rightSection s j)=rightSection t j := restriction_chartMap hst _

theorem restriction_linkage {s t : Finset (Fin 3)} (hst : s⊆t) :
    res hst (linkage s)=linkage t := restriction_chartMap hst _

theorem restriction_ideal_mem (side : Side) {s t : Finset (Fin 3)} (hst : s⊆t)
    (x : Chart s) (hx : x∈(linkageIdeal side (57:ℂ) Complex.I).map (chartMap s)) :
    res hst x ∈ (linkageIdeal side (57:ℂ) Complex.I).map (chartMap t) := by
  have hcomp : (res hst).comp (chartMap s)=chartMap t := by
    apply RingHom.ext
    exact restriction_chartMap hst
  have hh := Ideal.mem_map_of_mem (res hst) hx
  rw [Ideal.map_map,hcomp] at hh
  exact hh

def factorRestriction {s t : Finset (Fin 3)} (hst : s⊆t) :
    FactorSections s →ₗ[ℂ] FactorSections t where
  toFun V := (fun i => ⟨res hst (V.1 i),restriction_ideal_mem .left hst _ (V.1 i).property⟩,
    fun j => ⟨res hst (V.2 j),restriction_ideal_mem .right hst _ (V.2 j).property⟩)
  map_add' V W := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact map_add (res hst) (V.1 i:Chart s) (W.1 i:Chart s)
    · funext j
      apply Subtype.ext
      exact map_add (res hst) (V.2 j:Chart s) (W.2 j:Chart s)
  map_smul' c V := by
    apply Prod.ext
    · funext i
      apply Subtype.ext
      exact map_smul (restrictionLinear ℂ 57 Complex.I hst) c (V.1 i:Chart s)
    · funext j
      apply Subtype.ext
      exact map_smul (restrictionLinear ℂ 57 Complex.I hst) c (V.2 j:Chart s)

theorem factorRestriction_comp {s t u : Finset (Fin 3)} (hst : s⊆t) (htu : t⊆u)
    (V : FactorSections s) :
    factorRestriction htu (factorRestriction hst V)=factorRestriction (hst.trans htu) V := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    exact restriction_comp ℂ 57 Complex.I hst htu (V.1 i:Chart s)
  · funext j
    apply Subtype.ext
    exact restriction_comp ℂ 57 Complex.I hst htu (V.2 j:Chart s)

theorem factorRestriction_grade {s t : Finset (Fin 3)} (hst : s⊆t)
    (V : FactorSections s) (hL : LeftGrade s (fun i => (V.1 i:Chart s)))
    (hR : RightGrade s (fun j => (V.2 j:Chart s))) :
    LeftGrade t (fun i => ((factorRestriction hst V).1 i:Chart t)) ∧
    RightGrade t (fun j => ((factorRestriction hst V).2 j:Chart t)) := by
  exact ⟨fun i => hasLocalGrade_restriction ℂ 57 Complex.I hst (10,0) _ (hL i),
    fun j => hasLocalGrade_restriction ℂ 57 Complex.I hst (8,1) _ (hR j)⟩

/-- The canonical factor map commutes with every actual coordinate restriction. -/
theorem chartFactorMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (V : FactorSections s) :
    (res hst).mapMatrix (chartFactorMap s hs V)=
      chartFactorMap t ht (factorRestriction hst V) := by
  funext i j
  apply linkage_regular t
  change linkage t*res hst (chartFactorMap s hs V i j)=
    linkage t*chartFactorMap t ht (factorRestriction hst V) i j
  calc
    _ = res hst (linkage s*chartFactorMap s hs V i j) := by
      rw [map_mul,restriction_linkage]
    _ = res hst ((V.1 i:Chart s)*rightSection s j+leftSection s i*(V.2 j:Chart s)) :=
      congrArg (res hst) (chartFactorMap_formula s hs V i j)
    _ = ((factorRestriction hst V).1 i:Chart t)*rightSection t j+
        leftSection t i*((factorRestriction hst V).2 j:Chart t) := by
      rw [map_add,map_mul,map_mul,restriction_leftSection,restriction_rightSection]
      rfl
    _ = linkage t*chartFactorMap t ht (factorRestriction hst V) i j :=
      (chartFactorMap_formula t ht (factorRestriction hst V) i j).symm

theorem chartGaugeMap_restriction {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s⊆t) (c : Chart s) :
    factorRestriction hst (chartGaugeMap s hs c)=chartGaugeMap t ht (res hst c) := by
  apply Prod.ext
  · funext i
    apply Subtype.ext
    change res hst (c*leftSection s i)=res hst c*leftSection t i
    rw [map_mul,restriction_leftSection]
  · funext j
    apply Subtype.ext
    change res hst (-(c*rightSection s j))=-(res hst c*rightSection t j)
    rw [map_neg,map_mul,restriction_rightSection]

end CycleQ2SegreFactorRestrictions

#print axioms CycleQ2SegreFactorRestrictions.factorRestriction_comp
#print axioms CycleQ2SegreFactorRestrictions.chartFactorMap_restriction
#print axioms CycleQ2SegreFactorRestrictions.chartGaugeMap_restriction
end
end

/- Component: continuation_3/cylinder_bridge/SegreGaugeGrade.lean -/
section
/-! # The scalar gauge has the actual degree-zero grade -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace CycleQ2SegreFactorGraded

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SeedLocalizedProjection CycleQ2SeedFactorHomogeneous CycleQ2WeightedComponent
  CycleQ2SegreFactorExact CycleQ2SegreFactorSequence CycleQ2SegreFactorChartExact

/-- If all three selected left products have their prescribed grades, the
actual scalar itself has degree zero and trivial cubic character. -/
theorem gauge_scalar_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (c : Chart s) (hc : LeftGrade s (fun i => c*leftSection s i)) :
    HasLocalGrade ℂ 57 Complex.I s (0,0) c := by
  let f := polynomialMap ℂ 57 Complex.I s
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator ℂ 57 Complex.I s (fun _ _ => c)
  let Q := P 0 0
  let a := f (openPolynomial ℂ s^n)
  have hQ : f Q=a*c := hP 0 0
  let d : Grade := n • openGrade s
  let Q' := weightedHomogeneousComponent fullGrading d Q
  have hprod (i : Fin 3) : f (Q*polynomialLeft 57 i)=a*(c*leftSection s i) := by
    rw [map_mul,hQ,mul_assoc]
    rfl
  have hprodGrade (i : Fin 3) : HasLocalGrade ℂ 57 Complex.I s (d+(10,0))
      (f (Q*polynomialLeft 57 i)) := by
    rw [hprod]
    exact hasLocalGrade_mul ℂ 57 Complex.I s d (10,0) _ _
      (polynomial_hasLocalGrade ℂ 57 Complex.I s _ _
        ((openPolynomial_homogeneous ℂ s).pow n)) (hc i)
  have hproj (i : Fin 3) : f Q'*leftSection s i=a*(c*leftSection s i) := by
    have hh := component_eq_of_homogeneous_image ℂ 57 Complex.I s
      (Q*polynomialLeft 57 i) (d+(10,0)) (hprodGrade i)
    rw [component_mul fullGrading Q (polynomialLeft 57 i) d (10,0)
      (polynomialLeft_homogeneous 57 i)] at hh
    have he := hh.trans (hprod i)
    rw [map_mul] at he
    exact he
  have ha : IsUnit a := by
    simpa only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := Chart s)
        (algebraMap (CycleQ2SeedQuotientFiniteFree.Base ℂ) (SeedRing (57:ℂ) Complex.I)
          (CycleQ2SeedCechLocalization.baseProduct ℂ s)) n)
  obtain ⟨u,hu⟩ := ha
  let c' : Chart s := (↑(u⁻¹):Chart s)*f Q'
  have he (i : Fin 3) : c'*leftSection s i=c*leftSection s i := by
    calc
      c'*leftSection s i=(↑(u⁻¹):Chart s)*(f Q'*leftSection s i) := by dsimp only [c']; ring
      _ = (↑(u⁻¹):Chart s)*(a*(c*leftSection s i)) := by rw [hproj]
      _ = c*leftSection s i := by rw [← hu,← mul_assoc,u.inv_mul,one_mul]
  have hceq : c'=c := gauge_scalar_unique (linkage s) (linkage_regular s)
    (CycleQ2SegreComplexChartExact.chartMatrix s) (leftSection s) (rightSection s)
    (factorData s hs).product (factorData s hs).entries_generate c' c he
  rw [← hceq]
  apply fraction_hasLocalGrade ℂ 57 Complex.I s c' (0,0) n Q'
  · have hh : HG Q' d := weightedHomogeneousComponent_isWeightedHomogeneous _ _
    change HG Q' (d+0)
    simpa only [add_zero] using hh
  · change f Q'=a*((↑(u⁻¹):Chart s)*f Q')
    rw [← hu,← mul_assoc,u.mul_inv,one_mul]

theorem gaugeMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty)
    (c : Chart s) (hc : HasLocalGrade ℂ 57 Complex.I s (0,0) c) :
    LeftGrade s (fun i => ((chartGaugeMap s hs c).1 i:Chart s)) ∧
    RightGrade s (fun j => ((chartGaugeMap s hs c).2 j:Chart s)) := by
  constructor
  · intro i
    exact hasLocalGrade_mul ℂ 57 Complex.I s (0,0) (10,0)
      c (leftSection s i) hc (leftSection_grade s i)
  · intro j
    apply hasLocalGrade_neg ℂ 57 Complex.I s (8,1)
    exact hasLocalGrade_mul ℂ 57 Complex.I s (0,0) (8,1)
      c (rightSection s j) hc (rightSection_grade s j)

end CycleQ2SegreFactorGraded

#print axioms CycleQ2SegreFactorGraded.gauge_scalar_grade
#print axioms CycleQ2SegreFactorGraded.gaugeMap_grade
end
end

/- Component: continuation_3/cylinder_bridge/ModularFactorCechSpaces.lean -/
section
/-! # The graded factor and scalar modules on the actual Čech opens -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2ModularFactorCech

open CycleQ2IncidenceGaussianArithmetic

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedLocalizedProjection CycleQ2SeedCechActualTop
  CycleQ2ModularFactorChartExact CycleQ2ModularFactorGraded CycleQ2ModularFactorRestrictions

abbrev ScalarSections (s : Finset (Fin 3)) := gradedLocal F109 (57:F109) 33 s

def factorGrades (s : Finset (Fin 3)) : Submodule F109 (FactorSections s) where
  carrier := {V | LeftGrade s (fun i => (V.1 i:Chart s)) ∧ RightGrade s (fun j => (V.2 j:Chart s))}
  zero_mem' := ⟨fun i => hasLocalGrade_zero F109 57 33 s (10,0),
    fun j => hasLocalGrade_zero F109 57 33 s (8,1)⟩
  add_mem' hV hW := ⟨fun i => hasLocalGrade_add F109 57 33 s (10,0) _ _ (hV.1 i) (hW.1 i),
    fun j => hasLocalGrade_add F109 57 33 s (8,1) _ _ (hV.2 j) (hW.2 j)⟩
  smul_mem' c _ hV := ⟨fun i => hasLocalGrade_R_smul F109 57 33 s (10,0) c _ (hV.1 i),
    fun j => hasLocalGrade_R_smul F109 57 33 s (8,1) c _ (hV.2 j)⟩

abbrev GradedFactors (s : Finset (Fin 3)) := factorGrades s

def gradedFactorMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    GradedFactors s →ₗ[F109] Matrix (Fin 3) (Fin 3) (Chart s) :=
  ((chartFactorMap s hs).restrictScalars F109).comp (factorGrades s).subtype

def gradedGaugeMap (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ScalarSections s →ₗ[F109] GradedFactors s :=
  (((chartGaugeMap s hs).restrictScalars F109).comp (ScalarSections s).subtype).codRestrict _
    (fun c => gaugeMap_grade s hs c.val c.property)

def gradedFactorRestriction {s t : Finset (Fin 3)} (hst : s⊆t) :
    GradedFactors s →ₗ[F109] GradedFactors t :=
  ((factorRestriction hst).comp (factorGrades s).subtype).codRestrict _
    (fun V => factorRestriction_grade hst V.val V.property.1 V.property.2)

theorem gradedFactorMap_grade (s : Finset (Fin 3)) (hs : s.Nonempty) (V : GradedFactors s) :
    MatrixGrade s (gradedFactorMap s hs V) :=
  chartFactorMap_grade s hs V.val V.property.1 V.property.2

theorem gradedFactorMap_kernel (s : Finset (Fin 3)) (hs : s.Nonempty) (V : GradedFactors s) :
    cofactorDifferential (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s) (gradedFactorMap s hs V)=0 := by
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
  have hcg : HasLocalGrade F109 57 33 s (0,0) c := by
    apply gauge_scalar_grade s hs c
    intro i
    have hi := congrArg (fun W : FactorSections s => (W.1 i:Chart s)) hc
    change c*leftSection s i=(V.val.1 i:Chart s) at hi
    change HasLocalGrade F109 57 33 s (10,0) (c*leftSection s i)
    rw [hi]
    exact V.property.1 i
  refine ⟨⟨c,hcg⟩,?_⟩
  exact Subtype.ext hc

/-- Surjectivity onto the actual graded cofactor kernel. -/
theorem graded_factor_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (N : Matrix (Fin 3) (Fin 3) (Chart s))
    (hN : cofactorDifferential (CycleQ2SegreModularChartExact.chartMatrix (R:=F109) s) N=0)
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
      gradedGaugeMap t ht (gradedRestriction F109 57 33 hst c) := by
  apply Subtype.ext
  exact chartGaugeMap_restriction hs ht hst c.val

end CycleQ2ModularFactorCech

#print axioms CycleQ2ModularFactorCech.graded_zero_factor_gauge
#print axioms CycleQ2ModularFactorCech.graded_factor_lift
#print axioms CycleQ2ModularFactorCech.gradedFactorMap_restriction
end
end

/- Component: continuation_3/SeedGlobalFactorGauge.lean -/
section
/-! The global kernel of the actual graded factor map consists only of the
constant scalar gauge. Local gauges agree on genuine overlaps and glue to
a degree-zero polynomial in the actual seed quotient. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SeedGlobalFactorGauge

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedQuotientGrading CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechGlobalGluing
  CycleQ2SeedLocalizedProjection CycleQ2SegreFactorExact CycleQ2SeedGlobalFactorMap

 theorem homogeneous_zero_constant {R : Type*} [CommRing R] (p : Poly R)
    (hp : SignedHomogeneous R p (0,0)) : p=C (p.coeff 0) := by
  apply MvPolynomial.ext
  intro e
  by_cases he : e=0
  · simp [he]
  · have hz : p.coeff e=0 := by
      by_contra hne
      have hd := congrArg Prod.fst (hp e hne)
      rw [fullGrading_weight] at hd
      change (fullDegree e:ℤ)=0 at hd
      have hd' : fullDegree e=0 := by exact_mod_cast hd
      have he0 : e=0 := by
        apply Finsupp.ext
        intro i
        dsimp [fullDegree] at hd'
        fin_cases i
        · change e 0=0
          omega
        · change e 1=0
          omega
        · change e 2=0
          omega
        · change e 3=0
          omega
        · change e 4=0
          omega
      exact he he0
    simp only [coeff_C,if_neg (Ne.symm he),hz]

theorem exists_local_gauge (v : Domain) (hv : factorMap v=0)
    (s : Finset (Fin 3)) (hs : s.Nonempty) :
    ∃ c : Chart s, HasLocalGrade ℂ 57 Complex.I s (0,0) c ∧
      (∀ i, chartMap s (leftValue v i)=c*CycleQ2SegreFactorChartExact.leftSection s i) ∧
      (∀ j, chartMap s (rightValue v j)=-(c*CycleQ2SegreFactorChartExact.rightSection s j)) := by
  have hz : CycleQ2SegreFactorChartExact.chartFactorMap s hs (chartSections s v)=0 := by
    funext i j
    rw [←factorMap_localize s hs v i j,hv]
    exact map_zero (chartMap s)
  have hm : chartSections s v∈LinearMap.ker (CycleQ2SegreFactorChartExact.chartFactorMap s hs) := hz
  rw [(CycleQ2SegreFactorChartExact.actual_factor_sequence s hs).2.1] at hm
  obtain ⟨c,hc⟩ := hm
  have hl (i : Fin 3) : chartMap s (leftValue v i)=c*CycleQ2SegreFactorChartExact.leftSection s i := by
    have h := congrArg (fun w : CycleQ2SegreFactorChartExact.FactorSections s => (w.1 i:Chart s)) hc
    exact h.symm
  have hr (j : Fin 3) : chartMap s (rightValue v j)=-(c*CycleQ2SegreFactorChartExact.rightSection s j) := by
    have h := congrArg (fun w : CycleQ2SegreFactorChartExact.FactorSections s => (w.2 j:Chart s)) hc
    exact h.symm
  refine ⟨c,?_,hl,hr⟩
  apply CycleQ2SegreFactorGraded.gauge_scalar_grade s hs c
  intro i
  change HasLocalGrade ℂ 57 Complex.I s (10,0) (c*CycleQ2SegreFactorChartExact.leftSection s i)
  rw [←hl i]
  exact seedPiece_local_grade 57 Complex.I 10 0 (v.1 i).val s

theorem factorMap_kernel_constant (v : Domain) (hv : factorMap v=0) :
    ∃ c : ℂ, (∀ i, leftValue v i=algebraMap ℂ A c*left i) ∧
      (∀ j, rightValue v j=-(algebraMap ℂ A c*right j)) := by
  choose c hc hl hr using fun k : Fin 3 => exists_local_gauge v hv {k} (by simp)
  have hcomp : Compatible ℂ 57 Complex.I c := by
    intro i j
    let s : Finset (Fin 3) := {i,j}
    have hs : s.Nonempty := by simp [s]
    let F := CycleQ2SegreFactorChartExact.factorData s hs
    apply gauge_scalar_unique F.linkage F.regular F.matrix F.left F.right
      F.product F.entries_generate
    intro k
    have hi := congrArg (pairRestriction ℂ 57 Complex.I i j) (hl i k)
    have hj := congrArg (secondPairRestriction ℂ 57 Complex.I i j) (hl j k)
    simp only [map_mul,pairRestriction,secondPairRestriction,
      CycleQ2SegreFactorChartExact.leftSection,CycleQ2SegreFactorChartExact.chartMap,
      chartMap,restriction_algebraMap] at hi hj
    exact hi.symm.trans hj
  obtain ⟨p,_hp,hpg,hp⟩ := exists_homogeneous_polynomial_gluing ℂ 57 Complex.I c hcomp
    (0,0) (hc 0)
  have hpconst := homogeneous_zero_constant p hpg
  refine ⟨p.coeff 0,?_,?_⟩
  · intro i
    apply localization_injective ℂ 57 Complex.I {0}
    rw [map_mul]
    have h := hl 0 i
    rw [←hp 0,hpconst] at h
    exact h
  · intro j
    apply localization_injective ℂ 57 Complex.I {0}
    rw [map_neg,map_mul]
    have h := hr 0 j
    rw [←hp 0,hpconst] at h
    exact h

def leftClass (i : Fin 3) : LeftPiece :=
  ⟨⟨left i,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialLeft (57:ℂ) i,
    CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57:ℂ) i,rfl⟩⟩,
    CycleQ2SeedLinkagePrincipal.leftSection_mem (57:ℂ) Complex.I i⟩

def rightClass (j : Fin 3) : RightPiece :=
  ⟨⟨right j,Submodule.mem_map.mpr ⟨CycleQ2SeedFactorHomogeneous.polynomialRight (57:ℂ) j,
    CycleQ2SeedFactorHomogeneous.polynomialRight_homogeneous (57:ℂ) j,rfl⟩⟩,
    CycleQ2SeedLinkagePrincipal.rightSection_mem (57:ℂ) Complex.I j⟩

def gaugeVector : Domain := (leftClass,fun j => -rightClass j)

theorem gradedFactorMap_kernel_gauge (v : Domain) (hv : gradedFactorMap v=0) :
    ∃ c : ℂ, v=c • gaugeVector := by
  have hz : factorMap v=0 := by
    funext i j
    exact congrArg (fun N : MatrixPiece => (N i j).val) hv
  obtain ⟨c,hl,hr⟩ := factorMap_kernel_constant v hz
  refine ⟨c,?_⟩
  apply Prod.ext
  · funext i
    apply Subtype.ext
    apply Subtype.ext
    change leftValue v i=c • left i
    rw [Algebra.smul_def c (left i)]
    exact hl i
  · funext j
    apply Subtype.ext
    apply Subtype.ext
    change rightValue v j=c • (-right j)
    rw [smul_neg,Algebra.smul_def c (right j)]
    exact hr j

theorem gradedFactorMap_kernel_le_gauge :
    LinearMap.ker gradedFactorMap≤Submodule.span ℂ {gaugeVector} := by
  intro v hv
  obtain ⟨c,hc⟩ := gradedFactorMap_kernel_gauge v hv
  exact Submodule.mem_span_singleton.mpr ⟨c,hc.symm⟩

theorem gradedFactorMap_kernel_finrank_le_one :
    Module.finrank ℂ (LinearMap.ker gradedFactorMap)≤1 := by
  calc
    _≤Module.finrank ℂ (Submodule.span ℂ {gaugeVector}) :=
      Submodule.finrank_mono gradedFactorMap_kernel_le_gauge
    _≤1 := by simpa using (finrank_span_le_card (R:=ℂ) ({gaugeVector}:Set Domain))

end CycleQ2SeedGlobalFactorGauge

#print axioms CycleQ2SeedGlobalFactorGauge.factorMap_kernel_constant
#print axioms CycleQ2SeedGlobalFactorGauge.gradedFactorMap_kernel_finrank_le_one
end
end

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
