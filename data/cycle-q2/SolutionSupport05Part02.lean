import Proposal.SolutionSupport05Part01

/-! Components extracted from SolutionSupport05.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SegreCechThreeEntries.lean -/
section
/-! # The three independent pair entries of the actual Čech cocycles

The all-ordered-pair complex used by the connecting injection is determined
by its (0,1), (0,2), and (1,2) entries. This follows from actual localization
injectivity and the literal triple cocycle equations.
-/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R] [Nontrivial R]

theorem restriction_injective (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    Function.Injective (restriction R r ι hst) := by
  intro p q hpq
  apply localizedCoordinates_injective R r ι s
  funext ab
  have hh := congrArg (fun z : SeedLocal R r ι t => localizedCoordinates R r ι t z ab) hpq
  simpa only [coordinates_restriction] using hh

theorem restriction_matrix_injective (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    Function.Injective ((restriction R r ι hst).mapMatrix :
      Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s) →
        Matrix (Fin 3) (Fin 3) (SeedLocal R r ι t)) := by
  intro P Q hPQ
  funext i j
  apply restriction_injective R r ι hst
  exact congrArg (fun M => M i j) hPQ

def PairCocycle (r ι : R) (P : PairMatrices R r ι) : Prop :=
  ∀ i j k, (restriction R r ι (Finset.subset_univ {i,j})).mapMatrix (P i j)-
    (restriction R r ι (Finset.subset_univ {i,k})).mapMatrix (P i k)+
    (restriction R r ι (Finset.subset_univ {j,k})).mapMatrix (P j k)=0

theorem cocycle_three_zero (r ι : R) (P : PairMatrices R r ι)
    (hP : PairCocycle R r ι P) (h01 : P 0 1=0) (h02 : P 0 2=0) (h12 : P 1 2=0) : P=0 := by
  have hd (i : Fin 3) : P i i=0 := by
    apply restriction_matrix_injective R r ι (Finset.subset_univ {i,i})
    rw [map_zero]
    simpa only [sub_self,zero_add] using hP i i i
  have hr (i j : Fin 3) (h : P i j=0) : P j i=0 := by
    apply restriction_matrix_injective R r ι (Finset.subset_univ {j,i})
    rw [map_zero]
    have hh := hP j i j
    rw [hd j,h,map_zero,map_zero,sub_zero,add_zero] at hh
    exact hh
  funext i j
  fin_cases i <;> fin_cases j
  · exact hd 0
  · exact h01
  · exact h02
  · exact hr 0 1 h01
  · exact hd 1
  · exact h12
  · exact hr 0 2 h02
  · exact hr 1 2 h12
  · exact hd 2

theorem cocycle_eq_of_three (r ι : R) (P Q : PairMatrices R r ι)
    (hP : PairCocycle R r ι P) (hQ : PairCocycle R r ι Q)
    (h01 : P 0 1=Q 0 1) (h02 : P 0 2=Q 0 2) (h12 : P 1 2=Q 1 2) : P=Q := by
  apply sub_eq_zero.mp
  apply cocycle_three_zero R r ι (P-Q)
  · intro i j k
    change (restriction R r ι (Finset.subset_univ {i,j})).mapMatrix (P i j-Q i j)-
      (restriction R r ι (Finset.subset_univ {i,k})).mapMatrix (P i k-Q i k)+
      (restriction R r ι (Finset.subset_univ {j,k})).mapMatrix (P j k-Q j k)=0
    rw [map_sub,map_sub,map_sub]
    calc
      _ = ((restriction R r ι (Finset.subset_univ {i,j})).mapMatrix (P i j)-
          (restriction R r ι (Finset.subset_univ {i,k})).mapMatrix (P i k)+
          (restriction R r ι (Finset.subset_univ {j,k})).mapMatrix (P j k))-
        ((restriction R r ι (Finset.subset_univ {i,j})).mapMatrix (Q i j)-
          (restriction R r ι (Finset.subset_univ {i,k})).mapMatrix (Q i k)+
          (restriction R r ι (Finset.subset_univ {j,k})).mapMatrix (Q j k)) := by abel
      _ = 0 := by rw [hP i j k,hQ i j k,sub_self]
  · change P 0 1-Q 0 1=0
    rw [h01,sub_self]
  · change P 0 2-Q 0 2=0
    rw [h02,sub_self]
  · change P 1 2-Q 1 2=0
    rw [h12,sub_self]

theorem overlap_pairCocycle (r ι : R) (g : MatrixGrades) (N : localGraded R r ι g) :
    PairCocycle R r ι (overlapDifference R r ι N.val) := by
  intro i j k
  exact congrArg (fun T : TripleMatrices R r ι => T i j k)
    (cechDifferential_overlap R r ι g N)

theorem kernelCocycle_properties (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades)
    (P : kernelCocycles R r ι M g) :
    (∀ i j k l ab, HasGrade ab (g k l)
      (localizedCoordinates R r ι {i,j} (P.val i j k l) ab)) ∧
    (∀ i j, cofactorDifferential (localizeMatrix R r ι {i,j} M) (P.val i j)=0) ∧
    PairCocycle R r ι P.val := by
  obtain ⟨Q,hQ,hQP⟩ := P.property
  change Q.val=P.val at hQP
  rw [← hQP]
  refine ⟨Q.property,?_,?_⟩
  · intro i j
    have hh : pairD R r ι M g Q=0 := hQ.1
    exact congrArg (fun T : PairMatrices R r ι => T i j) hh
  · intro i j k
    have hh : cechDifferential R r ι g Q=0 := hQ.2
    exact congrArg (fun T : TripleMatrices R r ι => T i j k) hh

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.cocycle_eq_of_three
#print axioms CycleQ2SegreCechConnecting.kernelCocycle_properties
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


/- Component: continuation_3/CurveRestrictionLocalGrading.lean -/
section
/-! # The actual localized restriction preserves degree

For global curve gluing it suffices to check the first base chart. The
right coordinate change scales its denominator by two; the inverse scalar
is included explicitly in the homogeneous numerator below.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

theorem baseOpenMap_first_homogeneous (side : Side) (r ι : ℂ)
    (q : SL ℂ r ι (seedOpen {0})) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hq : ∀ ab, CycleQ2SeedCechThreeOpen.HasGrade ab g
      (CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r ι (seedOpen {0}) q ab)) :
    ∀ ab, CycleQ2CurveCechTwoOpen.HasDegree ab g.1
      (CycleQ2CurveCechLocalizedBasis.localizedCoordinates ℂ side r ι {0}
        (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q) ab) := by
  obtain ⟨n,p,hp,hn⟩ :=
    (CycleQ2SeedQuotientGrading.localized_homogeneous_iff_fraction ℂ r ι
      (seedOpen {0}) q g).mp hq
  let β := coordinateScale ℂ side
  let c : ℂ := (β^n)⁻¹
  let π : CurvePoly ℂ →ₐ[ℂ] CL ℂ side r ι {0} :=
    (IsScalarTower.toAlgHom ℂ (CurveRing side r ι) (CL ℂ side r ι {0})).comp
      (Ideal.Quotient.mkₐ ℂ (curveIdeal side r ι))
  have hπC (a : ℂ) : π (C a)=algebraMap ℂ (CL ℂ side r ι {0}) a := π.commutes a
  have hβ : β≠0 := (isUnit_iff_ne_zero.mp (complex_scale_unit side))
  have hunit : algebraMap ℂ (CL ℂ side r ι {0}) c *
      algebraMap ℂ (CL ℂ side r ι {0}) (β^n)=1 := by
    rw [←map_mul]
    simp only [c,inv_mul_cancel₀ (pow_ne_zero n hβ),map_one]
  have hd : (g + CycleQ2SeedQuotientGrading.baseGrade
      (n • CycleQ2SeedCechLocalization.openExponent (seedOpen {0}))).1=
      g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0}) := by
    simp [CycleQ2SeedQuotientGrading.baseGrade,CycleQ2CurveQuotientGrading.baseDegree,
      CycleQ2SeedCechLocalization.openExponent,CycleQ2CurveCechLocalization.openExponent,
      seedOpen,baseIndex,Fin.sum_univ_succ,Matrix.cons_val_succ,Fin.reduceSucc]
  have hp' : CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ (substitution side r p)
      (g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0})) :=
    hd ▸ substitution_signedHomogeneous ℂ side r p _ hp
  have hp'' : CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ (C c*substitution side r p)
      (g.1 + CycleQ2CurveQuotientGrading.baseDegree
        (n • CycleQ2CurveCechLocalization.openExponent {0})) := by
    intro e he
    apply hp' e
    rw [coeff_C_mul] at he
    exact (mul_ne_zero_iff.mp he).2
  apply (CycleQ2CurveQuotientGrading.localized_homogeneous_iff_fraction ℂ side r ι {0}
    (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q) g.1).mpr
  refine ⟨n,C c*substitution side r p,hp'',?_⟩
  have hh := congrArg (baseOpenMap ℂ side r ι {0} (complex_scale_unit side)) hn
  simp only [map_mul,baseOpenMap_algebraMap,seedRestriction_mk] at hh
  have hden : seedRestriction side r ι
      (algebraMap (SB ℂ) (SeedRing r ι)
        (CycleQ2SeedCechLocalization.baseProduct ℂ (seedOpen {0}) ^ n))=
      algebraMap ℂ (CurveRing side r ι) (β^n)*
        algebraMap (CB ℂ) (CurveRing side r ι)
          (CycleQ2CurveCechLocalization.baseProduct ℂ {0} ^ n) := by
    simp only [map_pow]
    change (curveProduct ℂ side r ι (seedOpen {0}))^n=_
    rw [curveProduct_baseOpen]
    simp only [Finset.card_singleton,pow_one,mul_pow]
    rfl
  rw [hden,map_mul] at hh
  have hscalar : algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
      (algebraMap ℂ (CurveRing side r ι) (β^n))=
      algebraMap ℂ (CL ℂ side r ι {0}) (β^n) :=
    (IsScalarTower.algebraMap_apply ℂ (CurveRing side r ι) (CL ℂ side r ι {0}) (β^n)).symm
  rw [hscalar] at hh
  change _ = π (substitution side r p) at hh
  change _ = π (C c*substitution side r p)
  rw [map_mul,hπC]
  calc
    _ = (algebraMap ℂ (CL ℂ side r ι {0}) c *
        algebraMap ℂ (CL ℂ side r ι {0}) (β^n)) *
        (baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q *
          algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
            (algebraMap (CB ℂ) (CurveRing side r ι)
              (CycleQ2CurveCechLocalization.baseProduct ℂ {0} ^ n))) := by rw [hunit,one_mul]
    _ = algebraMap ℂ (CL ℂ side r ι {0}) c * π (substitution side r p) := by
      rw [←hh]
      ring

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.baseOpenMap_first_homogeneous
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


/- Component: continuation_3/SeedLinkageRestrictionKernel.lean -/
section
/-! On every nonempty coordinate open, the actual fixed-character linkage
ideal is exactly the kernel of restriction to the chosen actual curve. -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageRestrictionKernel

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover CycleQ2SeedLinkageComponents
  CycleQ2SeedLinkageOrbitKernel CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis

theorem component_one_global_eq (s : Side) (r ι : ℂ) :
    CycleQ2LinkageComponentDecomposition.componentIdeal (1:SeedRing r ι)
      (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)=
      CycleQ2CurveRestrictionKernel.componentIdeal s r ι := by
  cases s <;>
    simp only [CycleQ2LinkageComponentDecomposition.componentIdeal,
      CycleQ2LinkageComponentDecomposition.componentGenerator,Matrix.range_cons_cons_empty,
      orbitB,orbitD,linkageA,linkageB,linkageC,linkageD,
      CycleQ2CurveRestrictionKernel.componentIdeal,CycleQ2CurveRestrictionKernel.componentFirst,
      CycleQ2CurveRestrictionKernel.componentSecond,quotientMap,one_mul,one_pow,
      map_sub,map_add,map_mul,map_pow,map_neg,neg_neg,sub_neg_eq_add,sub_eq_add_neg]

theorem localComponent_one_eq (s : Side) (r ι : ℂ) (t : Finset (Fin 3)) :
    localComponent s r ι t 1=
      (CycleQ2CurveRestrictionKernel.componentIdeal s r ι).map
        (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)) := by
  rw [←component_one_global_eq s r ι]
  have h := @CycleQ2LinkageComponentAlgebra.map_componentIdeal
    (SeedRing r ι) (SeedLocal ℂ r ι t)
    (inferInstance : CommRing (SeedRing r ι)) (inferInstance : CommRing (SeedLocal ℂ r ι t))
    (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)) 1
    (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)
  simpa only [localComponent,map_one (localScalar r ι t),
    map_one (algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t))] using h.symm

 theorem homogeneous_mem_linkage_iff_restriction_zero (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty)
    (q : SeedLocal ℂ r ι t) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates ℂ r ι t q ab)) :
    q∈localLinkageIdeal s r ι t ↔
      CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ s r ι t q=0 := by
  rw [homogeneous_mem_linkage_iff_component s r ι hr hι hι1 t ht q g hq,
    localComponent_one_eq,← CycleQ2CurveRestrictionKernel.localized_kernel_eq_componentIdeal]
  rfl

end CycleQ2SeedLinkageRestrictionKernel

#print axioms CycleQ2SeedLinkageRestrictionKernel.homogeneous_mem_linkage_iff_restriction_zero
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechAmbientExact.lean -/
section
/-! # Actual ambient matrix Čech H1 exactness

The already checked contraction for graded scalar coordinate sections is
applied to the nine matrix entries. The three independent pair entries
then determine the complete ordered-pair cocycle.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions

variable (R : Type*) [CommRing R] [Nontrivial R]

def threeMatrices (r ι : R)
    (N0 : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {0}))
    (N1 : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {1}))
    (N2 : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {2})) : LocalMatrices R r ι :=
  Fin.cons N0 (Fin.cons N1 (Fin.cons N2 (fun i => Fin.elim0 i)))

/-- Every actual graded matrix cocycle is an actual graded matrix boundary. -/
theorem gradedMatrixCech_exact (r ι : R) (g : MatrixGrades)
    (P : pairGraded R r ι g) (hP : PairCocycle R r ι P.val) :
    ∃ N : localGraded R r ι g, overlapDifference R r ι N.val=P.val := by
  have hex (k l : Fin 3) := coordinateCech_exact R r ι (g k l)
    (P.val 0 1 k l) (P.val 0 2 k l) (P.val 1 2 k l)
    (P.property 0 1 k l) (P.property 0 2 k l) (P.property 1 2 k l)
    (congrArg (fun T : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι Finset.univ) => T k l)
      (hP 0 1 2))
  choose N0 N1 N2 hg0 hg1 hg2 he01 he02 he12 using hex
  let N : LocalMatrices R r ι := threeMatrices R r ι N0 N1 N2
  have hNg : LocalHasGrades R r ι g N := by
    intro i
    fin_cases i
    · change ∀ k l ab, HasGrade ab (g k l)
        (localizedCoordinates R r ι {0} (N0 k l) ab)
      exact hg0
    · change ∀ k l ab, HasGrade ab (g k l)
        (localizedCoordinates R r ι {1} (N1 k l) ab)
      exact hg1
    · change ∀ k l ab, HasGrade ab (g k l)
        (localizedCoordinates R r ι {2} (N2 k l) ab)
      exact hg2
  let Ng : localGraded R r ι g := ⟨N,hNg⟩
  refine ⟨Ng,?_⟩
  apply cocycle_eq_of_three R r ι _ _ (overlap_pairCocycle R r ι g Ng) hP
  · funext k l
    exact (he01 k l).symm
  · funext k l
    exact (he02 k l).symm
  · funext k l
    exact (he12 k l).symm

/-- In particular, every actual cofactor-kernel cocycle has an ambient
matrix preimage, with its prescribed grades preserved. -/
theorem kernelCech_ambient_preimage (r ι : R) (M : GlobalMatrix R r ι)
    (g : MatrixGrades) (P : kernelCocycles R r ι M g) :
    ∃ N : localGraded R r ι g, overlapDifference R r ι N.val=P.val := by
  have hp := kernelCocycle_properties R r ι M g P
  exact gradedMatrixCech_exact R r ι g ⟨P.val,hp.1⟩ hp.2.2

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.gradedMatrixCech_exact
#print axioms CycleQ2SegreCechConnecting.kernelCech_ambient_preimage
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechLifts.lean -/
section
/-! # The genuine graded connecting injection

A cofactor variation admitting actual graded local lifts has a class in the
actual kernel Čech cohomology. Its kernel is precisely the submodule generated
by actual global homogeneous polynomial cofactor variations. The construction
uses the quotient universal property, so it is linear without choosing a
linear family of local preimages.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 100000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates CycleQ2SeedCechGlobalGluing
  CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]


theorem localization_R_smul (r ι : R) (s : Finset (Fin 3)) (c : R) (p : SeedRing r ι) :
    algebraMap (SeedRing r ι) (SeedLocal R r ι s) (c • p)=
      c • algebraMap (SeedRing r ι) (SeedLocal R r ι s) p := by
  exact map_smul (IsScalarTower.toAlgHom R (SeedRing r ι) (SeedLocal R r ι s)).toLinearMap c p

def liftPairs (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Submodule R (GlobalMatrix R r ι × localGraded R r ι g) where
  carrier := {p | HasLocalLift R r ι M p.1 p.2.val}
  zero_mem' := by
    intro i
    change cofactorDifferential (localizeMatrix R r ι {i} M) 0=localizeMatrix R r ι {i} 0
    have hh := map_zero (cofactorDifferentialLinear (localizeMatrix R r ι {i} M))
    change cofactorDifferential (localizeMatrix R r ι {i} M) 0=0 at hh
    rw [hh]
    funext k l
    exact (map_zero (algebraMap (SeedRing r ι) (SeedLocal R r ι {i}))).symm
  add_mem' {p q} hp hq := by
    intro i
    change cofactorDifferential (localizeMatrix R r ι {i} M) (p.2.val i+q.2.val i)=
      localizeMatrix R r ι {i} (p.1+q.1)
    have hh := map_add (cofactorDifferentialLinear (localizeMatrix R r ι {i} M)) (p.2.val i) (q.2.val i)
    change cofactorDifferential (localizeMatrix R r ι {i} M) (p.2.val i+q.2.val i)=
      cofactorDifferential (localizeMatrix R r ι {i} M) (p.2.val i)+
      cofactorDifferential (localizeMatrix R r ι {i} M) (q.2.val i) at hh
    rw [hh,hp i,hq i]
    funext k l
    exact (map_add (algebraMap (SeedRing r ι) (SeedLocal R r ι {i})) _ _).symm
  smul_mem' c p hp := by
    intro i
    change cofactorDifferential (localizeMatrix R r ι {i} M) (c • p.2.val i)=
      localizeMatrix R r ι {i} (c • p.1)
    have hh := map_smul ((cofactorDifferentialLinear (localizeMatrix R r ι {i} M)).restrictScalars R)
      c (p.2.val i)
    change cofactorDifferential (localizeMatrix R r ι {i} M) (c • p.2.val i)=
      c • cofactorDifferential (localizeMatrix R r ι {i} M) (p.2.val i) at hh
    rw [hh,hp i]
    funext k l
    exact (localization_R_smul R r ι {i} c (p.1 k l)).symm

theorem mem_liftPairs_iff (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades)
    (p : GlobalMatrix R r ι × localGraded R r ι g) :
    p ∈ liftPairs R r ι M g ↔ HasLocalLift R r ι M p.1 p.2.val := Iff.rfl

def liftProjection (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    liftPairs R r ι M g →ₗ[R] GlobalMatrix R r ι :=
  (LinearMap.fst R _ _).comp (liftPairs R r ι M g).subtype

def liftCocycle (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    liftPairs R r ι M g →ₗ[R] kernelCocycles R r ι M g where
  toFun p := ⟨overlapDifference R r ι p.val.2.val,
    overlap_mem_kernelCocycles R r ι M p.val.1 g p.val.2
      ((mem_liftPairs_iff R r ι M g p.val).mp p.property)⟩
  map_add' p q := by
    apply Subtype.ext
    change overlapDifference R r ι (p.val.2.val+q.val.2.val)=
      overlapDifference R r ι p.val.2.val+overlapDifference R r ι q.val.2.val
    exact congrArg (fun q : pairGraded R r ι g => q.val)
      (map_add (overlapLinear R r ι g) p.val.2 q.val.2)
  map_smul' c p := by
    apply Subtype.ext
    change overlapDifference R r ι (c • p.val.2.val)=c • overlapDifference R r ι p.val.2.val
    exact congrArg (fun q : pairGraded R r ι g => q.val)
      (map_smul (overlapLinear R r ι g) c p.val.2)


end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.liftCocycle
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


/- Component: continuation_3/CurveRestrictionGluing.lean -/
section
/-! # Gluing the actual restrictions from all three seed charts -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionGluing

open CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2CurveLocalizedRestriction

theorem natural_apply (side : Side) (r ι : ℂ)
    {s t : Finset (Fin 3)} (hst : s⊆t) (q : SL ℂ r ι s) :
    CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι hst
      (localRestrictionMap ℂ side r ι s q)=
      localRestrictionMap ℂ side r ι t (CycleQ2SeedCechRestrictions.restriction ℂ r ι hst q) :=
  congrArg (fun f : SL ℂ r ι s →+* RestrictedLocal ℂ side r ι t => f q)
    (localRestrictionMap_natural ℂ side r ι hst)

theorem base_natural_apply (side : Side) (r ι : ℂ)
    {s t : Finset (Fin 2)} (hst : s⊆t) (q : SL ℂ r ι (seedOpen s)) :
    CycleQ2CurveCechRestrictions.restriction ℂ side r ι hst
      (baseOpenMap ℂ side r ι s (complex_scale_unit side) q)=
      baseOpenMap ℂ side r ι t (complex_scale_unit side)
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι (Finset.image_subset_image hst) q) :=
  congrArg (fun f : SL ℂ r ι (seedOpen s) →+* CL ℂ side r ι t => f q)
    (baseOpenMap_natural ℂ side r ι hst (complex_scale_unit side))

/-- Compatibility on the two indicated overlaps produces one original
homogeneous curve polynomial agreeing with all three actual restrictions. -/
theorem exists_homogeneous_gluing (side : Side) (r ι : ℂ)
    (q0 : SL ℂ r ι {0}) (q1 : SL ℂ r ι {1}) (q2 : SL ℂ r ι {2})
    (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hg0 : ∀ ab,CycleQ2SeedCechThreeOpen.HasGrade ab g
      (CycleQ2SeedCechLocalizedBasis.localizedCoordinates ℂ r ι {0} q0 ab))
    (h02 : localRestrictionMap ℂ side r ι {0,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({0}:Finset (Fin 3))⊆{0,2} by decide) q0)=
      localRestrictionMap ℂ side r ι {0,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{0,2} by decide) q2))
    (h12 : localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({1}:Finset (Fin 3))⊆{1,2} by decide) q1)=
      localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{1,2} by decide) q2)) :
    ∃ p : CurvePoly ℂ, Standard side p ∧
      CycleQ2CurveQuotientGrading.SignedHomogeneous ℂ p g.1 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {0})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {0} q0 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {1})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {1} q1 ∧
      algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {2} q2 := by
  let c0 := baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q0
  let c1 := baseOpenMap ℂ side r ι {1} (complex_scale_unit side) q2
  have hbase : CycleQ2CurveCechRestrictions.restriction ℂ side r ι
      (show ({0}:Finset (Fin 2))⊆{0,1} by decide) c0=
      CycleQ2CurveCechRestrictions.restriction ℂ side r ι
        (show ({1}:Finset (Fin 2))⊆{0,1} by decide) c1 := by
    rw [show c0=baseOpenMap ℂ side r ι {0} (complex_scale_unit side) q0 from rfl,
      show c1=baseOpenMap ℂ side r ι {1} (complex_scale_unit side) q2 from rfl,
      base_natural_apply,base_natural_apply]
    exact congrArg (baseOpenEquiv ℂ side r ι {0,1} (complex_scale_unit side)) h02
  obtain ⟨p,hp,hpg,hp0,hp2⟩ := CycleQ2CurvePairGluing.exists_homogeneous_gluing
    ℂ side r ι c0 c1 hbase g.1 (baseOpenMap_first_homogeneous side r ι q0 g hg0)
  have h0 : algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {0})
      (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {0} q0 := by
    apply (baseOpenEquiv ℂ side r ι {0} (complex_scale_unit side)).injective
    calc
      _ = algebraMap (CurveRing side r ι) (CL ℂ side r ι {0})
          (Ideal.Quotient.mk (curveIdeal side r ι) p) :=
        (baseOpenEquiv ℂ side r ι {0} (complex_scale_unit side)).commutes _
      _ = _ := hp0
  have h2 : algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
      (Ideal.Quotient.mk (curveIdeal side r ι) p)=localRestrictionMap ℂ side r ι {2} q2 := by
    apply (baseOpenEquiv ℂ side r ι {1} (complex_scale_unit side)).injective
    calc
      _ = algebraMap (CurveRing side r ι) (CL ℂ side r ι {1})
          (Ideal.Quotient.mk (curveIdeal side r ι) p) :=
        (baseOpenEquiv ℂ side r ι {1} (complex_scale_unit side)).commutes _
      _ = _ := hp2
  refine ⟨p,hp,hpg,h0,?_,h2⟩
  apply CycleQ2CurveOpenFaithfulness.middle_to_overlap_injective side r ι
  rw [restriction_algebraMap]
  calc
    _ = CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
        (show ({2}:Finset (Fin 3))⊆{1,2} by decide)
        (algebraMap (CurveRing side r ι) (RestrictedLocal ℂ side r ι {2})
          (Ideal.Quotient.mk (curveIdeal side r ι) p)) :=
      (restriction_algebraMap ℂ side r ι _ _).symm
    _ = CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
        (show ({2}:Finset (Fin 3))⊆{1,2} by decide)
        (localRestrictionMap ℂ side r ι {2} q2) := congrArg _ h2
    _ = localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({2}:Finset (Fin 3))⊆{1,2} by decide) q2) := natural_apply _ _ _ _ _
    _ = localRestrictionMap ℂ side r ι {1,2}
        (CycleQ2SeedCechRestrictions.restriction ℂ r ι
          (show ({1}:Finset (Fin 3))⊆{1,2} by decide) q1) := h12.symm
    _ = _ := (natural_apply _ _ _ _ _).symm

end CycleQ2CurveRestrictionGluing

#print axioms CycleQ2CurveRestrictionGluing.exists_homogeneous_gluing
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


/- Component: continuation_3/cylinder_bridge/SegreCechInjection.lean -/
section
/-! # The genuine graded connecting injection

A cofactor variation admitting actual graded local lifts has a class in the
actual kernel Čech cohomology. Its kernel is precisely the submodule generated
by actual global homogeneous polynomial cofactor variations. The construction
uses the quotient universal property, so it is linear without choosing a
linear family of local preimages.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option synthInstance.maxHeartbeats 100000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates CycleQ2SeedCechGlobalGluing
  CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]


def liftClass (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    liftPairs R r ι M g →ₗ[R] KernelCechH1 R r ι M g :=
  (kernelBoundaries R r ι M g).mkQ.comp (liftCocycle R r ι M g)

theorem liftClass_zero_iff (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades)
    (p : liftPairs R r ι M g) :
    liftClass R r ι M g p=0 ↔ GradedKernelBoundary R r ι M g p.val.2.val := by
  change (Submodule.Quotient.mk (liftCocycle R r ι M g p) : KernelCechH1 R r ι M g)=0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨K,hK⟩
    refine ⟨K.val.val,?_,K.val.property,?_⟩
    · intro i
      have hh : localD R r ι M g K.val=0 := K.property
      exact congrFun hh i
    · intro i j
      have hh := congrArg (fun q : kernelCocycles R r ι M g => q.val i j) hK
      exact hh.symm
  · rintro ⟨K,hKD,hKg,hNK⟩
    let Kg : localGraded R r ι g := ⟨K,hKg⟩
    have hKg0 : Kg ∈ LinearMap.ker (localD R r ι M g) := by
      change localD R r ι M g Kg=0
      funext i
      exact hKD i
    refine ⟨⟨Kg,hKg0⟩,?_⟩
    apply Subtype.ext
    funext i j
    exact (hNK i j).symm

theorem ker_projection_le_ker_class (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    LinearMap.ker (liftProjection R r ι M g) ≤ LinearMap.ker (liftClass R r ι M g) := by
  intro p hp
  apply (liftClass_zero_iff R r ι M g p).mpr
  have hN := (mem_liftPairs_iff R r ι M g p.val).mp p.property
  have hC : p.val.1=0 := hp
  refine ⟨p.val.2.val,?_,p.val.2.property,by intro i j; rfl⟩
  intro i
  rw [hC] at hN
  have hh := hN i
  change cofactorDifferential (localizeMatrix R r ι {i} M) (p.val.2.val i)=
    localizeMatrix R r ι {i} 0 at hh
  rw [hh]
  ext k l
  exact map_zero (algebraMap (SeedRing r ι) (SeedLocal R r ι {i}))

/-- Actual global variations that have actual graded local matrix lifts. -/
abbrev LocallyLiftableVariations (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :=
  LinearMap.range (liftProjection R r ι M g)

/-- The canonical linear connecting map, constructed by the quotient
universal property rather than by a presumed linear choice of local lifts. -/
def connectingToH1 (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    LocallyLiftableVariations R r ι M g →ₗ[R] KernelCechH1 R r ι M g :=
  @CycleQ2LinearRangeDescent.descendRange R (liftPairs R r ι M g)
    (GlobalMatrix R r ι) (KernelCechH1 R r ι M g)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (liftProjection R r ι M g) (liftClass R r ι M g)
    (ker_projection_le_ker_class R r ι M g)

theorem connectingToH1_apply_lift (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades)
    (p : liftPairs R r ι M g) :
    connectingToH1 R r ι M g ⟨liftProjection R r ι M g p,⟨p,rfl⟩⟩=
      liftClass R r ι M g p := by
  exact @CycleQ2LinearRangeDescent.descendRange_apply_image R (liftPairs R r ι M g)
    (GlobalMatrix R r ι) (KernelCechH1 R r ι M g)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (liftProjection R r ι M g) (liftClass R r ι M g)
    (ker_projection_le_ker_class R r ι M g) p

/-- The kernel is characterized by actual standard homogeneous polynomial
preimages in the original five-variable ring. -/
theorem connectingToH1_zero_iff (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades)
    (C : LocallyLiftableVariations R r ι M g) :
    connectingToH1 R r ι M g C=0 ↔
      ∃ P : Matrix (Fin 3) (Fin 3) (Poly R),
        (∀ k l, FullStandard (P k l)) ∧
        (∀ k l, SignedHomogeneous R (P k l) (g k l)) ∧
        cofactorDifferential M (quotientMatrix R r ι P)=C.val := by
  obtain ⟨p,hp⟩ := C.property
  have hC : C=⟨liftProjection R r ι M g p,⟨p,rfl⟩⟩ := Subtype.ext hp.symm
  rw [hC,connectingToH1_apply_lift,liftClass_zero_iff]
  exact gradedKernelBoundary_iff_homogeneous_lift R r ι M p.val.1 g p.val.2.val
    ((mem_liftPairs_iff R r ι M g p.val).mp p.property) p.val.2.property

/-- The actual homogeneous global cofactor image, defined by its literal
polynomial generators independently of the connecting map. -/
def globalHomogeneousImage (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Submodule R (LocallyLiftableVariations R r ι M g) :=
  Submodule.span R {C | ∃ P : Matrix (Fin 3) (Fin 3) (Poly R),
    (∀ k l, FullStandard (P k l)) ∧
    (∀ k l, SignedHomogeneous R (P k l) (g k l)) ∧
    cofactorDifferential M (quotientMatrix R r ι P)=C.val}

theorem ker_connectingToH1 (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    LinearMap.ker (connectingToH1 R r ι M g)=globalHomogeneousImage R r ι M g := by
  apply le_antisymm
  · intro C hC
    apply Submodule.subset_span
    exact (connectingToH1_zero_iff R r ι M g C).mp hC
  · apply Submodule.span_le.mpr
    intro C hC
    exact (connectingToH1_zero_iff R r ι M g C).mpr hC

abbrev GlobalCofactorObstruction (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :=
  @HasQuotient.Quotient (LocallyLiftableVariations R r ι M g)
    (Submodule R (LocallyLiftableVariations R r ι M g))
    (@Submodule.hasQuotient R (LocallyLiftableVariations R r ι M g)
      inferInstance inferInstance inferInstance)
    (globalHomogeneousImage R r ι M g)

/-- The actual global cofactor cokernel injects into the actual graded
kernel Čech cohomology. Local liftability is recorded by the domain, not
assumed to equal the relation kernel. -/
def connectingInjection (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    GlobalCofactorObstruction R r ι M g →ₗ[R] KernelCechH1 R r ι M g :=
  CycleQ2LinearRangeDescent.kernelQuotientInjection
    (connectingToH1 R r ι M g) (globalHomogeneousImage R r ι M g)
    (ker_connectingToH1 R r ι M g)

theorem connectingInjection_injective (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Function.Injective (connectingInjection R r ι M g) := by
  exact CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
    (connectingToH1 R r ι M g) (globalHomogeneousImage R r ι M g)
    (ker_connectingToH1 R r ι M g)

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.connectingToH1_zero_iff
#print axioms CycleQ2SegreCechConnecting.ker_connectingToH1
#print axioms CycleQ2SegreCechConnecting.connectingInjection_injective
end
end


