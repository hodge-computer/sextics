import Proposal.GeometricCartierOrbit
import Proposal.SolutionSupport03Part02

/-! Components extracted from SolutionSupport03.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/SegreModularCorrelationChecks6_11.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_11 : ∀a b : Fin 3,checkBlock weights6 1 1 a b=true := by
  decide +kernel

theorem entry6_11 : checkEntry weights6 1 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 1 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_11 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_11
end


/- Component: continuation_3/SegreModularCorrelationChecks6_12.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_12 : ∀a b : Fin 3,checkBlock weights6 1 2 a b=true := by
  decide +kernel

theorem entry6_12 : checkEntry weights6 1 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 1 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_12 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_12
end


/- Component: continuation_3/SegreModularCorrelationChecks6_20.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_20 : ∀a b : Fin 3,checkBlock weights6 2 0 a b=true := by
  decide +kernel

theorem entry6_20 : checkEntry weights6 2 0=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 0
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_20 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_20
end


/- Component: continuation_3/SegreModularCorrelationChecks6_21.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_21 : ∀a b : Fin 3,checkBlock weights6 2 1 a b=true := by
  decide +kernel

theorem entry6_21 : checkEntry weights6 2 1=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 1
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_21 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_21
end


/- Component: continuation_3/SegreModularCorrelationChecks6_22.lean -/
section
set_option maxHeartbeats 2000000000
set_option maxRecDepth 100000
set_option Elab.async false
namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SegreModularDetectorData CycleQ2SegreModularCorrelationExpressions
  CycleQ2SegreModularDetectorExpressions

theorem numeric6_22 : ∀a b : Fin 3,checkBlock weights6 2 2 a b=true := by
  decide +kernel

theorem entry6_22 : checkEntry weights6 2 2=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  exact checkEntryBlock_of_correlation weights6 2 2
    ⟨a,List.mem_range.mp ha⟩ ⟨b,List.mem_range.mp hb⟩
    (numeric6_22 _ _)

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.entry6_22
end


/- Component: continuation_3/SegreModularDetectorEntryBinding.lean -/
section
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorEntryBinding
open MvPolynomial CycleQ2SparseModularFunctional CycleQ2SparseGaussianPolynomial
  CycleQ2SegreModularDetectorExpressions CycleQ2SegreModularDetectorData
  CycleQ2IncidenceMonomials CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
  CycleQ2IncidenceUniversalChart CycleQ2GenericEntryCoefficientBinding

 theorem dotAction_eq_nf (W : WeightData) (r s i j a b : Fin 3) (u v : ℕ) :
    (dotAction W r s i j a b u v : F)=functional W r s
      (nf (57:F) 33 (rawSeedMatrix (57:F) i j*MvPolynomial.monomial
        (tupleExponent (a.val,u,v,14-(a.val+u+v+2*b.val),b.val)) 1)) := by
  unfold dotAction
  rw [flatActionTable_eq]
  exact CycleQ2SegreModularActionSemantics.dot_flat_action_eq_nf W r s i j a b u v

 theorem standardIndex_exponent (e : StandardIndex 14) :
    tupleExponent (e.val.1.1.val,e.val.2.1.val,e.val.2.2.val,
      14-(e.val.1.1.val+e.val.2.1.val+e.val.2.2.val+2*e.val.1.2.val),e.val.1.2.val)=
      standardExponent e := by
  ext l
  fin_cases l <;> rfl

 theorem basisMatrix_eq (i j : Fin 3) (e : StandardIndex 14) :
    CycleQ2SegreModularDetectorMatrixBinding.basisMatrix ((i,j),e)=
      CycleQ2SegreModularDetectorExpressions.basisMatrix i j
        (MvPolynomial.monomial (standardExponent e) (1:F)) := by
  funext r s
  rw [CycleQ2SegreModularDetectorMatrixBinding.basisMatrix_apply]
  simp only [CycleQ2SegreModularDetectorExpressions.basisMatrix,Prod.mk.injEq]

 theorem entry_column_eq_dot (k : Fin 7) (c : MatrixParameter) :
    (CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33) k c=
      (entryDot c.1.1 c.1.2 (weights k) c.2.val.1.1.val c.2.val.1.2.val
        c.2.val.2.1.val c.2.val.2.2.val : F) := by
  rcases c with ⟨⟨i,j⟩,e⟩
  rw [CycleQ2SegreModularDetectorMatrixBinding.detector_entry_column,basisMatrix_eq]
  have hd := firstRow_basisDifferential (rawSeedMatrix (57:F))
    (MvPolynomial.monomial (standardExponent e) (1:F))
    (fun s => (functional (weights k) 0 s).comp (nf (57:F) 33)) i j
  simp only [LinearMap.comp_apply] at hd
  rw [hd]
  symm
  rw [cast_entryDot]
  apply congrArg (signedEntry i j)
  funext s r t
  rw [dotAction_eq_nf,standardIndex_exponent]

 theorem annihilates_entry_of_checks
    (hc : ∀k : Fin 7,∀i j : Fin 3,checkEntry (weights k) i j=true) :
    CycleQ2SegreModularDetectorMatrixBinding.detectorMatrix*entryJacobianBlock (57:F) 33=0 := by
  ext k c
  rw [entry_column_eq_dot]
  have h := entryDot_zero_of_check (weights k) c.1.1 c.1.2 (hc k c.1.1 c.1.2)
    c.2.val.1.1.val c.2.val.1.2.val c.2.val.2.1.val c.2.val.2.2.val
    c.2.val.1.1.isLt c.2.val.1.2.isLt c.2.val.2.1.isLt c.2.val.2.2.isLt c.2.property
  rw [h,Nat.cast_zero]
  rfl

end CycleQ2SegreModularDetectorEntryBinding
#print axioms CycleQ2SegreModularDetectorEntryBinding.entry_column_eq_dot
#print axioms CycleQ2SegreModularDetectorEntryBinding.annihilates_entry_of_checks
end
end


/- Component: continuation_3/CurveCechGlobalGluing.lean -/
section
/-! # Augmented degree-zero exactness for the actual two-open seed complex

Compatible sections in the actual coordinate localizations glue uniquely to
the actual seed quotient. The proof uses the checked six free coordinates:
compatibility removes every possible negative base exponent. The same proof
preserves the original signed degree and produces an
actual homogeneous polynomial representative.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2CurveCechGlobalGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree CycleQ2CurveCechTwoOpen
  CycleQ2CurveCechLocalization CycleQ2CurveCechLocalizedBasis
  CycleQ2CurveCechRestrictions CycleQ2CurveQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

def globalCoordinates (side : Side) (r ι : R) (q : CurveRing side r ι) : (ShiftIndex side) → Laurent (R := R) :=
  fun ab => baseToLaurent R ((curveBasis R side r ι).repr q ab)

theorem globalCoordinates_injective (side : Side) (r ι : R) :
    Function.Injective (globalCoordinates R side r ι) := by
  intro p q hpq
  apply (curveBasis R side r ι).repr.injective
  apply Finsupp.ext
  intro ab
  exact baseToLaurent_injective R (congrFun hpq ab)

theorem mem_range_globalCoordinates (side : Side) (r ι : R) (p : (ShiftIndex side) → Laurent (R := R)) :
    p ∈ Set.range (globalCoordinates R side r ι) ↔ ∀ ab, HasPoles ∅ (p ab) := by
  constructor
  · rintro ⟨q,rfl⟩ ab
    exact baseToLaurent_hasPoles R _
  · intro hp
    choose a ha using fun ab => (mem_range_baseToLaurent R (p ab)).mpr (hp ab)
    refine ⟨(curveBasis R side r ι).repr.symm (Finsupp.equivFunOnFinite.symm a),?_⟩
    funext ab
    simpa only [globalCoordinates,LinearEquiv.apply_symm_apply,
      Finsupp.coe_equivFunOnFinite_symm] using ha ab

theorem localization_injective (side : Side) (r ι : R) (s : Finset (Fin 2)) :
    Function.Injective (algebraMap (CurveRing side r ι) (CurveLocal R side r ι s)) := by
  intro p q hpq
  apply globalCoordinates_injective R side r ι
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι s z ab) hpq
  simpa only [localizedCoordinates_algebraMap,globalCoordinates] using hh

abbrev Sections (side : Side) (r ι : R) := (i : Fin 2) → CurveLocal R side r ι {i}

def pairRestriction (side : Side) (r ι : R) (i j : Fin 2) :
    CurveLocal R side r ι {i} →+* CurveLocal R side r ι {i,j} :=
  restriction R side r ι (by simp)

def secondPairRestriction (side : Side) (r ι : R) (i j : Fin 2) :
    CurveLocal R side r ι {j} →+* CurveLocal R side r ι {i,j} :=
  restriction R side r ι (by simp)

def Compatible (side : Side) (r ι : R) (q : Sections R side r ι) : Prop :=
  ∀ i j, pairRestriction R side r ι i j (q i)=secondPairRestriction R side r ι i j (q j)

theorem compatible_coordinates (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) (i j : Fin 2) :
    localizedCoordinates R side r ι {i} (q i)=localizedCoordinates R side r ι {j} (q j) := by
  funext ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι {i,j} z ab) (hq i j)
  simpa only [pairRestriction,secondPairRestriction,coordinates_restriction] using hh

/-- The actual coordinate opens satisfy the augmented H0 gluing property. -/
theorem existsUnique_gluing (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) :
    ∃! p : CurveRing side r ι, ∀ i,
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i := by
  let c := localizedCoordinates R side r ι {0} (q 0)
  have hpoles (ab : (ShiftIndex side)) : HasPoles ∅ (c ab) := by
    intro e i _ hi
    by_cases hi0 : i=0
    · subst i
      change (localizedCoordinates R side r ι {0} (q 0) ab).coeff e=0
      rw [compatible_coordinates R side r ι q hq 0 1]
      exact localizedCoordinates_hasPoles R side r ι {1} (q 1) ab e 0 (by decide) hi
    · exact localizedCoordinates_hasPoles R side r ι {0} (q 0) ab e i (by simpa using hi0) hi
  obtain ⟨p,hp⟩ := (mem_range_globalCoordinates R side r ι c).mpr hpoles
  have hm (i : Fin 2) : algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i := by
    apply localizedCoordinates_injective R side r ι {i}
    funext ab
    rw [localizedCoordinates_algebraMap]
    change globalCoordinates R side r ι p ab=_
    rw [hp]
    exact congrFun (compatible_coordinates R side r ι q hq 0 i) ab
  refine ⟨p,hm,?_⟩
  intro p' hp'
  exact localization_injective R side r ι {0} ((hp' 0).trans (hm 0).symm)

/-- Grading is inherited by the glued quotient class from any chart. -/
theorem gluing_preserves_grade (side : Side) (r ι : R) (q : Sections R side r ι) (p : CurveRing side r ι)
    (hp : ∀ i, algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i}) p=q i)
    (g : ℤ) (hg : ∀ ab, HasDegree ab g (localizedCoordinates R side r ι {0} (q 0) ab)) :
    ∀ ab, HasDegree ab g (globalCoordinates R side r ι p ab) := by
  intro ab
  have hh := congrArg (fun z => localizedCoordinates R side r ι {0} z ab) (hp 0)
  rw [localizedCoordinates_algebraMap] at hh
  change HasDegree ab g (baseToLaurent R ((curveBasis R side r ι).repr p ab))
  rw [hh]
  exact hg ab

/-- Compatible graded local sections have an actual globally homogeneous
polynomial representative in the original four variables. -/
theorem exists_homogeneous_polynomial_gluing (side : Side) (r ι : R) (q : Sections R side r ι)
    (hq : Compatible R side r ι q) (g : ℤ)
    (hg : ∀ ab, HasDegree ab g (localizedCoordinates R side r ι {0} (q 0) ab)) :
    ∃ p : CurvePoly R, Standard side p ∧ SignedHomogeneous R p g ∧ ∀ i,
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {i})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q i := by
  obtain ⟨p,hp,_⟩ := existsUnique_gluing R side r ι q hq
  obtain ⟨P,hP,hPg,hPp⟩ := exists_signed_homogeneous_representative R side r ι p g
    (gluing_preserves_grade R side r ι q p hp g hg)
  exact ⟨P,hP,hPg,by simpa only [hPp] using hp⟩

end CycleQ2CurveCechGlobalGluing

#print axioms CycleQ2CurveCechGlobalGluing.existsUnique_gluing
#print axioms CycleQ2CurveCechGlobalGluing.exists_homogeneous_polynomial_gluing
end
end


/- Component: continuation_3/SeedCyclicLocalization.lean -/
section
/-! The actual diagonal action on each coordinate localization.  Homogeneous
fractions retain ideal membership when their image under the action belongs
to that ideal, by clearing a homogeneous numerator and a unit denominator. -/

noncomputable section
set_option maxHeartbeats 500000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCyclicLocalization

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedQuotientGrading CycleQ2SeedCyclicAction

variable {R : Type*} [CommRing R]

theorem homogeneous_mem_of_action_mem [Nontrivial R] (ζ : R) (hζ : ζ^3=1)
    (r ι : R) (s : Finset (Fin 3)) (q : SeedLocal R r ι s) (g : LaurentGrade)
    (hq : ∀ ab, HasGrade ab g (localizedCoordinates R r ι s q ab))
    (J : Ideal (SeedLocal R r ι s)) (hTq : localAction ζ hζ r ι s q∈J) : q∈J := by
  obtain ⟨n,p,hp,hfrac⟩ := (localized_homogeneous_iff_fraction R r ι s q g).mp hq
  let φ := algebraMap (SeedRing r ι) (SeedLocal R r ι s)
  let π := Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
  let den := φ (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n))
  let u := φ (π (C (ζ^(g+baseGrade (n • openExponent s)).2.val)))
  have hden : IsUnit den := by
    dsimp [den,φ]
    simpa only [map_pow] using (seedProduct_isUnit R r ι (Finset.Subset.refl s)).pow n
  have hu : IsUnit u := (cube_root_isUnit ζ hζ).pow _ |>.map ((φ.comp π).comp C)
  have ht : localAction ζ hζ r ι s q*localAction ζ hζ r ι s den∈J := by
    rw [mul_comm (localAction ζ hζ r ι s q) (localAction ζ hζ r ι s den)]
    exact J.mul_mem_left _ hTq
  have he := congrArg (localAction ζ hζ r ι s) hfrac
  rw [map_mul,localAction_mk,polynomialAction_signedHomogeneous ζ hζ p _ hp,map_mul,map_mul] at he
  change localAction ζ hζ r ι s q*localAction ζ hζ r ι s den=u*(φ (π p)) at he
  change q*den=φ (π p) at hfrac
  rw [←hfrac] at he
  rw [he] at ht
  have hqd : q*den∈J := (J.unit_mul_mem_iff_mem hu).mp ht
  apply (J.unit_mul_mem_iff_mem hden).mp
  rw [mul_comm den q]
  exact hqd

end CycleQ2SeedCyclicLocalization

#print axioms CycleQ2SeedCyclicLocalization.localAction
#print axioms CycleQ2SeedCyclicLocalization.homogeneous_mem_of_action_mem
end
end


/- Component: continuation_3/SeedLinkageComponents.lean -/
section
/-! The literal three-component intersection for each actual linkage ideal
on every nonempty coordinate localization of the complex seed. -/

noncomputable section
set_option maxHeartbeats 100000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageComponents

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedCechLocalizedBasis

variable {K : Type*} [Field K]

def orbitB (s : Side) (r ι : K) : SeedRing r ι :=
  match s with | .left => linkageB r ι | .right => -linkageD r ι

def orbitD (s : Side) (r ι : K) : SeedRing r ι :=
  match s with | .left => linkageD r ι | .right => -linkageB r ι

theorem linkageIdeal_eq_generic (s : Side) (r ι : K) :
    linkageIdeal s r ι=leftIdeal (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι) := by
  cases s
  · change Ideal.span (Set.range (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j)))=_
    have hfun : (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageE (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j))=
        CycleQ2SegreSeed.linkageE (linkageA r ι) (linkageB r ι) (linkageC r ι) (linkageD r ι) := by
      funext j
      exact map_linkageE (quotientMap r ι) _ _ _ _ j
    rw [hfun]
    rfl
  · change Ideal.span (Set.range (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j)))=_
    have hfun : (fun j => quotientMap r ι
        (CycleQ2SegreSeed.linkageEprime (X 0^2) (C r*X 1*X 3) (X 4) (X 2^2) j))=
        CycleQ2SegreSeed.linkageEprime (linkageA r ι) (linkageB r ι) (linkageC r ι) (linkageD r ι) := by
      funext j
      exact map_linkageEprime (quotientMap r ι) _ _ _ _ j
    rw [hfun,rightIdeal_eq_leftIdeal]
    rfl

theorem span_pair_neg_swap {A : Type*} [CommRing A] (b d : A) :
    Ideal.span ({-d,-b} : Set A)=Ideal.span {b,d} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      exact (Ideal.span ({b,d}:Set A)).neg_mem (Ideal.subset_span (by simp))
    · rw [Set.mem_singleton_iff.mp hx]
      exact (Ideal.span ({b,d}:Set A)).neg_mem (Ideal.subset_span (by simp))
  · apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]
      have h : -b∈Ideal.span ({-d,-b}:Set A) := Ideal.subset_span (by simp)
      exact (Ideal.span ({-d,-b}:Set A)).neg_mem_iff.mp h
    · rw [Set.mem_singleton_iff.mp hx]
      have h : -d∈Ideal.span ({-d,-b}:Set A) := Ideal.subset_span (by simp)
      exact (Ideal.span ({-d,-b}:Set A)).neg_mem_iff.mp h

def localScalar (r ι : K) (t : Finset (Fin 3)) : K →+* SeedLocal K r ι t :=
  ((algebraMap (SeedRing r ι) (SeedLocal K r ι t)).comp (quotientMap r ι)).comp C

def localLinkageIdeal (s : Side) (r ι : K) (t : Finset (Fin 3)) : Ideal (SeedLocal K r ι t) :=
  (linkageIdeal s r ι).map (algebraMap (SeedRing r ι) (SeedLocal K r ι t))

def localComponent (s : Side) (r ι : K) (t : Finset (Fin 3)) (z : K) : Ideal (SeedLocal K r ι t) :=
  componentIdeal (localScalar r ι t z)
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageA r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageC r ι))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι))

theorem localLinkageIdeal_eq_generic (s : Side) (r ι : K) (t : Finset (Fin 3)) :
    localLinkageIdeal s r ι t=
      leftIdeal (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageA r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageC r ι))
        (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι)) := by
  rw [localLinkageIdeal,linkageIdeal_eq_generic]
  exact @map_leftIdeal (SeedRing r ι) (SeedLocal K r ι t)
    (inferInstance : CommRing (SeedRing r ι)) (inferInstance : CommRing (SeedLocal K r ι t))
    (algebraMap (SeedRing r ι) (SeedLocal K r ι t))
    (linkageA r ι) (orbitB s r ι) (linkageC r ι) (orbitD s r ι)

theorem local_orbit_vertex_cover (s : Side) (r ι : K)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    localLinkageIdeal s r ι t ⊔
      Ideal.span {algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitB s r ι),
        algebraMap (SeedRing r ι) (SeedLocal K r ι t) (orbitD s r ι)}=⊤ := by
  cases s
  · exact localized_vertex_cover .left r ι hr hι hι1 t ht
  · simp only [orbitB,orbitD,map_neg]
    rw [span_pair_neg_swap
      (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageB r ι))
      (algebraMap (SeedRing r ι) (SeedLocal K r ι t) (linkageD r ι))]
    exact localized_vertex_cover .right r ι hr hι hι1 t ht

theorem localized_linkageIdeal_eq_components (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    @localLinkageIdeal ℂ (inferInstance : Field ℂ) s r ι t=
      (@localComponent ℂ (inferInstance : Field ℂ) s r ι t 1 ⊓
        @localComponent ℂ (inferInstance : Field ℂ) s r ι t complexRoot) ⊓
        @localComponent ℂ (inferInstance : Field ℂ) s r ι t (complexRoot^2) := by
  let φ := algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)
  let z := localScalar r ι t complexRoot
  have hz : z^2+z+1=0 := by
    simpa only [map_add (localScalar r ι t),map_pow (localScalar r ι t),
      map_one (localScalar r ι t),map_zero (localScalar r ι t)] using
      congrArg (localScalar r ι t) complexRoot_quadratic
  have hcover := @local_orbit_vertex_cover ℂ (inferInstance : Field ℂ) s r ι hr hι hι1 t ht
  rw [localLinkageIdeal_eq_generic s r ι t] at hcover ⊢
  have h := @leftIdeal_eq_components (SeedLocal ℂ r ι t)
    (inferInstance : CommRing (SeedLocal ℂ r ι t)) z (φ (linkageA r ι)) (φ (orbitB s r ι))
    (φ (linkageC r ι)) (φ (orbitD s r ι)) hz
    (@mapped_root_units (SeedLocal ℂ r ι t) (inferInstance : CommRing (SeedLocal ℂ r ι t))
      (localScalar r ι t)) hcover
  simpa only [localComponent,map_one (localScalar r ι t),map_pow (localScalar r ι t)] using h

end CycleQ2SeedLinkageComponents

#print axioms CycleQ2SeedLinkageComponents.localized_linkageIdeal_eq_components
end
end


/- Component: continuation_3/SeedLinkageModularSeed.lean -/
section
set_option maxRecDepth 100000

set_option maxHeartbeats 0

set_option Elab.async false

set_option backward.isDefEq.respectTransparency false

set_option linter.unusedSimpArgs false

namespace CycleQ2SeedLinkageModularChecks

open MvPolynomial CycleQ2IncidenceEquations CycleQ2CurveRestriction CycleQ2CurveRestrictionReflection

open CycleQ2SparseModularPolynomial CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageSections

open CycleQ2SeedLinkageReflection CycleQ2CurveRestrictionMatrixCheck CycleQ2SeedLinkageModularData

noncomputable section

variable {R : Type*} [CommRing R] [CharP R 109]

theorem seedH_value : fullValue (R:=R) CycleQ2SeedLinkageModularData.seedH = smoothH (33:R) := by

  have hc : CharP (Poly R) 109 := inferInstance

  simp only [CycleQ2SeedLinkageModularData.seedH, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, smoothH, smoothB, smoothA]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

theorem seedG_value : fullValue (R:=R) CycleQ2SeedLinkageModularData.seedG = CycleQ2IncidenceEquations.seedG (57:R) := by

  have hc : CharP (Poly R) 109 := inferInstance

  simp only [CycleQ2SeedLinkageModularData.seedG, fullValue, CycleQ2SparseModularPolynomial.eval,
      CycleQ2SparseModularPolynomial.termValue, CycleQ2SparseModularPolynomial.monomial,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.cast_ofNat, pow_zero, pow_one, one_pow, mul_zero, mul_one, zero_mul, zero_add, add_zero,
      Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, map_ofNat, map_zero, map_one, map_add, map_sub, map_mul, map_neg, CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG]

  apply sub_eq_zero.mp

  ring_nf <;> reduce_mod_char!

end

end CycleQ2SeedLinkageModularChecks
end


/- Component: continuation_3/cylinder_bridge/SeedLocalizedClearing.lean -/
section
/-! # Common polynomial denominators in the actual seed coordinate charts -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SeedLocalizedClearing

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R]

def openPolynomial (s : Finset (Fin 3)) : Poly R :=
  remainingInclusion R (baseProduct R s)

def openGrade (s : Finset (Fin 3)) : Grade :=
  ∑ i ∈ s, fullGrading (remainingIndex i)

def polynomialMap (r ι : R) (s : Finset (Fin 3)) : Poly R →+* SeedLocal R r ι s :=
  (algebraMap (SeedRing r ι) (SeedLocal R r ι s)).comp
    (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))

@[simp] theorem quotient_openPolynomial (r ι : R) (s : Finset (Fin 3)) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (openPolynomial R s)=
      algebraMap (Base R) (SeedRing r ι) (baseProduct R s) := rfl

/-- The actual chart denominator is homogeneous for the original grading. -/
theorem openPolynomial_homogeneous (s : Finset (Fin 3)) :
    HG (openPolynomial R s) (openGrade s) := by
  unfold openPolynomial baseProduct
  rw [map_prod]
  apply IsWeightedHomogeneous.prod
  intro i hi
  simpa [remainingInclusion] using isWeightedHomogeneous_X R fullGrading (remainingIndex i)

def signedGradeHom : Grade →+ LaurentGrade where
  toFun := signedGrade
  map_zero' := rfl
  map_add' a b := by
    apply Prod.ext
    · exact Nat.cast_add _ _
    · rfl

theorem signed_openGrade : ∀ s : Finset (Fin 3),
    signedGrade (openGrade s)=baseGrade (openExponent s) := by decide

theorem signed_openGrade_nsmul (s : Finset (Fin 3)) (n : ℕ) :
    signedGrade (n • openGrade s)=baseGrade (n • openExponent s) := by
  change signedGradeHom (n • openGrade s)=_
  rw [map_nsmul]
  change n • signedGrade (openGrade s)=_
  rw [signed_openGrade,map_nsmul]

/-- Nine arbitrary actual local entries can be cleared with one power of
the chart denominator and lifted to the original polynomial ring. -/
theorem exists_common_polynomial_denominator (r ι : R) (s : Finset (Fin 3))
    (N : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s)) :
    ∃ (n : ℕ) (P : Matrix (Fin 3) (Fin 3) (Poly R)),
      ∀ i j, polynomialMap R r ι s (P i j)=
        polynomialMap R r ι s (openPolynomial R s ^ n)*N i j := by
  let d : SeedRing r ι := algebraMap (Base R) (SeedRing r ι) (baseProduct R s)
  obtain ⟨den,hden⟩ := IsLocalization.exist_integer_multiples_of_finite
    (Submonoid.powers d) (fun q : Fin 3 × Fin 3 => N q.1 q.2)
  choose a ha using hden
  obtain ⟨n,hn⟩ := den.property
  choose P hP using fun q : Fin 3 × Fin 3 =>
    Ideal.Quotient.mk_surjective (a q)
  refine ⟨n,fun i j => P (i,j),?_⟩
  intro i j
  have hh := ha (i,j)
  change algebraMap (SeedRing r ι) (SeedLocal R r ι s) (a (i,j))=
    (den : SeedRing r ι) • N i j at hh
  rw [← hP (i,j),← hn] at hh
  change algebraMap (SeedRing r ι) (SeedLocal R r ι s)
    (Ideal.Quotient.mk _ (P (i,j)))=(d^n) • N i j at hh
  rw [Algebra.smul_def (R := SeedRing r ι) (A := SeedLocal R r ι s)] at hh
  change polynomialMap R r ι s (P (i,j))=
    algebraMap (SeedRing r ι) (SeedLocal R r ι s) (d^n)*N i j at hh
  simpa only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial,d] using hh

end CycleQ2SeedLocalizedClearing

#print axioms CycleQ2SeedLocalizedClearing.exists_common_polynomial_denominator
#print axioms CycleQ2SeedLocalizedClearing.openPolynomial_homogeneous
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechConnecting.lean -/
section
/-! # The actual Čech connecting obstruction for the Segre cofactor map

Local preimages of a global cofactor variation differ by sections of the
actual cofactor-differential kernel. Their overlap differences form a Čech
cocycle. It is a kernel-valued boundary exactly when the variation admits a
global matrix preimage. The crucial gluing step uses the proved augmented
complex of the literal seed localizations, not an assumed sheaf exactness.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechGlobalGluing

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev GlobalMatrix (r ι : R) := Matrix (Fin 3) (Fin 3) (SeedRing r ι)
abbrev LocalMatrices (r ι : R) := (i : Fin 3) → Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {i})

def localizeMatrix (r ι : R) (s : Finset (Fin 3)) (M : GlobalMatrix R r ι) :
    Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s) :=
  (algebraMap (SeedRing r ι) (SeedLocal R r ι s)).mapMatrix M

theorem restrict_localizeMatrix (r ι : R) {s t : Finset (Fin 3)} (hst : s ⊆ t)
    (M : GlobalMatrix R r ι) :
    (restriction R r ι hst).mapMatrix (localizeMatrix R r ι s M)=
      localizeMatrix R r ι t M := by
  ext k l
  exact restriction_algebraMap R r ι hst (M k l)

theorem restriction_comp (r ι : R) {s t u : Finset (Fin 3)}
    (hst : s ⊆ t) (htu : t ⊆ u) (p : SeedLocal R r ι s) :
    restriction R r ι htu (restriction R r ι hst p)=
      restriction R r ι (hst.trans htu) p := by
  apply localizedCoordinates_injective R r ι u
  funext ab
  simp only [coordinates_restriction]

theorem cofactorDifferential_sub {A : Type*} [CommRing A]
    (M N K : Matrix (Fin 3) (Fin 3) A) :
    cofactorDifferential M (N-K)=cofactorDifferential M N-cofactorDifferential M K :=
  map_sub (cofactorDifferentialLinear M) N K

def overlapDifference (r ι : R) (N : LocalMatrices R r ι) (i j : Fin 3) :
    Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {i,j}) :=
  (secondPairRestriction R r ι i j).mapMatrix (N j)-
    (pairRestriction R r ι i j).mapMatrix (N i)

def HasLocalLift (r ι : R) (M C : GlobalMatrix R r ι) (N : LocalMatrices R r ι) : Prop :=
  ∀ i, cofactorDifferential (localizeMatrix R r ι {i} M) (N i)=
    localizeMatrix R r ι {i} C

/-- The overlap differences lie in the kernel of the literal cofactor map. -/
theorem overlapDifference_kernel (r ι : R) (M C : GlobalMatrix R r ι)
    (N : LocalMatrices R r ι) (hN : HasLocalLift R r ι M C N) (i j : Fin 3) :
    cofactorDifferential (localizeMatrix R r ι {i,j} M)
      (overlapDifference R r ι N i j)=0 := by
  have hi := map_cofactorDifferential (B := SeedLocal R r ι {i,j}) (pairRestriction R r ι i j)
    (localizeMatrix R r ι {i} M) (N i)
  have hj := map_cofactorDifferential (B := SeedLocal R r ι {i,j}) (secondPairRestriction R r ι i j)
    (localizeMatrix R r ι {j} M) (N j)
  rw [hN i] at hi
  rw [hN j] at hj
  simp only [pairRestriction,secondPairRestriction,restrict_localizeMatrix] at hi hj
  simp only [overlapDifference,cofactorDifferential_sub,pairRestriction,secondPairRestriction]
  rw [← hj,← hi,sub_self]

/-- The actual three-open cocycle identity, after canonical restriction to
the triple overlap. -/
theorem overlapDifference_cocycle (r ι : R) (N : LocalMatrices R r ι) :
    (restriction R r ι (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 0 1) -
      (restriction R r ι (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 0 2) +
      (restriction R r ι (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)).mapMatrix
        (overlapDifference R r ι N 1 2)=0 := by
  ext k l
  change restriction R r ι (show ({0,1} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 0 1 (N 1 k l)-pairRestriction R r ι 0 1 (N 0 k l)) - restriction R r ι (show ({0,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 0 2 (N 2 k l)-pairRestriction R r ι 0 2 (N 0 k l)) + restriction R r ι (show ({1,2} : Finset (Fin 3)) ⊆ Finset.univ by decide)
      (secondPairRestriction R r ι 1 2 (N 2 k l)-pairRestriction R r ι 1 2 (N 1 k l))=0
  simp only [map_sub,pairRestriction,secondPairRestriction,restriction_comp]
  abel

def KernelBoundary (r ι : R) (M : GlobalMatrix R r ι) (N : LocalMatrices R r ι) : Prop :=
  ∃ K : LocalMatrices R r ι,
    (∀ i, cofactorDifferential (localizeMatrix R r ι {i} M) (K i)=0) ∧
    ∀ i j, overlapDifference R r ι N i j=overlapDifference R r ι K i j

/-- Entrywise augmented gluing for the actual nine matrix coefficients. -/
theorem exists_matrix_gluing (r ι : R) (Q : LocalMatrices R r ι)
    (hQ : ∀ i j, (pairRestriction R r ι i j).mapMatrix (Q i)=
      (secondPairRestriction R r ι i j).mapMatrix (Q j)) :
    ∃ P : GlobalMatrix R r ι, ∀ i, localizeMatrix R r ι {i} P=Q i := by
  have hc (k l : Fin 3) : Compatible R r ι (fun i => Q i k l) := by
    intro i j
    exact congrArg (fun T => T k l) (hQ i j)
  choose P hP using fun k l => (existsUnique_gluing R r ι (fun i => Q i k l) (hc k l)).exists
  refine ⟨P,?_⟩
  intro i
  ext k l
  exact hP k l i

theorem global_differential_of_local (r ι : R) (M C P : GlobalMatrix R r ι)
    (hP : cofactorDifferential (localizeMatrix R r ι {0} M)
      (localizeMatrix R r ι {0} P)=localizeMatrix R r ι {0} C) :
    cofactorDifferential M P=C := by
  have hh := map_cofactorDifferential (B := SeedLocal R r ι {0})
    (algebraMap (SeedRing r ι) (SeedLocal R r ι {0})) M P
  change localizeMatrix R r ι {0} (cofactorDifferential M P)=
    cofactorDifferential (localizeMatrix R r ι {0} M) (localizeMatrix R r ι {0} P) at hh
  rw [hP] at hh
  ext k l
  apply localization_injective R r ι {0}
  exact congrArg (fun T => T k l) hh

/-- The zero-class criterion for the actual connecting obstruction. No rank
bound, global preimage, or cohomology vanishing is assumed. -/
theorem kernelBoundary_iff_global_lift (r ι : R) (M C : GlobalMatrix R r ι)
    (N : LocalMatrices R r ι) (hN : HasLocalLift R r ι M C N) :
    KernelBoundary R r ι M N ↔ ∃ P : GlobalMatrix R r ι, cofactorDifferential M P=C := by
  constructor
  · rintro ⟨K,hK,hNK⟩
    let Q : LocalMatrices R r ι := fun i => N i-K i
    have hQ (i j : Fin 3) : (pairRestriction R r ι i j).mapMatrix (Q i)=
        (secondPairRestriction R r ι i j).mapMatrix (Q j) := by
      ext k l
      have hh := congrArg (fun T => T k l) (hNK i j)
      change secondPairRestriction R r ι i j (N j k l)-pairRestriction R r ι i j (N i k l)=
        secondPairRestriction R r ι i j (K j k l)-pairRestriction R r ι i j (K i k l) at hh
      change pairRestriction R r ι i j (N i k l-K i k l)=
        secondPairRestriction R r ι i j (N j k l-K j k l)
      rw [map_sub,map_sub]
      linear_combination -hh
    obtain ⟨P,hP⟩ := exists_matrix_gluing R r ι Q hQ
    refine ⟨P,global_differential_of_local R r ι M C P ?_⟩
    rw [hP 0]
    change cofactorDifferential _ (N 0-K 0)=_
    rw [cofactorDifferential_sub,hN 0,hK 0,sub_zero]
  · rintro ⟨P,hP⟩
    let K : LocalMatrices R r ι := fun i => N i-localizeMatrix R r ι {i} P
    refine ⟨K,?_,?_⟩
    · intro i
      change cofactorDifferential _ (N i-localizeMatrix R r ι {i} P)=0
      rw [cofactorDifferential_sub,hN i]
      have hh := map_cofactorDifferential (B := SeedLocal R r ι {i})
        (algebraMap (SeedRing r ι) (SeedLocal R r ι {i})) M P
      rw [hP] at hh
      change localizeMatrix R r ι {i} C=cofactorDifferential
        (localizeMatrix R r ι {i} M) (localizeMatrix R r ι {i} P) at hh
      rw [← hh,sub_self]
    · intro i j
      ext k l
      have hi := restriction_algebraMap R r ι
        (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) (P k l)
      have hj := restriction_algebraMap R r ι
        (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) (P k l)
      change secondPairRestriction R r ι i j (N j k l)-pairRestriction R r ι i j (N i k l) = secondPairRestriction R r ι i j
        (N j k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {j}) (P k l))-
        pairRestriction R r ι i j
          (N i k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) (P k l))
      simp only [map_sub,pairRestriction,secondPairRestriction,hi,hj]
      abel

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.overlapDifference_kernel
#print axioms CycleQ2SegreCechConnecting.overlapDifference_cocycle
#print axioms CycleQ2SegreCechConnecting.kernelBoundary_iff_global_lift
end
end


/- Component: continuation_3/SegreModularCorrelationChecks.lean -/
section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SegreModularCorrelationChecks
open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2SegreModularDetectorExpressions

theorem checkEntry_first_row (W : WeightData) (j : Fin 3) :
    checkEntry W 0 j=true := by
  have hz (a b u v : ℕ) : entryDot 0 j W a b u v=0 := by
    fin_cases j <;> rfl
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  apply List.all_eq_true.mpr
  intro u hu
  apply List.all_eq_true.mpr
  intro v hv
  simp [hz]

theorem all_entry_checks (k : Fin 7) (i j : Fin 3) :
    checkEntry (weights k) i j=true := by
  fin_cases k <;> fin_cases i <;> fin_cases j
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry0_10
  · exact entry0_11
  · exact entry0_12
  · exact entry0_20
  · exact entry0_21
  · exact entry0_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry1_10
  · exact entry1_11
  · exact entry1_12
  · exact entry1_20
  · exact entry1_21
  · exact entry1_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry2_10
  · exact entry2_11
  · exact entry2_12
  · exact entry2_20
  · exact entry2_21
  · exact entry2_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry3_10
  · exact entry3_11
  · exact entry3_12
  · exact entry3_20
  · exact entry3_21
  · exact entry3_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry4_10
  · exact entry4_11
  · exact entry4_12
  · exact entry4_20
  · exact entry4_21
  · exact entry4_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry5_10
  · exact entry5_11
  · exact entry5_12
  · exact entry5_20
  · exact entry5_21
  · exact entry5_22
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact checkEntry_first_row _ _
  · exact entry6_10
  · exact entry6_11
  · exact entry6_12
  · exact entry6_20
  · exact entry6_21
  · exact entry6_22

end CycleQ2SegreModularCorrelationChecks
#print axioms CycleQ2SegreModularCorrelationChecks.all_entry_checks
end


/- Component: continuation_3/CurveCoordinateCover.lean -/
section
/-! # The two base-coordinate opens cover each actual projective curve -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveCoordinateCover

open MvPolynomial CycleQ2CurveRestriction

variable {R : Type*} [CommRing R]

theorem zero_coordinates {S : Type*} [CommRing S] [IsDomain S]
    (side : Side) (r ι : R) (ψ : CurvePoly R →+* S)
    (hQ : ψ (quadric side r)=0) (hH : ψ (cubic side r ι)=0)
    (h1 : ψ (X 1)=0) (h3 : ψ (X 3)=0) : ∀ j : Fin 4,ψ (X j)=0 := by
  cases side
  · have h0 : ψ (X 0)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=2)
      simpa only [quadric,map_sub,map_mul,map_pow,h1,h3,mul_zero,sub_zero] using hQ
    have h2 : ψ (X 2)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=3)
      simpa only [cubic,map_add,map_sub,map_mul,map_pow,h0,h1,h3,zero_mul,mul_zero,
        zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),add_zero,sub_zero] using hH
    intro j
    fin_cases j <;> assumption
  · have h0 : ψ (X 0)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=3)
      simpa only [cubic,map_add,map_sub,map_mul,map_pow,h1,h3,zero_mul,mul_zero,
        zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),add_zero,sub_zero] using hH
    have h2 : ψ (X 2)=0 := by
      apply eq_zero_of_pow_eq_zero (n:=2)
      simpa only [quadric,map_add,map_pow,h0,zero_pow (by decide : 2≠0),add_zero] using hQ
    intro j
    fin_cases j <;> assumption

def coordinate (side : Side) (r ι : R) (j : Fin 4) : CurveRing side r ι :=
  Ideal.Quotient.mk _ (X j)

/-- The statement holds at every relevant prime, not just closed points. -/
theorem prime_cover (side : Side) (r ι : R) (P : Ideal (CurveRing side r ι))
    (hP : P.IsPrime) (hrelevant : ∃ j,coordinate side r ι j∉P) :
    coordinate side r ι 1∉P ∨ coordinate side r ι 3∉P := by
  letI : P.IsPrime := hP
  by_contra hn
  have h1 : coordinate side r ι 1∈P := by tauto
  have h3 : coordinate side r ι 3∈P := by tauto
  let ψ : CurvePoly R →+* (CurveRing side r ι ⧸ P) :=
    (Ideal.Quotient.mk P).comp (Ideal.Quotient.mk (curveIdeal side r ι))
  have hQ : ψ (quadric side r)=0 := by
    have hz : Ideal.Quotient.mk (curveIdeal side r ι) (quadric side r)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [curveIdeal]))
    change Ideal.Quotient.mk P (Ideal.Quotient.mk _ (quadric side r))=0
    rw [hz,map_zero]
  have hH : ψ (cubic side r ι)=0 := by
    have hz : Ideal.Quotient.mk (curveIdeal side r ι) (cubic side r ι)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [curveIdeal]))
    change Ideal.Quotient.mk P (Ideal.Quotient.mk _ (cubic side r ι))=0
    rw [hz,map_zero]
  have hz1 : ψ (X 1)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h1
  have hz3 : ψ (X 3)=0 := Ideal.Quotient.eq_zero_iff_mem.mpr h3
  have hz : ∀ j : Fin 4, ψ (X j)=0 :=
    zero_coordinates (R:=R) (S:=CurveRing side r ι ⧸ P) side r ι ψ hQ hH hz1 hz3
  obtain ⟨j,hj⟩ := hrelevant
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp (hz j))

end CycleQ2CurveCoordinateCover

#print axioms CycleQ2CurveCoordinateCover.prime_cover
end
end


/- Component: continuation_3/CurvePairGluing.lean -/
section
/-! # Two-chart gluing with one explicit overlap equality -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurvePairGluing

open CycleQ2CurveRestriction CycleQ2CurveQuotientFiniteFree
  CycleQ2CurveCechTwoOpen CycleQ2CurveCechLocalizedBasis
  CycleQ2CurveCechRestrictions CycleQ2CurveQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

def sections (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    CycleQ2CurveCechGlobalGluing.Sections R side r ι :=
  Fin.cons q0 (Fin.cons q1 (fun i => Fin.elim0 i))

@[simp] theorem sections_zero (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    sections R side r ι q0 q1 0=q0 := rfl

@[simp] theorem sections_one (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1}) :
    sections R side r ι q0 q1 1=q1 := rfl

theorem compatible (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1})
    (h : restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0=
      restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1) :
    CycleQ2CurveCechGlobalGluing.Compatible R side r ι (sections R side r ι q0 q1) := by
  have hc : localizedCoordinates R side r ι {0} q0=localizedCoordinates R side r ι {1} q1 := by
    funext ab
    have hh := congrArg (fun z => localizedCoordinates R side r ι {0,1} z ab) h
    simpa only [coordinates_restriction] using hh
  intro i j
  apply localizedCoordinates_injective R side r ι {i,j}
  funext ab
  simp only [CycleQ2CurveCechGlobalGluing.pairRestriction,
    CycleQ2CurveCechGlobalGluing.secondPairRestriction,coordinates_restriction]
  fin_cases i <;> fin_cases j
  · rfl
  · change localizedCoordinates R side r ι {0} q0 ab=
      localizedCoordinates R side r ι {1} q1 ab
    exact congrFun hc ab
  · change localizedCoordinates R side r ι {1} q1 ab=
      localizedCoordinates R side r ι {0} q0 ab
    exact (congrFun hc ab).symm
  · rfl

theorem exists_homogeneous_gluing (side : Side) (r ι : R)
    (q0 : CurveLocal R side r ι {0}) (q1 : CurveLocal R side r ι {1})
    (h : restriction R side r ι (show ({0}:Finset (Fin 2))⊆{0,1} by decide) q0=
      restriction R side r ι (show ({1}:Finset (Fin 2))⊆{0,1} by decide) q1)
    (g : ℤ) (hg : ∀ ab,HasDegree ab g (localizedCoordinates R side r ι {0} q0 ab)) :
    ∃ p : CurvePoly R, Standard side p ∧ SignedHomogeneous R p g ∧
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {0})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q0 ∧
      algebraMap (CurveRing side r ι) (CurveLocal R side r ι {1})
        (Ideal.Quotient.mk (curveIdeal side r ι) p)=q1 := by
  have hg0 : ∀ ab,HasDegree ab g (localizedCoordinates R side r ι {0}
      (sections R side r ι q0 q1 0) ab) := by
    simpa only [sections_zero] using hg
  obtain ⟨p,hp,hg',he⟩ := CycleQ2CurveCechGlobalGluing.exists_homogeneous_polynomial_gluing
    R side r ι (sections R side r ι q0 q1) (compatible R side r ι q0 q1 h) g hg0
  refine ⟨p,hp,hg',?_,?_⟩
  · simpa only [sections_zero] using he 0
  · simpa only [sections_one] using he 1

end CycleQ2CurvePairGluing

#print axioms CycleQ2CurvePairGluing.exists_homogeneous_gluing
end
end


/- Component: continuation_3/cylinder_bridge/SeedHomogeneousDenominator.lean -/
section
/-! # Common homogeneous numerators on the actual coordinate charts

A finite family of actual homogeneous localized sections admits one common
coordinate-product denominator, with the expected shifted numerator grades.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedHomogeneousDenominator

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedClearing

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Common denominators preserve the original weighted degree and character,
not merely an abstract grading of a chosen quotient basis. -/
theorem exists_common_homogeneous_denominator {I : Type*} [Fintype I]
    (r ι : R) (s : Finset (Fin 3)) (g : I → Grade)
    (z : I → SeedLocal R r ι s)
    (hz : ∀ i ab, HasGrade ab (signedGrade (g i)) (localizedCoordinates R r ι s (z i) ab)) :
    ∃ (n : ℕ) (P : I → Poly R),
      (∀ i, HG (P i) (n • openGrade s+g i)) ∧
      ∀ i, polynomialMap R r ι s (P i)=
        polynomialMap R r ι s (openPolynomial R s^n)*z i := by
  classical
  choose n P hP he using fun i =>
    (localized_homogeneous_iff_fraction R r ι s (z i) (signedGrade (g i))).mp (hz i)
  let N := ∑ i, n i
  have hn (i : I) : n i≤N :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hg (i : I) : HG (P i) (n i • openGrade s+g i) := by
    apply (signedHomogeneous_iff R (P i) _).mp
    have hgrade : signedGrade (n i • openGrade s+g i)=
        signedGrade (g i)+baseGrade (n i • openExponent s) := by
      change signedGradeHom (n i • openGrade s+g i)=_
      rw [map_add]
      change signedGrade (n i • openGrade s)+signedGrade (g i)=_
      rw [signed_openGrade_nsmul,add_comm]
    rw [hgrade]
    exact hP i
  let Q : I → Poly R := fun i => openPolynomial R s^(N-n i)*P i
  refine ⟨N,Q,?_,?_⟩
  · intro i
    have hh := ((openPolynomial_homogeneous R s).pow (N-n i)).mul (hg i)
    have hgrade : (N-n i) • openGrade s+(n i • openGrade s+g i)=N • openGrade s+g i := by
      rw [← add_assoc,← add_nsmul,Nat.sub_add_cancel (hn i)]
    exact hgrade ▸ hh
  · intro i
    let f := polynomialMap R r ι s
    have hden : algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n i))=
        f (openPolynomial R s^n i) := by
      simp only [f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial]
    have hei := he i
    rw [hden] at hei
    change z i*f (openPolynomial R s^n i)=f (P i) at hei
    change f (openPolynomial R s^(N-n i)*P i)=f (openPolynomial R s^N)*z i
    calc
      _ = f (openPolynomial R s)^(N-n i)*(z i*f (openPolynomial R s)^n i) := by
        rw [map_mul,← hei,map_pow,map_pow]
      _ = f (openPolynomial R s)^((N-n i)+n i)*z i := by rw [pow_add]; ring
      _ = f (openPolynomial R s^N)*z i := by rw [Nat.sub_add_cancel (hn i),map_pow]

end CycleQ2SeedHomogeneousDenominator

#print axioms CycleQ2SeedHomogeneousDenominator.exists_common_homogeneous_denominator
end
end


/- Component: continuation_3/cylinder_bridge/SeedLinkageGrading.lean -/
section
/-! # Homogeneous projection in the actual linkage ideals

The actual polynomial preimage of each linkage ideal is homogeneous for
the original weighted degree and cubic character. The same projection
property holds after localization at any coordinate product: clearing a
power of the homogeneous denominator reduces it to polynomial projection.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageGrading

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2CurveRestriction
  CycleQ2SeedLinkageIdeals CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedLocalizedClearing CycleQ2WeightedComponent

variable {R : Type*} [CommRing R]

local instance : GradedAlgebra (weightedHomogeneousSubmodule R fullGrading) :=
  MvPolynomial.weightedGradedAlgebra R fullGrading

def polynomialIdeal (side : Side) (r : R) : Ideal (Poly R) :=
  Ideal.span (Set.range (linkageGenerator side r))

theorem polynomialIdeal_homogeneous (side : Side) (r : R) :
    (polynomialIdeal side r).IsHomogeneous (weightedHomogeneousSubmodule R fullGrading) := by
  apply Ideal.homogeneous_span
  rintro p ⟨j,rfl⟩
  exact ⟨(generatorDegree j,(generatorCharacter j:ZMod 3)),linkageGenerator_homogeneous side r j⟩

theorem polynomialIdeal_map (side : Side) (r ι : R) :
    (polynomialIdeal side r).map
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))=linkageIdeal side r ι := by
  unfold polynomialIdeal linkageIdeal
  rw [Ideal.map_span,← Set.range_comp]
  rfl

theorem polynomial_preimage_homogeneous (side : Side) (r ι : R) :
    ((linkageIdeal side r ι).comap
      (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))).IsHomogeneous
      (weightedHomogeneousSubmodule R fullGrading) := by
  rw [← polynomialIdeal_map side r ι,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot,Ideal.mk_ker]
  exact (polynomialIdeal_homogeneous side r).sup
    (CycleQ2SegreWeightedProjection.equationsIdeal_homogeneous r ι)

/-- Projection preserves membership in the actual quotient ideal. -/
theorem quotient_component_mem (side : Side) (r ι : R) (p : Poly R) (d : Grade)
    (hp : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p ∈
      linkageIdeal side r ι) :
    Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (weightedHomogeneousComponent fullGrading d p) ∈ linkageIdeal side r ι :=
  weightedHomogeneousComponent_mem_of_mem R fullGrading
    (polynomial_preimage_homogeneous side r ι) hp d

/-- Localized ideal membership survives selection of any weighted-degree
and character component of a polynomial numerator. -/
theorem localized_component_mem (side : Side) (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (d : Grade)
    (hp : polynomialMap R r ι s p ∈ (linkageIdeal side r ι).map
      (algebraMap (SeedRing r ι) (SeedLocal R r ι s))) :
    polynomialMap R r ι s (weightedHomogeneousComponent fullGrading d p) ∈
      (linkageIdeal side r ι).map
        (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) := by
  let den : SeedRing r ι := algebraMap (Base R) (SeedRing r ι) (baseProduct R s)
  obtain ⟨z,hz,hzp⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers den)
      (SeedLocal R r ι s) (linkageIdeal side r ι)
      (Ideal.Quotient.mk _ p)).mp hp
  obtain ⟨n,hn⟩ := hz
  have hpre : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (openPolynomial R s^n*p) ∈ linkageIdeal side r ι := by
    rw [map_mul,map_pow,quotient_openPolynomial]
    rw [← hn] at hzp
    exact hzp
  have hc := quotient_component_mem side r ι (openPolynomial R s^n*p)
    (n • openGrade s+d) hpre
  rw [component_mul_left fullGrading (openPolynomial R s^n) p
    (n • openGrade s) d ((openPolynomial_homogeneous R s).pow n)] at hc
  have hl := Ideal.mem_map_of_mem (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) hc
  change polynomialMap R r ι s
    (openPolynomial R s^n*weightedHomogeneousComponent fullGrading d p) ∈ _ at hl
  rw [map_mul] at hl
  have hu : IsUnit (polynomialMap R r ι s (openPolynomial R s^n)) := by
    have hh := IsLocalization.map_units (SeedLocal R r ι s)
      (⟨den^n,⟨n,rfl⟩⟩ : Submonoid.powers den)
    simpa only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial,den] using hh
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hl

end CycleQ2SeedLinkageGrading

#print axioms CycleQ2SeedLinkageGrading.polynomial_preimage_homogeneous
#print axioms CycleQ2SeedLinkageGrading.localized_component_mem
end
end


