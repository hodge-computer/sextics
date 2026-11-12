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
import Proposal.SolutionSupport04

/-! Source partition of Solution.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SegreCechGraded.lean -/
section
/-! # Graded cofactor gluing in the actual seed quotient

A boundary in the actual graded cofactor kernel gives a global preimage
whose nine coefficients are actual standard polynomials of the prescribed
degrees and characters. This is the graded form needed to compare the
Čech obstruction with the finite incidence coefficient matrix.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev MatrixGrades := Matrix (Fin 3) (Fin 3) LaurentGrade

def LocalHasGrades (r ι : R) (g : MatrixGrades) (N : LocalMatrices R r ι) : Prop :=
  ∀ i k l ab, HasGrade ab (g k l) (localizedCoordinates R r ι {i} (N i k l) ab)

def GradedKernelBoundary (r ι : R) (M : GlobalMatrix R r ι)
    (g : MatrixGrades) (N : LocalMatrices R r ι) : Prop :=
  ∃ K : LocalMatrices R r ι,
    (∀ i, cofactorDifferential (localizeMatrix R r ι {i} M) (K i)=0) ∧
    LocalHasGrades R r ι g K ∧
    ∀ i j, overlapDifference R r ι N i j=overlapDifference R r ι K i j

def quotientMatrix (r ι : R) (P : Matrix (Fin 3) (Fin 3) (Poly R)) :
    GlobalMatrix R r ι :=
  (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))).mapMatrix P

theorem localHasGrades_quotientMatrix (r ι : R) (g : MatrixGrades)
    (P : Matrix (Fin 3) (Fin 3) (Poly R))
    (hg : ∀ k l, SignedHomogeneous R (P k l) (g k l)) :
    LocalHasGrades R r ι g (fun i => localizeMatrix R r ι {i} (quotientMatrix R r ι P)) := by
  intro i k l ab
  change HasGrade ab (g k l) (localizedCoordinates R r ι {i}
    (algebraMap (SeedRing r ι) (SeedLocal R r ι {i})
      (Ideal.Quotient.mk _ (P k l))) ab)
  rw [localizedCoordinates_algebraMap]
  exact seedCoordinates_signedHomogeneous R r ι (P k l) (g k l) (hg k l) ab

theorem localHasGrades_sub (r ι : R) (g : MatrixGrades)
    (N K : LocalMatrices R r ι) (hN : LocalHasGrades R r ι g N)
    (hK : LocalHasGrades R r ι g K) :
    LocalHasGrades R r ι g (fun i => N i-K i) := by
  intro i k l ab
  change HasGrade ab (g k l) (localizedCoordinates R r ι {i} (N i k l-K i k l) ab)
  rw [map_sub,Pi.sub_apply]
  exact hasGrade_sub ab (g k l) (hN i k l ab) (hK i k l ab)

/-- Entrywise gluing preserves every prescribed degree and character and
returns standard representatives in the original polynomial ring. -/
theorem exists_homogeneous_matrix_gluing (r ι : R) (g : MatrixGrades)
    (Q : LocalMatrices R r ι)
    (hQ : ∀ i j, (pairRestriction R r ι i j).mapMatrix (Q i)=
      (secondPairRestriction R r ι i j).mapMatrix (Q j))
    (hg : LocalHasGrades R r ι g Q) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Poly R),
      (∀ k l, FullStandard (P k l)) ∧
      (∀ k l, SignedHomogeneous R (P k l) (g k l)) ∧
      ∀ i, localizeMatrix R r ι {i} (quotientMatrix R r ι P)=Q i := by
  have hc (k l : Fin 3) : Compatible R r ι (fun i => Q i k l) := by
    intro i j
    exact congrArg (fun T => T k l) (hQ i j)
  choose P hP hPg hPQ using fun k l => exists_homogeneous_polynomial_gluing
    R r ι (fun i => Q i k l) (hc k l) (g k l) (hg 0 k l)
  refine ⟨P,hP,hPg,?_⟩
  intro i
  ext k l
  exact hPQ k l i

/-- A graded zero connecting class produces an actual homogeneous global
matrix preimage, not just an ungraded element of the quotient ring. -/
theorem homogeneous_lift_of_gradedKernelBoundary (r ι : R)
    (M C : GlobalMatrix R r ι) (g : MatrixGrades) (N : LocalMatrices R r ι)
    (hN : HasLocalLift R r ι M C N) (hgN : LocalHasGrades R r ι g N)
    (hB : GradedKernelBoundary R r ι M g N) :
    ∃ P : Matrix (Fin 3) (Fin 3) (Poly R),
      (∀ k l, FullStandard (P k l)) ∧
      (∀ k l, SignedHomogeneous R (P k l) (g k l)) ∧
      cofactorDifferential M (quotientMatrix R r ι P)=C := by
  obtain ⟨K,hK,hgK,hNK⟩ := hB
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
  obtain ⟨P,hP,hPg,hPQ⟩ := exists_homogeneous_matrix_gluing R r ι g Q hQ
    (localHasGrades_sub R r ι g N K hgN hgK)
  refine ⟨P,hP,hPg,global_differential_of_local R r ι M C (quotientMatrix R r ι P) ?_⟩
  rw [hPQ 0]
  change cofactorDifferential _ (N 0-K 0)=_
  rw [cofactorDifferential_sub,hN 0,hK 0,sub_zero]

/-- Conversely, a global homogeneous polynomial preimage kills the actual
graded connecting class by its literal local restrictions. -/
theorem gradedKernelBoundary_of_homogeneous_lift (r ι : R)
    (M C : GlobalMatrix R r ι) (g : MatrixGrades) (N : LocalMatrices R r ι)
    (hN : HasLocalLift R r ι M C N) (hgN : LocalHasGrades R r ι g N)
    (P : Matrix (Fin 3) (Fin 3) (Poly R))
    (hPg : ∀ k l, SignedHomogeneous R (P k l) (g k l))
    (hP : cofactorDifferential M (quotientMatrix R r ι P)=C) :
    GradedKernelBoundary R r ι M g N := by
  let Pq := quotientMatrix R r ι P
  let K : LocalMatrices R r ι := fun i => N i-localizeMatrix R r ι {i} Pq
  refine ⟨K,?_,localHasGrades_sub R r ι g N _ hgN
    (localHasGrades_quotientMatrix R r ι g P hPg),?_⟩
  · intro i
    change cofactorDifferential _ (N i-localizeMatrix R r ι {i} Pq)=0
    rw [cofactorDifferential_sub,hN i]
    have hh := map_cofactorDifferential (B := SeedLocal R r ι {i})
      (algebraMap (SeedRing r ι) (SeedLocal R r ι {i})) M Pq
    rw [hP] at hh
    change localizeMatrix R r ι {i} C=cofactorDifferential
      (localizeMatrix R r ι {i} M) (localizeMatrix R r ι {i} Pq) at hh
    rw [← hh,sub_self]
  · intro i j
    ext k l
    have hi := restriction_algebraMap R r ι
      (show ({i} : Finset (Fin 3)) ⊆ {i,j} by simp) (Pq k l)
    have hj := restriction_algebraMap R r ι
      (show ({j} : Finset (Fin 3)) ⊆ {i,j} by simp) (Pq k l)
    change secondPairRestriction R r ι i j (N j k l)-pairRestriction R r ι i j (N i k l) =
      secondPairRestriction R r ι i j
        (N j k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {j}) (Pq k l))-
      pairRestriction R r ι i j
        (N i k l-algebraMap (SeedRing r ι) (SeedLocal R r ι {i}) (Pq k l))
    simp only [map_sub,pairRestriction,secondPairRestriction,hi,hj]
    abel

theorem gradedKernelBoundary_iff_homogeneous_lift (r ι : R)
    (M C : GlobalMatrix R r ι) (g : MatrixGrades) (N : LocalMatrices R r ι)
    (hN : HasLocalLift R r ι M C N) (hgN : LocalHasGrades R r ι g N) :
    GradedKernelBoundary R r ι M g N ↔
      ∃ P : Matrix (Fin 3) (Fin 3) (Poly R),
        (∀ k l, FullStandard (P k l)) ∧
        (∀ k l, SignedHomogeneous R (P k l) (g k l)) ∧
        cofactorDifferential M (quotientMatrix R r ι P)=C := by
  constructor
  · exact homogeneous_lift_of_gradedKernelBoundary R r ι M C g N hN hgN
  · rintro ⟨P,_,hPg,hP⟩
    exact gradedKernelBoundary_of_homogeneous_lift R r ι M C g N hN hgN P hPg hP

end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.exists_homogeneous_matrix_gluing
#print axioms CycleQ2SegreCechConnecting.gradedKernelBoundary_iff_homogeneous_lift
end
end


/- Component: continuation_3/cylinder_bridge/SegreLocalizedGradedLift.lean -/
section
/-! # Actual graded local lifts of homogeneous cofactor variations

An arbitrary local matrix solution is cleared by one actual chart denominator.
Projection in the original polynomial grading then gives a solution of degree
fourteen and invariant character, because the literal seed ideal is homogeneous.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace CycleQ2SegreLocalizedGradedLift

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedClearing
  CycleQ2SegreWeightedProjection

variable (R : Type*) [CommRing R] [Nontrivial R]

/-- Every actual local solution of a homogeneous cofactor equation has a
solution in the required degree and character. No graded-lift assumption
is supplied: it is obtained by common-denominator clearing and projection. -/
theorem exists_graded_local_lift (r ι : R) (s : Finset (Fin 3))
    (M C : Matrix (Fin 3) (Fin 3) (Poly R))
    (hM : ∀ i j, HG (M i j) (14,0)) (hC : ∀ i j, HG (C i j) (28,0))
    (N : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s))
    (hN : cofactorDifferential ((polynomialMap R r ι s).mapMatrix M) N=
      (polynomialMap R r ι s).mapMatrix C) :
    ∃ N' : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s),
      (∀ i j ab, HasGrade ab (14,0) (localizedCoordinates R r ι s (N' i j) ab)) ∧
      cofactorDifferential ((polynomialMap R r ι s).mapMatrix M) N'=
        (polynomialMap R r ι s).mapMatrix C := by
  let f := polynomialMap R r ι s
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator R r ι s N
  let a := f (openPolynomial R s ^ n)
  have hPM : f.mapMatrix P=a • N := by
    funext i j
    exact hP i j
  have hD : f.mapMatrix (cofactorDifferential M P)=a • f.mapMatrix C := by
    rw [map_cofactorDifferential (B := SeedLocal R r ι s),hPM]
    exact (map_smul (cofactorDifferentialLinear (f.mapMatrix M)) a N).trans
      (congrArg (fun Q => a • Q) hN)
  have hres (i j : Fin 3) : cofactorDifferential M P i j-
      openPolynomial R s ^ n*C i j ∈ equationsIdeal (smoothH ι) (smoothF r ι) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply localization_injective R r ι s
    have hh := congrArg (fun Q => Q i j) hD
    change f (cofactorDifferential M P i j)=a*f (C i j) at hh
    rw [map_zero]
    change f (cofactorDifferential M P i j-openPolynomial R s ^ n*C i j)=0
    rw [map_sub,map_mul,hh]
    exact sub_self _
  let d : Grade := n • openGrade s
  let P' := matrixComponent (d+(14,0)) P
  have hCt (i j : Fin 3) : HG (openPolynomial R s ^ n*C i j) (d+(28,0)) :=
    ((openPolynomial_homogeneous R s).pow n).mul (hC i j)
  have hproj := projected_residual_mem r ι M P
    (fun i j => openPolynomial R s ^ n*C i j) hM d hCt hres
  have hD' : cofactorDifferential (f.mapMatrix M) (f.mapMatrix P')=a • f.mapMatrix C := by
    rw [← map_cofactorDifferential (B := SeedLocal R r ι s)]
    funext i j
    have hh := congrArg (algebraMap (SeedRing r ι) (SeedLocal R r ι s))
      (Ideal.Quotient.eq_zero_iff_mem.mpr (hproj i j))
    rw [map_zero] at hh
    change f (cofactorDifferential M P' i j-openPolynomial R s ^ n*C i j)=0 at hh
    rw [map_sub,map_mul] at hh
    exact sub_eq_zero.mp hh
  have ha : IsUnit a := by
    simpa only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial] using
      (IsLocalization.Away.algebraMap_pow_isUnit (S := SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s)) n)
  obtain ⟨u,hu⟩ := ha
  let N' : Matrix (Fin 3) (Fin 3) (SeedLocal R r ι s) :=
    (↑(u⁻¹) : SeedLocal R r ι s) • f.mapMatrix P'
  have hden : algebraMap (SeedRing r ι) (SeedLocal R r ι s)
      (algebraMap (Base R) (SeedRing r ι) (baseProduct R s ^ n))=a := by
    simp only [a,f,polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial]
  refine ⟨N',?_,?_⟩
  · intro i j
    apply (localized_homogeneous_iff_fraction R r ι s (N' i j) (14,0)).mpr
    have hgP' : HG (P' i j) (d+(14,0)) :=
      weightedHomogeneousComponent_isWeightedHomogeneous _ _
    have hgrade : signedGrade (d+(14,0))=
        (14,0)+baseGrade (n • openExponent s) := by
      change signedGradeHom (n • openGrade s+(14,0))=_
      rw [map_add]
      change signedGrade (n • openGrade s)+signedGrade (14,0)=_
      rw [signed_openGrade_nsmul]
      change baseGrade (n • openExponent s)+(14,0)=(14,0)+baseGrade (n • openExponent s)
      exact add_comm _ _
    refine ⟨n,P' i j,hgrade ▸ (signedHomogeneous_iff R (P' i j) _).mpr hgP',?_⟩
    rw [hden]
    change ((↑(u⁻¹) : SeedLocal R r ι s)*f (P' i j))*a=f (P' i j)
    rw [← hu]
    calc
      _ = ((↑(u⁻¹) : SeedLocal R r ι s)*(u : SeedLocal R r ι s))*f (P' i j) := by ring
      _ = f (P' i j) := by rw [u.inv_mul,one_mul]
  · change cofactorDifferential (f.mapMatrix M)
      ((↑(u⁻¹) : SeedLocal R r ι s) • f.mapMatrix P')=f.mapMatrix C
    have hs := map_smul (cofactorDifferentialLinear (f.mapMatrix M))
      (↑(u⁻¹) : SeedLocal R r ι s) (f.mapMatrix P')
    change cofactorDifferential (f.mapMatrix M) ((↑(u⁻¹) : SeedLocal R r ι s) • f.mapMatrix P')=
      (↑(u⁻¹) : SeedLocal R r ι s) • cofactorDifferential (f.mapMatrix M) (f.mapMatrix P') at hs
    rw [hs,hD',← hu,smul_smul,u.inv_mul,one_smul]

end CycleQ2SegreLocalizedGradedLift

#print axioms CycleQ2SegreLocalizedGradedLift.exists_graded_local_lift
end
end


/- Component: continuation_3/SegreModularDetectorCertificate.lean -/
section
/-! # Seven checked annihilators of the actual entry Jacobian

The coefficient functionals below annihilate every actual entry column. Their
values on the nine displayed invariant cubic columns have a checked right
inverse. All finite arithmetic is replayable by Lean's ordinary kernel.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SegreModularDetectorCertificate
open scoped Matrix

open CycleQ2SparseModularFunctional CycleQ2SegreModularDetectorData
  CycleQ2IncidenceEquations CycleQ2GenericEntryCoefficientBinding
  CycleQ2SegreModularDetectorExpressions CycleQ2SegreModularDetectorEntryBinding
  CycleQ2SegreModularCorrelationChecks
  CycleQ2SegreModularDetectorMatrixBinding CycleQ2SegreModularCubicPairing
  CycleQ2SegreModularCubicData CycleQ2SegreModularCubicSemantics

def L : Matrix (Fin 7) EquationIndex F := detectorMatrix

theorem annihilates_entry : L * entryJacobianBlock (57:F) 33=0 :=
  annihilates_entry_of_checks all_entry_checks

theorem cast_cubicDot (W : WeightData) (c : Fin 9) :
    (cubicDot W c : F)=
      ∑s : Fin 3,(dot W 0 s (0,0,0,0,0)
        (flattenTowersData (cubicTable s c)) : F) := by
  simp only [cubicDot,ZMod.natCast_mod,Nat.cast_add,Fin.sum_univ_three]

theorem cubic_pairing_eq : L * selectedCubicBlock=cubicPairingMatrix := by
  ext k c
  change (detectorMatrix*selectedCubicBlock) k c=(cubicPairing k c : F)
  rw [detector_cubic_numeric,←cast_cubicDot,all_pairing_checks]

theorem cubic_right_inverse : (L * selectedCubicBlock) * rightInverse=1 := by
  rw [cubic_pairing_eq]
  exact literal_cubic_right_inverse

theorem detected_kernelCubic : (L * selectedCubicBlock) *ᵥ kernelCubic=0 := by
  rw [cubic_pairing_eq]
  exact pairing_kernelCubic

end CycleQ2SegreModularDetectorCertificate

#print axioms CycleQ2SegreModularDetectorCertificate.annihilates_entry
#print axioms CycleQ2SegreModularDetectorCertificate.cubic_right_inverse
#print axioms CycleQ2SegreModularDetectorCertificate.detected_kernelCubic
end
end


/- Component: continuation_3/CurveLocalizedRestriction.lean -/
section
/-!
# Restriction of the actual seed coordinate localizations to the curves

The target of each map is the localization of the actual curve quotient
at the image of the source denominator. The two base-coordinate charts
are compared with the previously checked six-coordinate curve complex.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal

variable (R : Type*) [CommRing R]

abbrev SB := CycleQ2SeedQuotientFiniteFree.Base R
abbrev CB := CycleQ2CurveQuotientFiniteFree.Base R
abbrev SL (r ι : R) (t : Finset (Fin 3)) := CycleQ2SeedCechLocalizedBasis.SeedLocal R r ι t
abbrev CL (side : Side) (r ι : R) (t : Finset (Fin 2)) :=
  CycleQ2CurveCechLocalizedBasis.CurveLocal R side r ι t

def seedProduct (r ι : R) (t : Finset (Fin 3)) : SeedRing r ι :=
  algebraMap (SB R) (SeedRing r ι) (CycleQ2SeedCechLocalization.baseProduct R t)

instance sourceAway (r ι : R) (t : Finset (Fin 3)) :
    IsLocalization.Away (seedProduct R r ι t) (SL R r ι t) :=
  CycleQ2SeedCechRestrictions.seedLocalAway R r ι t

def curveProduct (side : Side) (r ι : R) (t : Finset (Fin 3)) : CurveRing side r ι :=
  seedRestriction side r ι (seedProduct R r ι t)

abbrev RestrictedLocal (side : Side) (r ι : R) (t : Finset (Fin 3)) :=
  Localization.Away (curveProduct R side r ι t)

instance targetAway (side : Side) (r ι : R) (t : Finset (Fin 3)) :
    IsLocalization.Away ((seedRestriction side r ι).toRingHom (seedProduct R r ι t))
      (RestrictedLocal R side r ι t) :=
  inferInstanceAs (IsLocalization.Away (curveProduct R side r ι t)
    (Localization.Away (curveProduct R side r ι t)))

def localRestrictionMap (side : Side) (r ι : R) (t : Finset (Fin 3)) :
    SL R r ι t →+* RestrictedLocal R side r ι t :=
  IsLocalization.Away.map (SL R r ι t) (RestrictedLocal R side r ι t)
    (seedRestriction side r ι).toRingHom (seedProduct R r ι t)

@[simp] theorem localRestrictionMap_algebraMap (side : Side) (r ι : R)
    (t : Finset (Fin 3)) (p : SeedRing r ι) :
    localRestrictionMap R side r ι t (algebraMap (SeedRing r ι) (SL R r ι t) p)=
      algebraMap (CurveRing side r ι) (RestrictedLocal R side r ι t) (seedRestriction side r ι p) :=
  by
  unfold localRestrictionMap IsLocalization.Away.map
  exact IsLocalization.map_eq _ p

theorem curveProduct_dvd (side : Side) (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    curveProduct R side r ι s ∣ curveProduct R side r ι t := by
  exact (seedRestriction side r ι).toRingHom.map_dvd
    ((algebraMap (SB R) (SeedRing r ι)).map_dvd
      (CycleQ2SeedCechRestrictions.baseProduct_dvd R hst))

def restriction (side : Side) (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t) :
    RestrictedLocal R side r ι s →+* RestrictedLocal R side r ι t :=
  IsLocalization.Away.lift (curveProduct R side r ι s)
    (IsLocalization.Away.isUnit_of_dvd (S:=RestrictedLocal R side r ι t)
      (curveProduct R side r ι t) (curveProduct_dvd R side r ι hst))

@[simp] theorem restriction_algebraMap (side : Side) (r ι : R)
    {s t : Finset (Fin 3)} (hst : s⊆t) (p : CurveRing side r ι) :
    restriction R side r ι hst (algebraMap _ (RestrictedLocal R side r ι s) p)=
      algebraMap _ (RestrictedLocal R side r ι t) p := IsLocalization.Away.lift_eq _ _ _

theorem localRestrictionMap_natural (side : Side) (r ι : R)
    {s t : Finset (Fin 3)} (hst : s⊆t) :
    (restriction R side r ι hst).comp (localRestrictionMap R side r ι s)=
      (localRestrictionMap R side r ι t).comp (CycleQ2SeedCechRestrictions.restriction R r ι hst) := by
  apply IsLocalization.ringHom_ext (S:=SL R r ι s) (Submonoid.powers (seedProduct R r ι s))
  apply RingHom.ext
  intro p
  simp only [RingHom.comp_apply,localRestrictionMap_algebraMap,restriction_algebraMap,
    CycleQ2SeedCechRestrictions.restriction_algebraMap]

def baseIndex : Fin 2 → Fin 3 := ![0,2]

theorem baseIndex_injective : Function.Injective baseIndex := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [baseIndex] at h ⊢

def seedOpen (t : Finset (Fin 2)) : Finset (Fin 3) := t.image baseIndex

def coordinateScale (side : Side) : R := match side with | .left => 1 | .right => 2

theorem restriction_baseCoordinate (side : Side) (r ι : R) (j : Fin 2) :
    seedRestriction side r ι
      (algebraMap (SB R) (SeedRing r ι) (X (baseIndex j)))=
      algebraMap R (CurveRing side r ι) (coordinateScale R side)*
        algebraMap (CB R) (CurveRing side r ι) (X j) := by
  change seedRestriction side r ι
    (Ideal.Quotient.mk _ (CycleQ2SeedQuotientFiniteFree.remainingInclusion R (X (baseIndex j))))=_
  rw [seedRestriction_mk]
  change Ideal.Quotient.mk _ (substitution side r
    (CycleQ2SeedQuotientFiniteFree.remainingInclusion R (X (baseIndex j))))=
      Ideal.Quotient.mk _ (C (coordinateScale R side))*
        Ideal.Quotient.mk _ (CycleQ2CurveQuotientFiniteFree.remainingInclusion R (X j))
  have hCtwo : (C (2:R):CurvePoly R)=2 := map_ofNat C 2
  cases side <;> fin_cases j <;>
    simp [hCtwo,CycleQ2SeedQuotientFiniteFree.remainingInclusion,
      CycleQ2SeedQuotientFiniteFree.remainingIndex,
      CycleQ2CurveQuotientFiniteFree.remainingInclusion,
      CycleQ2CurveQuotientFiniteFree.remainingIndex,
      baseIndex,coordinateScale,restrictionValues,Matrix.cons_val_succ,Fin.reduceSucc] <;> norm_num

theorem curveProduct_baseOpen (side : Side) (r ι : R) (t : Finset (Fin 2)) :
    curveProduct R side r ι (seedOpen t)=
      (algebraMap R (CurveRing side r ι) (coordinateScale R side))^t.card*
        algebraMap (CB R) (CurveRing side r ι) (CycleQ2CurveCechLocalization.baseProduct R t) := by
  classical
  unfold curveProduct seedProduct CycleQ2SeedCechLocalization.baseProduct seedOpen
  rw [Finset.prod_image baseIndex_injective.injOn]
  simp only [map_prod]
  simp only [restriction_baseCoordinate]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  simp [CycleQ2CurveCechLocalization.baseProduct]

theorem baseOpen_isLocalization (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    IsLocalization.Away (curveProduct R side r ι (seedOpen t)) (CL R side r ι t) := by
  rw [curveProduct_baseOpen]
  apply IsLocalization.Away.mul_of_isUnit'
  exact ((hscale.map (algebraMap R (CurveRing side r ι))).pow t.card).map
    (algebraMap (CurveRing side r ι) (CL R side r ι t))

def baseOpenEquiv (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    RestrictedLocal R side r ι (seedOpen t) ≃ₐ[CurveRing side r ι] CL R side r ι t := by
  letI := baseOpen_isLocalization R side r ι t hscale
  exact IsLocalization.algEquiv (Submonoid.powers (curveProduct R side r ι (seedOpen t)))
    (RestrictedLocal R side r ι (seedOpen t)) (CL R side r ι t)

def baseOpenMap (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) :
    SL R r ι (seedOpen t) →+* CL R side r ι t :=
  (baseOpenEquiv R side r ι t hscale).toRingHom.comp (localRestrictionMap R side r ι (seedOpen t))

@[simp] theorem baseOpenMap_algebraMap (side : Side) (r ι : R) (t : Finset (Fin 2))
    (hscale : IsUnit (coordinateScale R side)) (p : SeedRing r ι) :
    baseOpenMap R side r ι t hscale
      (algebraMap (SeedRing r ι) (SL R r ι (seedOpen t)) p)=
      algebraMap (CurveRing side r ι) (CL R side r ι t) (seedRestriction side r ι p) := by
  simp only [baseOpenMap,RingHom.comp_apply,localRestrictionMap_algebraMap]
  exact (baseOpenEquiv R side r ι t hscale).commutes _

theorem complex_scale_unit (side : Side) : IsUnit (coordinateScale ℂ side) := by
  cases side <;> simp [coordinateScale]

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.localRestrictionMap_natural
#print axioms CycleQ2CurveLocalizedRestriction.baseOpenEquiv
end
end


/- Component: continuation_3/SeedLinkageIdealRanks.lean -/
section
/-! The actual linkage ideals have exactly the two required graded section
dimensions.  Checked generator minors give the lower bounds; actual curve
restriction kernels give the matching upper bounds. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageIdealRanks

open CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals CycleQ2SeedLinkageSections
  CycleQ2SeedLinkageModularData CycleQ2SeedLinkageModularChecks
  CycleQ2IncidenceGaussianArithmetic

theorem left_columns_good : ∀ j : Fin 56, sectionGood 10 0 (leftColumns j)=true := by decide +kernel

theorem right_columns_good : ∀ j : Fin 23, sectionGood 8 1 (rightColumns j)=true := by decide +kernel

noncomputable section

theorem complex_section_minor_nonzero_of_modular (s : Side) {n : ℕ}
    (rows : Fin n → SourceTuple) (columns : Fin n → SectionColumn)
    (hmod : Matrix.det (fun i j : Fin n =>
      sectionCoefficient s (57:F109) 33 (rows i) (columns j))≠0) :
    Matrix.det (fun i j : Fin n => sectionCoefficient s (57:ℂ) Complex.I (rows i) (columns j))≠0 := by
  let A : Matrix (Fin n) (Fin n) GaussianInt :=
    fun i j => sectionCoefficient s 57 gaussianI (rows i) (columns j)
  have hm : A.map reduction =
      (fun i j : Fin n => sectionCoefficient s (57:F109) 33 (rows i) (columns j)) := by
    ext i j
    change reduction (sectionCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,reduction_I] using
      sectionCoefficient_map reduction s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hc : A.map GaussianInt.toComplex =
      (fun i j : Fin n => sectionCoefficient s (57:ℂ) Complex.I (rows i) (columns j)) := by
    ext i j
    change GaussianInt.toComplex (sectionCoefficient s (57:GaussianInt) gaussianI (rows i) (columns j))=_
    simpa only [map_ofNat,complex_I] using
      sectionCoefficient_map GaussianInt.toComplex s (57:GaussianInt) gaussianI (rows i) (columns j)
  have hA := determinant_nonzero_of_reduction A (by rw [hm]; exact hmod)
  rwa [hc] at hA

theorem left_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 56 => sectionCoefficient .left (57:ℂ) Complex.I (leftRows i) (leftColumns j))≠0 :=
  complex_section_minor_nonzero_of_modular .left leftRows leftColumns (left_minor_det_ne_zero (R:=F109))

theorem right_complex_minor_nonzero :
    Matrix.det (fun i j : Fin 23 => sectionCoefficient .right (57:ℂ) Complex.I (rightRows i) (rightColumns j))≠0 :=
  complex_section_minor_nonzero_of_modular .right rightRows rightColumns (right_minor_det_ne_zero (R:=F109))

theorem left_linkagePiece_rank :
    Module.finrank ℂ (linkagePiece .left (57:ℂ) Complex.I 10 0)=56 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 10 0 (by decide))
  apply le_antisymm
  · have h := Submodule.finrank_mono (linkagePiece_le_restrictionKernel .left (57:ℂ) Complex.I 10 0)
    simpa only [left_restriction_kernel_rank] using h
  · exact linkagePiece_rank_lower_bound .left 57 Complex.I 10 0 56 (by decide)
      leftRows leftColumns left_columns_good left_complex_minor_nonzero

theorem right_linkagePiece_rank :
    Module.finrank ℂ (linkagePiece .right (57:ℂ) Complex.I 8 1)=23 := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 8 1 (by decide))
  apply le_antisymm
  · have h := Submodule.finrank_mono (linkagePiece_le_restrictionKernel .right (57:ℂ) Complex.I 8 1)
    simpa only [right_restriction_kernel_rank] using h
  · exact linkagePiece_rank_lower_bound .right 57 Complex.I 8 1 23 (by decide)
      rightRows rightColumns right_columns_good right_complex_minor_nonzero

theorem left_linkagePiece_eq_restrictionKernel :
    linkagePiece .left (57:ℂ) Complex.I 10 0=
      LinearMap.ker (seedRestrictionPiece .left (57:ℂ) Complex.I 10 0) := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 10 0) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 10 0 (by decide))
  apply Submodule.eq_of_le_of_finrank_eq (linkagePiece_le_restrictionKernel .left (57:ℂ) Complex.I 10 0)
  rw [left_linkagePiece_rank,left_restriction_kernel_rank]

theorem right_linkagePiece_eq_restrictionKernel :
    linkagePiece .right (57:ℂ) Complex.I 8 1=
      LinearMap.ker (seedRestrictionPiece .right (57:ℂ) Complex.I 8 1) := by
  letI : FiniteDimensional ℂ (SeedPiece (57:ℂ) Complex.I 8 1) :=
    Module.Finite.of_basis (seedPieceBasis (57:ℂ) Complex.I 8 1 (by decide))
  apply Submodule.eq_of_le_of_finrank_eq (linkagePiece_le_restrictionKernel .right (57:ℂ) Complex.I 8 1)
  rw [right_linkagePiece_rank,right_restriction_kernel_rank]

end
end CycleQ2SeedLinkageIdealRanks

#print axioms CycleQ2SeedLinkageIdealRanks.left_linkagePiece_rank
#print axioms CycleQ2SeedLinkageIdealRanks.right_linkagePiece_rank
#print axioms CycleQ2SeedLinkageIdealRanks.left_linkagePiece_eq_restrictionKernel
#print axioms CycleQ2SeedLinkageIdealRanks.right_linkagePiece_eq_restrictionKernel
end


/- Component: continuation_3/cylinder_bridge/SeedLinkageOrbitProduct.lean -/
section
/-! The actual linkage ideal is the product of the three literal orbit
component ideals on every nonempty coordinate chart. The diagonal action
maps the selected component onto each component, with equality of ideals.
This identifies the orbit product algebraically; it does not identify a
cycle class or assume equal numerical contributions to an Abel--Jacobi
pairing. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageOrbitProduct
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedLinkagePrincipal CycleQ2SeedLinkageOrbitCover CycleQ2SeedLinkageComponents
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedCyclicAction CycleQ2SeedCyclicLocalization
  CycleQ2SeedLinkageOrbitKernel

section Generic
variable {A : Type*} [CommRing A]

theorem three_product_eq_intersection (I J K : Ideal A)
    (hIJ : I⊔J=⊤) (hIK : I⊔K=⊤) (hJK : J⊔K=⊤) :
    I*J*K=(I⊓J)⊓K := by
  have hp : I*J⊔K=⊤ := by rw [Ideal.mul_sup_eq_of_coprime_left hIK,hJK]
  rw [Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hp),
    Ideal.mul_eq_inf_of_isCoprime (Ideal.isCoprime_iff_sup_eq.mpr hIJ)]

theorem leftIdeal_eq_product (ζ a b c d : A) (hζ : ζ^2+ζ+1=0)
    (hunits : ∀ i j : Fin 3, i≠j → IsUnit (rootValues ζ i-rootValues ζ j) ∧
      IsUnit (rootValues ζ i^2-rootValues ζ j^2))
    (hcover : leftIdeal a b c d⊔Ideal.span {b,d}=⊤) :
    leftIdeal a b c d=componentIdeal 1 a b c d*componentIdeal ζ a b c d*
      componentIdeal (ζ^2) a b c d := by
  have h01 := components_sup_top (rootValues ζ 0) (rootValues ζ 1) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 1)
    (hunits 0 1 (by decide)).1 (hunits 0 1 (by decide)).2 hcover
  have h02 := components_sup_top (rootValues ζ 0) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 0) (rootValues_cube ζ hζ 2)
    (hunits 0 2 (by decide)).1 (hunits 0 2 (by decide)).2 hcover
  have h12 := components_sup_top (rootValues ζ 1) (rootValues ζ 2) a b c d
    (rootValues_cube ζ hζ 1) (rootValues_cube ζ hζ 2)
    (hunits 1 2 (by decide)).1 (hunits 1 2 (by decide)).2 hcover
  rw [leftIdeal_eq_components ζ a b c d hζ hunits hcover]
  exact (three_product_eq_intersection _ _ _ h01 h02 h12).symm

theorem map_component_one_eq (T : A →+* A) (z a b c d : A) (hz : IsUnit z)
    (ha : T a=z*a) (hb : T b=z^2*b) (hc : T c=c) (hd : T d=z^2*d) :
    (componentIdeal 1 a b c d).map T=componentIdeal z a b c d := by
  apply le_antisymm (map_component_one_le T z a b c d ha hb hc hd)
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · have h := Ideal.mem_map_of_mem T (componentGenerator_mem 1 a b c d 0)
    change T (a-1*b)∈(componentIdeal 1 a b c d).map T at h
    rw [one_mul,map_sub,ha,hb] at h
    have he : z*a-z^2*b=z*(a-z*b) := by ring
    rw [he] at h
    exact (Ideal.unit_mul_mem_iff_mem _ hz).mp h
  · change c+z^2*d∈(componentIdeal 1 a b c d).map T
    have h := Ideal.mem_map_of_mem T (componentGenerator_mem 1 a b c d 1)
    change T (c+1^2*d)∈(componentIdeal 1 a b c d).map T at h
    simpa only [one_pow,one_mul,map_add,hc,hd] using h

end Generic

variable {K : Type*} [Field K]

theorem localAction_component_map_eq (s : Side) (r ι ζ : K) (hζ : ζ^3=1)
    (t : Finset (Fin 3)) :
    (localComponent s r ι t 1).map (localAction ζ hζ r ι t)=localComponent s r ι t ζ := by
  let φ := algebraMap (SeedRing r ι) (SeedLocal K r ι t)
  let T := localAction ζ hζ r ι t
  have hA : T (φ (linkageA r ι))=localScalar r ι t ζ*φ (linkageA r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 0^2)))=_
    rw [localAction_mk,polynomialAction_A ζ hζ,map_mul,map_mul]
    rfl
  have hB : T (φ (linkageB r ι))=localScalar r ι t ζ^2*φ (linkageB r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (C r*X 1*X 3)))=_
    rw [localAction_mk,polynomialAction_B,map_mul,map_mul]
    change localScalar r ι t (ζ^2)*φ (linkageB r ι)=_
    rw [map_pow]
  have hC : T (φ (linkageC r ι))=φ (linkageC r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 4)))=_
    rw [localAction_mk,polynomialAction_X]
    rfl
  have hD : T (φ (linkageD r ι))=localScalar r ι t ζ^2*φ (linkageD r ι) := by
    change localAction ζ hζ r ι t (φ (Ideal.Quotient.mk _ (X 2^2)))=_
    rw [localAction_mk,polynomialAction_D,map_mul,map_mul]
    change localScalar r ι t (ζ^2)*φ (linkageD r ι)=_
    rw [map_pow]
  have hoB : T (φ (orbitB s r ι))=localScalar r ι t ζ^2*φ (orbitB s r ι) := by
    cases s
    · exact hB
    · simpa only [orbitB,map_neg,mul_neg] using congrArg Neg.neg hD
  have hoD : T (φ (orbitD s r ι))=localScalar r ι t ζ^2*φ (orbitD s r ι) := by
    cases s
    · exact hD
    · simpa only [orbitD,map_neg,mul_neg] using congrArg Neg.neg hB
  simpa only [localComponent,map_one] using
    map_component_one_eq T (localScalar r ι t ζ) (φ (linkageA r ι)) (φ (orbitB s r ι))
      (φ (linkageC r ι)) (φ (orbitD s r ι))
      ((cube_root_isUnit ζ hζ).map (localScalar r ι t)) hA hoB hC hoD

theorem localized_linkageIdeal_eq_product (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    localLinkageIdeal s r ι t=localComponent s r ι t 1*localComponent s r ι t complexRoot*
      localComponent s r ι t (complexRoot^2) := by
  let φ := algebraMap (SeedRing r ι) (SeedLocal ℂ r ι t)
  let z := localScalar r ι t complexRoot
  have hz : z^2+z+1=0 := by
    simpa only [map_add (localScalar r ι t),map_pow (localScalar r ι t),
      map_one (localScalar r ι t),map_zero (localScalar r ι t)] using
      congrArg (localScalar r ι t) complexRoot_quadratic
  have hcover := @local_orbit_vertex_cover ℂ (inferInstance : Field ℂ) s r ι hr hι hι1 t ht
  rw [localLinkageIdeal_eq_generic s r ι t] at hcover ⊢
  have h := @leftIdeal_eq_product (SeedLocal ℂ r ι t)
    (inferInstance : CommRing (SeedLocal ℂ r ι t)) z (φ (linkageA r ι)) (φ (orbitB s r ι))
    (φ (linkageC r ι)) (φ (orbitD s r ι)) hz
    (@mapped_root_units (SeedLocal ℂ r ι t) (inferInstance : CommRing (SeedLocal ℂ r ι t))
      (localScalar r ι t)) hcover
  simpa only [localComponent,map_one (localScalar r ι t),map_pow (localScalar r ι t)] using h

theorem localized_linkageIdeal_eq_orbit_product (s : Side) (r ι : ℂ)
    (hr : r≠0) (hι : ι≠0) (hι1 : ι≠1) (t : Finset (Fin 3)) (ht : t.Nonempty) :
    localLinkageIdeal s r ι t=localComponent s r ι t 1*
      (localComponent s r ι t 1).map (localAction complexRoot complexRoot_cube r ι t)*
      (localComponent s r ι t 1).map
        (localAction (complexRoot^2) (rootValues_cube complexRoot complexRoot_quadratic 2) r ι t) := by
  rw [localAction_component_map_eq,localAction_component_map_eq]
  exact localized_linkageIdeal_eq_product s r ι hr hι hι1 t ht

end CycleQ2SeedLinkageOrbitProduct

#print axioms CycleQ2SeedLinkageOrbitProduct.localAction_component_map_eq
#print axioms CycleQ2SeedLinkageOrbitProduct.localized_linkageIdeal_eq_orbit_product
end
end


/- Component: continuation_3/cylinder_bridge/SeedLocalizedProjection.lean -/
section
/-! # Homogeneous projection and regular division in actual coordinate rings -/

noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizedProjection

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading CycleQ2SeedLocalizedClearing
  CycleQ2SeedHomogeneousDenominator CycleQ2WeightedComponent

variable (R : Type*) [CommRing R] [Nontrivial R]

def HasLocalGrade (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (q : SeedLocal R r ι s) : Prop :=
  ∀ ab, HasGrade ab (signedGrade d) (localizedCoordinates R r ι s q ab)

theorem signed_shift_grade (s : Finset (Fin 3)) (n : ℕ) (d : Grade) :
    signedGrade (n • openGrade s+d)=signedGrade d+baseGrade (n • openExponent s) := by
  change signedGradeHom (n • openGrade s+d)=_
  rw [map_add]
  change signedGrade (n • openGrade s)+signedGrade d=_
  rw [signed_openGrade_nsmul,add_comm]

theorem polynomial_hasLocalGrade (r ι : R) (s : Finset (Fin 3)) (p : Poly R)
    (d : Grade) (hp : HG p d) : HasLocalGrade R r ι s d (polynomialMap R r ι s p) :=
  localized_polynomial_homogeneous R r ι s p d hp

theorem hasLocalGrade_add (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (p q : SeedLocal R r ι s) (hp : HasLocalGrade R r ι s d p)
    (hq : HasLocalGrade R r ι s d q) : HasLocalGrade R r ι s d (p+q) := by
  intro ab
  change HasGrade ab (signedGrade d) (localizedCoordinates R r ι s (p+q) ab)
  rw [map_add,Pi.add_apply]
  exact hasGrade_add ab _ (hp ab) (hq ab)

/-- A polynomial whose actual localized image has one homogeneous grade is
unchanged in that localization by projecting its original polynomial grade. -/
theorem component_eq_of_homogeneous_image (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (d : Grade)
    (hp : HasLocalGrade R r ι s d (polynomialMap R r ι s p)) :
    polynomialMap R r ι s (weightedHomogeneousComponent fullGrading d p)=
      polynomialMap R r ι s p := by
  have hq (ab : ShiftIndex) : HasGrade ab (signedGrade d)
      (baseToLaurent R ((seedBasis R r ι).repr (Ideal.Quotient.mk _ p) ab)) := by
    simpa only [polynomialMap,RingHom.comp_apply,localizedCoordinates_algebraMap] using hp ab
  obtain ⟨P,_,hPg,hPq⟩ := exists_signed_homogeneous_representative R r ι
    (Ideal.Quotient.mk _ p) (signedGrade d) hq
  have hPw : HG P d := (signedHomogeneous_iff R P d).mp hPg
  have hmem : p-P ∈ equationsIdeal (smoothH ι) (smoothF r ι) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub,hPq,sub_self]
  have hc := weightedHomogeneousComponent_mem_of_mem R fullGrading
    (CycleQ2SegreWeightedProjection.equationsIdeal_homogeneous r ι) hmem d
  rw [map_sub,hPw.weightedHomogeneousComponent_same] at hc
  have he : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (weightedHomogeneousComponent fullGrading d p)=Ideal.Quotient.mk _ P :=
    Ideal.Quotient.eq.mpr hc
  exact congrArg (algebraMap (SeedRing r ι) (SeedLocal R r ι s)) (he.trans hPq)

theorem fraction_hasLocalGrade (r ι : R) (s : Finset (Fin 3))
    (q : SeedLocal R r ι s) (d : Grade) (n : ℕ) (p : Poly R)
    (hp : HG p (n • openGrade s+d))
    (he : polynomialMap R r ι s p=polynomialMap R r ι s (openPolynomial R s^n)*q) :
    HasLocalGrade R r ι s d q := by
  apply (localized_homogeneous_iff_fraction R r ι s q (signedGrade d)).mpr
  refine ⟨n,p,?_,?_⟩
  · rw [← signed_shift_grade s n d]
    exact (signedHomogeneous_iff R p _).mpr hp
  · have hden : algebraMap (SeedRing r ι) (SeedLocal R r ι s)
        (algebraMap (Base R) (SeedRing r ι) (baseProduct R s^n))=
        polynomialMap R r ι s (openPolynomial R s^n) := by
      simp only [polynomialMap,RingHom.comp_apply,map_pow,quotient_openPolynomial]
    rw [hden]
    calc
      q*polynomialMap R r ι s (openPolynomial R s^n)=
          polynomialMap R r ι s (openPolynomial R s^n)*q :=
        mul_comm q (polynomialMap R r ι s (openPolynomial R s^n))
      _ = polynomialMap R r ι s p := he.symm

/-- Multiplication in the actual localized seed ring respects the original
degree and character. -/
theorem hasLocalGrade_mul (r ι : R) (s : Finset (Fin 3)) (d e : Grade)
    (x y : SeedLocal R r ι s) (hx : HasLocalGrade R r ι s d x)
    (hy : HasLocalGrade R r ι s e y) : HasLocalGrade R r ι s (d+e) (x*y) := by
  let z : Fin 2 → SeedLocal R r ι s := ![x,y]
  let g : Fin 2 → Grade := ![d,e]
  have hz : ∀ i ab, HasGrade ab (signedGrade (g i))
      (localizedCoordinates R r ι s (z i) ab) := by
    intro i
    fin_cases i
    · exact hx
    · exact hy
  obtain ⟨n,P,hP,hEq⟩ := exists_common_homogeneous_denominator R r ι s g z hz
  have hP0 : HG (P 0) (n • openGrade s+d) := hP 0
  have hP1 : HG (P 1) (n • openGrade s+e) := hP 1
  have hE0 : polynomialMap R r ι s (P 0)=
      polynomialMap R r ι s (openPolynomial R s^n)*x := hEq 0
  have hE1 : polynomialMap R r ι s (P 1)=
      polynomialMap R r ι s (openPolynomial R s^n)*y := hEq 1
  apply fraction_hasLocalGrade R r ι s (x*y) (d+e) (n+n) (P 0*P 1)
  · have hgrade : (n • openGrade s+d)+(n • openGrade s+e)=
        (n+n) • openGrade s+(d+e) := by rw [add_nsmul]; abel
    exact hgrade ▸ hP0.mul hP1
  · rw [map_mul,hE0,hE1,pow_add,map_mul]
    ring

/-- Division by a regular homogeneous polynomial preserves the expected
grade in the actual localization. No domain assumption is needed. -/
theorem regular_division_hasLocalGrade (r ι : R) (s : Finset (Fin 3))
    (p : Poly R) (e d : Grade) (hp : HG p e)
    (hreg : Function.Injective (fun z : SeedLocal R r ι s => polynomialMap R r ι s p*z))
    (x : SeedLocal R r ι s)
    (hx : HasLocalGrade R r ι s (d+e) (polynomialMap R r ι s p*x)) :
    HasLocalGrade R r ι s d x := by
  let f := polynomialMap R r ι s
  obtain ⟨n,P,hP⟩ := exists_common_polynomial_denominator R r ι s (fun _ _ => x)
  let Q := P 0 0
  have hQ : f Q=f (openPolynomial R s^n)*x := hP 0 0
  have hmul := hasLocalGrade_mul R r ι s (n • openGrade s) (d+e)
    (f (openPolynomial R s^n)) (f p*x)
    (polynomial_hasLocalGrade R r ι s _ _ ((openPolynomial_homogeneous R s).pow n)) hx
  have hEq : f (p*Q)=f (openPolynomial R s^n)*(f p*x) := by rw [map_mul,hQ]; ring
  rw [← hEq] at hmul
  have hc := component_eq_of_homogeneous_image R r ι s (p*Q)
    (n • openGrade s+(d+e)) hmul
  have hgrade : n • openGrade s+(d+e)=e+(n • openGrade s+d) := by abel
  rw [hgrade,component_mul_left fullGrading p Q e (n • openGrade s+d) hp,map_mul,map_mul] at hc
  have hcancel : f (weightedHomogeneousComponent fullGrading (n • openGrade s+d) Q)=f Q := hreg hc
  apply fraction_hasLocalGrade R r ι s x d n
    (weightedHomogeneousComponent fullGrading (n • openGrade s+d) Q)
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  exact hcancel.trans hQ

end CycleQ2SeedLocalizedProjection

#print axioms CycleQ2SeedLocalizedProjection.component_eq_of_homogeneous_image
#print axioms CycleQ2SeedLocalizedProjection.hasLocalGrade_mul
#print axioms CycleQ2SeedLocalizedProjection.regular_division_hasLocalGrade
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechComplex.lean -/
section
/-! # The actual graded cofactor Čech complex

The cochains below are literal matrix-valued sections of the seed coordinate
localizations. Both differentials use the canonical localization maps.
The kernel-valued first cohomology is a quotient of actual cocycles by the
actual local-kernel boundaries.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 100000

namespace CycleQ2SegreCechConnecting

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalization CycleQ2SeedCechLocalizedBasis
  CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates CycleQ2SeedCechGlobalGluing
  CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

abbrev PairMatrices (r ι : R) :=
  (i j : Fin 3) → Matrix (Fin 3) (Fin 3) (SeedLocal R r ι {i,j})
abbrev TripleMatrices (r ι : R) :=
  (i j k : Fin 3) → Matrix (Fin 3) (Fin 3) (SeedLocal R r ι Finset.univ)

def localGraded (r ι : R) (g : MatrixGrades) : Submodule R (LocalMatrices R r ι) where
  carrier := {N | LocalHasGrades R r ι g N}
  zero_mem' := by intro i k l ab e he; simp
  add_mem' hN hK := by
    intro i k l ab
    change HasGrade ab (g k l) (localizedCoordinates R r ι {i} (_+_) ab)
    rw [map_add,Pi.add_apply]
    exact hasGrade_add ab (g k l) (hN i k l ab) (hK i k l ab)
  smul_mem' c N hN := by
    intro i k l ab
    change HasGrade ab (g k l) (localizedCoordinates R r ι {i} (c • N i k l) ab)
    rw [localizedCoordinates_R_smul,Pi.smul_apply]
    intro e he
    simp [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,hN i k l ab e he]

def pairGraded (r ι : R) (g : MatrixGrades) : Submodule R (PairMatrices R r ι) where
  carrier := {P | ∀ i j k l ab,
    HasGrade ab (g k l) (localizedCoordinates R r ι {i,j} (P i j k l) ab)}
  zero_mem' := by intro i j k l ab e he; simp
  add_mem' hP hQ := by
    intro i j k l ab
    change HasGrade ab (g k l) (localizedCoordinates R r ι {i,j} (_+_) ab)
    rw [map_add,Pi.add_apply]
    exact hasGrade_add ab (g k l) (hP i j k l ab) (hQ i j k l ab)
  smul_mem' c P hP := by
    intro i j k l ab
    change HasGrade ab (g k l) (localizedCoordinates R r ι {i,j} (c • P i j k l) ab)
    rw [localizedCoordinates_R_smul,Pi.smul_apply]
    intro e he
    simp [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,hP i j k l ab e he]

def localD (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    localGraded R r ι g →ₗ[R] LocalMatrices R r ι where
  toFun N i := cofactorDifferential (localizeMatrix R r ι {i} M) (N.val i)
  map_add' N K := by
    funext i
    exact map_add ((cofactorDifferentialLinear (localizeMatrix R r ι {i} M)).restrictScalars R) _ _
  map_smul' c N := by
    funext i
    exact map_smul ((cofactorDifferentialLinear (localizeMatrix R r ι {i} M)).restrictScalars R) c _

def pairD (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    pairGraded R r ι g →ₗ[R] PairMatrices R r ι where
  toFun P i j := cofactorDifferential (localizeMatrix R r ι {i,j} M) (P.val i j)
  map_add' P Q := by
    funext i j
    exact map_add ((cofactorDifferentialLinear (localizeMatrix R r ι {i,j} M)).restrictScalars R) _ _
  map_smul' c P := by
    funext i j
    exact map_smul ((cofactorDifferentialLinear (localizeMatrix R r ι {i,j} M)).restrictScalars R) c _

def overlapLinear (r ι : R) (g : MatrixGrades) :
    localGraded R r ι g →ₗ[R] pairGraded R r ι g where
  toFun N := ⟨overlapDifference R r ι N.val,by
    intro i j k l ab
    change HasGrade ab (g k l) (localizedCoordinates R r ι {i,j}
      (secondPairRestriction R r ι i j (N.val j k l)-pairRestriction R r ι i j (N.val i k l)) ab)
    rw [map_sub,Pi.sub_apply]
    simp only [secondPairRestriction,pairRestriction,coordinates_restriction]
    exact hasGrade_sub ab (g k l) (N.property j k l ab) (N.property i k l ab)⟩
  map_add' N K := by
    apply Subtype.ext
    funext i j k l
    change secondPairRestriction R r ι i j (N.val j k l+K.val j k l)-
      pairRestriction R r ι i j (N.val i k l+K.val i k l)=
      (secondPairRestriction R r ι i j (N.val j k l)-pairRestriction R r ι i j (N.val i k l))+
      (secondPairRestriction R r ι i j (K.val j k l)-pairRestriction R r ι i j (K.val i k l))
    rw [map_add,map_add]
    abel
  map_smul' c N := by
    apply Subtype.ext
    funext i j k l
    change secondPairRestriction R r ι i j (c • N.val j k l)-
      pairRestriction R r ι i j (c • N.val i k l)=
      c • (secondPairRestriction R r ι i j (N.val j k l)-pairRestriction R r ι i j (N.val i k l))
    change restrictionLinear R r ι (show ({j}:Finset (Fin 3)) ⊆ {i,j} by simp) (c • N.val j k l)-
      restrictionLinear R r ι (show ({i}:Finset (Fin 3)) ⊆ {i,j} by simp) (c • N.val i k l)=_
    rw [map_smul,map_smul,smul_sub]
    rfl

def cechDifferential (r ι : R) (g : MatrixGrades) :
    pairGraded R r ι g →ₗ[R] TripleMatrices R r ι where
  toFun P i j k :=
    (restriction R r ι (Finset.subset_univ {i,j})).mapMatrix (P.val i j)-
    (restriction R r ι (Finset.subset_univ {i,k})).mapMatrix (P.val i k)+
    (restriction R r ι (Finset.subset_univ {j,k})).mapMatrix (P.val j k)
  map_add' P Q := by
    funext i j k a b
    change restriction R r ι (Finset.subset_univ {i,j}) (P.val i j a b+Q.val i j a b)-
      restriction R r ι (Finset.subset_univ {i,k}) (P.val i k a b+Q.val i k a b)+
      restriction R r ι (Finset.subset_univ {j,k}) (P.val j k a b+Q.val j k a b)=
      (restriction R r ι (Finset.subset_univ {i,j}) (P.val i j a b)-
        restriction R r ι (Finset.subset_univ {i,k}) (P.val i k a b)+
        restriction R r ι (Finset.subset_univ {j,k}) (P.val j k a b))+
      (restriction R r ι (Finset.subset_univ {i,j}) (Q.val i j a b)-
        restriction R r ι (Finset.subset_univ {i,k}) (Q.val i k a b)+
        restriction R r ι (Finset.subset_univ {j,k}) (Q.val j k a b))
    rw [map_add,map_add,map_add]
    abel
  map_smul' c P := by
    funext i j k a b
    change restrictionLinear R r ι (Finset.subset_univ {i,j}) (c • P.val i j a b)-
      restrictionLinear R r ι (Finset.subset_univ {i,k}) (c • P.val i k a b)+
      restrictionLinear R r ι (Finset.subset_univ {j,k}) (c • P.val j k a b)=
      c • (restrictionLinear R r ι (Finset.subset_univ {i,j}) (P.val i j a b)-
        restrictionLinear R r ι (Finset.subset_univ {i,k}) (P.val i k a b)+
        restrictionLinear R r ι (Finset.subset_univ {j,k}) (P.val j k a b))
    rw [map_smul,map_smul,map_smul,smul_add,smul_sub]

theorem cechDifferential_overlap (r ι : R) (g : MatrixGrades)
    (N : localGraded R r ι g) :
    cechDifferential R r ι g (overlapLinear R r ι g N)=0 := by
  funext i j k a b
  change restriction R r ι (Finset.subset_univ {i,j})
      (secondPairRestriction R r ι i j (N.val j a b)-pairRestriction R r ι i j (N.val i a b))-
    restriction R r ι (Finset.subset_univ {i,k})
      (secondPairRestriction R r ι i k (N.val k a b)-pairRestriction R r ι i k (N.val i a b))+
    restriction R r ι (Finset.subset_univ {j,k})
      (secondPairRestriction R r ι j k (N.val k a b)-pairRestriction R r ι j k (N.val j a b))=0
  simp only [map_sub,pairRestriction,secondPairRestriction,restriction_comp]
  abel

def gradedKernelCocycles (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Submodule R (pairGraded R r ι g) :=
  LinearMap.ker (pairD R r ι M g) ⊓ LinearMap.ker (cechDifferential R r ι g)

theorem overlap_mem_gradedKernelCocycles (r ι : R) (M C : GlobalMatrix R r ι)
    (g : MatrixGrades) (N : localGraded R r ι g)
    (hN : HasLocalLift R r ι M C N.val) :
    overlapLinear R r ι g N ∈ gradedKernelCocycles R r ι M g := by
  constructor
  · change pairD R r ι M g (overlapLinear R r ι g N)=0
    funext i j
    exact overlapDifference_kernel R r ι M C N.val hN i j
  · exact cechDifferential_overlap R r ι g N

/-- The actual cocycles viewed as a single submodule of the raw pair sections.
Flattening the two conditions keeps the quotient's canonical module structure
independent of nested subtype presentations. -/
def kernelCocycles (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Submodule R (PairMatrices R r ι) :=
  (gradedKernelCocycles R r ι M g).map (pairGraded R r ι g).subtype

theorem overlap_mem_kernelCocycles (r ι : R) (M C : GlobalMatrix R r ι)
    (g : MatrixGrades) (N : localGraded R r ι g)
    (hN : HasLocalLift R r ι M C N.val) :
    overlapDifference R r ι N.val ∈ kernelCocycles R r ι M g :=
  ⟨overlapLinear R r ι g N,overlap_mem_gradedKernelCocycles R r ι M C g N hN,rfl⟩

def kernelCoboundary (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    LinearMap.ker (localD R r ι M g) →ₗ[R] kernelCocycles R r ι M g where
  toFun N := ⟨overlapDifference R r ι N.val.val,
    overlap_mem_kernelCocycles R r ι M 0 g N.val (by
      intro i
      have hz : localD R r ι M g N.val=0 := N.property
      have hh := congrFun hz i
      change cofactorDifferential (localizeMatrix R r ι {i} M) (N.val.val i)=0 at hh
      change cofactorDifferential (localizeMatrix R r ι {i} M) (N.val.val i)=
        localizeMatrix R r ι {i} 0
      rw [hh]
      ext a b
      exact (map_zero (algebraMap (SeedRing r ι) (SeedLocal R r ι {i}))).symm)⟩
  map_add' N K := by
    apply Subtype.ext
    change overlapDifference R r ι (N.val.val+K.val.val)=
      overlapDifference R r ι N.val.val+overlapDifference R r ι K.val.val
    exact congrArg (fun q : pairGraded R r ι g => q.val)
      (map_add (overlapLinear R r ι g) N.val K.val)
  map_smul' c N := by
    apply Subtype.ext
    change overlapDifference R r ι (c • N.val.val)=c • overlapDifference R r ι N.val.val
    exact congrArg (fun q : pairGraded R r ι g => q.val)
      (map_smul (overlapLinear R r ι g) c N.val)


end CycleQ2SegreCechConnecting

#print axioms CycleQ2SegreCechConnecting.cechDifferential_overlap
#print axioms CycleQ2SegreCechConnecting.overlap_mem_kernelCocycles
#print axioms CycleQ2SegreCechConnecting.kernelCoboundary
end
end


/- Component: continuation_3/cylinder_bridge/SegreGradedChartExact.lean -/
section
/-! # Actual graded relation-kernel lifts on the modular and complex covers

Every homogeneous global relation-kernel vector has the required homogeneous
local cofactor preimages. All local exactness, basepoint generation, denominator
clearing and grading premises are discharged for the literal seed matrices.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000

namespace CycleQ2SegreGradedChartExact

open Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal CycleQ2SegreRelationsLocal
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedLocalizedClearing
  CycleQ2SegreLocalizedGradedLift CycleQ2IncidenceJacobianNaturality

section Naturality

variable {A B : Type*} [CommRing A] [CommRing B]

theorem map_vector (φ : A →+* B) (C : Matrix (Fin 3) (Fin 3) A) :
    (fun j => φ (vector C j))=vector (φ.mapMatrix C) := by
  funext j
  fin_cases j <;> rfl

theorem map_relations_action (φ : A →+* B) (M C : Matrix (Fin 3) (Fin 3) A) :
    (fun k => φ ((CycleQ2SegreRelations.relations M *ᵥ vector C) k))=
      CycleQ2SegreRelations.relations (φ.mapMatrix M) *ᵥ vector (φ.mapMatrix C) := by
  funext k
  change φ (∑ j, CycleQ2SegreRelations.relations M k j*vector C j)=
    ∑ j, CycleQ2SegreRelations.relations (φ.mapMatrix M) k j*vector (φ.mapMatrix C) j
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_mul,segreRelations_map]
  congr 1
  exact congrFun (map_vector φ C) j

theorem map_relations_zero (φ : A →+* B) (M C : Matrix (Fin 3) (Fin 3) A)
    (h : CycleQ2SegreRelations.relations M *ᵥ vector C=0) :
    CycleQ2SegreRelations.relations (φ.mapMatrix M) *ᵥ vector (φ.mapMatrix C)=0 := by
  rw [← map_relations_action,h]
  funext k
  exact map_zero φ

end Naturality

section Modular

variable {R : Type*} [CommRing R] [Nontrivial R] [CharP R 109]

theorem modular_graded_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (Poly R))
    (hC : ∀ i j, HG (C i j) (28,0))
    (hrel : CycleQ2SegreRelations.relations (seedQuotientMatrix (57 : R) 33) *ᵥ
      vector ((Ideal.Quotient.mk (equationsIdeal (smoothH 33) (smoothF 57 33))).mapMatrix C)=0) :
    ∃ N : Matrix (Fin 3) (Fin 3) (SeedLocal R 57 33 s),
      (∀ i j ab, HasGrade ab (14,0) (localizedCoordinates R 57 33 s (N i j) ab)) ∧
      cofactorDifferential (CycleQ2SegreModularChartExact.chartMatrix (R := R) s) N=
        (polynomialMap R 57 33 s).mapMatrix C := by
  have hlocal := map_relations_zero (B := SeedLocal R 57 33 s)
    (algebraMap (SeedRing (57 : R) 33) (SeedLocal R 57 33 s))
    (seedQuotientMatrix (57 : R) 33)
    ((Ideal.Quotient.mk (equationsIdeal (smoothH 33) (smoothF 57 33))).mapMatrix C) hrel
  change CycleQ2SegreRelations.relations (CycleQ2SegreModularChartExact.chartMatrix (R := R) s) *ᵥ
    vector ((polynomialMap R 57 33 s).mapMatrix C)=0 at hlocal
  obtain ⟨N,hN⟩ := (CycleQ2SegreModularChartExact.coordinate_chart_relations_exact (R := R) s hs _).mp hlocal
  exact exists_graded_local_lift R 57 33 s (rawSeedMatrix 57) C
    (rawSeedMatrix_homogeneous 57) hC N hN

end Modular

/-- Characteristic-zero graded local exactness at the actual complex seed,
with no rank, minor, pivot, span, or graded-lift premise. -/
theorem complex_graded_lift (s : Finset (Fin 3)) (hs : s.Nonempty)
    (C : Matrix (Fin 3) (Fin 3) (Poly ℂ))
    (hC : ∀ i j, HG (C i j) (28,0))
    (hrel : CycleQ2SegreRelations.relations (seedQuotientMatrix (57 : ℂ) Complex.I) *ᵥ
      vector ((Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF 57 Complex.I))).mapMatrix C)=0) :
    ∃ N : Matrix (Fin 3) (Fin 3) (SeedLocal ℂ 57 Complex.I s),
      (∀ i j ab, HasGrade ab (14,0) (localizedCoordinates ℂ 57 Complex.I s (N i j) ab)) ∧
      cofactorDifferential (CycleQ2SegreComplexChartExact.chartMatrix s) N=
        (polynomialMap ℂ 57 Complex.I s).mapMatrix C := by
  have hlocal := map_relations_zero (B := SeedLocal ℂ 57 Complex.I s)
    (algebraMap (SeedRing (57 : ℂ) Complex.I) (SeedLocal ℂ 57 Complex.I s))
    (seedQuotientMatrix (57 : ℂ) Complex.I)
    ((Ideal.Quotient.mk (equationsIdeal (smoothH Complex.I) (smoothF 57 Complex.I))).mapMatrix C) hrel
  change CycleQ2SegreRelations.relations (CycleQ2SegreComplexChartExact.chartMatrix s) *ᵥ
    vector ((polynomialMap ℂ 57 Complex.I s).mapMatrix C)=0 at hlocal
  obtain ⟨N,hN⟩ := (CycleQ2SegreComplexChartExact.coordinate_chart_relations_exact s hs _).mp hlocal
  exact exists_graded_local_lift ℂ 57 Complex.I s (rawSeedMatrix 57) C
    (rawSeedMatrix_homogeneous 57) hC N hN

end CycleQ2SegreGradedChartExact

#print axioms CycleQ2SegreGradedChartExact.modular_graded_lift
#print axioms CycleQ2SegreGradedChartExact.complex_graded_lift
end
end


/- Component: continuation_3/CurveOpenFaithfulness.lean -/
section
/-! # Faithfulness of the remaining curve chart comparison

The third normal base coordinate is regular in the curve quotient because
that quotient is free over its two-variable base. Thus adjoining that
coordinate to the middle seed chart loses no sections.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveOpenFaithfulness

open MvPolynomial CycleQ2CurveRestriction CycleQ2CurveLocalizedRestriction
  CycleQ2CurveQuotientFiniteFree

theorem baseCoordinate_mul_injective (R : Type*) [CommRing R] [IsDomain R]
    (side : Side) (r ι : R) (j : Fin 2) :
    Function.Injective (fun q : CurveRing side r ι =>
      algebraMap (Base R) (CurveRing side r ι) (X j)*q) := by
  intro p q hpq
  have hsm : (X j:Base R) • p=(X j:Base R) • q := by
    change algebraMap (Base R) (CurveRing side r ι) (X j)*p=
      algebraMap (Base R) (CurveRing side r ι) (X j)*q
    exact hpq
  apply (curveBasis R side r ι).repr.injective
  apply Finsupp.ext
  intro ab
  have hh := congrArg (fun z : CurveRing side r ι => (curveBasis R side r ι).repr z ab) hsm
  simp only [map_smul,Finsupp.smul_apply,smul_eq_mul] at hh
  exact mul_left_cancel₀ (X_ne_zero j) hh

theorem last_curveProduct (side : Side) (r ι : ℂ) :
    curveProduct ℂ side r ι {2}=
      algebraMap ℂ (CurveRing side r ι) (coordinateScale ℂ side)*
        algebraMap (Base ℂ) (CurveRing side r ι) (X (1:Fin 2)) := by
  have hh := restriction_baseCoordinate ℂ side r ι (1:Fin 2)
  simpa [curveProduct,seedProduct,CycleQ2SeedCechLocalization.baseProduct,
    baseIndex,CB,Matrix.cons_val_succ,Matrix.cons_val_zero,Fin.reduceSucc] using hh

theorem last_curveProduct_regular (side : Side) (r ι : ℂ) :
    Function.Injective (fun q : CurveRing side r ι => curveProduct ℂ side r ι {2}*q) := by
  rw [last_curveProduct]
  intro p q h
  apply baseCoordinate_mul_injective ℂ side r ι 1
  apply ((complex_scale_unit side).map (algebraMap ℂ (CurveRing side r ι))).mul_right_injective
  simpa only [mul_assoc] using h

theorem middle_last_product (side : Side) (r ι : ℂ) :
    curveProduct ℂ side r ι {1,2}=
      curveProduct ℂ side r ι {1}*curveProduct ℂ side r ι {2} := by
  simp [curveProduct,seedProduct,CycleQ2SeedCechLocalization.baseProduct]

/-- The exact comparison needed to recover the middle chart from its
overlap with the last base-coordinate chart. -/
theorem middle_to_overlap_injective (side : Side) (r ι : ℂ) :
    Function.Injective (CycleQ2CurveLocalizedRestriction.restriction ℂ side r ι
      (show ({1}:Finset (Fin 3))⊆{1,2} by decide)) := by
  letI : IsLocalization.Away
      (curveProduct ℂ side r ι {1}*curveProduct ℂ side r ι {2})
      (RestrictedLocal ℂ side r ι {1,2}) := by
    rw [←middle_last_product]
    infer_instance
  apply CycleQ2LocalizationRegularFactor.restriction_injective
    (curveProduct ℂ side r ι {1}) (curveProduct ℂ side r ι {2})
    (last_curveProduct_regular side r ι)
  exact fun p => restriction_algebraMap ℂ side r ι _ p

end CycleQ2CurveOpenFaithfulness

#print axioms CycleQ2CurveOpenFaithfulness.middle_to_overlap_injective
end
end


/- Component: continuation_3/CurveRestrictionGrading.lean -/
section
/-! # Grading and naturality of the actual curve restriction -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveLocalizedRestriction

open MvPolynomial CycleQ2CurveRestriction CycleQ2SegreTangentLocal
  CycleQ2IncidenceGradedBasis CycleQ2IncidenceNormalForm

variable (R : Type*) [CommRing R]

theorem baseOpenMap_natural (side : Side) (r ι : R) {s t : Finset (Fin 2)}
    (hst : s⊆t) (hscale : IsUnit (coordinateScale R side)) :
    (CycleQ2CurveCechRestrictions.restriction R side r ι hst).comp (baseOpenMap R side r ι s hscale)=
      (baseOpenMap R side r ι t hscale).comp
        (CycleQ2SeedCechRestrictions.restriction R r ι (Finset.image_subset_image hst)) := by
  apply IsLocalization.ringHom_ext (S:=SL R r ι (seedOpen s))
    (Submonoid.powers (seedProduct R r ι (seedOpen s)))
  apply RingHom.ext
  intro p
  change CycleQ2CurveCechRestrictions.restriction R side r ι hst
      (baseOpenMap R side r ι s hscale (algebraMap (SeedRing r ι) (SL R r ι (seedOpen s)) p))=
    baseOpenMap R side r ι t hscale
      (CycleQ2SeedCechRestrictions.restriction R r ι
        (show seedOpen s⊆seedOpen t from Finset.image_subset_image hst)
        (algebraMap (SeedRing r ι) (SL R r ι (seedOpen s)) p))
  calc
    _ = CycleQ2CurveCechRestrictions.restriction R side r ι hst
        (algebraMap (CurveRing side r ι) (CL R side r ι s) (seedRestriction side r ι p)) :=
      congrArg (CycleQ2CurveCechRestrictions.restriction R side r ι hst)
        (baseOpenMap_algebraMap R side r ι s hscale p)
    _ = algebraMap (CurveRing side r ι) (CL R side r ι t) (seedRestriction side r ι p) :=
      CycleQ2CurveCechRestrictions.restriction_algebraMap R side r ι hst _
    _ = baseOpenMap R side r ι t hscale (algebraMap (SeedRing r ι) (SL R r ι (seedOpen t)) p) :=
      (baseOpenMap_algebraMap R side r ι t hscale p).symm
    _ = _ := congrArg (baseOpenMap R side r ι t hscale)
      (CycleQ2SeedCechRestrictions.restriction_algebraMap R r ι
        (show seedOpen s⊆seedOpen t from Finset.image_subset_image hst) p).symm

theorem substitution_signedHomogeneous (side : Side) (r : R)
    (p : MvPolynomial (Fin 5) R) (g : CycleQ2SeedCechThreeOpen.LaurentGrade)
    (hp : CycleQ2SeedQuotientGrading.SignedHomogeneous R p g) :
    CycleQ2CurveQuotientGrading.SignedHomogeneous R (substitution side r p) g.1 := by
  by_cases hz : p=0
  · subst p
    intro e he
    simp at he
  · obtain ⟨e,he⟩ := exists_coeff_ne_zero hz
    have hg := hp e he
    have hh : p.IsWeightedHomogeneous fullGrading (Finsupp.weight fullGrading e) := by
      apply (CycleQ2SeedQuotientGrading.signedHomogeneous_iff R p _).mp
      exact hg.symm ▸ hp
    have hs := substitution_homogeneous side r hh
    have ho := (CycleQ2CurveQuotientGrading.signedHomogeneous_iff R
      (substitution side r p) (Finsupp.weight fullGrading e).1).mpr hs
    have hd := congrArg Prod.fst hg
    exact hd ▸ ho

end CycleQ2CurveLocalizedRestriction

#print axioms CycleQ2CurveLocalizedRestriction.baseOpenMap_natural
#print axioms CycleQ2CurveLocalizedRestriction.substitution_signedHomogeneous
end
end


/- Component: continuation_3/CurveRestrictionKernel.lean -/
section
/-! # The actual component ideals are the kernels of the curve restrictions -/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestrictionKernel

open MvPolynomial CycleQ2CurveRestriction CycleQ2IncidenceNormalForm
  CycleQ2IncidenceEquations CycleQ2SegreTangentLocal

abbrev P5 := MvPolynomial (Fin 5) ℂ

def componentFirst (side : Side) (r : ℂ) : P5 := match side with
  | .left => X 0^2-C r*X 1*X 3
  | .right => X 0^2+X 2^2

def componentSecond (side : Side) (r : ℂ) : P5 := match side with
  | .left => X 4+X 2^2
  | .right => X 4-C r*X 1*X 3

def componentIdeal (side : Side) (r ι : ℂ) : Ideal (SeedRing r ι) :=
  Ideal.span {Ideal.Quotient.mk _ (componentFirst side r),
    Ideal.Quotient.mk _ (componentSecond side r)}

abbrev ComponentQuotient (side : Side) (r ι : ℂ) := SeedRing r ι ⧸ componentIdeal side r ι

def ambientToComponent (side : Side) (r ι : ℂ) : P5 →ₐ[ℂ] ComponentQuotient side r ι :=
  (Ideal.Quotient.mkₐ ℂ (componentIdeal side r ι)).comp
    (Ideal.Quotient.mkₐ ℂ (equationsIdeal (smoothH ι) (smoothF r ι)))

theorem ambient_first (side : Side) (r ι : ℂ) :
    ambientToComponent side r ι (componentFirst side r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp [componentIdeal])

theorem ambient_second (side : Side) (r ι : ℂ) :
    ambientToComponent side r ι (componentSecond side r)=0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp [componentIdeal])

theorem ambient_h (side : Side) (r ι : ℂ) : ambientToComponent side r ι (smoothH ι)=0 := by
  have hh : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (smoothH ι)=0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))
  change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (smoothH ι))=0
  rw [hh,map_zero]

def variableIndex (j : Fin 4) : Fin 5 := j.castSucc

def inclusion : CP →ₐ[ℂ] P5 := rename variableIndex

theorem inclusion_quadric (side : Side) (r : ℂ) :
    inclusion (originalQuadric side r)=componentFirst side r := by
  cases side <;> simp [inclusion,variableIndex,originalQuadric,componentFirst]

theorem inclusion_cubic (ι : ℂ) : inclusion (originalCubic ι)=smoothH ι := by
  simp [inclusion,variableIndex,originalCubic,smoothH,smoothB,smoothA]
  ring

def originalToComponent (side : Side) (r ι : ℂ) :
    CP ⧸ originalCurveIdeal side r ι →ₐ[ℂ] ComponentQuotient side r ι :=
  Ideal.Quotient.liftₐ _ ((ambientToComponent side r ι).comp inclusion) (by
    intro p hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    rw [←hab,map_add,map_mul,map_mul]
    change _*ambientToComponent side r ι (inclusion (originalQuadric side r))+
      _*ambientToComponent side r ι (inclusion (originalCubic ι))=0
    rw [inclusion_quadric,inclusion_cubic,ambient_first,ambient_h]
    ring)

@[simp] theorem originalToComponent_mk (side : Side) (r ι : ℂ) (p : CP) :
    originalToComponent side r ι (Ideal.Quotient.mk (originalCurveIdeal side r ι) p)=
      ambientToComponent side r ι (inclusion p) := rfl

theorem originalToComponent_substitution (side : Side) (r ι : ℂ) (p : P5) :
    originalToComponent side r ι
      (Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p))=
      ambientToComponent side r ι p := by
  have h : (originalToComponent side r ι).comp
      ((Ideal.Quotient.mkₐ ℂ (originalCurveIdeal side r ι)).comp (originalSubstitution side r))=
      ambientToComponent side r ι := by
    apply MvPolynomial.algHom_ext
    intro j
    have hw := ambient_second side r ι
    cases side <;> fin_cases j <;>
      simp [AlgHom.comp_apply,originalToComponent_mk,originalSubstitution,
        originalRestrictionValues,inclusion,variableIndex,Matrix.cons_val_succ,Fin.reduceSucc]
    · simp only [componentSecond,map_add,map_pow] at hw
      linear_combination -hw
    · simp only [componentSecond,map_sub,map_mul] at hw
      have hc : ambientToComponent .right r ι (C r)=
          algebraMap ℂ (ComponentQuotient .right r ι) r :=
        (ambientToComponent .right r ι).commutes r
      rw [hc] at hw
      linear_combination -hw
  exact congrArg (fun f : P5 →ₐ[ℂ] ComponentQuotient side r ι => f p) h

theorem actualRestriction_mk_original (side : Side) (r ι : ℂ) (p : P5) :
    seedRestriction side r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      originalCurveEquiv side r ι
        (Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p)) := by
  rw [seedRestriction_mk,originalCurveEquiv_mk]
  congr 1
  exact congrArg (fun f : P5 →ₐ[ℂ] CP => f p) (coordinateMap_substitution side r).symm

theorem component_le_kernel (side : Side) (r ι : ℂ) :
    componentIdeal side r ι≤RingHom.ker (seedRestriction side r ι).toRingHom := by
  apply Ideal.span_le.mpr
  intro p hp
  rcases hp with rfl | ⟨rfl⟩
  · change seedRestriction side r ι (Ideal.Quotient.mk _ (componentFirst side r))=0
    rw [actualRestriction_mk_original]
    have hq : originalSubstitution side r (componentFirst side r)=originalQuadric side r := by
      cases side <;> simp [originalSubstitution,originalRestrictionValues,componentFirst,originalQuadric]
    rw [hq]
    have hz : Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalQuadric side r)=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [originalCurveIdeal]))
    rw [hz,map_zero]
  · change seedRestriction side r ι (Ideal.Quotient.mk _ (componentSecond side r))=0
    rw [actualRestriction_mk_original]
    have hz : originalSubstitution side r (componentSecond side r)=0 := by
      cases side <;> simp [originalSubstitution,originalRestrictionValues,componentSecond]
    rw [hz,map_zero,map_zero]

/-- The normal-form restriction has exactly the original two-generator
component ideal as its kernel, including the right coordinate change. -/
theorem kernel_eq_componentIdeal (side : Side) (r ι : ℂ) :
    RingHom.ker (seedRestriction side r ι).toRingHom=componentIdeal side r ι := by
  apply le_antisymm _ (component_le_kernel side r ι)
  intro q hq
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  have hh : seedRestriction side r ι (Ideal.Quotient.mk _ p)=0 := hq
  rw [actualRestriction_mk_original] at hh
  have ho : Ideal.Quotient.mk (originalCurveIdeal side r ι) (originalSubstitution side r p)=0 :=
    (originalCurveEquiv side r ι).injective (hh.trans (map_zero _).symm)
  have hc := congrArg (originalToComponent side r ι) ho
  rw [originalToComponent_substitution,map_zero] at hc
  exact Ideal.Quotient.eq_zero_iff_mem.mp hc

/-- Localizing the actual restriction introduces exactly the extension of
the chosen component ideal. No saturation or kernel condition is assumed. -/
theorem localized_kernel_eq_componentIdeal (side : Side) (r ι : ℂ)
    (t : Finset (Fin 3)) :
    RingHom.ker (CycleQ2CurveLocalizedRestriction.localRestrictionMap ℂ side r ι t)=
      (componentIdeal side r ι).map
        (algebraMap (SeedRing r ι) (CycleQ2CurveLocalizedRestriction.SL ℂ r ι t)) := by
  change RingHom.ker (IsLocalization.Away.map
    (CycleQ2CurveLocalizedRestriction.SL ℂ r ι t)
    (CycleQ2CurveLocalizedRestriction.RestrictedLocal ℂ side r ι t)
    (seedRestriction side r ι).toRingHom
    (CycleQ2CurveLocalizedRestriction.seedProduct ℂ r ι t))=_
  rw [CycleQ2LocalizationKernel.kernel_away,kernel_eq_componentIdeal]

end CycleQ2CurveRestrictionKernel

#print axioms CycleQ2CurveRestrictionKernel.kernel_eq_componentIdeal
#print axioms CycleQ2CurveRestrictionKernel.localized_kernel_eq_componentIdeal
end
end


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


/- Component: continuation_3/ModularGlobalCurveGluing.lean -/
section
/-! Graded local linkage sections glue into the actual global curve
restriction kernels over F109. Only the forward ideal-to-curve-kernel
inclusion is used; no orbit or global linkage-ideal comparison is assumed. -/

noncomputable section
set_option maxHeartbeats 300000
set_option maxRecDepth 20000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2ModularGlobalCurveGluing

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SegreTangentLocal CycleQ2CurveRestriction CycleQ2SeedLinkageIdeals
  CycleQ2SeedCechThreeOpen CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions
  CycleQ2SeedCechGlobalGluing CycleQ2SeedQuotientGrading
  CycleQ2ModularGlobalFactorSpaces CycleQ2ModularFactorChartExact

def threeSections {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    (i : Fin 3) → P i := Fin.cases q0 (Fin.cases q1 (Fin.cases q2 (fun i => Fin.elim0 i)))

@[simp] theorem threeSections_zero {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 0=q0 := rfl
@[simp] theorem threeSections_one {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 1=q1 := rfl
@[simp] theorem threeSections_two {P : Fin 3 → Type*} (q0 : P 0) (q1 : P 1) (q2 : P 2) :
    threeSections q0 q1 q2 2=q2 := rfl

theorem compatible_of_two_differences (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (h01 : restriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    Compatible K 57 33 (threeSections (P:=fun i => Chart {i}) q0 q1 q2) := by
  have hc01 (ab) : localizedCoordinates K 57 33 {1} q1 ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates K 57 33 {0,1} q ab) h01
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hc02 (ab) : localizedCoordinates K 57 33 {2} q2 ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    have hh := congrArg (fun q => localizedCoordinates K 57 33 {0,2} q ab) h02
    simp only [map_sub,Pi.sub_apply,map_zero,Pi.zero_apply,coordinates_restriction] at hh
    exact sub_eq_zero.mp hh
  have hcoord (i : Fin 3) (ab) :
      localizedCoordinates K 57 33 {i} (threeSections (P:=fun i => Chart {i}) q0 q1 q2 i) ab=
      localizedCoordinates K 57 33 {0} q0 ab := by
    fin_cases i
    · rfl
    · exact hc01 ab
    · exact hc02 ab
  intro i j
  apply localizedCoordinates_injective K 57 33 {i,j}
  funext ab
  simp only [pairRestriction,secondPairRestriction,coordinates_restriction]
  exact (hcoord i ab).trans (hcoord j ab).symm

theorem scale_unit (side : Side) :
    IsUnit (CycleQ2CurveLocalizedRestriction.coordinateScale K side) := by
  cases side
  · exact isUnit_one
  · exact isUnit_iff_ne_zero.mpr (by decide : (2:K)≠0)

theorem local_ideal_restriction_zero (side : Side) (t : Finset (Fin 3))
    (q : Chart t)
    (hq : q∈(linkageIdeal side (57:K) 33).map (chartMap t)) :
    CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t q=0 := by
  have hle : (linkageIdeal side (57:K) 33).map (chartMap t) ≤
      RingHom.ker (CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t) := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro z hz
    change CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 t (chartMap t z)=0
    have hh := linkageIdeal_le_restrictionKernel side (57:K) 33 hz
    change seedRestriction side (57:K) 33 z=0 at hh
    calc
      _ = algebraMap (CurveRing side (57:K) 33)
          (CycleQ2CurveLocalizedRestriction.RestrictedLocal K side 57 33 t)
          (seedRestriction side (57:K) 33 z) :=
        CycleQ2CurveLocalizedRestriction.localRestrictionMap_algebraMap K side 57 33 t z
      _ = 0 := by rw [hh,map_zero]
  exact hle hq

theorem seedRestriction_zero_of_first_local_zero (side : Side) (q : A)
    (hq : CycleQ2CurveLocalizedRestriction.localRestrictionMap K side 57 33 {0}
      (chartMap {0} q)=0) : seedRestriction side (57:K) 33 q=0 := by
  let e := CycleQ2CurveLocalizedRestriction.baseOpenEquiv K side 57 33 {0}
    (scale_unit side)
  have h := congrArg e hq
  have hb : CycleQ2CurveLocalizedRestriction.baseOpenMap K side 57 33 {0}
      (scale_unit side) (chartMap {0} q)=0 := by
    exact h.trans (map_zero e)
  apply CycleQ2CurveCechGlobalGluing.localization_injective K side 57 33 {0}
  rw [map_zero]
  rw [←CycleQ2CurveLocalizedRestriction.baseOpenMap_algebraMap K side 57 33 {0}
    (scale_unit side) q]
  exact hb

theorem exists_global_curve_kernel_piece (side : Side) (d ch : ℕ)
    (q0 : Chart {0}) (q1 : Chart {1}) (q2 : Chart {2})
    (hq0 : ∀ ab, HasGrade ab ((d:ℤ),(ch:ZMod 3)) (localizedCoordinates K 57 33 {0} q0 ab))
    (hi0 : q0∈(linkageIdeal side (57:K) 33).map (chartMap {0}))
    (h01 : restriction K 57 33 (by decide : ({1}:Finset (Fin 3))⊆{0,1}) q1-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,1}) q0=0)
    (h02 : restriction K 57 33 (by decide : ({2}:Finset (Fin 3))⊆{0,2}) q2-
      restriction K 57 33 (by decide : ({0}:Finset (Fin 3))⊆{0,2}) q0=0) :
    ∃ q : LinearMap.ker (seedRestrictionPiece side (57:K) 33 d ch),
      chartMap {0} q.val.val=q0 ∧ chartMap {1} q.val.val=q1 ∧ chartMap {2} q.val.val=q2 := by
  let qs := threeSections (P:=fun i => Chart {i}) q0 q1 q2
  have hcomp := compatible_of_two_differences q0 q1 q2 h01 h02
  obtain ⟨p,_hstd,hp,hglue⟩ := exists_homogeneous_polynomial_gluing K 57 33 qs hcomp
    ((d:ℤ),(ch:ZMod 3)) hq0
  have hpg : HG p (d,(ch:ZMod 3)) := (signedHomogeneous_iff K p _).mp hp
  let q : SeedPiece (57:K) 33 d ch :=
    ⟨Ideal.Quotient.mk (equationsIdeal (smoothH (33:K)) (smoothF (57:K) 33)) p,
      Submodule.mem_map.mpr ⟨p,hpg,rfl⟩⟩
  have hqzero : seedRestriction side (57:K) 33 q.val=0 := by
    apply seedRestriction_zero_of_first_local_zero side q.val
    have hzero := local_ideal_restriction_zero side {0} q0 hi0
    have he : chartMap {0} q.val=q0 := hglue 0
    rw [he]
    exact hzero
  have hmem : q∈LinearMap.ker (seedRestrictionPiece side (57:K) 33 d ch) := by
    change seedRestrictionPiece side (57:K) 33 d ch q=0
    apply Subtype.ext
    exact hqzero
  exact ⟨⟨q,hmem⟩,hglue 0,hglue 1,hglue 2⟩

end CycleQ2ModularGlobalCurveGluing

#print axioms CycleQ2ModularGlobalCurveGluing.exists_global_curve_kernel_piece
end
end


/- Component: continuation_3/cylinder_bridge/SeedLocalizedGradeLinear.lean -/
section
/-! Linear closure and restriction of the actual localized homogeneous grades. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizedProjection

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalizedBasis CycleQ2SeedCechRestrictions CycleQ2SeedCechLinearCoordinates
  CycleQ2SeedQuotientGrading

variable (R : Type*) [CommRing R] [Nontrivial R]

theorem hasLocalGrade_zero (r ι : R) (s : Finset (Fin 3)) (d : Grade) :
    HasLocalGrade R r ι s d 0 := by
  intro ab e he
  simp

theorem hasLocalGrade_neg (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι s d (-q) := by
  intro ab
  rw [map_neg,Pi.neg_apply]
  intro e he
  simp [hq ab e he]

theorem hasLocalGrade_sub (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (p q : SeedLocal R r ι s) (hp : HasLocalGrade R r ι s d p)
    (hq : HasLocalGrade R r ι s d q) : HasLocalGrade R r ι s d (p-q) := by
  rw [sub_eq_add_neg]
  exact hasLocalGrade_add R r ι s d p (-q) hp (hasLocalGrade_neg R r ι s d q hq)

theorem hasLocalGrade_R_smul (r ι : R) (s : Finset (Fin 3)) (d : Grade)
    (c : R) (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι s d (c • q) := by
  intro ab
  rw [localizedCoordinates_R_smul,Pi.smul_apply]
  intro e he
  simp [AddMonoidAlgebra.coeff_smul,Finsupp.smul_apply,hq ab e he]

theorem hasLocalGrade_restriction (r ι : R) {s t : Finset (Fin 3)} (hst : s⊆t)
    (d : Grade) (q : SeedLocal R r ι s) (hq : HasLocalGrade R r ι s d q) :
    HasLocalGrade R r ι t d (restriction R r ι hst q) := by
  intro ab
  rw [coordinates_restriction]
  exact hq ab

def gradeSubmodule (r ι : R) (s : Finset (Fin 3)) (d : Grade) :
    Submodule R (SeedLocal R r ι s) where
  carrier := {q | HasLocalGrade R r ι s d q}
  zero_mem' := hasLocalGrade_zero R r ι s d
  add_mem' := fun hp hq => hasLocalGrade_add R r ι s d _ _ hp hq
  smul_mem' := fun c _ hq => hasLocalGrade_R_smul R r ι s d c _ hq

end CycleQ2SeedLocalizedProjection

#print axioms CycleQ2SeedLocalizedProjection.gradeSubmodule
end
end


/- Component: continuation_3/cylinder_bridge/SegreCechH1.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000

namespace CycleQ2SegreCechConnecting

variable (R : Type*) [CommRing R] [Nontrivial R]

def kernelBoundaries (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Submodule R (kernelCocycles R r ι M g) :=
  LinearMap.range (kernelCoboundary R r ι M g)

abbrev KernelCechH1 (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :=
  @HasQuotient.Quotient (kernelCocycles R r ι M g)
    (Submodule R (kernelCocycles R r ι M g))
    (@Submodule.hasQuotient R (kernelCocycles R r ι M g) inferInstance inferInstance inferInstance)
    (kernelBoundaries R r ι M g)

example (r ι : R) (M : GlobalMatrix R r ι) (g : MatrixGrades) :
    Module R (KernelCechH1 R r ι M g) := inferInstance

end CycleQ2SegreCechConnecting
end
end


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


