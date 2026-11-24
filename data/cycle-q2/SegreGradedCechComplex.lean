import Proposal.SeedLinkageGluing
import Proposal.IncidenceLinearSplittings

/-!
# The graded Segre Čech complex on three opens
-/

set_option Elab.async false

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
