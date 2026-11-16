import Proposal.SolutionSupport07Part01
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The actual étale parameter space of the moving incidence

The finite trace field was constructed from a Jacobian-localized square
system. Here that same algebra is retained before passage to its generic
fiber. Its universal coordinates satisfy every original incidence equation,
lie in the prescribed basepoint open, and specialize to the literal seed.
The parameter scheme is étale over the ring containing the free time
coordinate and all independent invariant sextic coefficients.

The time derivation is extended through the actual étale algebra by the
canonical isomorphism of Kähler differentials. Thus the nonzero projective
cubic motion is regular on this parameter scheme, rather than just a
derivation of an auxiliary finite extension field.

These statements integrate the polynomial incidence equations. Smoothness
of the projective curve fibers and the comparison with the cycle derivative
remain separate mathematical obligations.

The geometric strategy is due to Ben Diamond and the cited work of Claire
Voisin. Prepared for fqlx with OpenAI ChatGPT assistance.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2EtaleDerivation

open scoped TensorProduct

variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S] [Algebra R S] [IsScalarTower k R S]
  [Algebra.FormallyEtale R S]

/-- Extend a coefficient derivation through a formally étale algebra using
the actual base-change isomorphism of Kähler differentials. -/
def extend (D : Derivation k R R) : Derivation k S S :=
  (KaehlerDifferential.linearMapEquivDerivation k S)
    ((((Algebra.ofId R S).toLinearMap.comp D.liftKaehlerDifferential).liftBaseChange S).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S).symm.toLinearMap)

@[simp] theorem extend_algebraMap (D : Derivation k R R) (r : R) :
    extend (S := S) D (algebraMap R S r) = algebraMap R S (D r) := by
  change (((Algebra.ofId R S).toLinearMap.comp D.liftKaehlerDifferential).liftBaseChange S)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R S).symm
      (KaehlerDifferential.D k S (algebraMap R S r))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul, one_smul, LinearMap.comp_apply,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

end CycleQ2EtaleDerivation

namespace CycleQ2IncidenceEtaleParameter

open MvPolynomial Matrix HoldoutConstruction
  CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2PolynomialAffineSlice
  CycleQ2CompatibleEquationCoordinates CycleQ2SlicedCompatibleSystem
  CycleQ2IncidenceCompatibleGenericPoint CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceGenericPoint CycleQ2IncidenceTraceDirection
  CycleQ2IncidenceTraceDerivative

open CycleQ2IncidenceBasepointOpen (basepointPolynomial)

/-- All matrices are chosen from the already proved exact finite sequence.
This structure contains no geometric or cohomological existence input. -/
structure SeedSplitting where
  P : Matrix SquareIndex ColumnIndex ℂ
  Q : Matrix ColumnIndex SquareIndex ℂ
  V : Matrix ColumnIndex ComplementIndex ℂ
  W : Matrix ComplementIndex ColumnIndex ℂ
  T₀ : Matrix ComplementIndex RelationIndex ℂ
  B : Matrix FixedSexticParameters SquareIndex ℂ
  decomposition : Q * P + V * W = 1
  jacobian : P * fixedJacobian * B = 1
  complement : T₀ * literalRelations * V = 1

theorem seedSplitting_nonempty : Nonempty SeedSplitting := by
  obtain ⟨P, Q, V, W, T₀, B, hd, hj, hc, _, _⟩ :=
    CycleQ2LinearExactSequenceSplit.exists_matrix_split fixedJacobian literalRelations
      CycleQ2IncidenceCertifiedGenericPoint.literal_exactness
  exact ⟨⟨P, Q, V, W, T₀, B, hd, hj, hc⟩⟩

def splitting : SeedSplitting := Classical.choice seedSplitting_nonempty

def retainedEquations : SquareIndex → MvPolynomial SquareIndex TraceRing :=
  CycleQ2SlicedCompatibleSystem.equations centre (directions splitting.B)
    (splitting.P.map (C : ℂ →+* TraceRing)) CycleQ2IncidenceTraceFamily.equations

def retainedOpen : MvPolynomial SquareIndex TraceRing :=
  substitute centre (directions splitting.B)
      (totalOpen splitting.P splitting.B basepointPolynomial) *
    (relationA centre (directions splitting.B)
      (splitting.T₀.map (C : ℂ →+* TraceRing)) relations
      (splitting.V.map (C : ℂ →+* TraceRing))).det

/-- The inverse coordinate makes the required principal open part of the
literal polynomial presentation. -/
def augmentedEquations : Unit ⊕ SquareIndex →
    MvPolynomial (Unit ⊕ SquareIndex) TraceRing :=
  CycleQ2OpenSquareLifting.openSystem retainedEquations retainedOpen

abbrev ParameterAlgebra := SquareEtaleRing augmentedEquations

instance parameter_etale : Algebra.Etale TraceRing ParameterAlgebra :=
  square_system_jacobian_etale augmentedEquations

def augmentedCoordinate (j : Unit ⊕ SquareIndex) : ParameterAlgebra :=
  CycleQ2SquareAdicLifting.polynomialToEtale augmentedEquations (X j)

def sliceCoordinate (j : SquareIndex) : ParameterAlgebra :=
  augmentedCoordinate (Sum.inr j)

def incidencePoint : ParameterIndex → ParameterAlgebra :=
  pointValue (algebraMap TraceRing ParameterAlgebra) centre
    (directions splitting.B) sliceCoordinate

theorem augmented_evaluation (p : MvPolynomial (Unit ⊕ SquareIndex) TraceRing) :
    aeval augmentedCoordinate p =
      CycleQ2SquareAdicLifting.polynomialToEtale augmentedEquations p := by
  have h : aeval augmentedCoordinate =
      CycleQ2SquareAdicLifting.polynomialToEtale augmentedEquations := by
    ext j
    simp [augmentedCoordinate]
  exact AlgHom.congr_fun h p

theorem augmented_solution (j : Unit ⊕ SquareIndex) :
    aeval augmentedCoordinate (augmentedEquations j) = 0 := by
  rw [augmented_evaluation,
    CycleQ2SquareAdicLifting.polynomialToEtale_equation]

theorem retained_solution_and_open :
    (∀ j, aeval sliceCoordinate (retainedEquations j) = 0) ∧
      IsUnit (aeval sliceCoordinate retainedOpen) :=
  CycleQ2OpenSquareLifting.solution_on_open retainedEquations retainedOpen
    augmentedCoordinate augmented_solution

/-- The complementary relations recover all equations, not only the chosen
square subset. The same conclusion holds in the whole parameter algebra. -/
theorem incidence_solution_and_open :
    (∀ q, aeval incidencePoint (CycleQ2IncidenceTraceFamily.equations q) = 0) ∧
      IsUnit (aeval incidencePoint (totalOpen splitting.P splitting.B basepointPolynomial)) := by
  exact CycleQ2PointedCompatibleAffineLifting.affine_lift_semantics
    centre (directions splitting.B)
    (splitting.P.map (C : ℂ →+* TraceRing)) (splitting.Q.map (C : ℂ →+* TraceRing))
    (splitting.V.map (C : ℂ →+* TraceRing)) (splitting.W.map (C : ℂ →+* TraceRing))
    (splitting.T₀.map (C : ℂ →+* TraceRing)) relations
    CycleQ2IncidenceTraceFamily.equations (totalOpen splitting.P splitting.B basepointPolynomial)
    (mapped_decomposition (C : ℂ →+* TraceRing) splitting.P splitting.Q splitting.V
      splitting.W splitting.decomposition) CycleQ2IncidenceTraceFamily.relation_identity
    sliceCoordinate retained_solution_and_open.1 retained_solution_and_open.2

theorem incidence_isTracePoint :
    IsTracePoint splitting.P splitting.B basepointPolynomial sliceCoordinate :=
  isTracePoint_of_lift splitting.P splitting.B basepointPolynomial sliceCoordinate
    incidence_solution_and_open.1 incidence_solution_and_open.2

theorem incidence_sextic_fixed (j : FullInvariantIndex 6) :
    incidencePoint (Sum.inr (Sum.inl j)) =
      algebraMap TraceRing ParameterAlgebra (sexticParameter j) :=
  sextic_coordinate_fixed splitting.B sliceCoordinate j

/-! ## The actual complex seed belongs to this parameter scheme -/

private theorem full_seed_jacobian :
    splitting.P * seedJacobian ℂ (57 : ℂ) Complex.I *
      CycleQ2IncidenceSexticFamily.extendDirections splitting.B = 1 := by
  rw [Matrix.mul_assoc, CycleQ2IncidenceSexticFamily.jacobian_extendDirections,
    ← Matrix.mul_assoc]
  exact splitting.jacobian

private theorem mapped_seed_jacobian :
    (splitting.P.map (C : ℂ →+* TraceRing)).map seedEvaluation *
      jacobian seedEvaluation (seedEvaluation ∘ centre) CycleQ2IncidenceTraceFamily.equations *
      (directions splitting.B).map seedEvaluation = 1 := by
  rw [CycleQ2IncidenceTraceFamily.constantMatrix_seed,
    CycleQ2IncidenceTraceFamily.seed_jacobian, directions_seed]
  exact full_seed_jacobian

private theorem mapped_seed_complement :
    (splitting.T₀.map (C : ℂ →+* TraceRing)).map seedEvaluation *
      relations.map (eval₂Hom seedEvaluation (seedEvaluation ∘ centre)) *
      (splitting.V.map (C : ℂ →+* TraceRing)).map seedEvaluation = 1 := by
  rw [CycleQ2IncidenceTraceFamily.constantMatrix_seed,
    CycleQ2IncidenceTraceFamily.constantMatrix_seed, seed_relation]
  exact splitting.complement

theorem retained_seed_zero (j : SquareIndex) :
    eval₂Hom seedEvaluation (0 : SquareIndex → ℂ) (retainedEquations j) = 0 :=
  CycleQ2SlicedCompatibleSystem.seed_equations_zero seedEvaluation centre (directions splitting.B)
    (splitting.P.map (C : ℂ →+* TraceRing)) CycleQ2IncidenceTraceFamily.equations
    CycleQ2IncidenceTraceFamily.seed_zero j

theorem retained_seed_jacobian :
    Matrix.det (fun i j => eval₂Hom seedEvaluation (0 : SquareIndex → ℂ)
      (pderiv i (retainedEquations j))) = 1 :=
  seed_jacobian_det_one seedEvaluation centre (directions splitting.B)
    (splitting.P.map (C : ℂ →+* TraceRing)) CycleQ2IncidenceTraceFamily.equations
    mapped_seed_jacobian

theorem retainedOpen_seed :
    eval₂Hom seedEvaluation (0 : SquareIndex → ℂ) retainedOpen = 1 := by
  rw [retainedOpen, map_mul,
    eval_zero_substitute seedEvaluation centre (directions splitting.B),
    seed_relationA_det_one seedEvaluation centre (directions splitting.B)
      (splitting.T₀.map (C : ℂ →+* TraceRing)) relations
      (splitting.V.map (C : ℂ →+* TraceRing)) mapped_seed_complement,
    mul_one, totalOpen, map_mul,
    protectedOpen_seed splitting.P _ full_seed_jacobian, eval_coefficientMap]
  change 1 * CycleQ2IncidenceBasepointOpen.seedEvaluation basepointPolynomial = 1
  rw [CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial, one_mul]

def augmentedSeed : Unit ⊕ SquareIndex → ℂ :=
  CycleQ2OpenSquareLifting.extendedPoint (0 : SquareIndex → ℂ) 1

theorem augmented_seed_zero (j : Unit ⊕ SquareIndex) :
    eval₂Hom seedEvaluation augmentedSeed (augmentedEquations j) = 0 := by
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  exact CycleQ2OpenSquareLifting.openSystem_seed retainedEquations retainedOpen
    (0 : SquareIndex → ℂ) 1 retained_seed_zero (by rw [one_mul]; exact retainedOpen_seed) j

theorem augmented_seed_jacobian :
    IsUnit (Matrix.det (fun i j =>
      eval₂Hom seedEvaluation augmentedSeed (pderiv i (augmentedEquations j)))) := by
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  change IsUnit (Matrix.det (fun i j =>
    aeval (CycleQ2OpenSquareLifting.extendedPoint (0 : SquareIndex → ℂ) 1)
      (pderiv i (CycleQ2OpenSquareLifting.openSystem retainedEquations retainedOpen j))))
  rw [CycleQ2OpenSquareLifting.openSystem_jacobian_det]
  change IsUnit (eval₂Hom seedEvaluation (0 : SquareIndex → ℂ) retainedOpen *
    Matrix.det (fun i j => eval₂Hom seedEvaluation (0 : SquareIndex → ℂ)
      (pderiv i (retainedEquations j))))
  rw [retainedOpen_seed, retained_seed_jacobian, one_mul]
  exact isUnit_one

/-- This is a map out of the finite-presentation parameter algebra, not a
specialization map out of its fraction field. -/
def seedMap : ParameterAlgebra →+* ℂ := by
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  exact (squareSystemEtaleEval augmentedEquations augmentedSeed
    augmented_seed_zero augmented_seed_jacobian).toRingHom

@[simp] theorem seedMap_algebraMap (r : TraceRing) :
    seedMap (algebraMap TraceRing ParameterAlgebra r) = seedEvaluation r := by
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  exact (squareSystemEtaleEval augmentedEquations augmentedSeed
    augmented_seed_zero augmented_seed_jacobian).commutes r

@[simp] theorem seedMap_augmentedCoordinate (j : Unit ⊕ SquareIndex) :
    seedMap (augmentedCoordinate j) = augmentedSeed j := by
  letI : Algebra TraceRing ℂ := seedEvaluation.toAlgebra
  change squareSystemEtaleEval augmentedEquations augmentedSeed
      augmented_seed_zero augmented_seed_jacobian
      (algebraMap (SquareSystemRing augmentedEquations) ParameterAlgebra
        (Ideal.Quotient.mk _ (X j))) = augmentedSeed j
  simpa only [aeval_X] using
    CycleQ2PointedSquareGeneric.seedEtaleEval_polynomial augmentedEquations augmentedSeed
      augmented_seed_zero augmented_seed_jacobian (X j)

@[simp] theorem seedMap_sliceCoordinate (j : SquareIndex) :
    seedMap (sliceCoordinate j) = 0 := by
  rw [sliceCoordinate, seedMap_augmentedCoordinate]
  rfl

@[simp] theorem seedMap_incidencePoint (j : ParameterIndex) :
    seedMap (incidencePoint j) = seedPoint (57 : ℂ) Complex.I j := by
  simp only [incidencePoint, pointValue, map_add, map_sum, map_mul,
    seedMap_algebraMap, seedMap_sliceCoordinate, mul_zero, Finset.sum_const_zero, add_zero]
  exact congrFun centre_seed j

instance parameter_nontrivial : Nontrivial ParameterAlgebra := seedMap.domain_nontrivial

/-- The universal point carries a literal specialization to the same seed
used by the finite rank and nonzero trace calculation. -/
theorem incidence_isPointedTracePoint :
    IsPointedTracePoint splitting.P splitting.B basepointPolynomial sliceCoordinate := by
  refine ⟨incidence_isTracePoint, ?_⟩
  intro p hp
  have heval : seedMap (aeval incidencePoint p) =
      eval₂Hom seedEvaluation (seedEvaluation ∘ centre) p := by
    change seedMap (eval₂Hom (algebraMap TraceRing ParameterAlgebra) incidencePoint p) = _
    rw [map_eval₂Hom]
    have hcoeff : seedMap.comp (algebraMap TraceRing ParameterAlgebra) = seedEvaluation := by
      apply RingHom.ext
      intro r
      exact seedMap_algebraMap r
    have hpoint : seedMap ∘ incidencePoint = seedEvaluation ∘ centre := by
      rw [centre_seed]
      funext j
      exact seedMap_incidencePoint j
    change eval₂Hom (seedMap.comp (algebraMap TraceRing ParameterAlgebra))
      (seedMap ∘ incidencePoint) p = _
    rw [hcoeff, hpoint]
  change aeval incidencePoint p = 0 at hp
  rw [← heval, hp, map_zero]

/-! ## A regular time vector field with fixed sextic coefficients -/

def timeDerivation : Derivation ℂ ParameterAlgebra ParameterAlgebra :=
  CycleQ2EtaleDerivation.extend (pderiv (Sum.inl ()) : Derivation ℂ TraceRing TraceRing)

theorem timeDerivation_polynomial (p : TraceRing) :
    timeDerivation (algebraMap TraceRing ParameterAlgebra p) =
      algebraMap TraceRing ParameterAlgebra (pderiv (Sum.inl ()) p) :=
  CycleQ2EtaleDerivation.extend_algebraMap _ p

theorem timeDerivation_traceParameter :
    timeDerivation (algebraMap TraceRing ParameterAlgebra traceParameter) = 1 := by
  rw [timeDerivation_polynomial, traceParameter, pderiv_X_self, map_one]

theorem timeDerivation_sexticParameter (j : FullInvariantIndex 6) :
    timeDerivation (algebraMap TraceRing ParameterAlgebra (sexticParameter j)) = 0 := by
  rw [timeDerivation_polynomial, sexticParameter,
    pderiv_X_of_ne (by simp), map_zero]

theorem incidence_sextic_derivative_zero (j : FullInvariantIndex 6) :
    timeDerivation (incidencePoint (Sum.inr (Sum.inl j))) = 0 := by
  rw [incidence_sextic_fixed, timeDerivation_sexticParameter]

theorem incidence_trace_derivative_isUnit :
    IsUnit ((algebraMap ℂ ParameterAlgebra ∘ traceWeights) ⬝ᵥ
      (fun j => timeDerivation (incidencePoint j))) :=
  actual_derivative_trace_isUnit timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter splitting.P splitting.B sliceCoordinate
    incidence_isTracePoint.1 incidence_isTracePoint.2.1

theorem incidence_cubic_derivative_not_rescaling :
    ¬ ∃ a : ParameterAlgebra, ∀ j : FullInvariantIndex 3,
      timeDerivation (incidencePoint (Sum.inl j)) = a * incidencePoint (Sum.inl j) :=
  actual_cubic_derivative_not_rescaling timeDerivation timeDerivation_traceParameter
    timeDerivation_sexticParameter splitting.P splitting.B sliceCoordinate
    incidence_isTracePoint.1 incidence_isTracePoint.2.1

/-! ## The actual affine parameter scheme -/

open CategoryTheory AlgebraicGeometry

def parameterScheme : Scheme := Spec (CommRingCat.of ParameterAlgebra)
def timeAndSexticBase : Scheme := Spec (CommRingCat.of TraceRing)

def parameterToBase : parameterScheme ⟶ timeAndSexticBase :=
  Spec.map (CommRingCat.ofHom (algebraMap TraceRing ParameterAlgebra))

theorem parameterToBase_etale : Etale parameterToBase := by
  apply (HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Etale)).mpr
  exact RingHom.etale_algebraMap.mpr parameter_etale

def seedPointMorphism : Spec (CommRingCat.of ℂ) ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom seedMap)

theorem seedPointMorphism_overBase :
    seedPointMorphism ≫ parameterToBase =
      Spec.map (CommRingCat.ofHom seedEvaluation) := by
  rw [seedPointMorphism, parameterToBase, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact seedMap_algebraMap r

end CycleQ2IncidenceEtaleParameter

#print axioms CycleQ2IncidenceEtaleParameter.incidence_isPointedTracePoint
#print axioms CycleQ2IncidenceEtaleParameter.incidence_cubic_derivative_not_rescaling
#print axioms CycleQ2IncidenceEtaleParameter.parameterToBase_etale
#print axioms CycleQ2IncidenceEtaleParameter.seedPointMorphism_overBase

end
