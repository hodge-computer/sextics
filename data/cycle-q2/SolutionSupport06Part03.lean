import Proposal.SolutionSupport06Part02

/-! Components extracted from SolutionSupport06.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

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


