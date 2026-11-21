import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Proposal.GeometricSeedCubicGradient
import Proposal.IncidenceBasepointCharts
import Proposal.SegreDetectorCorrelation
import Proposal.SegreGlobalFactorRanks

/-!
# The detected tangent and trace at the generic incidence point
-/

set_option Elab.async false

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

/- Component: continuation_3/cylinder_bridge/IncidenceCertifiedGenericPoint.lean -/
section
/-! The proved exact ranks discharge the last finite-linear input of the
actual generic incidence and trace-preserving family.  The basepoint open
is included using its proved seed value.  No cylinder or primitive claim
is made by these algebraic existence statements. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace CycleQ2IncidenceCertifiedGenericPoint
open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceCompatibleGenericPoint CycleQ2IncidenceFiniteGenericSolution
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceFieldDerivation
  CycleQ2IncidenceTraceGenericPoint
open CycleQ2IncidenceBasepointOpen (basepointPolynomial)

theorem literal_exactness :
    LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations) := by
  rw [fixedJacobian_eq_ordered,literalRelations_eq]
  exact CycleQ2SegreExactRanks.fixed_range_eq_relation_kernel

theorem finite_generic_incidence :
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
        IsGenericIncidence h δ :=
  finite_generic_incidence_of_exactness literal_exactness

theorem finite_trace_point :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B basepointPolynomial)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I),
        IsTracePoint P B basepointPolynomial z := by
  apply finite_trace_point_of_exactness literal_exactness basepointPolynomial
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

theorem finite_pointed_trace_point :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B basepointPolynomial)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I),
        IsPointedTracePoint P B basepointPolynomial z := by
  apply finite_pointed_trace_point_of_exactness literal_exactness basepointPolynomial
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

end CycleQ2IncidenceCertifiedGenericPoint

#print axioms CycleQ2IncidenceCertifiedGenericPoint.literal_exactness
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_generic_incidence
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_trace_point

#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_pointed_trace_point
end
end

/- Component: continuation_3/cylinder_bridge/IncidenceTraceGeometry.lean -/
section
/-! The finite trace family, restricted to the proved basepoint open,
has the actual cofactor incidence, a rank-one localized global image, and
regular principal equations for the literal generic-column section ideal.
No line bundle or regular section is an input hypothesis. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceGeometry
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice CycleQ2PolynomialImplicitTrace
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDerivative CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceImageLine CycleQ2SegreGenericSection
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)
open CycleQ2IncidenceBasepointOpen (basepointPolynomial curveCoordinate curveMatrix)

theorem basepoint_seed : eval (seedPoint (57:ℂ) Complex.I) basepointPolynomial=1 := by
  change CycleQ2IncidenceBasepointOpen.seedEvaluation basepointPolynomial=1
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

variable {S : Type} [CommRing S] [Algebra TraceRing S]
  [Algebra ℂ S] [IsScalarTower ℂ TraceRing S]

abbrev tracePointValue (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) : ParameterIndex → S :=
  pointValue (algebraMap TraceRing S) centre (directions B) z

theorem tracePoint_original_equations
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) (q : ColumnIndex) :
    aeval (tracePointValue B z) ((presentation ℂ 57).equation q)=0 := by
  rw [←eval_coefficient_map]
  exact hz.1 q

theorem tracePoint_leading_unit
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) :
    IsUnit (aeval (tracePointValue B z) (leadingProduct ℂ)) := by
  exact (protectedOpen_components P
    (CycleQ2IncidenceSexticFamily.extendDirections B) (tracePointValue B z) hz.2.1).1

theorem tracePoint_extra_unit
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) :
    IsUnit (aeval (tracePointValue B z) c) := by
  have h := hz.2.2.1
  rwa [eval_coefficient_map] at h

theorem tracePoint_localized_image_line [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B basepointPolynomial z)
    (p : Ideal (PointSurface (tracePointValue B z))) [p.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap (tracePointValue B z)) j∉p) :
    Nonempty (PointPrimeRing (tracePointValue B z) p ≃ₗ[PointPrimeRing (tracePointValue B z) p]
      (LinearMap.range (curveMatrix (pointMap (tracePointValue B z))).mulVecLin).localized'
        (PointPrimeRing (tracePointValue B z) p) p.primeCompl
        (CycleQ2MatrixImageLocalization.vectorMap
          (R := PointSurface (tracePointValue B z))
          (S := PointPrimeRing (tracePointValue B z) p))) :=
  localized_global_image_line (tracePointValue B z)
    (tracePoint_original_equations P B _ z hz) (tracePoint_leading_unit P B _ z hz)
    (tracePoint_extra_unit P B _ z hz) p hx

/-- The chosen generic-section ideal is locally principal with a proved
regular generator at every relevant prime, over the polynomial ring in
the three independent section coefficients. -/
theorem tracePoint_regular_section [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B basepointPolynomial z)
    (p : Ideal (PointSurface (tracePointValue B z))) [p.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap (tracePointValue B z)) j∉p) :
    ∃ q : CycleQ2SegreCech.Chart,
      sectionIdeal (primeMatrix (tracePointValue B z) p)=
        Ideal.span {localEquation (primeMatrix (tracePointValue B z) p) q} ∧
      IsRegular (localEquation (primeMatrix (tracePointValue B z) p) q) := by
  let y := tracePointValue B z
  have hb := tracePoint_extra_unit P B _ z hz
  obtain ⟨i,j,hij⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap y) hb p hx
  have hu : IsUnit (primeMatrix y p i j) :=
    IsLocalization.map_units (M := p.primeCompl) (PointPrimeRing y p)
      ⟨curveMatrix (pointMap y) i j,hij⟩
  have hcof := @CycleQ2SegreCech.cofactors_map_zero
    (PointSurface y) (inferInstance : CommRing (PointSurface y))
    (PointPrimeRing y p) (inferInstance : CommRing (PointPrimeRing y p))
    (algebraMap (PointSurface y) (PointPrimeRing y p)) (curveMatrix (pointMap y))
    (curveMatrix_cofactors y (tracePoint_original_equations P B _ z hz)
      (tracePoint_leading_unit P B _ z hz))
  obtain ⟨u,hu'⟩ := hu
  exact ⟨(i,j),sectionIdeal_principal (primeMatrix y p) hcof (i,j) u hu',
    localEquation_regular (primeMatrix y p) (i,j) ⟨u,hu'⟩⟩

end CycleQ2IncidenceTraceGeometry

#print axioms CycleQ2IncidenceTraceGeometry.tracePoint_localized_image_line
#print axioms CycleQ2IncidenceTraceGeometry.tracePoint_regular_section
end
end
