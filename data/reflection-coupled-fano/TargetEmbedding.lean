import Proposal.CoupledDomain
import Proposal.EndpointDomain
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting

/-!
Dominance of the anchored quartic family and the resulting finite extension
of function fields.  The transverse coordinate may have arbitrary positive
degree: its zero constant term and nonvanishing suffice for injectivity.
The finite-type hypothesis in the transcendence-degree argument is explicit.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace ReflectionCoupledFano.Target

open Polynomial HoldoutConstruction

abbrev Ring (c : ℂ) := AdjoinRoot (polynomial c 3 1)
abbrev Field (c : ℂ) := FractionRing (Ring c)

instance ring_commRing (c : ℂ) : CommRing (Ring c) := inferInstance

instance ring_isDomain (c : ℂ) : IsDomain (Ring c) :=
  weighted_polynomial_adjoinRoot_isDomain c

theorem of_injective (c : ℂ) :
    Function.Injective (AdjoinRoot.of (polynomial c 3 1)) := by
  apply AdjoinRoot.of.injective_of_degree_ne_zero
  exact ne_of_gt ((polynomial_monic c 3 1).degree_pos_of_not_isUnit
    (polynomial_irreducible c (-1) 3 1 (by norm_num)).not_isUnit)

instance ring_charZero (c : ℂ) : CharZero (Ring c) :=
  charZero_of_injective_ringHom
    (f := (AdjoinRoot.of (polynomial c 3 1)).comp
      (MvPolynomial.C : ℂ →+* MvPolynomial (Fin 5) ℂ))
    ((of_injective c).comp (MvPolynomial.C_injective (Fin 5) ℂ))

noncomputable instance field_field (c : ℂ) : _root_.Field (Field c) := inferInstance
instance field_charZero (c : ℂ) : CharZero (Field c) := inferInstance

def projection (c : ℂ) : MvPolynomial (Fin 6) ℂ →+* Ring c :=
  (AdjoinRoot.mk (polynomial c 3 1)).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom

theorem projection_surjective (c : ℂ) : Function.Surjective (projection c) :=
  (AdjoinRoot.mk_surjective (g := polynomial c 3 1)).comp
    (MvPolynomial.finSuccEquiv ℂ 5).surjective

theorem projection_kernel (c : ℂ) (p : MvPolynomial (Fin 6) ℂ) :
    projection c p = 0 ↔ hypersurface c 3 1 ∣ p := by
  change AdjoinRoot.mk (polynomial c 3 1) (MvPolynomial.finSuccEquiv ℂ 5 p) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero, ← hypersurface_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)

def residueMap (c : ℂ) : MvPolynomial (Fin 6) ℂ →+* Field c :=
  (algebraMap (Ring c) (Field c)).comp (projection c)

@[simp] theorem residueMap_C (c r : ℂ) :
    residueMap c (MvPolynomial.C r) = algebraMap ℂ (Field c) r := by
  change algebraMap (Ring c) (Field c) (AdjoinRoot.mk (polynomial c 3 1)
    (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C r))) = _
  rw [show MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.C r) =
    C (MvPolynomial.C r) from (MvPolynomial.finSuccEquiv ℂ 5).commutes r]
  rfl

@[simp] theorem residueMap_X_zero (c : ℂ) :
    residueMap c (MvPolynomial.X (R := ℂ) (0 : Fin 6)) =
      algebraMap (Ring c) (Field c) (AdjoinRoot.root (polynomial c 3 1)) := by
  simp [residueMap, projection, MvPolynomial.finSuccEquiv_apply]

@[simp] theorem residueMap_X_succ (c : ℂ) (i : Fin 5) :
    residueMap c (MvPolynomial.X (R := ℂ) i.succ) =
      algebraMap (Ring c) (Field c)
        (AdjoinRoot.of (polynomial c 3 1) (MvPolynomial.X i)) := by
  change algebraMap (Ring c) (Field c) (AdjoinRoot.mk (polynomial c 3 1)
    (MvPolynomial.finSuccEquiv ℂ 5 (MvPolynomial.X i.succ))) = _
  rw [MvPolynomial.finSuccEquiv_X_succ]
  rfl

theorem residueMap_kernel (c : ℂ) (p : MvPolynomial (Fin 6) ℂ) :
    residueMap c p = 0 ↔ hypersurface c 3 1 ∣ p :=
  residue_fractionMap_kernel (projection c) (hypersurface c 3 1) (projection_kernel c) p

theorem normal_ne_zero (c : ℂ) :
    residueMap c (MvPolynomial.pderiv 0 (hypersurface c 3 1)) ≠ 0 := by
  intro h
  exact hypersurface_not_dvd_pderiv_zero c 3 1 (by decide)
    ((residueMap_kernel c _).mp h)

theorem field_trdeg (c : ℂ) : Algebra.trdeg ℂ (Field c) = 5 := by
  apply monic_hypersurface_field_trdeg (polynomial c 3 1) (polynomial_monic c 3 1)
  exact ne_of_gt ((polynomial_monic c 3 1).degree_pos_of_not_isUnit
    (polynomial_irreducible c (-1) 3 1 (by norm_num)).not_isUnit)

section Family

attribute [local irreducible] Endpoint.polynomial polynomial

variable (c : ℂ) (E : Type) [_root_.Field E]
variable [Algebra (Endpoint.Field c) E] [Algebra ℂ E]
variable [IsScalarTower ℂ (Endpoint.Field c) E]

set_option backward.isDefEq.respectTransparency true in
/-- Only these four facts about the constructed curve are used in dominance.
The endpoint is generic on the transverse section, while the first moving
coordinate has zero constant coefficient and is not the zero polynomial. -/
structure AnchoredFamily where
  curve : Fin 6 → E[X]
  constant : ∀ i, (curve i).coeff 0 =
    algebraMap (Endpoint.Field c) E
      (algebraMap (Endpoint.Ring c) (Endpoint.Field c) (Endpoint.point c i))
  equation : H (C (algebraMap ℂ E c)) curve = 0
  moves : curve 1 ≠ 0

namespace AnchoredFamily

variable {c E}
variable (a : AnchoredFamily c E)

def endpointCoefficientEmbedding (_a : AnchoredFamily c E) : MvPolynomial (Fin 4) ℂ →+* E :=
  (algebraMap (Endpoint.Field c) E).comp
    ((algebraMap (Endpoint.Ring c) (Endpoint.Field c)).comp
      (AdjoinRoot.of (Endpoint.polynomial c)))

theorem endpointCoefficientEmbedding_injective :
    Function.Injective (a.endpointCoefficientEmbedding) :=
  (algebraMap (Endpoint.Field c) E).injective.comp
    ((IsFractionRing.injective (Endpoint.Ring c) (Endpoint.Field c)).comp
      (Endpoint.of_injective c))

def remainingCoefficientMap : MvPolynomial (Fin 4) ℂ →+* E[X] :=
  MvPolynomial.eval₂Hom (C.comp (algebraMap ℂ E))
    (fun i => a.curve i.succ.succ)

theorem remainingCoefficientMap_constant :
    Polynomial.constantCoeff.comp a.remainingCoefficientMap =
      a.endpointCoefficientEmbedding := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, remainingCoefficientMap,
      MvPolynomial.eval₂Hom_C, Polynomial.coeff_C_zero,
      Polynomial.constantCoeff_apply, endpointCoefficientEmbedding]
    exact IsScalarTower.algebraMap_apply ℂ (Endpoint.Field c) E r
  · intro i
    simp only [RingHom.comp_apply, remainingCoefficientMap,
      MvPolynomial.eval₂Hom_X', Polynomial.constantCoeff_apply,
      endpointCoefficientEmbedding]
    rw [a.constant]
    congr 2
    change Endpoint.point c i.succ.succ = Endpoint.parameter c i
    fin_cases i <;> rfl

def coefficientMap : MvPolynomial (Fin 5) ℂ →+* E[X] :=
  (Polynomial.eval₂RingHom a.remainingCoefficientMap (a.curve 1)).comp
    (MvPolynomial.finSuccEquiv ℂ 4).toRingHom

theorem curve_one_constant : (a.curve 1).coeff 0 = 0 := by
  rw [a.constant]
  simp [Endpoint.point]

theorem coefficientMap_injective : Function.Injective a.coefficientMap := by
  have hc : Function.Injective (Polynomial.constantCoeff.comp a.remainingCoefficientMap) := by
    rw [a.remainingCoefficientMap_constant]
    exact a.endpointCoefficientEmbedding_injective
  exact (anchored_polynomial_family_injective a.remainingCoefficientMap hc
    (a.curve 1) a.curve_one_constant a.moves).comp
    (MvPolynomial.finSuccEquiv ℂ 4).injective

@[simp] theorem coefficientMap_C (r : ℂ) :
    a.coefficientMap (MvPolynomial.C r) = C (algebraMap ℂ E r) := by
  simp [coefficientMap, MvPolynomial.finSuccEquiv_apply, remainingCoefficientMap]

@[simp] theorem coefficientMap_X (i : Fin 5) :
    a.coefficientMap (MvPolynomial.X i) = a.curve i.succ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [coefficientMap, MvPolynomial.finSuccEquiv_X_zero]
  · change (Polynomial.eval₂RingHom a.remainingCoefficientMap (a.curve 1))
      (MvPolynomial.finSuccEquiv ℂ 4 (MvPolynomial.X j.succ)) = _
    rw [MvPolynomial.finSuccEquiv_X_succ]
    change Polynomial.eval₂ a.remainingCoefficientMap (a.curve 1)
      (Polynomial.C (MvPolynomial.X j)) = _
    rw [Polynomial.eval₂_C]
    simp [remainingCoefficientMap]

abbrev FunctionField := FractionRing E[X]

def fieldCoordinate (i : Fin 6) : FunctionField (E := E) :=
  algebraMap E[X] (FunctionField (E := E)) (a.curve i)

def fieldEval : MvPolynomial (Fin 6) ℂ →+* FunctionField (E := E) :=
  MvPolynomial.eval₂Hom (algebraMap ℂ (FunctionField (E := E))) a.fieldCoordinate

def fieldCoefficientMap : MvPolynomial (Fin 5) ℂ →+* FunctionField (E := E) :=
  (algebraMap E[X] (FunctionField (E := E))).comp a.coefficientMap

theorem fieldCoefficientMap_injective : Function.Injective a.fieldCoefficientMap :=
  (IsFractionRing.injective E[X] (FunctionField (E := E))).comp a.coefficientMap_injective

@[simp] theorem fieldCoefficientMap_C (r : ℂ) :
    a.fieldCoefficientMap (MvPolynomial.C r) =
      algebraMap ℂ (FunctionField (E := E)) r := by
  rw [fieldCoefficientMap, RingHom.comp_apply, coefficientMap_C]
  rfl

@[simp] theorem fieldCoefficientMap_X (i : Fin 5) :
    a.fieldCoefficientMap (MvPolynomial.X i) = a.fieldCoordinate i.succ := by
  rw [fieldCoefficientMap, RingHom.comp_apply, coefficientMap_X]
  rfl

theorem polynomial_root : (polynomial c 3 1).eval₂ a.coefficientMap (a.curve 0) = 0 := by
  have h := a.equation
  simp only [polynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    map_add, map_mul, map_pow, map_ofNat, coefficientMap_C, coefficientMap_X,
    show (0 : Fin 5).succ = (1 : Fin 6) by decide,
    show (1 : Fin 5).succ = (2 : Fin 6) by decide,
    show (2 : Fin 5).succ = (3 : Fin 6) by decide,
    show (3 : Fin 5).succ = (4 : Fin 6) by decide,
    show (4 : Fin 5).succ = (5 : Fin 6) by decide, pow_one]
  unfold H at h
  linear_combination h

theorem field_root :
    (polynomial c 3 1).eval₂ a.fieldCoefficientMap (a.fieldCoordinate 0) = 0 := by
  have h := congrArg (algebraMap E[X] (FunctionField (E := E))) a.polynomial_root
  rw [map_zero, Polynomial.hom_eval₂] at h
  exact h

def ringMap : Ring c →+* FunctionField (E := E) :=
  AdjoinRoot.lift (f := polynomial c 3 1) a.fieldCoefficientMap
    (a.fieldCoordinate 0) a.field_root

theorem ringMap_injective : Function.Injective a.ringMap :=
  monic_root_embedding_injective (polynomial c 3 1) (polynomial_monic c 3 1)
    (polynomial_irreducible c (-1) 3 1 (by norm_num)) a.fieldCoefficientMap
    a.fieldCoefficientMap_injective (a.fieldCoordinate 0) a.field_root

def fieldMap : Field c →+* FunctionField (E := E) :=
  IsFractionRing.lift a.ringMap_injective

@[simp] theorem fieldMap_ring (r : Ring c) :
    a.fieldMap (algebraMap (Ring c) (Field c) r) = a.ringMap r :=
  IsFractionRing.lift_algebraMap a.ringMap_injective r

@[simp] theorem fieldMap_base (r : ℂ) :
    a.fieldMap (algebraMap ℂ (Field c) r) = algebraMap ℂ (FunctionField (E := E)) r := by
  change a.fieldMap (algebraMap (Ring c) (Field c)
    (AdjoinRoot.of (polynomial c 3 1) (MvPolynomial.C r))) = _
  rw [fieldMap_ring]
  change AdjoinRoot.lift _ _ _
    (AdjoinRoot.of (polynomial c 3 1) (MvPolynomial.C r)) = _
  rw [AdjoinRoot.lift_of, fieldCoefficientMap_C]

@[instance_reducible] def targetAlgebra :
    Algebra (Field c) (FunctionField (E := E)) := a.fieldMap.toAlgebra

theorem baseTower : letI := a.targetAlgebra;
    IsScalarTower ℂ (Field c) (FunctionField (E := E)) := by
  letI := a.targetAlgebra
  exact IsScalarTower.of_algebraMap_eq (R := ℂ) (S := Field c)
    (A := FunctionField (E := E)) (fun r => (a.fieldMap_base r).symm)

theorem fieldMap_coordinate (i : Fin 6) :
    a.fieldMap (residueMap c (MvPolynomial.X i)) = a.fieldCoordinate i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [residueMap_X_zero, fieldMap_ring]
    exact AdjoinRoot.lift_root a.field_root
  · rw [residueMap_X_succ, fieldMap_ring]
    change AdjoinRoot.lift _ _ _
      (AdjoinRoot.of (polynomial c 3 1) (MvPolynomial.X j)) = _
    rw [AdjoinRoot.lift_of, fieldCoefficientMap_X]

theorem fieldMap_residue (p : MvPolynomial (Fin 6) ℂ) :
    a.fieldMap (residueMap c p) = a.fieldEval p := by
  have h : a.fieldMap.comp (residueMap c) = a.fieldEval := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [fieldEval]
    · intro i
      simp only [RingHom.comp_apply, fieldMap_coordinate,
        fieldEval, MvPolynomial.eval₂Hom_X']
  exact congrArg (fun φ : MvPolynomial (Fin 6) ℂ →+* FunctionField (E := E) => φ p) h

theorem functionField_trdeg [Module.Finite (Endpoint.Field c) E] :
    Algebra.trdeg ℂ (FunctionField (E := E)) = 5 := by
  rw [polynomial_fractionRing_trdeg ℂ (Endpoint.Field c) E, Endpoint.field_trdeg]
  norm_num

theorem functionField_finite [Module.Finite (Endpoint.Field c) E] :
    letI := a.targetAlgebra;
    Module.Finite (Field c) (FunctionField (E := E)) := by
  letI := a.targetAlgebra
  letI := a.baseTower
  letI : Algebra.EssFiniteType ℂ (Endpoint.Field c) :=
    monic_hypersurface_field_essFiniteType (Endpoint.polynomial c)
  letI : Algebra.EssFiniteType ℂ (FunctionField (E := E)) :=
    polynomial_fractionRing_essFiniteType ℂ (Endpoint.Field c) E
  apply finite_of_same_finite_trdeg (K := ℂ)
  · rw [field_trdeg]
    exact Cardinal.natCast_lt_aleph0
  · rw [field_trdeg, functionField_trdeg (c := c) (E := E)]

end AnchoredFamily
end Family
end ReflectionCoupledFano.Target

#print axioms ReflectionCoupledFano.Target.AnchoredFamily.ringMap_injective
#print axioms ReflectionCoupledFano.Target.AnchoredFamily.fieldMap_residue
#print axioms ReflectionCoupledFano.Target.AnchoredFamily.functionField_finite
