import Proposal.LineSeed
import Proposal.LineFamily
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting

/-! A finite algebraic family over the generic endpoint, lifted from rbajaj5's line.
The nonsingular-incidence/flatness argument is due to fqlx's reflection-coupled-fano proof. -/
noncomputable section
namespace CyclicTriple.Lifting
open Polynomial HoldoutConstruction

abbrev Base := Endpoint.Ring coupling
abbrev GenericEndpoint := Endpoint.Field coupling

def seedBaseMap : Base →+* ℂ :=
  AdjoinRoot.lift (f := Endpoint.polynomial coupling)
    (MvPolynomial.eval₂Hom (RingHom.id ℂ) ![0,1,0,0]) Complex.I (by
      have hi6 : Complex.I^6 = -1 := by
        rw [show (6 : ℕ) = 2*3 by decide, pow_mul, Complex.I_sq]
        norm_num
      simp only [Endpoint.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_mul, map_add, map_mul, map_pow,
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C, RingHom.id_apply]
      norm_num [hi6, show (![0,1,0,0] : Fin 4 → ℂ) 2 = 0 from rfl,
        show (![0,1,0,0] : Fin 4 → ℂ) 3 = 0 from rfl, coupling])

@[simp] theorem seedBaseMap_coefficient (r : ℂ) :
    seedBaseMap (algebraMap ℂ Base r) = r := by
  change seedBaseMap (AdjoinRoot.of _ (MvPolynomial.C r)) = r
  simp [seedBaseMap]

@[simp] theorem seedBaseMap_point (i : Fin 6) :
    seedBaseMap (Endpoint.point coupling i) = seedEndpoint i := by
  fin_cases i <;> simp [Endpoint.point, Endpoint.root, Endpoint.parameter,
    seedBaseMap, seedEndpoint]

def familyEquations : Index → MvPolynomial Index Base :=
  equations (algebraMap ℂ Base coupling) (Endpoint.point coupling)

abbrev Incidence := SquareGenericAlgebra GenericEndpoint familyEquations

attribute [local irreducible] Endpoint.polynomial familyEquations coupling

@[simp] theorem equations_specialize (i : Index) :
    MvPolynomial.map seedBaseMap (familyEquations i) =
      equations coupling seedEndpoint i := by
  rw [familyEquations, equations_map]
  simp only [seedBaseMap_coefficient, seedBaseMap_point]

theorem seed_solution (i : Index) :
    MvPolynomial.eval₂Hom seedBaseMap seedCoefficients (familyEquations i) = 0 := by
  have h := seedEquations i
  rw [← equations_specialize, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp] at h
  exact h

theorem seed_jacobian :
    IsUnit (Matrix.det (fun i j : Index => MvPolynomial.eval₂Hom seedBaseMap
      seedCoefficients (MvPolynomial.pderiv i (familyEquations j)))) := by
  have hm : (fun i j : Index => MvPolynomial.eval₂Hom seedBaseMap
      seedCoefficients (MvPolynomial.pderiv i (familyEquations j))) =
      Matrix.transpose (fun i j : Index => MvPolynomial.eval₂Hom (RingHom.id ℂ)
        seedCoefficients (MvPolynomial.pderiv j (equations coupling seedEndpoint i))) := by
    funext i j
    change _ = MvPolynomial.eval₂Hom (RingHom.id ℂ) seedCoefficients
      (MvPolynomial.pderiv i (equations coupling seedEndpoint j))
    rw [← equations_specialize, MvPolynomial.pderiv_map,
      MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  rw [hm]
  exact (congrArg IsUnit (Matrix.det_transpose _)).mpr seedJacobian_unit

theorem exists_field :
    ∃ I : Ideal Incidence, I.IsMaximal ∧ Module.Finite GenericEndpoint (Incidence ⧸ I) ∧
      Algebra.IsSeparable GenericEndpoint (Incidence ⧸ I) ∧
      (∀ i, MvPolynomial.aeval (squareGenericCoordinates familyEquations I)
        (familyEquations i) = 0) ∧
      IsUnit (Matrix.det (fun i j => MvPolynomial.aeval
        (squareGenericCoordinates familyEquations I)
          (MvPolynomial.pderiv i (familyEquations j)))) := by
  letI : Algebra Base ℂ := seedBaseMap.toAlgebra
  exact ReflectionCoupledFano.square_system_generic_lift familyEquations seedCoefficients
    seed_solution seed_jacobian (IsFractionRing.injective Base GenericEndpoint)

abbrev CoefficientField (I : Ideal Incidence) := Incidence ⧸ I
instance coefficientField_commRing (I : Ideal Incidence) : CommRing (CoefficientField I) := inferInstance
noncomputable instance coefficientField_field (I : Ideal Incidence) [I.IsMaximal] :
    Field (CoefficientField I) := Ideal.Quotient.field I
instance coefficientField_charZero (I : Ideal Incidence) [I.IsMaximal] :
    CharZero (CoefficientField I) :=
  charZero_of_injective_ringHom (f := algebraMap GenericEndpoint (CoefficientField I))
    (algebraMap GenericEndpoint (CoefficientField I)).injective

def coefficients (I : Ideal Incidence) : Index → CoefficientField I :=
  squareGenericCoordinates familyEquations I

def sourceMap (I : Ideal Incidence) : Base →+* CoefficientField I :=
  algebraMap Base (CoefficientField I)

@[simp] theorem sourceMap_coefficient (I : Ideal Incidence) (r : ℂ) :
    sourceMap I (algebraMap ℂ Base r) = algebraMap ℂ (CoefficientField I) r :=
  (IsScalarTower.algebraMap_apply ℂ Base (CoefficientField I) r).symm

@[simp] theorem sourceMap_point (I : Ideal Incidence) [I.IsMaximal] (i : Fin 6) :
    sourceMap I (Endpoint.point coupling i) =
      familyEndpoint coupling (CoefficientField I) i :=
  IsScalarTower.algebraMap_apply Base GenericEndpoint (CoefficientField I) _

theorem equations_map_to_field (I : Ideal Incidence) [I.IsMaximal] (i : Index) :
    MvPolynomial.map (sourceMap I) (familyEquations i) =
      equations (algebraMap ℂ (CoefficientField I) coupling)
        (familyEndpoint coupling (CoefficientField I)) i := by
  have he : familyEquations i =
      equations (algebraMap ℂ Base coupling) (Endpoint.point coupling) i := by
    unfold familyEquations
    rfl
  rw [he, equations_map, sourceMap_coefficient]
  congr 1

theorem coefficients_equations (I : Ideal Incidence) [I.IsMaximal] (i : Index) :
    MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
      (equations (algebraMap ℂ (CoefficientField I) coupling)
        (familyEndpoint coupling (CoefficientField I)) i) = 0 := by
  rw [← equations_map_to_field, MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
  exact squareGeneric_solution familyEquations I i

theorem coefficients_jacobian (I : Ideal Incidence) [I.IsMaximal] :
    IsUnit (Matrix.det (fun i j : Index =>
      MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
        (MvPolynomial.pderiv j
          (equations (algebraMap ℂ (CoefficientField I) coupling)
            (familyEndpoint coupling (CoefficientField I)) i)))) := by
  have he (i j : Index) :
      MvPolynomial.eval₂Hom (RingHom.id (CoefficientField I)) (coefficients I)
        (MvPolynomial.pderiv j
          (equations (algebraMap ℂ (CoefficientField I) coupling)
            (familyEndpoint coupling (CoefficientField I)) i)) =
      MvPolynomial.aeval (coefficients I) (MvPolynomial.pderiv j (familyEquations i)) := by
    rw [← equations_map_to_field, MvPolynomial.pderiv_map,
      MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
    rfl
  simp_rw [he]
  rw [show (fun i j => MvPolynomial.aeval (coefficients I) (MvPolynomial.pderiv j (familyEquations i))) =
    Matrix.transpose (fun i j => MvPolynomial.aeval (coefficients I) (MvPolynomial.pderiv i (familyEquations j))) from rfl]
  exact (congrArg IsUnit (Matrix.det_transpose _)).mpr (squareGeneric_jacobian familyEquations I)

def family (I : Ideal Incidence) [I.IsMaximal] : LineFamily coupling (CoefficientField I) where
  coefficients := coefficients I
  equations := coefficients_equations I
  jacobian := coefficients_jacobian I

end CyclicTriple.Lifting
#print axioms CyclicTriple.Lifting.exists_field
