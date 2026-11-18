import Proposal.EndpointDomain
import Proposal.QuarticNormal
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

/-!
The exact quartic family over a finite extension of the generic transverse
endpoint field. The existence of the coefficient field and its point is a
separate arithmetic lifting theorem; the structure below records precisely
the resulting equations, invertible Jacobian, and transversality.
-/

noncomputable section
namespace ReflectionCoupledFano
open Polynomial HoldoutConstruction

attribute [local irreducible] Endpoint.polynomial

variable {R : Type*} [Field R] [CharZero R]
variable (c : R) (E : Type*) [Field E]
variable [Algebra R E] [Algebra (Endpoint.Field c) E]
variable [IsScalarTower R (Endpoint.Field c) E]

def familyEndpoint (i : Fin 6) : E :=
  algebraMap (Endpoint.Field c) E
    (algebraMap (Endpoint.Ring c) (Endpoint.Field c) (Endpoint.point c i))

@[simp] theorem familyEndpoint_one : familyEndpoint c E 1 = 0 := by
  simp [familyEndpoint, Endpoint.point]

theorem familyEndpoint_parameter (i : Fin 4) :
    familyEndpoint c E i.succ.succ = algebraMap (Endpoint.Field c) E
      (algebraMap (Endpoint.Ring c) (Endpoint.Field c) (Endpoint.parameter c i)) := by
  fin_cases i <;> rfl

theorem familyEndpoint_relation : H (algebraMap R E c) (familyEndpoint c E) = 0 := by
  have h := congrArg (algebraMap (Endpoint.Field c) E)
    (congrArg (algebraMap (Endpoint.Ring c) (Endpoint.Field c)) (Endpoint.relation c))
  simpa only [H, familyEndpoint, map_add, map_mul, map_pow, map_ofNat, map_zero,
    ← IsScalarTower.algebraMap_apply R (Endpoint.Ring c) (Endpoint.Field c),
    ← IsScalarTower.algebraMap_apply R (Endpoint.Field c) E] using h

theorem familyEndpoint_normal : gradient (algebraMap R E c) (familyEndpoint c E) 0 ≠ 0 := by
  have h := (map_ne_zero (algebraMap (Endpoint.Field c) E)).2 (Endpoint.normal_ne_zero c)
  rw [Endpoint.normal_eq_gradient, gradient_map,
    ← IsScalarTower.algebraMap_apply R (Endpoint.Field c) E] at h
  exact h

structure QuarticFamily where
  coefficients : Index → E
  equations : ∀ i : Index,
    MvPolynomial.eval₂Hom (RingHom.id E) coefficients
      (ReflectionCoupledFano.equations (algebraMap R E c) (familyEndpoint c E) i) = 0
  jacobian : IsUnit (Matrix.det (fun i j : Index =>
    MvPolynomial.eval₂Hom (RingHom.id E) coefficients
      (MvPolynomial.pderiv j
        (ReflectionCoupledFano.equations (algebraMap R E c) (familyEndpoint c E) i))))
  transverse : coefficients (1,0) ≠ 0

namespace QuarticFamily

variable {c E}

def curve (p : QuarticFamily c E) : Fin 6 → Polynomial E :=
  valueCurve (familyEndpoint c E) p.coefficients

@[simp] theorem curve_constant (p : QuarticFamily c E) (i : Fin 6) :
    (p.curve i).coeff 0 = familyEndpoint c E i :=
  valueCurve_constant _ _ _

theorem curve_equation (p : QuarticFamily c E) :
    H (Polynomial.C (algebraMap R E c)) p.curve = 0 := by
  let f := H (Polynomial.C (algebraMap R E c)) p.curve
  have hmap : (systemPoly (algebraMap R E c) (familyEndpoint c E)).map
      (MvPolynomial.eval₂Hom (RingHom.id E) p.coefficients) = f :=
    systemPoly_eval₂ (RingHom.id E) _ _ _
  have hdeg : f.natDegree ≤ 24 := by
    rw [← hmap]
    exact Polynomial.natDegree_map_le.trans (systemPoly_degree_le _ _)
  have hpos (i : Index) : f.coeff (equationDegree i) = 0 := by
    rw [← hmap, Polynomial.coeff_map]
    exact p.equations i
  have hc : f.coeff 0 = 0 := by
    rw [← hmap, Polynomial.coeff_map, systemPoly_constant, familyEndpoint_relation]
    simp
  have hf := eq_constant_of_positive_coefficients f hdeg hpos
  rw [hc, Polynomial.C_0] at hf
  exact hf

theorem curve_one_linear (p : QuarticFamily c E) :
    (p.curve 1).coeff 1 = p.coefficients (1,0) := by
  simp [curve, valueCurve_explicit, Fin.sum_univ_succ]

theorem curve_one_ne_zero (p : QuarticFamily c E) : p.curve 1 ≠ 0 := by
  intro h
  have h' := p.curve_one_linear
  rw [h, Polynomial.coeff_zero] at h'
  exact p.transverse h'.symm

theorem exists_normal (p : QuarticFamily c E) :
    ∃ psi : Fin 6 → Polynomial E,
      polynomialPairing (gradient (Polynomial.C (algebraMap R E c)) p.curve) psi = 1 ∧
      ∀ i, (psi i).coeff 0 =
        if i = 0 then (gradient (algebraMap R E c) (familyEndpoint c E) 0)⁻¹ else 0 :=
  exists_polynomial_normal _ _ _ (familyEndpoint_normal c E) p.jacobian

def normal (p : QuarticFamily c E) : Fin 6 → Polynomial E :=
  Classical.choose p.exists_normal

theorem normal_pairing (p : QuarticFamily c E) :
    polynomialPairing (gradient (Polynomial.C (algebraMap R E c)) p.curve) p.normal = 1 :=
  (Classical.choose_spec p.exists_normal).1

@[simp] theorem normal_constant (p : QuarticFamily c E) (i : Fin 6) :
    (p.normal i).coeff 0 =
      if i = 0 then (gradient (algebraMap R E c) (familyEndpoint c E) 0)⁻¹ else 0 :=
  (Classical.choose_spec p.exists_normal).2 i

end QuarticFamily
end ReflectionCoupledFano

#print axioms ReflectionCoupledFano.QuarticFamily.curve_equation
#print axioms ReflectionCoupledFano.QuarticFamily.normal_pairing
