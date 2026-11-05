import Proposal.BundlePhysicalTransport
import Proposal.BundleQuotientModel
import HodgeComputer.Constructions.HoldoutCover.FermatCoefficientDerivations

/-!
The residue transport depends only on the values of the actual diagonal
field embedding on its generators.  The geometric field construction
provides `DiagonalFieldMap`; this file proves every derivative, normal,
volume, source, and certificate-clearing obligation from those values.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace HoldoutBundle

open HoldoutConstruction MvPolynomial
open scoped BigOperators

attribute [local instance] holdoutCoordinateRing_isDomain

local instance : Algebra ℤ HoldoutFunctionField := Ring.toIntAlgebra _
local instance : Algebra ℤ QuotientField := Ring.toIntAlgebra _
local instance : CharZero HoldoutFunctionField :=
  charZero_of_injective_ringHom (f := algebraMap ℂ HoldoutFunctionField)
    (algebraMap ℂ HoldoutFunctionField).injective

def quotientDensity : MvPolynomial (Fin 5) BaseField :=
  C (-(6*lambda)⁻¹)*X 0^3*X 3

def quotientNormal : QuotientField :=
  quotientResidueMap (integerPartial 0 (kPoly genericA genericB))

def quotientResidueSource : QuotientField :=
  (quotientResidueMap (integerPartial 0 quotientDensity)*quotientNormal-
    quotientResidueMap quotientDensity*
      quotientResidueMap (integerPartial 0 (integerPartial 0 (kPoly genericA genericB)))) /
        quotientNormal^2

theorem five_tuple_castSucc {R : Type*} (a b c d e : R) (j : Fin 4) :
    (![a,b,c,d,e] : Fin 5 → R) j.castSucc = (![a,b,c,d] : Fin 4 → R) j := by
  fin_cases j <;> rfl

structure DiagonalFieldMap where
  baseMap : BaseField →+* HoldoutFunctionField
  fieldMap : QuotientField →+* HoldoutFunctionField
  complex : ∀ c : ℂ, baseMap (algebraMap ℂ BaseField c)=
    algebraMap ℂ HoldoutFunctionField c
  lambda : baseMap HoldoutBundle.lambda=physicalLambda
  coefficient : ∀ c : BaseField,
    fieldMap (algebraMap BaseField QuotientField c)=baseMap c
  root : fieldMap (quotientResidueMap (X 0))=physicalY 0
  parameter : ∀ j : Fin 4, fieldMap (quotientResidueMap (X j.succ))=
    physicalQuotientTail j.castSucc

namespace DiagonalFieldMap

variable (m : DiagonalFieldMap)

def residue : MvPolynomial (Fin 5) BaseField →+* HoldoutFunctionField :=
  m.fieldMap.comp quotientResidueMap

@[simp] theorem residue_C (c : BaseField) : m.residue (C c)=m.baseMap c := by
  simp only [residue, RingHom.comp_apply, quotientResidueMap_C, m.coefficient]

@[simp] theorem residue_X_zero : m.residue (X 0)=physicalY 0 := m.root

@[simp] theorem residue_X_succ (j : Fin 4) :
    m.residue (X j.succ)=physicalQuotientTail j.castSucc := m.parameter j

set_option maxHeartbeats 100000 in
@[simp] theorem residue_X (j : Fin 5) :
    m.residue (X j)=![physicalY 0,physicalY 1,physicalY 2,physicalP,physicalQ] j := by
  refine Fin.cases ?_ (fun k => ?_) j
  · exact m.root
  · rw [m.residue_X_succ]
    simpa only [physicalQuotientTail, Matrix.cons_val_succ] using
      five_tuple_castSucc (physicalY 1) (physicalY 2) physicalP physicalQ physicalLambda k

theorem tangent_base (j : Fin 4) (c : BaseField) :
    physicalDiagonalTangent j.castSucc (m.baseMap c)=0 := by
  have hring (p : ParameterRing) :
      physicalDiagonalTangent j.castSucc
        (m.baseMap (algebraMap ParameterRing BaseField p))=0 := by
    apply derivation_zero_polynomial_image (physicalDiagonalTangent j.castSucc)
      (m.baseMap.comp (algebraMap ParameterRing BaseField))
    · intro a
      change physicalDiagonalTangent j.castSucc
        (m.baseMap (algebraMap ℂ BaseField a))=0
      rw [m.complex]
      exact physicalDiagonalTangent_constant j.castSucc a
    · change physicalDiagonalTangent j.castSucc (m.baseMap HoldoutBundle.lambda)=0
      rw [m.lambda]
      exact physicalDiagonalTangent_lambda j
  obtain ⟨a,b,_,rfl⟩ := IsFractionRing.div_surjective ParameterRing c
  rw [map_div₀, Derivation.leibniz_div, hring a, hring b]
  simp

theorem residue_equation : m.residue (kPoly genericA genericB)=0 := by
  have h := (quotientResidueMap_kernel (kPoly genericA genericB)).mpr (dvd_refl _)
  simp only [residue, RingHom.comp_apply, h, map_zero]

theorem residue_normal_ne_zero :
    m.residue (integerPartial 0 (kPoly genericA genericB)) ≠ 0 :=
  (map_ne_zero m.fieldMap).mpr quotient_normal_ne_zero

theorem tangent_root (j : Fin 4) :
    physicalDiagonalTangent j.castSucc (physicalY 0) =
      -m.residue (integerPartial j.succ (kPoly genericA genericB)) /
        m.residue (integerPartial 0 (kPoly genericA genericB)) := by
  have h := derivation_polynomial_ringHom_chain (physicalDiagonalTangent j.castSucc)
    m.residue (by
      intro c
      rw [m.residue_C]
      exact m.tangent_base j c) (kPoly genericA genericB)
  rw [m.residue_equation, map_zero, Fin.sum_univ_succ] at h
  simp only [m.residue_X_zero, m.residue_X_succ,
    physicalDiagonalTangent_coordinate, Fin.castSucc_inj] at h
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true] at h
  apply (eq_div_iff m.residue_normal_ne_zero).mpr
  simp only [integerPartial_apply]
  linear_combination -h

theorem tangent_compatible (j : Fin 4) (x : QuotientField) :
    physicalDiagonalTangent j.castSucc (m.fieldMap x)=m.fieldMap (quotientTangent j x) := by
  apply derivation_intertwines_quotient_fraction quotientProjection
    quotientProjection_surjective m.fieldMap (quotientTangent j)
    (physicalDiagonalTangent j.castSucc)
  · intro c
    change physicalDiagonalTangent j.castSucc
      (m.fieldMap (quotientResidueMap (C c)))=
      m.fieldMap (quotientTangent j (quotientResidueMap (C c)))
    simp only [quotientResidueMap_C, m.coefficient,
      quotientTangent_algebraMap, map_zero, m.tangent_base]
  · intro i
    change physicalDiagonalTangent j.castSucc (m.residue (X i))=
      m.fieldMap (quotientTangent j (quotientResidueMap (X i)))
    refine Fin.cases ?_ (fun k => ?_) i
    · rw [m.residue_X_zero, quotientResidueMap_X_zero,
        quotientTangent_root, map_div₀, map_neg, m.tangent_root]
      rfl
    · rw [m.residue_X_succ, quotientResidueMap_X_succ,
        quotientTangent_parameter, physicalDiagonalTangent_coordinate]
      simp only [Fin.castSucc_inj]
      split_ifs <;> simp

theorem normal_polynomial :
    integerPartial 0 (kPoly genericA genericB)=
      6*X 0^5+3*X 0^2*X 1*X 3 := by
  rw [integerPartial_apply, kPoly_pderiv]
  simp [gradient]

theorem second_normal_polynomial :
    integerPartial 0 (integerPartial 0 (kPoly genericA genericB))=
      30*X 0^4+6*X 0*X 1*X 3 := by
  rw [normal_polynomial]
  have hthree : pderiv (0 : Fin 5) (3 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 3
  have hsix : pderiv (0 : Fin 5) (6 : MvPolynomial (Fin 5) BaseField)=0 :=
    Derivation.map_natCast _ 6
  norm_num [integerPartial_apply, MvPolynomial.pderiv_pow, MvPolynomial.pderiv_mul,
    Pi.single_apply, Fin.ext_iff, hthree, hsix]
  ring

theorem normal_binding : m.fieldMap quotientNormal=physicalNormal := by
  change m.residue (integerPartial 0 (kPoly genericA genericB))=physicalNormal
  rw [normal_polynomial, physical_normal_value]
  simp only [map_add, map_mul, map_pow, map_ofNat, m.residue_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]

theorem second_normal_binding :
    m.residue (integerPartial 0 (integerPartial 0 (kPoly genericA genericB)))=
      physicalResidueMap (integerPartial 0 (integerPartial 0 holdoutSextic)) := by
  rw [second_normal_polynomial, physical_second_normal_value]
  simp only [map_add, map_mul, map_pow, map_ofNat, m.residue_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]

theorem density_partial : integerPartial 0 quotientDensity=
    3*C (-(6*HoldoutBundle.lambda)⁻¹)*X 0^2*X 3 :=
  scaledCoverQuotientSource_partial (-(6*HoldoutBundle.lambda)⁻¹)

theorem density_binding : m.residue quotientDensity=physicalDiagonalDensity := by
  simp only [quotientDensity, map_mul, map_pow, m.residue_C, m.residue_X,
    map_neg, map_inv₀, map_ofNat, m.lambda,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  unfold physicalDiagonalDensity HoldoutBundle.densityValue
  ring

theorem density_normal_binding :
    m.residue (integerPartial 0 quotientDensity)=physicalDiagonalDensityNormal := by
  rw [density_partial]
  simp only [map_mul, map_pow, m.residue_C, m.residue_X,
    map_neg, map_inv₀, map_ofNat, m.lambda,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  unfold physicalDiagonalDensityNormal
  ring

theorem source_binding :
    physicalDiagonalJacobian.det*m.fieldMap quotientResidueSource=physicalSourceFor Astar := by
  simp only [quotientResidueSource, map_div₀, map_sub, map_mul, map_pow]
  change physicalDiagonalJacobian.det *
    ((m.residue (integerPartial 0 quotientDensity)*m.fieldMap quotientNormal-
      m.residue quotientDensity*
        m.residue (integerPartial 0 (integerPartial 0 (kPoly genericA genericB)))) /
          (m.fieldMap quotientNormal)^2) = _
  rw [m.normal_binding, m.density_normal_binding, m.density_binding,
    m.second_normal_binding]
  simpa only [mul_div_assoc] using physical_diagonal_normal_source_binding

end DiagonalFieldMap

theorem certificate_of_quotient_residue (m : DiagonalFieldMap)
    (w : Fin 4 → QuotientField)
    (equation : quotientResidueSource+residueDivergence quotientTangent quotientNormal w=0) :
    HodgeComputer.HasCertificate holdoutSextic Astar 1 := by
  exact physical_certificate_of_diagonal_residue Astar Astar_isHomogeneous
    m.fieldMap quotientTangent physicalDiagonalTangent
    physicalDiagonalJacobian inversePhysicalDiagonalJacobian
    physicalDiagonalJacobian_mul_inverse inversePhysicalDiagonalJacobian_mul_actual
    physicalDiagonalJacobian_det_ne_zero physicalDiagonalTangent_apply
    physicalDiagonalJacobian_mixed m.tangent_compatible
    quotientNormal quotientResidueSource w equation m.normal_binding m.source_binding

end HoldoutBundle

#print axioms HoldoutBundle.DiagonalFieldMap.tangent_compatible
#print axioms HoldoutBundle.certificate_of_quotient_residue
