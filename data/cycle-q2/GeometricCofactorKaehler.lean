import Proposal.GeometricCofactorResidue
import Proposal.GeometricAffineCurveCharts
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The cofactor cokernel is the actual localized differential module

This module binds the two-gradient cokernel to the Kähler differentials of
the literal affine chart quotient localized at its Jacobian minor. Coordinates are ordered by an arbitrary permutation, so all Jacobian
pivot charts are included with their induced orientation. The map
sends each coordinate class to the differential of that coordinate.
The freeness and generation statements use the constructed submersive
presentation of the actual ring; no comparison is supplied as a hypothesis.

This is a local algebraic comparison. A global canonical-sheaf comparison,
geometric Serre trace, and the final certificate remain separate steps.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCofactorKaehler

open MvPolynomial Module
open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricCofactorResidue

variable (e : Equiv.Perm (Fin 3))

abbrev LocalRing (v : Fin 2 → AffinePoly) := JacobianPatch v e

def polynomialMap (v : Fin 2 → AffinePoly) : AffinePoly →ₐ[ℂ] LocalRing e v :=
  (IsScalarTower.toAlgHom ℂ (ChartRing v) (LocalRing e v)).comp
    (Ideal.Quotient.mkₐ ℂ (chartIdeal v))

def coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) : LocalRing e v :=
  polynomialMap e v (X (e j))

def gradient (v : Fin 2 → AffinePoly) (i : Fin 2) : Coordinates (LocalRing e v) :=
  fun j => polynomialMap e v (pderiv (e j) (v i))

def differential (v : Fin 2 → AffinePoly) :
    Coordinates (LocalRing e v) →ₗ[LocalRing e v] KaehlerDifferential ℂ (LocalRing e v) :=
  (Pi.basisFun (LocalRing e v) (Fin 3)).constr (LocalRing e v)
    (fun j => KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j))

@[simp] theorem differential_coordinateVector (v : Fin 2 → AffinePoly) (j : Fin 3) :
    differential e v (coordinateVector j) =
      KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j) := by
  have h : coordinateVector j = (Pi.basisFun (LocalRing e v) (Fin 3)) j := by
    funext i
    simp [coordinateVector, Pi.basisFun_apply, Pi.single_apply, eq_comm]
  rw [h, differential, Basis.constr_basis]

theorem differential_apply (v : Fin 2 → AffinePoly) (x : Coordinates (LocalRing e v)) :
    differential e v x = ∑ j : Fin 3, x j •
      KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j) := by
  rw [differential, Basis.constr_apply_fintype]
  rfl

@[simp] theorem polynomialMap_relation (v : Fin 2 → AffinePoly) (i : Fin 2) :
    polynomialMap e v (v i) = 0 := by
  have h : (Ideal.Quotient.mk (chartIdeal v)) (v i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  change algebraMap (ChartRing v) (LocalRing e v)
    ((Ideal.Quotient.mk (chartIdeal v)) (v i)) = 0
  rw [h, map_zero]

@[simp] theorem polynomialMap_eq_algebraMap (v : Fin 2 → AffinePoly) (p : AffinePoly) :
    polynomialMap e v p = algebraMap AffinePoly (LocalRing e v) p := rfl

/-- The chain rule for the actual universal differential. -/
theorem polynomial_differential (v : Fin 2 → AffinePoly) (p : AffinePoly) :
    KaehlerDifferential.D ℂ (LocalRing e v) (polynomialMap e v p) =
      ∑ j : Fin 3, polynomialMap e v (pderiv (e j) p) •
        KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j) := by
  have h := congrArg (KaehlerDifferential.map ℂ ℂ AffinePoly (LocalRing e v))
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Fin 3)).sum_repr
      (KaehlerDifferential.D ℂ AffinePoly p))
  have h' : KaehlerDifferential.D ℂ (LocalRing e v) (polynomialMap e v p) =
      ∑ j : Fin 3, polynomialMap e v (pderiv j p) •
        KaehlerDifferential.D ℂ (LocalRing e v) (polynomialMap e v (X j)) := by
    simpa only [map_sum, map_smul,
      KaehlerDifferential.mvPolynomialBasis_repr_apply,
      KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D,
      polynomialMap_eq_algebraMap, IsScalarTower.algebraMap_smul]
      using h.symm
  exact h'.trans (Equiv.sum_comp e (fun j : Fin 3 =>
    polynomialMap e v (pderiv j p) •
      KaehlerDifferential.D ℂ (LocalRing e v) (polynomialMap e v (X j)))).symm

/-- Both defining equations give zero actual differentials. -/
theorem differential_gradient (v : Fin 2 → AffinePoly) (i : Fin 2) :
    differential e v (gradient e v i) = 0 := by
  rw [differential_apply]
  change (∑ j : Fin 3, polynomialMap e v (pderiv (e j) (v i)) •
    KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j)) = 0
  rw [← polynomial_differential, polynomialMap_relation, map_zero]

/-- The omitted coordinate is complementary to the actual pivot map of
    the localized presentation, including its new inverse variable. -/
theorem free_coordinate_compl (v : Fin 2 → AffinePoly) :
    IsCompl (Set.range (fun _ : Unit => (Sum.inr (e 0) : Unit ⊕ Fin 3)))
      (Set.range (smoothPresentation v e).map) := by
  apply IsCompl.of_eq
  · ext x
    cases x with
    | inl u => simp [smoothPresentation, Algebra.PreSubmersivePresentation.comp_map]
    | inr j =>
      obtain ⟨j, rfl⟩ := e.surjective j
      fin_cases j <;>
        simp [smoothPresentation, chartPresentation,
          Algebra.PreSubmersivePresentation.comp_map, Algebra.PreSubmersivePresentation.naive,
          e.injective.eq_iff]
  · ext x
    cases x with
    | inl u => simp [smoothPresentation, Algebra.PreSubmersivePresentation.comp_map]
    | inr j =>
      obtain ⟨j, rfl⟩ := e.surjective j
      fin_cases j <;>
        simp [smoothPresentation, chartPresentation,
          Algebra.PreSubmersivePresentation.comp_map, Algebra.PreSubmersivePresentation.naive,
          e.injective.eq_iff]

/-- A constructed basis of the genuine localized Kähler differential module. -/
def kaehlerBasis (v : Fin 2 → AffinePoly) :
    Basis Unit (LocalRing e v) (KaehlerDifferential ℂ (LocalRing e v)) :=
  (smoothPresentation v e).basisKaehlerOfIsCompl
    (f := fun _ : Unit => (Sum.inr (e 0) : Unit ⊕ Fin 3))
    (fun _ _ _ => Subsingleton.elim _ _) (free_coordinate_compl e v)

@[simp] theorem kaehlerBasis_apply (v : Fin 2 → AffinePoly) (j : Unit) :
    kaehlerBasis e v j =
      KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v 0) := by
  rw [kaehlerBasis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

/-- The defining Jacobian minor is exactly the oriented cofactor, so its
    invertibility follows from the actual localization. -/
theorem cofactor_zero_eq_jacobian (v : Fin 2 → AffinePoly) :
    cofactor (gradient e v 0) (gradient e v 1) 0 =
      algebraMap (ChartRing v) (LocalRing e v)
        (chartPresentation v e).jacobian := by
  calc
    cofactor (gradient e v 0) (gradient e v 1) 0 =
        polynomialMap e v (chartPresentation v e).jacobiMatrix.det := by
      have hentry (i j : Fin 2) :
          (chartPresentation v e).jacobiMatrix i j =
            pderiv (e i.succ) (v j) := by
        rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
        rfl
      simp [gradient, cofactor, Matrix.det_fin_two, hentry]
      ring
    _ = _ := (congrArg (algebraMap (ChartRing v) (LocalRing e v))
      (chartPresentation v e).jacobian_eq_jacobiMatrix_det).symm

theorem cofactor_zero_isUnit (v : Fin 2 → AffinePoly) :
    IsUnit (cofactor (gradient e v 0) (gradient e v 1) 0) := by
  rw [cofactor_zero_eq_jacobian]
  exact IsLocalization.Away.algebraMap_isUnit _

def cofactorUnit (v : Fin 2 → AffinePoly) : (LocalRing e v)ˣ :=
  (cofactor_zero_isUnit e v).unit

@[simp] theorem cofactorUnit_value (v : Fin 2 → AffinePoly) :
    cofactor (gradient e v 0) (gradient e v 1) 0 = (cofactorUnit e v : LocalRing e v) :=
  (cofactor_zero_isUnit e v).unit_spec.symm

/-- The equation-gradient span maps to zero by the universal differential. -/
theorem relations_le_differential_kernel (v : Fin 2 → AffinePoly) :
    relations (gradient e v 0) (gradient e v 1) ≤ LinearMap.ker (differential e v) := by
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with hx | hx
  · subst x
    exact differential_gradient e v 0
  · subst x
    exact differential_gradient e v 1

/-- The actual map from the conormal cokernel to Kähler differentials. -/
def toKaehler (v : Fin 2 → AffinePoly) :
    ResidueModule (gradient e v 0) (gradient e v 1) →ₗ[LocalRing e v]
      KaehlerDifferential ℂ (LocalRing e v) :=
  (relations (gradient e v 0) (gradient e v 1)).liftQ
    (differential e v) (relations_le_differential_kernel e v)

@[simp] theorem toKaehler_toResidue (v : Fin 2 → AffinePoly)
    (x : Coordinates (LocalRing e v)) :
    toKaehler e v (toResidue (gradient e v 0) (gradient e v 1) x) = differential e v x := rfl

@[simp] theorem toKaehler_normalizedResidue (v : Fin 2 → AffinePoly)
    (k : Fin 3) (u : (LocalRing e v)ˣ) :
    toKaehler e v (normalizedResidue (gradient e v 0) (gradient e v 1) k u) =
      (↑(u⁻¹) : LocalRing e v) •
        KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v k) := by
  rw [normalizedResidue, map_smul, toKaehler_toResidue, differential_coordinateVector]

theorem toKaehler_reconstruction (v : Fin 2 → AffinePoly)
    (η : ResidueModule (gradient e v 0) (gradient e v 1)) :
    toKaehler e v η =
      (residueFunctional (gradient e v 0) (gradient e v 1) η *
        (↑((cofactorUnit e v)⁻¹) : LocalRing e v)) • kaehlerBasis e v () := by
  calc
    toKaehler e v η =
        toKaehler e v (residueFunctional (gradient e v 0) (gradient e v 1) η •
          normalizedResidue (gradient e v 0) (gradient e v 1) 0 (cofactorUnit e v)) :=
      congrArg (toKaehler e v) (reconstruction _ _ 0 _ (cofactorUnit_value e v) η)
    _ = _ := by
      rw [map_smul, toKaehler_normalizedResidue, smul_smul, kaehlerBasis_apply]

theorem toKaehler_injective (v : Fin 2 → AffinePoly) :
    Function.Injective (toKaehler e v) := by
  intro η ζ h
  have hc := congrArg (fun ω => (kaehlerBasis e v).repr ω ()) h
  rw [toKaehler_reconstruction, toKaehler_reconstruction] at hc
  simp only [map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_eq_same, smul_eq_mul, mul_one] at hc
  have hd := congrArg (fun c : LocalRing e v => c * (cofactorUnit e v : LocalRing e v)) hc
  simp only [mul_assoc, (cofactorUnit e v).inv_mul, mul_one] at hd
  exact residueFunctional_injective _ _ 0 _ (cofactorUnit_value e v) hd

theorem toKaehler_surjective (v : Fin 2 → AffinePoly) :
    Function.Surjective (toKaehler e v) := by
  intro ω
  refine ⟨(kaehlerBasis e v).repr ω () •
    toResidue (gradient e v 0) (gradient e v 1) (coordinateVector 0), ?_⟩
  rw [map_smul, toKaehler_toResidue, differential_coordinateVector,
    ← kaehlerBasis_apply e v ()]
  simpa using (kaehlerBasis e v).sum_repr ω

/-- This equivalence is induced by the actual universal differential; it
    identifies the actual quotient module with the actual Kähler module. -/
def residueKaehlerEquiv (v : Fin 2 → AffinePoly) :
    ResidueModule (gradient e v 0) (gradient e v 1) ≃ₗ[LocalRing e v]
      KaehlerDifferential ℂ (LocalRing e v) :=
  LinearEquiv.ofBijective (toKaehler e v)
    ⟨toKaehler_injective e v, toKaehler_surjective e v⟩

@[simp] theorem residueKaehlerEquiv_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    residueKaehlerEquiv e v (toResidue (gradient e v 0) (gradient e v 1) (coordinateVector j)) =
      KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j) :=
  differential_coordinateVector e v j

/-- The cofactor functional now trivializes the actual Kähler module. -/
def kaehlerResidueEquiv (v : Fin 2 → AffinePoly) :
    KaehlerDifferential ℂ (LocalRing e v) ≃ₗ[LocalRing e v] LocalRing e v :=
  (residueKaehlerEquiv e v).symm.trans
    (residueLinearEquiv (gradient e v 0) (gradient e v 1) 0
      (cofactorUnit e v) (cofactorUnit_value e v))

@[simp] theorem kaehlerResidueEquiv_coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) :
    kaehlerResidueEquiv e v
      (KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j)) =
        cofactor (gradient e v 0) (gradient e v 1) j := by
  change residueFunctional (gradient e v 0) (gradient e v 1)
    ((residueKaehlerEquiv e v).symm
      (KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v j))) = _
  rw [← residueKaehlerEquiv_coordinate e v j, LinearEquiv.symm_apply_apply,
    residueFunctional_toResidue, coefficient_coordinateVector]

/-- The explicit normalized differential is the inverse image of one. -/
theorem kaehlerResidueEquiv_normalized (v : Fin 2 → AffinePoly) :
    kaehlerResidueEquiv e v
      ((↑((cofactorUnit e v)⁻¹) : LocalRing e v) •
        KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v 0)) = 1 := by
  rw [map_smul, kaehlerResidueEquiv_coordinate, cofactorUnit_value]
  exact (cofactorUnit e v).inv_mul

/-- Whenever two minors are invertible on this same actual ring, the
    corresponding normalized Kähler differentials agree. -/
theorem normalized_differentials_agree (v : Fin 2 → AffinePoly)
    (k l : Fin 3) (u w : (LocalRing e v)ˣ)
    (hu : cofactor (gradient e v 0) (gradient e v 1) k = (u : LocalRing e v))
    (hw : cofactor (gradient e v 0) (gradient e v 1) l = (w : LocalRing e v)) :
    (↑(u⁻¹) : LocalRing e v) •
        KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v k) =
      (↑(w⁻¹) : LocalRing e v) •
        KaehlerDifferential.D ℂ (LocalRing e v) (coordinate e v l) := by
  rw [← toKaehler_normalizedResidue, ← toKaehler_normalizedResidue]
  exact congrArg (toKaehler e v)
    (normalizedResidues_agree (gradient e v 0) (gradient e v 1) k l u w hu hw)

/-- The first literal affine equation pair has the constructed comparison. -/
def firstChartResidueKaehlerEquiv (r θ : ℂ) :=
  residueKaehlerEquiv e ![firstQuadric r, firstCubic θ]

/-- The second literal affine equation pair has the constructed comparison. -/
def secondChartResidueKaehlerEquiv (r θ : ℂ) :=
  residueKaehlerEquiv e ![secondQuadric r, secondCubic θ]

#print axioms residueKaehlerEquiv
#print axioms residueKaehlerEquiv_coordinate
#print axioms kaehlerResidueEquiv
#print axioms normalized_differentials_agree
#print axioms firstChartResidueKaehlerEquiv
#print axioms secondChartResidueKaehlerEquiv

end CycleQ2GeometricCofactorKaehler

end
