import Proposal.GeometricAffineCurveCharts
import Proposal.GeometricCofactorResidue
import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The cofactor quotient as the actual affine Kähler module

For the actual Jacobian localization of the two affine curve equations,
the coordinate-vector map sends the two gradient rows to zero in
`KaehlerDifferential ℂ`. The resulting quotient map is identified with an
explicit linear equivalence, using the constructed submersive presentation
and the proved cofactor reconstruction formula.

Coordinates are ordered by the permutation used to choose the Jacobian
minor. Thus the free coordinate is numbered zero and its cofactor is exactly
the inverted minor, with no suppressed permutation sign. This is a local
comparison on the existing affine ring; it does not assert the global
canonical-sheaf or Serre-trace comparison.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricKaehlerResidue

open MvPolynomial Module
open CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricCofactorResidue

/-- The actual polynomial map to the quotient and then its localization. -/
def patchMap (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    AffinePoly →ₐ[ℂ] JacobianPatch v e :=
  (IsScalarTower.toAlgHom ℂ (ChartRing v) (JacobianPatch v e)).comp
    (Ideal.Quotient.mkₐ ℂ (chartIdeal v))

/-- The coordinates in the order used to select the Jacobian minor. -/
def coordinate (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3))
    (j : Fin 3) : JacobianPatch v e := patchMap v e (X (e j))

/-- These are the actual polynomial partial derivatives in the same ring. -/
def gradient (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3))
    (i : Fin 2) : Coordinates (JacobianPatch v e) :=
  fun j => patchMap v e (pderiv (e j) (v i))

@[simp] theorem patchMap_relation (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (i : Fin 2) : patchMap v e (v i) = 0 := by
  have h : Ideal.Quotient.mk (chartIdeal v) (v i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  change algebraMap (ChartRing v) (JacobianPatch v e)
    (Ideal.Quotient.mk (chartIdeal v) (v i)) = 0
  rw [h, map_zero]

/-- The finite polynomial chain rule for the actual universal derivation. -/
theorem differential_polynomial {S : Type*} [CommRing S] [Algebra ℂ S]
    (f : AffinePoly →ₐ[ℂ] S) (p : AffinePoly) :
    KaehlerDifferential.D ℂ S (f p) =
      ∑ i : Fin 3, f (pderiv i p) • KaehlerDifferential.D ℂ S (f (X i)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
      simp only [map_mul, Derivation.leibniz, hp, smul_eq_mul, map_add,
        pderiv_X, map_mul, add_smul, Finset.sum_add_distrib, mul_smul]
      simp [Pi.single_apply, Finset.smul_sum]

/-- The literal map from the free coordinate module to universal differentials. -/
def coordinateDifferentials (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    Coordinates (JacobianPatch v e) →ₗ[JacobianPatch v e]
      KaehlerDifferential ℂ (JacobianPatch v e) where
  toFun x := ∑ j : Fin 3, x j • KaehlerDifferential.D ℂ _ (coordinate v e j)
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c x := by simp [smul_smul, Finset.smul_sum]

@[simp] theorem coordinateDifferentials_coordinateVector
    (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    coordinateDifferentials v e (coordinateVector j) =
      KaehlerDifferential.D ℂ _ (coordinate v e j) := by
  simp [coordinateDifferentials, coordinateVector]

theorem coordinateDifferentials_gradient (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (i : Fin 2) :
    coordinateDifferentials v e (gradient v e i) = 0 := by
  change (∑ j : Fin 3, patchMap v e (pderiv (e j) (v i)) •
    KaehlerDifferential.D ℂ _ (patchMap v e (X (e j)))) = 0
  have hs : (∑ j : Fin 3, patchMap v e (pderiv (e j) (v i)) •
      KaehlerDifferential.D ℂ _ (patchMap v e (X (e j)))) =
      ∑ j : Fin 3, patchMap v e (pderiv j (v i)) •
        KaehlerDifferential.D ℂ _ (patchMap v e (X j)) :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  rw [hs, ← differential_polynomial, patchMap_relation, map_zero]

theorem relations_le_ker_coordinateDifferentials (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    relations (gradient v e 0) (gradient v e 1) ≤
      LinearMap.ker (coordinateDifferentials v e) := by
  apply Submodule.span_le.mpr
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  change coordinateDifferentials v e x = 0
  rcases hx with hx | hx
  · rw [hx, coordinateDifferentials_gradient]
  · rw [hx, coordinateDifferentials_gradient]

/-- The map out of the actual gradient-row quotient, with no assumed exactness. -/
def quotientToKaehler (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    ResidueModule (gradient v e 0) (gradient v e 1) →ₗ[JacobianPatch v e]
      KaehlerDifferential ℂ (JacobianPatch v e) :=
  (relations (gradient v e 0) (gradient v e 1)).liftQ
    (coordinateDifferentials v e) (relations_le_ker_coordinateDifferentials v e)

@[simp] theorem quotientToKaehler_toResidue (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (x : Coordinates (JacobianPatch v e)) :
    quotientToKaehler v e (toResidue (gradient v e 0) (gradient v e 1) x) =
      coordinateDifferentials v e x := rfl

@[simp] theorem quotientToKaehler_coordinateVector (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    quotientToKaehler v e
        (toResidue (gradient v e 0) (gradient v e 1) (coordinateVector j)) =
      KaehlerDifferential.D ℂ _ (coordinate v e j) := by simp

/-- The unique variable not selected by the actual submersive presentation. -/
def freeIndex (e : Equiv.Perm (Fin 3)) (_ : Unit) : Unit ⊕ Fin 3 := .inr (e 0)

theorem freeIndex_injective (e : Equiv.Perm (Fin 3)) :
    Function.Injective (freeIndex e) := fun _ _ _ => Subsingleton.elim _ _

theorem freeIndex_complement (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    IsCompl (Set.range (freeIndex e)) (Set.range (smoothPresentation v e).map) := by
  constructor
  · rw [Set.disjoint_left]
    rintro x ⟨u, rfl⟩ ⟨j, hj⟩
    cases j with
    | inl u => cases hj
    | inr j =>
        change Sum.inr (e j.succ) = Sum.inr (e 0) at hj
        exact Fin.succ_ne_zero j (e.injective (Sum.inr.inj hj))
  · apply codisjoint_iff_le_sup.mpr
    intro x hx
    change x ∈ Set.range (freeIndex e) ∨ x ∈ Set.range (smoothPresentation v e).map
    cases x with
    | inl u => exact Or.inr ⟨.inl u, rfl⟩
    | inr i =>
        obtain ⟨j, rfl⟩ := e.surjective i
        fin_cases j
        · exact Or.inl ⟨(), rfl⟩
        · exact Or.inr ⟨.inr 0, rfl⟩
        · exact Or.inr ⟨.inr 1, rfl⟩

/-- A constructed basis of the genuine Kähler module on the actual localization. -/
def kaehlerBasis (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    Basis Unit (JacobianPatch v e) (KaehlerDifferential ℂ (JacobianPatch v e)) :=
  (smoothPresentation v e).basisKaehlerOfIsCompl
    (freeIndex_injective e) (freeIndex_complement v e)

@[simp] theorem kaehlerBasis_apply (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (u : Unit) :
    kaehlerBasis v e u = KaehlerDifferential.D ℂ _ (coordinate v e 0) := by
  rw [kaehlerBasis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

/-- The canonical coordinate of a differential in that singleton basis. -/
def kaehlerCoordinateEquiv (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    KaehlerDifferential ℂ (JacobianPatch v e) ≃ₗ[JacobianPatch v e] JacobianPatch v e :=
  (kaehlerBasis v e).equivFun.trans
    (LinearEquiv.funUnique Unit (JacobianPatch v e) (JacobianPatch v e))

@[simp] theorem kaehlerCoordinateEquiv_symm_apply (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (c : JacobianPatch v e) :
    (kaehlerCoordinateEquiv v e).symm c =
      c • KaehlerDifferential.D ℂ _ (coordinate v e 0) := by
  simp [kaehlerCoordinateEquiv]

theorem chartPresentation_jacobian (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    (chartPresentation v e).jacobian =
      Ideal.Quotient.mk (chartIdeal v)
        (pderiv (e 1) (v 0) * pderiv (e 2) (v 1) -
          pderiv (e 1) (v 1) * pderiv (e 2) (v 0)) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    Matrix.det_fin_two]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

/-- The cofactor in the free-coordinate position is the minor actually inverted. -/
theorem cofactor_zero_eq_jacobian (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    cofactor (gradient v e 0) (gradient v e 1) 0 =
      algebraMap (ChartRing v) (JacobianPatch v e) (chartPresentation v e).jacobian := by
  have hj := congrArg (algebraMap (ChartRing v) (JacobianPatch v e))
    (chartPresentation_jacobian v e)
  rw [hj]
  change patchMap v e (pderiv (e 1) (v 0)) * patchMap v e (pderiv (e 2) (v 1)) -
      patchMap v e (pderiv (e 2) (v 0)) * patchMap v e (pderiv (e 1) (v 1)) =
    patchMap v e (pderiv (e 1) (v 0) * pderiv (e 2) (v 1) -
      pderiv (e 1) (v 1) * pderiv (e 2) (v 0))
  simp only [map_sub, map_mul]
  ring

/-- This unit comes from the existing localization, not an added regularity premise. -/
def jacobianUnit (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    (JacobianPatch v e)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := JacobianPatch v e)
    (chartPresentation v e).jacobian).unit

theorem cofactor_zero_eq_unit (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) :
    cofactor (gradient v e 0) (gradient v e 1) 0 = (jacobianUnit v e : JacobianPatch v e) := by
  rw [cofactor_zero_eq_jacobian]
  exact (IsLocalization.Away.algebraMap_isUnit (S := JacobianPatch v e)
    (chartPresentation v e).jacobian).unit_spec.symm

/-- The cofactor cokernel is the actual Kähler module on this Jacobian patch.
The equivalence is constructed from two proved bases, with the precise
inverse-Jacobian normalization. No geometric comparison is supplied as input. -/
def residueKaehlerEquiv (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    ResidueModule (gradient v e 0) (gradient v e 1) ≃ₗ[JacobianPatch v e]
      KaehlerDifferential ℂ (JacobianPatch v e) :=
  (residueLinearEquiv (gradient v e 0) (gradient v e 1) 0
    (jacobianUnit v e) (cofactor_zero_eq_unit v e)).trans
    ((Units.mulLeftLinearEquiv (JacobianPatch v e) (JacobianPatch v e)
      (jacobianUnit v e)⁻¹).trans (kaehlerCoordinateEquiv v e).symm)

theorem residueKaehlerEquiv_apply (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3))
    (η : ResidueModule (gradient v e 0) (gradient v e 1)) :
    residueKaehlerEquiv v e η =
      (↑((jacobianUnit v e)⁻¹) : JacobianPatch v e) •
        (residueFunctional (gradient v e 0) (gradient v e 1) η •
          KaehlerDifferential.D ℂ _ (coordinate v e 0)) := by
  change (kaehlerCoordinateEquiv v e).symm
    ((↑((jacobianUnit v e)⁻¹) : JacobianPatch v e) *
      residueFunctional (gradient v e 0) (gradient v e 1) η) = _
  rw [kaehlerCoordinateEquiv_symm_apply, mul_smul]

/-- The constructed equivalence is exactly the quotient of the coordinate
map to universal differentials, rather than an arbitrary rank-one isomorphism. -/
theorem residueKaehlerEquiv_eq_quotientToKaehler (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3))
    (η : ResidueModule (gradient v e 0) (gradient v e 1)) :
    residueKaehlerEquiv v e η = quotientToKaehler v e η := by
  rw [residueKaehlerEquiv_apply]
  conv_rhs => rw [reconstruction (gradient v e 0) (gradient v e 1) 0
    (jacobianUnit v e) (cofactor_zero_eq_unit v e) η]
  rw [map_smul, normalizedResidue, map_smul, quotientToKaehler_coordinateVector]
  exact smul_comm _ _ _

@[simp] theorem residueKaehlerEquiv_coordinateVector (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    residueKaehlerEquiv v e
        (toResidue (gradient v e 0) (gradient v e 1) (coordinateVector j)) =
      KaehlerDifferential.D ℂ _ (coordinate v e j) := by
  rw [residueKaehlerEquiv_eq_quotientToKaehler, quotientToKaehler_coordinateVector]

/-- The local residue generator has the promised universal-differential formula. -/
@[simp] theorem residueKaehlerEquiv_normalizedResidue
    (v : Fin 2 → AffinePoly) (e : Equiv.Perm (Fin 3)) :
    residueKaehlerEquiv v e
        (normalizedResidue (gradient v e 0) (gradient v e 1) 0 (jacobianUnit v e)) =
      (↑((jacobianUnit v e)⁻¹) : JacobianPatch v e) •
        KaehlerDifferential.D ℂ _ (coordinate v e 0) := by
  rw [normalizedResidue, map_smul, residueKaehlerEquiv_coordinateVector]

theorem quotientToKaehler_bijective (v : Fin 2 → AffinePoly)
    (e : Equiv.Perm (Fin 3)) : Function.Bijective (quotientToKaehler v e) := by
  have he : (quotientToKaehler v e :
      ResidueModule (gradient v e 0) (gradient v e 1) →
        KaehlerDifferential ℂ (JacobianPatch v e)) = residueKaehlerEquiv v e :=
    funext (fun η => (residueKaehlerEquiv_eq_quotientToKaehler v e η).symm)
  rw [he]
  exact (residueKaehlerEquiv v e).bijective

end CycleQ2GeometricKaehlerResidue

end
