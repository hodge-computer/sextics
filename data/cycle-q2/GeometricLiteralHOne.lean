import Proposal.GeometricCofactorResidue
import Proposal.GeometricAffineCurveCharts
import Mathlib.RingTheory.Kaehler.Polynomial
import Proposal.GeometricAffineOverlap
import Proposal.GeometricGlobalResidue
import Proposal.GeometricAffineCohomology
import Proposal.GeometricLiteralCanonicalClass
import Proposal.GeometricIncidenceCechTrace

/-! Consolidated existing geometry components. Their declaration bodies
are preserved verbatim; chronological notes inside them describe their original stage. -/

section RetainedGeometryPart01

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

end RetainedGeometryPart01

section RetainedGeometryPart02

/-!
# The full overlap transition of the affine residue frames

The actual coordinate Jacobian sends the second gradient cokernel to the
first. Its residue coefficient scales by minus the coordinate x2/x1.
Consequently the global frames constructed from the unit Jacobian ideals
have the required projective transition on the entire coordinate overlap,
including points where the middle Jacobian minor vanishes.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricGlobalAdjunction

open CycleQ2GeometricAffineCurveCharts CycleQ2GeometricAdjunctionOverlap
  CycleQ2GeometricCofactorResidue CycleQ2GeometricGlobalResidue

variable {R : Type*} [CommRing R]

/-- Pullback of coordinate one-forms by (a,b,c) ↦ (a/b,1/b,c/b). -/
def pullForm (a c t : R) : Coordinates R →ₗ[R] Coordinates R where
  toFun v := ![t * v 0,
    -(a * t ^ 2) * v 0 - t ^ 2 * v 1 - c * t ^ 2 * v 2,
    t * v 2]
  map_add' v w := by
    ext j
    fin_cases j <;> simp <;> ring
  map_smul' q v := by
    ext j
    fin_cases j <;> simp <;> ring

theorem pullForm_eq_pullRow (a c t : R) (v : Coordinates R) :
    pullForm a c t v = pullRow a c t v := by
  ext j
  fin_cases j <;>
    simp [pullForm, pullRow, coordinateJacobian, Fin.sum_univ_succ] <;> ring

variable (r i θ a b c t : R)
  (ht : b * t = 1) (hf : quadricOne r a b c = 0) (hh : cubicOne i θ a b c = 0)

include hf in
theorem pullForm_quadric :
    pullForm a c t (gradQuadricTwo r (a * t) t (c * t)) =
      t ^ 2 • gradQuadricOne r a := by
  rw [pullForm_eq_pullRow, quadratic_differential_change]
  have hf' : quadricOne r a 0 c = 0 := hf
  ext j
  simp only [hf', mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul, ite_self]

include ht hh in
theorem pullForm_cubic :
    pullForm a c t (gradCubicTwo i θ (a * t) t (c * t)) =
      t ^ 3 • gradCubicOne i θ a b c := by
  rw [pullForm_eq_pullRow, cubic_differential_change i θ a b c t ht]
  ext j
  simp only [hh, mul_zero, sub_zero, Pi.smul_apply, smul_eq_mul, ite_self]

abbrev FirstResidue := ResidueModule (gradQuadricOne r a) (gradCubicOne i θ a b c)
abbrev SecondResidue := ResidueModule (gradQuadricTwo r (a * t) t (c * t))
  (gradCubicTwo i θ (a * t) t (c * t))

include ht hf hh in
private theorem relations_le_pull_kernel :
    relations (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) ≤
      LinearMap.ker
        ((toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)).comp (pullForm a c t)) := by
  apply Submodule.span_le.mpr
  intro v hv
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
  rcases hv with hv | hv
  · subst v
    change toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (pullForm a c t (gradQuadricTwo r (a * t) t (c * t))) = 0
    rw [pullForm_quadric r a b c t hf, map_smul]
    have hz : toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
        (gradQuadricOne r a) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (first_relation_mem _ _)
    rw [hz, smul_zero]
  · subst v
    change toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (pullForm a c t (gradCubicTwo i θ (a * t) t (c * t))) = 0
    rw [pullForm_cubic i θ a b c t ht hh, map_smul]
    have hz : toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)
        (gradCubicOne i θ a b c) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr (second_relation_mem _ _)
    rw [hz, smul_zero]

/-- The coordinate pullback on the actual two-gradient cokernels. -/
def residuePullback : SecondResidue r i θ a c t →ₗ[R] FirstResidue r i θ a b c :=
  (relations (gradQuadricTwo r (a * t) t (c * t))
    (gradCubicTwo i θ (a * t) t (c * t))).liftQ
    ((toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c)).comp (pullForm a c t))
    (relations_le_pull_kernel r i θ a b c t ht hf hh)

@[simp] theorem residuePullback_toResidue (v : Coordinates R) :
    residuePullback r i θ a b c t ht hf hh
      (toResidue (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) v) =
      toResidue (gradQuadricOne r a) (gradCubicOne i θ a b c) (pullForm a c t v) := rfl

include ht hf hh in
/-- The complete cofactor transformation, with no chosen invertible minor. -/
theorem coefficient_pullForm (v : Coordinates R) :
    coefficient (gradQuadricOne r a) (gradCubicOne i θ a b c) (pullForm a c t v) =
      -b * coefficient (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) v := by
  have he := CycleQ2GeometricAffineOverlap.cofactor_change_on_curve
    r i θ a b c t ht hf hh
  change cofactor (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) =
    ![-t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 0 +
        a * t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
      t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
      -t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 2 +
        c * t ^ 3 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1] at he
  simp only [coefficient_apply, he]
  simp [pullForm]
  linear_combination
    (t ^ 2 * cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 1 *
        (a * v 0 + v 1 + c * v 2) -
      t * (cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 0 * v 0 +
        cofactor (gradQuadricOne r a) (gradCubicOne i θ a b c) 2 * v 2)) * ht

theorem residueFunctional_pullback (η : SecondResidue r i θ a c t) :
    residueFunctional (gradQuadricOne r a) (gradCubicOne i θ a b c)
      (residuePullback r i θ a b c t ht hf hh η) =
      -b * residueFunctional (gradQuadricTwo r (a * t) t (c * t))
        (gradCubicTwo i θ (a * t) t (c * t)) η := by
  refine Quotient.inductionOn' η (fun v => ?_)
  exact coefficient_pullForm r i θ a b c t ht hf hh v

/-- The global affine frames have the expected transition everywhere on
the coordinate overlap. Projective orientation changes the sign to +b. -/
theorem globalResidue_transport
    (hfirst : minorIdeal (gradQuadricOne r a) (gradCubicOne i θ a b c) = ⊤)
    (hsecond : minorIdeal (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) = ⊤) :
    residuePullback r i θ a b c t ht hf hh
      (globalResidue _ _ hsecond) = -b • globalResidue _ _ hfirst := by
  apply CycleQ2GeometricGlobalResidue.residueFunctional_injective _ _ hfirst
  rw [residueFunctional_pullback, residueFunctional_globalResidue, mul_one,
    map_smul, residueFunctional_globalResidue, smul_eq_mul, mul_one]

#print axioms residuePullback
#print axioms residueFunctional_pullback
#print axioms globalResidue_transport

end CycleQ2GeometricGlobalAdjunction
end

end RetainedGeometryPart02

section RetainedGeometryPart03

/-!
# The complete literal canonical cohomology line

The complex action on the existing homogeneous Cech quotient is compared
with multiplication by actual projective coefficients. This makes the
proved Cech-to-derived equivalence complex-linear for every r ≠ 0.

At the literal incidence seed (r, θ) = (57, 1), the exact incoming Cech
coordinate and the already constructed literal canonical module isomorphism
then identify all actual H¹(Ω) with ℂ. The normalization is explicitly the
image of x₃⁹/(g₁g₂) through that canonical isomorphism. Every nonzero linear
functional on this derived group has the same kernel on maps into it.
The original paired numerators give the computed derivative row there.

No identification with a geometric Serre trace or a moving-cycle map is
asserted by this construction.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricLiteralHOne

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
  CycleQ2NormalConnecting CycleQ2SeedCechTheta
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricProjectiveCohomologyLinear
  CycleQ2GeometricProjectiveCanonical CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafCohomologyScalar
  CycleQ2GeometricLiteralCanonicalClass
  CycleQ2GeometricCechComplex CycleQ2GeometricIncidenceCechSurjectivity
  CycleQ2GeometricIncidenceCechTrace

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) := HasExt.standard _

private def linearEquivOfAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℂ M] [Module ℂ N] (e : M ≃+ N)
    (h : ∀ (c : ℂ) (x : M), e (c • x) = c • e x) : M ≃ₗ[ℂ] N :=
  { toAddEquiv := e
    map_smul' := h }

/-- The incoming complex action and the already checked degree-zero
coefficient action are equal in the actual overlap localization. -/
theorem overlapCoefficient_smul_eq_complex (r θ c : ℂ)
    (x : OverlapDegreeOne r θ) :
    overlapCoefficient r θ c • x = c • x := by
  apply Subtype.ext
  change (overlapCoefficient r θ c).val * (x : Overlap r θ) =
    c • (x : Overlap r θ)
  rw [Algebra.smul_def]
  congr 1

/-- The actual Mayer-Vietoris quotient map respects the original complex
module structure on the homogeneous Cech quotient. -/
theorem degreeOneToProjectiveH1_smul (r θ : ℂ) (hr : r ≠ 0)
    (c : ℂ) (z : DegreeOneCech r θ) :
    degreeOneToProjectiveH1 r θ hr (c • z) =
      c • degreeOneToProjectiveH1 r θ hr z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  rw [← cech_mk_smul]
  change degreeOneConnecting r θ hr (c • x) = c • degreeOneConnecting r θ hr x
  rw [← overlapCoefficient_smul_eq_complex]
  exact degreeOneConnecting_scalar r θ hr c x

/-- The full existing Cech-to-derived equivalence is linear for the
intrinsic complex action coming from the projective structure morphism. -/
def degreeOneCechHOneLinearEquiv (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ ≃ₗ[ℂ] ProjectiveSheafH1 r θ :=
  linearEquivOfAddEquiv (degreeOneCechHOneEquiv r θ hr)
    (degreeOneToProjectiveH1_smul r θ hr)

@[simp] theorem degreeOneCechHOneLinearEquiv_apply (r θ : ℂ) (hr : r ≠ 0)
    (z : DegreeOneCech r θ) :
    degreeOneCechHOneLinearEquiv r θ hr z = degreeOneToProjectiveH1 r θ hr z := rfl

private def canonicalAdditiveIsoAt (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ) :
    differentialAdditiveSheaf r θ ≅ degreeOneSheaf r θ :=
  (SheafOfModules.toSheaf (ringSheaf (projectiveCurve r θ).sheaf)).mapIso e

private def canonicalH1EquivAt (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ) :
    ProjectiveSheafH1 r θ ≃+ DifferentialSheafH1 r θ :=
  (((Sheaf.cohomologyPresheafFunctor
      (Opens.grothendieckTopology (projectiveCurve r θ)) 1).mapIso
        (canonicalAdditiveIsoAt r θ e)).app (op ⊤)).addCommGroupIsoToAddEquiv.symm

private theorem canonicalH1EquivAt_smul (r θ : ℂ)
    (e : projectiveDifferentialSheaf r θ ≅ degreeOneModuleSheaf r θ)
    (c : ℂ) (x : ProjectiveSheafH1 r θ) :
    canonicalH1EquivAt r θ e (c • x) = c • canonicalH1EquivAt r θ e x :=
  cohomologyMap_scalar (projectiveCurve r θ).sheaf (projectiveGlobalCoefficient r θ)
    (degreeOneModuleSheaf r θ) e.inv 1 ⊤ c x

/-- The already constructed literal canonical map commutes with the
intrinsic scalar actions because it comes from a module-sheaf morphism. -/
theorem literalCanonicalH1Equiv_smul (c : ℂ) (x : ProjectiveSheafH1 57 1) :
    literalCanonicalH1Equiv (c • x) = c • literalCanonicalH1Equiv x :=
  canonicalH1EquivAt_smul 57 1 literalProjectiveCanonicalIso c x

private def cechCanonicalAddEquiv (r θ : ℂ) (hr : r ≠ 0)
    (e : ProjectiveSheafH1 r θ ≃+ DifferentialSheafH1 r θ) :
    DegreeOneCech r θ ≃+ DifferentialSheafH1 r θ :=
  (degreeOneCechHOneEquiv r θ hr).trans e

/-- The existing actual additive Cech and canonical comparisons. -/
def literalCechCanonicalAddEquiv :
    DegreeOneCech 57 1 ≃+ DifferentialSheafH1 57 1 :=
  cechCanonicalAddEquiv 57 1 (by norm_num) literalCanonicalH1Equiv

@[simp] theorem literalCechCanonicalAddEquiv_apply (z : DegreeOneCech 57 1) :
    literalCechCanonicalAddEquiv z =
      literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) z) := rfl

theorem literalCechCanonicalAddEquiv_smul (c : ℂ) (z : DegreeOneCech 57 1) :
    literalCechCanonicalAddEquiv (c • z) = c • literalCechCanonicalAddEquiv z := by
  change literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) (c • z)) = _
  exact (congrArg literalCanonicalH1Equiv
    (degreeOneToProjectiveH1_smul 57 1 (by norm_num) c z)).trans
      (literalCanonicalH1Equiv_smul c _)

/-- The precise canonical normalization: the image of x₃⁹/(g₁g₂). -/
def literalCanonicalNormalization : DifferentialSheafH1 57 1 :=
  literalCechCanonicalAddEquiv incidenceCechNormalization

/-- Scalar multiplication of the actual normalization class. -/
def literalCanonicalNormalizationLinear : ℂ →ₗ[ℂ] DifferentialSheafH1 57 1 :=
  LinearMap.toSpanSingleton ℂ (DifferentialSheafH1 57 1) literalCanonicalNormalization

/-- The scalar parameterization agrees pointwise with the original
Cech coordinate followed by the already constructed canonical map. -/
theorem literalCanonicalNormalizationLinear_eq_actual (c : ℂ) :
    literalCanonicalNormalizationLinear c =
      literalCechCanonicalAddEquiv (incidenceCechEquiv c) := by
  change c • literalCechCanonicalAddEquiv incidenceCechNormalization =
    literalCechCanonicalAddEquiv (c • incidenceCechNormalization)
  exact (literalCechCanonicalAddEquiv_smul c incidenceCechNormalization).symm

theorem literalCanonicalNormalizationLinear_injective :
    Function.Injective literalCanonicalNormalizationLinear := by
  intro a b hab
  apply incidenceCechEquiv.injective
  apply literalCechCanonicalAddEquiv.injective
  simpa only [literalCanonicalNormalizationLinear_eq_actual] using hab

theorem literalCanonicalNormalizationLinear_surjective :
    Function.Surjective literalCanonicalNormalizationLinear := by
  intro x
  obtain ⟨z, rfl⟩ := literalCechCanonicalAddEquiv.surjective x
  obtain ⟨c, hc⟩ := incidenceCechEquiv.surjective z
  refine ⟨c, ?_⟩
  rw [literalCanonicalNormalizationLinear_eq_actual, hc]

/-- A linear parameterization of the complete actual H¹(Ω) on the literal
incidence curve, using the original Cech normalization. -/
def literalCanonicalNormalizationEquiv : ℂ ≃ₗ[ℂ] DifferentialSheafH1 57 1 :=
  LinearEquiv.ofBijective literalCanonicalNormalizationLinear
    ⟨literalCanonicalNormalizationLinear_injective,
      literalCanonicalNormalizationLinear_surjective⟩

/-- The linear Cech comparison, recovered through the proved coordinate. -/
def literalCechCanonicalEquiv :
    DegreeOneCech 57 1 ≃ₗ[ℂ] DifferentialSheafH1 57 1 :=
  incidenceCechEquiv.symm.trans literalCanonicalNormalizationEquiv

@[simp] theorem literalCechCanonicalEquiv_apply (z : DegreeOneCech 57 1) :
    literalCechCanonicalEquiv z =
      literalCanonicalH1Equiv (degreeOneToProjectiveH1 57 1 (by norm_num) z) := by
  change literalCanonicalNormalizationLinear (incidenceCechEquiv.symm z) = _
  exact (literalCanonicalNormalizationLinear_eq_actual _).trans
    (congrArg literalCechCanonicalAddEquiv (incidenceCechEquiv.apply_symm_apply z))

@[simp] theorem literalCechCanonicalEquiv_normalization :
    literalCechCanonicalEquiv incidenceCechNormalization = literalCanonicalNormalization :=
  literalCechCanonicalEquiv_apply incidenceCechNormalization

@[simp] theorem literalCanonicalNormalizationEquiv_one :
    literalCanonicalNormalizationEquiv 1 = literalCanonicalNormalization := by
  change (1 : ℂ) • literalCanonicalNormalization = literalCanonicalNormalization
  exact one_smul _ _

/-- The resulting coordinate on the complete derived cohomology group. -/
def literalCanonicalCoordinate : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ :=
  literalCanonicalNormalizationEquiv.symm.toLinearMap

instance literalDifferentialSheafH1_finite : Module.Finite ℂ (DifferentialSheafH1 57 1) :=
  Module.Finite.of_surjective literalCanonicalNormalizationEquiv.toLinearMap
    literalCanonicalNormalizationEquiv.surjective

theorem literalDifferentialSheafH1_finrank : Module.finrank ℂ (DifferentialSheafH1 57 1) = 1 := by
  rw [← literalCanonicalNormalizationEquiv.finrank_eq]
  exact Module.finrank_self ℂ

@[simp] theorem literalCanonicalCoordinate_normalization :
    literalCanonicalCoordinate literalCanonicalNormalization = 1 := by
  change literalCanonicalNormalizationEquiv.symm literalCanonicalNormalization = 1
  apply literalCanonicalNormalizationEquiv.injective
  rw [LinearEquiv.apply_symm_apply]
  exact literalCanonicalNormalizationEquiv_one.symm

theorem literalCanonicalCoordinate_eq_zero_iff (x : DifferentialSheafH1 57 1) :
    literalCanonicalCoordinate x = 0 ↔ x = 0 :=
  literalCanonicalNormalizationEquiv.symm.map_eq_zero_iff

theorem literalCanonicalNormalization_ne_zero : literalCanonicalNormalization ≠ 0 := by
  intro hz
  have h := literalCanonicalCoordinate_normalization
  rw [hz, map_zero] at h
  exact zero_ne_one h

/-- Pulling a nonzero derived-cohomology functional back through the
actual Cech equivalence preserves nonzeroness. -/
theorem trace_comp_cech_ne_zero (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) :
    τ.comp literalCechCanonicalEquiv.toLinearMap ≠ 0 := by
  intro hz
  apply hτ
  ext x
  obtain ⟨z, rfl⟩ := literalCechCanonicalEquiv.surjective x
  exact congrArg (fun f : DegreeOneCech 57 1 →ₗ[ℂ] ℂ => f z) hz

/-- Every nonzero linear functional on the complete actual H¹(Ω) is
injective; the conclusion concerns the intrinsic complex action. -/
theorem nonzero_canonical_trace_injective
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) : Function.Injective τ := by
  intro x y hxy
  apply literalCechCanonicalEquiv.symm.injective
  apply nonzero_trace_injective (τ.comp literalCechCanonicalEquiv.toLinearMap)
    (trace_comp_cech_ne_zero τ hτ)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.apply_symm_apply] using hxy

/-- Nonzero functionals on the actual canonical cohomology differ by
one common nonzero complex scalar. -/
theorem nonzero_canonical_traces_proportional
    (τ σ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    ∃ a : ℂ, a ≠ 0 ∧ τ = a • σ := by
  obtain ⟨a, ha, heq⟩ := nonzero_traces_proportional
    (τ.comp literalCechCanonicalEquiv.toLinearMap)
    (σ.comp literalCechCanonicalEquiv.toLinearMap)
    (trace_comp_cech_ne_zero τ hτ) (trace_comp_cech_ne_zero σ hσ)
  refine ⟨a, ha, ?_⟩
  ext x
  obtain ⟨z, rfl⟩ := literalCechCanonicalEquiv.surjective x
  exact congrArg (fun f : DegreeOneCech 57 1 →ₗ[ℂ] ℂ => f z) heq

/-- Trace normalization has no effect on the kernel of any linear map
into the complete actual canonical cohomology line. -/
theorem canonical_trace_kernel_independent {V : Type*} [AddCommGroup V] [Module ℂ V]
    (f : V →ₗ[ℂ] DifferentialSheafH1 57 1)
    (τ σ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) (hσ : σ ≠ 0) :
    LinearMap.ker (τ.comp f) = LinearMap.ker (σ.comp f) := by
  ext v
  change τ (f v) = 0 ↔ σ (f v) = 0
  constructor
  · intro hv
    have hz : f v = 0 := nonzero_canonical_trace_injective τ hτ
      (hv.trans (map_zero τ).symm)
    rw [hz, map_zero]
  · intro hv
    have hz : f v = 0 := nonzero_canonical_trace_injective σ hσ
      (hv.trans (map_zero σ).symm)
    rw [hz, map_zero]

/-- The original paired degree-nine numerator, transported through our
fixed actual canonical isomorphism. -/
def literalPairedCanonicalLinear : (Fin 9 → ℂ) →ₗ[ℂ] DifferentialSheafH1 57 1 :=
  literalCechCanonicalEquiv.toLinearMap.comp pairedClassLinear

@[simp] theorem literalPairedCanonicalLinear_apply (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v = literalCanonicalH1Equiv
      (degreeOneToProjectiveH1 57 1 (by norm_num) (pairedDegreeOneClass 57 1 v)) :=
  literalCechCanonicalEquiv_apply (pairedDegreeOneClass 57 1 v)

/-- The exact original paired-class coefficient now holds in the full
actual derived cohomology of Ω, with the displayed normalization. -/
theorem literalPairedCanonicalLinear_eq (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v =
      (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • literalCanonicalNormalization := by
  change literalCechCanonicalEquiv (pairedDegreeOneClass 57 1 v) = _
  exact ((congrArg literalCechCanonicalEquiv
    (pairedClass_eq_derivativeTrace_smul_normalization v)).trans
      (literalCechCanonicalEquiv.map_smul _ _)).trans
        (congrArg (fun z : DifferentialSheafH1 57 1 =>
          (((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v) • z)
          literalCechCanonicalEquiv_normalization)

theorem literalCanonicalCoordinate_paired (v : Fin 9 → ℂ) :
    literalCanonicalCoordinate (literalPairedCanonicalLinear v) =
      ((12 + 24 * Complex.I) / 5) * derivativeTrace 1 v := by
  rw [literalPairedCanonicalLinear_eq, map_smul,
    literalCanonicalCoordinate_normalization, smul_eq_mul, mul_one]

theorem literalPairedCanonicalLinear_eq_zero_iff (v : Fin 9 → ℂ) :
    literalPairedCanonicalLinear v = 0 ↔ derivativeTrace 1 v = 0 := by
  constructor
  · intro hz
    have hc : pairedDegreeOneClass 57 1 v = 0 :=
      literalCechCanonicalEquiv.injective (hz.trans (map_zero literalCechCanonicalEquiv).symm)
    exact (pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero v).mp hc
  · intro hz
    have hc := (pairedDegreeOneClass_eq_zero_iff_derivativeTrace_zero v).mpr hz
    change literalCechCanonicalEquiv (pairedDegreeOneClass 57 1 v) = 0
    rw [hc, map_zero]

/-- Every functional on actual canonical H¹ gives the two-entry row
with one common scalar, fixed by its value on the canonical normalization. -/
theorem literal_paired_trace_formula
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (v : Fin 9 → ℂ) :
    τ (literalPairedCanonicalLinear v) =
      (((12 + 24 * Complex.I) / 5) * τ literalCanonicalNormalization) *
        ((Complex.I * v 1 - (1 + Complex.I) * v 8) / 6) := by
  rw [literalPairedCanonicalLinear_eq, map_smul, smul_eq_mul, smooth_derivativeTrace_explicit]
  ring

theorem literal_paired_trace_scale_ne_zero
    (τ : DifferentialSheafH1 57 1 →ₗ[ℂ] ℂ) (hτ : τ ≠ 0) :
    (((12 + 24 * Complex.I) / 5) * τ literalCanonicalNormalization) ≠ 0 := by
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    literalCechCanonicalEquiv_normalization] using
      paired_trace_scale_ne_zero (τ.comp literalCechCanonicalEquiv.toLinearMap)
        (trace_comp_cech_ne_zero τ hτ)

#print axioms degreeOneCechHOneLinearEquiv
#print axioms literalCanonicalH1Equiv_smul
#print axioms literalCanonicalNormalizationEquiv
#print axioms literalDifferentialSheafH1_finrank
#print axioms canonical_trace_kernel_independent
#print axioms literalCanonicalCoordinate_paired
#print axioms literalPairedCanonicalLinear_eq_zero_iff
#print axioms literal_paired_trace_scale_ne_zero

end CycleQ2GeometricLiteralHOne
end

end RetainedGeometryPart03
