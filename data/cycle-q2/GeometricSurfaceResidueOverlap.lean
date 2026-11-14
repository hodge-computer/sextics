import Proposal.GeometricSurfaceAdjunction
import Proposal.GeometricSurfaceResidueFunctoriality
import Mathlib.Tactic.Ring
import Proposal.GeometricSurfaceDehomogenizedCharts
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Proposal.GeometricSurfaceOverlap
import Proposal.GeometricExteriorSheaf
import Proposal.GeometricSurfaceNormalCharts
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Grp.Limits

section

/-!
# The literal ambient surface overlap and its differential volume

The polynomial ring is the actual four-variable ring of the surface
adjunction construction. Its normal coordinate is `z = f₂`. After
inverting the middle coordinate `b`, the coordinate substitution is
`(z,a,b,c) ↦ (z/b²,a/b,1/b,c/b)`. The map below is an actual algebra
homomorphism, and every differential is the universal Kähler differential
of this localization. This file concerns the ambient overlap; descent to
the surface quotient and projective gluing are separate constructions.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceOverlapVolume

open MvPolynomial Module
open CycleQ2GeometricSurfaceAdjunction
open scoped TensorProduct

def middle : SurfacePoly := X (some (1 : Fin 3))

abbrev AmbientOverlap := Localization.Away middle

def polynomialMap : SurfacePoly →ₐ[ℂ] AmbientOverlap :=
  IsScalarTower.toAlgHom ℂ SurfacePoly AmbientOverlap

def coordinate (j : Option (Fin 3)) : AmbientOverlap := polynomialMap (X j)

def middleUnit : AmbientOverlapˣ :=
  (IsLocalization.Away.algebraMap_isUnit middle).unit

@[simp] theorem middleUnit_val : (middleUnit : AmbientOverlap) = coordinate (some 1) :=
  (IsLocalization.Away.algebraMap_isUnit middle).unit_spec

def inverse : AmbientOverlap := ↑(middleUnit⁻¹)

@[simp] theorem coordinate_mul_inverse : coordinate (some 1) * inverse = 1 := by
  rw [← middleUnit_val]
  exact middleUnit.mul_inv

@[simp] theorem inverse_mul_coordinate : inverse * coordinate (some 1) = 1 := by
  rw [mul_comm]
  exact coordinate_mul_inverse

@[simp] theorem inverse_pow_mul_coordinate_pow (n : ℕ) :
    inverse ^ n * coordinate (some 1) ^ n = 1 := by
  rw [← mul_pow, inverse_mul_coordinate, one_pow]

theorem coordinate_algHom_ext {S : Type*} [CommSemiring S] [Algebra ℂ S]
    {f g : AmbientOverlap →ₐ[ℂ] S}
    (h : ∀ j, f (coordinate j) = g (coordinate j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers middle)
  apply MvPolynomial.algHom_ext
  exact h

/-- Pullback from the second literal coordinate chart to the first,
before imposing either surface equation. -/
def changeEvaluation : SurfacePoly →ₐ[ℂ] AmbientOverlap :=
  aeval (fun j => match j with
    | none => coordinate none * inverse ^ 2
    | some i => ![coordinate (some 0) * inverse, inverse,
        coordinate (some 2) * inverse] i)

@[simp] theorem changeEvaluation_normal :
    changeEvaluation (X none) = coordinate none * inverse ^ 2 := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_first :
    changeEvaluation (X (some 0)) = coordinate (some 0) * inverse := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_middle :
    changeEvaluation (X (some 1)) = inverse := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_last :
    changeEvaluation (X (some 2)) = coordinate (some 2) * inverse := by
  simp [changeEvaluation]

/-- The same literal substitution extends across the inverted middle
coordinate. -/
def overlapMap : AmbientOverlap →ₐ[ℂ] AmbientOverlap :=
  IsLocalization.liftAlgHom (M := Submonoid.powers middle)
    (f := changeEvaluation) (by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      apply IsUnit.pow n
      change IsUnit (changeEvaluation (X (some 1)))
      rw [changeEvaluation_middle]
      exact (middleUnit⁻¹).isUnit)

@[simp] theorem overlapMap_polynomial (p : SurfacePoly) :
    overlapMap (polynomialMap p) = changeEvaluation p := by
  change IsLocalization.lift _ (algebraMap SurfacePoly AmbientOverlap p) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp] theorem overlapMap_coordinate (j : Option (Fin 3)) :
    overlapMap (coordinate j) = changeEvaluation (X j) :=
  overlapMap_polynomial (X j)

@[simp] theorem overlapMap_inverse : overlapMap inverse = coordinate (some 1) := by
  have h := congrArg overlapMap coordinate_mul_inverse
  rw [map_mul, overlapMap_coordinate, changeEvaluation_middle, map_one] at h
  calc
    overlapMap inverse = coordinate (some 1) * (inverse * overlapMap inverse) := by
      rw [← mul_assoc, coordinate_mul_inverse, one_mul]
    _ = coordinate (some 1) := by rw [h, mul_one]

theorem overlapMap_involutive : Function.Involutive overlapMap := by
  have h : overlapMap.comp overlapMap = AlgHom.id ℂ AmbientOverlap := by
    apply coordinate_algHom_ext
    intro j
    change overlapMap (overlapMap (coordinate j)) = coordinate j
    cases j with
    | none => simp [map_mul, map_pow, mul_assoc]
    | some i => fin_cases i <;> simp [map_mul, mul_assoc]
  exact fun x => AlgHom.congr_fun h x

/-- An actual algebra equivalence of the two ambient overlap coordinate
descriptions. Its inverse is the same coordinate substitution. -/
def overlapEquiv : AmbientOverlap ≃ₐ[ℂ] AmbientOverlap :=
  { overlapMap with
    invFun := overlapMap
    left_inv := overlapMap_involutive
    right_inv := overlapMap_involutive }

abbrev Differential := KaehlerDifferential ℂ AmbientOverlap

def dCoordinate (j : Option (Fin 3)) : Differential :=
  KaehlerDifferential.D ℂ AmbientOverlap (coordinate j)

theorem differential_inverse :
    KaehlerDifferential.D ℂ AmbientOverlap inverse =
      -(inverse ^ 2) • dCoordinate (some 1) :=
  (KaehlerDifferential.D ℂ AmbientOverlap).leibniz_of_mul_eq_one inverse_mul_coordinate

theorem differential_change_normal :
    KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X none)) =
      inverse ^ 2 • dCoordinate none -
        (2 * coordinate none * inverse ^ 3) • dCoordinate (some 1) := by
  rw [changeEvaluation_normal, Derivation.leibniz, Derivation.leibniz_pow,
    differential_inverse]
  change coordinate none • ((2 : ℕ) • inverse ^ (2 - 1) •
      (-(inverse ^ 2) • dCoordinate (some 1))) +
      inverse ^ 2 • dCoordinate none = _
  norm_num only [Nat.reduceSub, pow_one]
  rw [← Nat.cast_smul_eq_nsmul AmbientOverlap]
  simp only [Nat.cast_ofNat, smul_smul]
  have h : coordinate none * ((2 : AmbientOverlap) * (inverse * -(inverse ^ 2))) =
      -(2 * coordinate none * inverse ^ 3) := by ring
  rw [h, neg_smul, sub_eq_add_neg, add_comm]

theorem differential_change_first :
    KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 0))) =
      inverse • dCoordinate (some 0) -
        (coordinate (some 0) * inverse ^ 2) • dCoordinate (some 1) := by
  rw [changeEvaluation_first, Derivation.leibniz, differential_inverse]
  change coordinate (some 0) • (-(inverse ^ 2) • dCoordinate (some 1)) +
      inverse • dCoordinate (some 0) = _
  simp only [neg_smul, smul_neg, smul_smul, sub_eq_add_neg, add_comm]

theorem differential_change_middle :
    KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 1))) =
      -(inverse ^ 2) • dCoordinate (some 1) := by
  rw [changeEvaluation_middle, differential_inverse]

theorem differential_change_last :
    KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 2))) =
      inverse • dCoordinate (some 2) -
        (coordinate (some 2) * inverse ^ 2) • dCoordinate (some 1) := by
  rw [changeEvaluation_last, Derivation.leibniz, differential_inverse]
  change coordinate (some 2) • (-(inverse ^ 2) • dCoordinate (some 1)) +
      inverse • dCoordinate (some 2) = _
  simp only [neg_smul, smul_neg, smul_smul, sub_eq_add_neg, add_comm]

/-- The actual Kähler localization theorem supplies the basis comparison. -/
def localizedDifferentialEquiv :
    AmbientOverlap ⊗[SurfacePoly] KaehlerDifferential ℂ SurfacePoly ≃ₗ[AmbientOverlap]
      Differential := by
  letI : Algebra.FormallyEtale SurfacePoly AmbientOverlap :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := AmbientOverlap) (Submonoid.powers middle)
  exact KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ SurfacePoly AmbientOverlap

@[simp] theorem localizedDifferentialEquiv_tmul_D (p : SurfacePoly) :
    localizedDifferentialEquiv
      ((1 : AmbientOverlap) ⊗ₜ[SurfacePoly] KaehlerDifferential.D ℂ SurfacePoly p) =
      KaehlerDifferential.D ℂ AmbientOverlap (polynomialMap p) := by
  change KaehlerDifferential.mapBaseChange ℂ SurfacePoly AmbientOverlap _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

/-- The genuine differential basis has the incoming adjunction order
`(dz,da,db,dc)`. -/
def differentialBasis : Basis (Fin 4) AmbientOverlap Differential :=
  (((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).baseChange AmbientOverlap).map
    localizedDifferentialEquiv).reindex (finSuccEquiv 3).symm

@[simp] theorem differentialBasis_apply (j : Fin 4) :
    differentialBasis j = dCoordinate (finSuccEquiv 3 j) := by
  simp only [differentialBasis, Basis.reindex_apply, Equiv.symm_symm, Basis.map_apply,
    Basis.baseChange_apply, KaehlerDifferential.mvPolynomialBasis_apply,
    localizedDifferentialEquiv_tmul_D, dCoordinate, coordinate]

def changedDifferentials (j : Fin 4) : Differential :=
  KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (finSuccEquiv 3 j)))

def changeMatrix : Matrix (Fin 4) (Fin 4) AmbientOverlap :=
  !![inverse ^ 2, 0, 0, 0;
     0, inverse, 0, 0;
     -(2 * coordinate none * inverse ^ 3), -(coordinate (some 0) * inverse ^ 2),
       -(inverse ^ 2), -(coordinate (some 2) * inverse ^ 2);
     0, 0, 0, inverse]

theorem differential_coordinate_matrix : differentialBasis.toMatrix changedDifferentials =
    changeMatrix := by
  have hn : dCoordinate none = differentialBasis 0 := (differentialBasis_apply 0).symm
  have ha : dCoordinate (some 0) = differentialBasis 1 := (differentialBasis_apply 1).symm
  have hb : dCoordinate (some 1) = differentialBasis 2 := (differentialBasis_apply 2).symm
  have hc : dCoordinate (some 2) = differentialBasis 3 := (differentialBasis_apply 3).symm
  have hfamily : changedDifferentials =
      ![inverse ^ 2 • differentialBasis 0 -
          (2 * coordinate none * inverse ^ 3) • differentialBasis 2,
        inverse • differentialBasis 1 -
          (coordinate (some 0) * inverse ^ 2) • differentialBasis 2,
        -(inverse ^ 2) • differentialBasis 2,
        inverse • differentialBasis 3 -
          (coordinate (some 2) * inverse ^ 2) • differentialBasis 2] := by
    funext j
    fin_cases j
    · change KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X none)) = _
      rw [differential_change_normal, hn, hb]
      rfl
    · change KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 0))) = _
      rw [differential_change_first, ha, hb]
      rfl
    · change KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 1))) = _
      rw [differential_change_middle, hb]
      rfl
    · change KaehlerDifferential.D ℂ AmbientOverlap (changeEvaluation (X (some 2))) = _
      rw [differential_change_last, hc, hb]
      rfl
  rw [hfamily]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-differentialBasis_apply, Basis.toMatrix, changeMatrix]

theorem changeMatrix_det : changeMatrix.det = -(inverse ^ 6) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, changeMatrix, Matrix.det_fin_three]
  ring

theorem differential_coordinate_determinant :
    (differentialBasis.toMatrix changedDifferentials).det = -(inverse ^ 6) := by
  rw [differential_coordinate_matrix, changeMatrix_det]

/-- The actual ambient volume in the fixed incoming order `(z,a,b,c)`. -/
def ambientVolume : ⋀[AmbientOverlap]^4 Differential :=
  exteriorPower.ιMulti AmbientOverlap 4 differentialBasis

/-- The pullback of the four coordinate differentials multiplies the actual
ambient volume by `−b⁻⁶`. -/
theorem differential_volume_change :
    exteriorPower.ιMulti AmbientOverlap 4 changedDifferentials =
      -(inverse ^ 6) • ambientVolume := by
  rw [CycleQ2ResidueWedgeLinear.topWedge_eq_det_smul differentialBasis,
    differential_coordinate_determinant]
  rfl

section UniversalExteriorPullback

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The value of the genuine exterior power of the universal differential
base-change map. The source scalar action is induced by the specified
algebra homomorphism. -/
def exteriorDifferentialPullback (f : A →ₐ[ℂ] B) {n : ℕ} (v : Fin n → A) :
    ⋀[B]^n (KaehlerDifferential ℂ B) := by
  letI := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algHom f
  exact exteriorPower.map n (KaehlerDifferential.mapBaseChange ℂ A B)
    (exteriorPower.ιMulti B n
      (fun j => (1 : B) ⊗ₜ[A] KaehlerDifferential.D ℂ A (v j)))

theorem exteriorDifferentialPullback_eq (f : A →ₐ[ℂ] B) {n : ℕ} (v : Fin n → A) :
    exteriorDifferentialPullback f v = exteriorPower.ιMulti B n
      (fun j => KaehlerDifferential.D ℂ B (f (v j))) := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algHom f
  change exteriorPower.map n (KaehlerDifferential.mapBaseChange ℂ A B)
    (exteriorPower.ιMulti B n
      (fun j => (1 : B) ⊗ₜ[A] KaehlerDifferential.D ℂ A (v j))) = _
  rw [exteriorPower.map_apply_ιMulti]
  congr 1
  funext j
  rw [Function.comp_apply, KaehlerDifferential.mapBaseChange_tmul,
    one_smul, KaehlerDifferential.map_D]
  rfl

end UniversalExteriorPullback

/-- The actual exterior pullback of the polynomial coordinate volume is
`−b⁻⁶` times the original ambient overlap volume. -/
theorem polynomial_exterior_pullback :
    exteriorDifferentialPullback changeEvaluation
      (fun j : Fin 4 => X (finSuccEquiv 3 j)) =
      -(inverse ^ 6) • ambientVolume := by
  rw [exteriorDifferentialPullback_eq]
  exact differential_volume_change

end CycleQ2SurfaceOverlapVolume

end

end


section

/-!
# The literal localized surface coordinate overlap

The weighted coordinate identity is proved before passing to either
surface quotient. It gives the exact degree-six and degree-three scaling
of the two defining equations. These identities construct mutually
inverse algebra maps between the actual localized affine surface rings.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceAffineOverlap

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2GeometricSurfaceAdjunction
open CycleQ2CartierSurfaceGrading

namespace Volume

open CycleQ2SurfaceOverlapVolume

/-- The weighted substitution is the composite of the literal second
dehomogenization with the actual ambient overlap map. -/
theorem dehomogenization_change_map :
    changeEvaluation.comp secondSurfaceDehomogenize =
      aeval (fun k : Fin 5 => inverse ^ weight k *
        polynomialMap (firstSurfaceDehomogenize (X k))) := by
  apply MvPolynomial.algHom_ext
  intro k
  have hcoordinate (j : Option (Fin 3)) : polynomialMap (X j) = coordinate j := rfl
  fin_cases k <;>
    simp [AlgHom.comp_apply, firstSurfaceDehomogenize, secondSurfaceDehomogenize,
      changeEvaluation, weight, hcoordinate, mul_sub, mul_comm]

theorem first_dehomogenization_evaluation :
    aeval (fun k : Fin 5 => polynomialMap (firstSurfaceDehomogenize (X k))) =
      polynomialMap.comp firstSurfaceDehomogenize := by
  apply MvPolynomial.algHom_ext
  intro k
  simp

/-- A degree-n weighted polynomial acquires precisely the factor b⁻ⁿ. -/
theorem homogeneous_change (p : WeightedPoly) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    changeEvaluation (secondSurfaceDehomogenize p) =
      inverse ^ n * polynomialMap (firstSurfaceDehomogenize p) := by
  change (changeEvaluation.comp secondSurfaceDehomogenize) p = _
  rw [dehomogenization_change_map]
  have hs : aeval (fun k : Fin 5 => inverse ^ weight k *
        polynomialMap (firstSurfaceDehomogenize (X k))) p =
      inverse ^ n * aeval (fun k : Fin 5 =>
        polynomialMap (firstSurfaceDehomogenize (X k))) p :=
    CycleQ2GeometricSurfaceDehomogenizedCharts.weighted_homogeneous_eval_scale
      (algebraMap ℂ AmbientOverlap)
      (fun k => polynomialMap (firstSurfaceDehomogenize (X k))) inverse p n hp
  rw [hs, first_dehomogenization_evaluation]
  rfl

theorem overlapMap_changeEvaluation (p : SurfacePoly) :
    overlapMap (changeEvaluation p) = polynomialMap p := by
  rw [← overlapMap_polynomial]
  exact overlapMap_involutive _

/-- Applying the actual involution gives the reverse equation scaling. -/
theorem homogeneous_reverse_change (p : WeightedPoly) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    changeEvaluation (firstSurfaceDehomogenize p) =
      inverse ^ n * polynomialMap (secondSurfaceDehomogenize p) := by
  have h := congrArg overlapMap (homogeneous_change p hp)
  rw [overlapMap_changeEvaluation, map_mul, map_pow,
    overlapMap_inverse, overlapMap_polynomial] at h
  calc
    changeEvaluation (firstSurfaceDehomogenize p) =
        inverse ^ n * (coordinate (some 1) ^ n *
          changeEvaluation (firstSurfaceDehomogenize p)) := by
      rw [← mul_assoc, inverse_pow_mul_coordinate_pow, one_mul]
    _ = inverse ^ n * polynomialMap (secondSurfaceDehomogenize p) := by rw [← h]

theorem surface_equation_change (r θ : ℂ) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 0) =
      inverse ^ 6 * polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 0) := by
  simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations,
    CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations, Matrix.cons_val_zero,
    firstSurfaceDehomogenize_equation, secondSurfaceDehomogenize_equation] using
      homogeneous_change (actualSeedEquation r θ) (actualSeedEquation_homogeneous r θ)

theorem cubic_equation_change (r θ : ℂ) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 1) =
      inverse ^ 3 * polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 1) := by
  simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations,
    CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations, Matrix.cons_val_one, Matrix.cons_val_zero,
    firstSurfaceDehomogenize_h, secondSurfaceDehomogenize_h] using
      homogeneous_change (thetaH θ) (thetaH_homogeneous θ)

theorem surface_equation_reverse_change (r θ : ℂ) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 0) =
      inverse ^ 6 * polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 0) := by
  simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations,
    CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations, Matrix.cons_val_zero,
    firstSurfaceDehomogenize_equation, secondSurfaceDehomogenize_equation] using
      homogeneous_reverse_change (actualSeedEquation r θ) (actualSeedEquation_homogeneous r θ)

theorem cubic_equation_reverse_change (r θ : ℂ) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 1) =
      inverse ^ 3 * polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 1) := by
  simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations,
    CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations, Matrix.cons_val_one, Matrix.cons_val_zero,
    firstSurfaceDehomogenize_h, secondSurfaceDehomogenize_h] using
      homogeneous_reverse_change (thetaH θ) (thetaH_homogeneous θ)

/-- The literal volume factor and the two equation factors give the
raw residue factor `−b³`. -/
theorem raw_residue_scaling :
    -(coordinate (some 1) ^ 3) * (inverse ^ 6 * inverse ^ 3) = -(inverse ^ 6) := by
  calc
    -(coordinate (some 1) ^ 3) * (inverse ^ 6 * inverse ^ 3) =
        -(inverse ^ 6 * (inverse ^ 3 * coordinate (some 1) ^ 3)) := by ring
    _ = -(inverse ^ 6) := by rw [inverse_pow_mul_coordinate_pow, mul_one]

end Volume

def chartMap (v : Fin 2 → SurfacePoly) : SurfacePoly →ₐ[ℂ] SurfaceChartRing v :=
  Ideal.Quotient.mkₐ ℂ (surfaceChartIdeal v)

def middle (v : Fin 2 → SurfacePoly) : SurfaceChartRing v :=
  chartMap v (X (some 1))

abbrev ChartOverlap (v : Fin 2 → SurfacePoly) := Localization.Away (middle v)

def polynomialMap (v : Fin 2 → SurfacePoly) : SurfacePoly →ₐ[ℂ] ChartOverlap v :=
  (IsScalarTower.toAlgHom ℂ (SurfaceChartRing v) (ChartOverlap v)).comp (chartMap v)

def coordinate (v : Fin 2 → SurfacePoly) (j : Option (Fin 3)) : ChartOverlap v :=
  polynomialMap v (X j)

def middleUnit (v : Fin 2 → SurfacePoly) : (ChartOverlap v)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (middle v)).unit

@[simp] theorem middleUnit_val (v : Fin 2 → SurfacePoly) :
    (middleUnit v : ChartOverlap v) = coordinate v (some 1) :=
  (IsLocalization.Away.algebraMap_isUnit (middle v)).unit_spec

def inverse (v : Fin 2 → SurfacePoly) : ChartOverlap v := ↑((middleUnit v)⁻¹)

@[simp] theorem coordinate_mul_inverse (v : Fin 2 → SurfacePoly) :
    coordinate v (some 1) * inverse v = 1 := by
  rw [← middleUnit_val]
  exact (middleUnit v).mul_inv

@[simp] theorem inverse_mul_coordinate (v : Fin 2 → SurfacePoly) :
    inverse v * coordinate v (some 1) = 1 := by
  rw [mul_comm]
  exact coordinate_mul_inverse v

@[simp] theorem inverse_pow_mul_coordinate_pow (v : Fin 2 → SurfacePoly) (n : ℕ) :
    inverse v ^ n * coordinate v (some 1) ^ n = 1 := by
  rw [← mul_pow, inverse_mul_coordinate, one_pow]

theorem polynomialMap_relation (v : Fin 2 → SurfacePoly) (i : Fin 2) :
    polynomialMap v (v i) = 0 := by
  have h : chartMap v (v i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  change algebraMap (SurfaceChartRing v) (ChartOverlap v) (chartMap v (v i)) = 0
  rw [h, map_zero]

/-- The canonical map from the actual ambient localization to the actual
localized surface quotient. -/
def ambientMap (v : Fin 2 → SurfacePoly) :
    CycleQ2SurfaceOverlapVolume.AmbientOverlap →ₐ[ℂ] ChartOverlap v :=
  IsLocalization.liftAlgHom
    (M := Submonoid.powers CycleQ2SurfaceOverlapVolume.middle)
    (f := polynomialMap v) (by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      apply IsUnit.pow n
      exact IsLocalization.Away.algebraMap_isUnit (middle v))

@[simp] theorem ambientMap_polynomial (v : Fin 2 → SurfacePoly) (p : SurfacePoly) :
    ambientMap v (CycleQ2SurfaceOverlapVolume.polynomialMap p) = polynomialMap v p := by
  change IsLocalization.lift _
    (algebraMap SurfacePoly CycleQ2SurfaceOverlapVolume.AmbientOverlap p) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp] theorem ambientMap_coordinate (v : Fin 2 → SurfacePoly) (j : Option (Fin 3)) :
    ambientMap v (CycleQ2SurfaceOverlapVolume.coordinate j) = coordinate v j :=
  ambientMap_polynomial v (X j)

@[simp] theorem ambientMap_inverse (v : Fin 2 → SurfacePoly) :
    ambientMap v CycleQ2SurfaceOverlapVolume.inverse = inverse v := by
  have h := congrArg (ambientMap v) CycleQ2SurfaceOverlapVolume.coordinate_mul_inverse
  rw [map_mul, ambientMap_coordinate, map_one] at h
  calc
    ambientMap v CycleQ2SurfaceOverlapVolume.inverse =
        inverse v * (coordinate v (some 1) *
          ambientMap v CycleQ2SurfaceOverlapVolume.inverse) := by
      rw [← mul_assoc, inverse_mul_coordinate, one_mul]
    _ = inverse v := by rw [h, mul_one]

def changeEvaluation (v : Fin 2 → SurfacePoly) : SurfacePoly →ₐ[ℂ] ChartOverlap v :=
  (ambientMap v).comp CycleQ2SurfaceOverlapVolume.changeEvaluation

@[simp] theorem changeEvaluation_normal (v : Fin 2 → SurfacePoly) :
    changeEvaluation v (X none) = coordinate v none * inverse v ^ 2 := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_first (v : Fin 2 → SurfacePoly) :
    changeEvaluation v (X (some 0)) = coordinate v (some 0) * inverse v := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_middle (v : Fin 2 → SurfacePoly) :
    changeEvaluation v (X (some 1)) = inverse v := by
  simp [changeEvaluation]

@[simp] theorem changeEvaluation_last (v : Fin 2 → SurfacePoly) :
    changeEvaluation v (X (some 2)) = coordinate v (some 2) * inverse v := by
  simp [changeEvaluation]

def quotientLift (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) : SurfaceChartRing v →ₐ[ℂ] ChartOverlap w :=
  Ideal.Quotient.liftₐ (surfaceChartIdeal v) (changeEvaluation w) (by
    change surfaceChartIdeal v ≤ RingHom.ker (changeEvaluation w).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i)

def localizationLift (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) : ChartOverlap v →ₐ[ℂ] ChartOverlap w :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (middle v))
    (f := quotientLift v w h) (by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      apply IsUnit.pow n
      change IsUnit (changeEvaluation w (X (some 1)))
      rw [changeEvaluation_middle]
      exact ((middleUnit w)⁻¹).isUnit)

@[simp] theorem localizationLift_polynomialMap (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) (p : SurfacePoly) :
    localizationLift v w h (polynomialMap v p) = changeEvaluation w p := by
  change IsLocalization.lift _ (algebraMap (SurfaceChartRing v) (ChartOverlap v)
    (chartMap v p)) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp] theorem localizationLift_coordinate (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) (j : Option (Fin 3)) :
    localizationLift v w h (coordinate v j) = changeEvaluation w (X j) :=
  localizationLift_polynomialMap v w h (X j)

@[simp] theorem localizationLift_inverse (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) :
    localizationLift v w h (inverse v) = coordinate w (some 1) := by
  have hh := congrArg (localizationLift v w h) (coordinate_mul_inverse v)
  rw [map_mul, localizationLift_coordinate, changeEvaluation_middle, map_one] at hh
  calc
    localizationLift v w h (inverse v) = coordinate w (some 1) *
        (inverse w * localizationLift v w h (inverse v)) := by
      rw [← mul_assoc, coordinate_mul_inverse, one_mul]
    _ = coordinate w (some 1) := by rw [hh, mul_one]

theorem coordinate_algHom_ext (v : Fin 2 → SurfacePoly)
    {S : Type*} [CommSemiring S] [Algebra ℂ S] {f g : ChartOverlap v →ₐ[ℂ] S}
    (h : ∀ j, f (coordinate v j) = g (coordinate v j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middle v))
  apply Ideal.Quotient.algHom_ext ℂ
  apply MvPolynomial.algHom_ext
  exact h

theorem localizationLift_inverse_comp (v w : Fin 2 → SurfacePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0)
    (h' : ∀ i, changeEvaluation v (w i) = 0) :
    (localizationLift w v h').comp (localizationLift v w h) = AlgHom.id ℂ (ChartOverlap v) := by
  apply coordinate_algHom_ext v
  intro j
  cases j with
  | none => simp [map_mul, map_pow, mul_assoc]
  | some i => fin_cases i <;> simp [map_mul, mul_assoc]

abbrev FirstOverlap (r θ : ℂ) :=
  ChartOverlap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)

abbrev SecondOverlap (r θ : ℂ) :=
  ChartOverlap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)

theorem second_relations_change_zero (r θ : ℂ) (i : Fin 2) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ i) = 0 := by
  fin_cases i
  · change ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)
      (CycleQ2SurfaceOverlapVolume.changeEvaluation
        (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 0)) = 0
    rw [Volume.surface_equation_change r θ, map_mul, ambientMap_polynomial,
      polynomialMap_relation, mul_zero]
  · change ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)
      (CycleQ2SurfaceOverlapVolume.changeEvaluation
        (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ 1)) = 0
    rw [Volume.cubic_equation_change r θ, map_mul, ambientMap_polynomial,
      polynomialMap_relation, mul_zero]

theorem first_relations_change_zero (r θ : ℂ) (i : Fin 2) :
    changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ i) = 0 := by
  fin_cases i
  · change ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
      (CycleQ2SurfaceOverlapVolume.changeEvaluation
        (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 0)) = 0
    rw [Volume.surface_equation_reverse_change r θ, map_mul, ambientMap_polynomial,
      polynomialMap_relation, mul_zero]
  · change ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
      (CycleQ2SurfaceOverlapVolume.changeEvaluation
        (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ 1)) = 0
    rw [Volume.cubic_equation_reverse_change r θ, map_mul, ambientMap_polynomial,
      polynomialMap_relation, mul_zero]

def secondToFirst (r θ : ℂ) : SecondOverlap r θ →ₐ[ℂ] FirstOverlap r θ :=
  localizationLift _ _ (second_relations_change_zero r θ)

def firstToSecond (r θ : ℂ) : FirstOverlap r θ →ₐ[ℂ] SecondOverlap r θ :=
  localizationLift _ _ (first_relations_change_zero r θ)

/-- The actual localized surface quotient rings are isomorphic by the
literal weighted coordinate change. Both parameters remain arbitrary. -/
def overlapEquiv (r θ : ℂ) : SecondOverlap r θ ≃ₐ[ℂ] FirstOverlap r θ :=
  { secondToFirst r θ with
    invFun := firstToSecond r θ
    left_inv := fun x => AlgHom.congr_fun
      (localizationLift_inverse_comp _ _ (second_relations_change_zero r θ)
        (first_relations_change_zero r θ)) x
    right_inv := fun x => AlgHom.congr_fun
      (localizationLift_inverse_comp _ _ (first_relations_change_zero r θ)
        (second_relations_change_zero r θ)) x }

@[simp] theorem overlapEquiv_polynomialMap (r θ : ℂ) (p : SurfacePoly) :
    overlapEquiv r θ (polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ) p) =
      changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ) p :=
  localizationLift_polynomialMap _ _ _ p

/-- The quotient overlap map is genuinely induced by the constructed
ambient overlap involution. -/
theorem overlapEquiv_ambientMap (r θ : ℂ) :
    (overlapEquiv r θ).toAlgHom.comp
        (ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)) =
      (ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)).comp
        CycleQ2SurfaceOverlapVolume.overlapMap := by
  apply CycleQ2SurfaceOverlapVolume.coordinate_algHom_ext
  intro j
  change overlapEquiv r θ
      (ambientMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
        (CycleQ2SurfaceOverlapVolume.coordinate j)) = _
  rw [ambientMap_coordinate]
  change overlapEquiv r θ (polynomialMap _ (X j)) = _
  rw [overlapEquiv_polynomialMap]
  simp only [changeEvaluation, AlgHom.comp_apply, CycleQ2SurfaceOverlapVolume.overlapMap_coordinate]

/-- Every actual weighted homogeneous function has the expected overlap
coordinate, not only the two defining equations. -/
theorem overlapEquiv_dehomogenization (r θ : ℂ) (p : WeightedPoly) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    overlapEquiv r θ
        (polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
          (secondSurfaceDehomogenize p)) =
      inverse (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ) ^ n *
        polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)
          (firstSurfaceDehomogenize p) := by
  rw [overlapEquiv_polynomialMap]
  change ambientMap _ (CycleQ2SurfaceOverlapVolume.changeEvaluation _) = _
  rw [Volume.homogeneous_change p hp, map_mul, map_pow,
    ambientMap_inverse, ambientMap_polynomial]

@[simp] theorem overlapEquiv_symm_polynomialMap (r θ : ℂ) (p : SurfacePoly) :
    (overlapEquiv r θ).symm
        (polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ) p) =
      changeEvaluation (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ) p :=
  localizationLift_polynomialMap _ _ _ p

theorem overlapEquiv_symm_dehomogenization (r θ : ℂ) (p : WeightedPoly) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    (overlapEquiv r θ).symm
        (polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.firstEquations r θ)
          (firstSurfaceDehomogenize p)) =
      inverse (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ) ^ n *
        polynomialMap (CycleQ2GeometricSurfaceDehomogenizedCharts.secondEquations r θ)
          (secondSurfaceDehomogenize p) := by
  rw [overlapEquiv_symm_polynomialMap]
  change ambientMap _ (CycleQ2SurfaceOverlapVolume.changeEvaluation _) = _
  rw [Volume.homogeneous_reverse_change p hp, map_mul, map_pow,
    ambientMap_inverse, ambientMap_polynomial]

end CycleQ2SurfaceAffineOverlap

end

end


section

/-!
# Actual ambient differentials restricted to the surface overlap

The module is the tensor product of the ambient Kähler module of
rank four with the first localized surface ring. The two conormal
vectors therefore remain present. Literal equation scaling and quotient
vanishing remove only the extra Leibniz terms. The volume is transported
by the actual tensor map on every wedge.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceOverlapConormal

open Module MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2SurfaceAffineOverlap CycleQ2ExteriorTopBaseChange
open scoped TensorProduct

abbrev AmbientRing := CycleQ2SurfaceOverlapVolume.AmbientOverlap
abbrev AmbientDifferentials := KaehlerDifferential ℂ AmbientRing

/-- The scalar action is induced by the actual localized quotient map. -/
@[instance_reducible]
def firstAmbientAlgebra (r θ : ℂ) : Algebra AmbientRing (FirstOverlap r θ) :=
  (ambientMap (firstEquations r θ)).toRingHom.toAlgebra

attribute [local instance] firstAmbientAlgebra

@[simp] theorem firstAmbientAlgebraMap (r θ : ℂ) (a : AmbientRing) :
    algebraMap AmbientRing (FirstOverlap r θ) a = ambientMap (firstEquations r θ) a := rfl

abbrev RestrictedAmbientDifferentials (r θ : ℂ) :=
  FirstOverlap r θ ⊗[AmbientRing] AmbientDifferentials

def restrictedAmbientBasis (r θ : ℂ) :
    Basis (Fin 4) (FirstOverlap r θ) (RestrictedAmbientDifferentials r θ) :=
  CycleQ2SurfaceOverlapVolume.differentialBasis.baseChange (FirstOverlap r θ)

@[simp] theorem restrictedAmbientBasis_apply (r θ : ℂ) (j : Fin 4) :
    restrictedAmbientBasis r θ j =
      (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing]
        CycleQ2SurfaceOverlapVolume.differentialBasis j := by
  simp only [restrictedAmbientBasis, Basis.baseChange_apply]

/-- This is the universal ambient differential followed by the literal
tensor inclusion. It is not a differential in the surface quotient. -/
def tensorD (r θ : ℂ) (a : AmbientRing) : RestrictedAmbientDifferentials r θ :=
  (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing a

theorem tensor_smul (r θ : ℂ) (a : AmbientRing) (m : AmbientDifferentials) :
    (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing] (a • m) =
      ambientMap (firstEquations r θ) a • ((1 : FirstOverlap r θ) ⊗ₜ[AmbientRing] m) := by
  rw [TensorProduct.tmul_smul]
  exact (IsScalarTower.algebraMap_smul (FirstOverlap r θ) a _).symm

theorem tensorD_mul (r θ : ℂ) (a b : AmbientRing) :
    tensorD r θ (a * b) =
      ambientMap (firstEquations r θ) a • tensorD r θ b +
        ambientMap (firstEquations r θ) b • tensorD r θ a := by
  simp only [tensorD, Derivation.leibniz, TensorProduct.tmul_add, tensor_smul]

theorem tensorD_mul_of_right_zero (r θ : ℂ) (a b : AmbientRing)
    (hb : ambientMap (firstEquations r θ) b = 0) :
    tensorD r θ (a * b) = ambientMap (firstEquations r θ) a • tensorD r θ b := by
  rw [tensorD_mul, hb, zero_smul, add_zero]

theorem first_equation_vanish (r θ : ℂ) (i : Fin 2) :
    ambientMap (firstEquations r θ)
        (CycleQ2SurfaceOverlapVolume.polynomialMap (firstEquations r θ i)) = 0 := by
  rw [ambientMap_polynomial, polynomialMap_relation]

/-- The transformed degree-six conormal vector in the retained ambient
module is exactly the inverse-sixth-power multiple of the first vector. -/
theorem surface_conormal_change (r θ : ℂ) :
    tensorD r θ
        (CycleQ2SurfaceOverlapVolume.changeEvaluation (secondEquations r θ 0)) =
      inverse (firstEquations r θ) ^ 6 • tensorD r θ
        (CycleQ2SurfaceOverlapVolume.polynomialMap (firstEquations r θ 0)) := by
  rw [Volume.surface_equation_change r θ,
    tensorD_mul_of_right_zero r θ _ _ (first_equation_vanish r θ 0),
    map_pow, ambientMap_inverse]

/-- The cubic conormal vector has its literal inverse-third-power factor. -/
theorem cubic_conormal_change (r θ : ℂ) :
    tensorD r θ
        (CycleQ2SurfaceOverlapVolume.changeEvaluation (secondEquations r θ 1)) =
      inverse (firstEquations r θ) ^ 3 • tensorD r θ
        (CycleQ2SurfaceOverlapVolume.polynomialMap (firstEquations r θ 1)) := by
  rw [Volume.cubic_equation_change r θ,
    tensorD_mul_of_right_zero r θ _ _ (first_equation_vanish r θ 1),
    map_pow, ambientMap_inverse]

def ambientVolume (r θ : ℂ) :
    ⋀[FirstOverlap r θ]^4 (RestrictedAmbientDifferentials r θ) :=
  exteriorPower.ιMulti (FirstOverlap r θ) 4
    (fun j => (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing]
      CycleQ2SurfaceOverlapVolume.differentialBasis j)

def changedVolume (r θ : ℂ) :
    ⋀[FirstOverlap r θ]^4 (RestrictedAmbientDifferentials r θ) :=
  exteriorPower.ιMulti (FirstOverlap r θ) 4
    (fun j => (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing]
      CycleQ2SurfaceOverlapVolume.changedDifferentials j)

/-- The volume transition is the actual scalar extension of the ambient
four-fold differential identity. Both sides retain the conormal vectors. -/
theorem restricted_volume_change (r θ : ℂ) :
    changedVolume r θ = -(inverse (firstEquations r θ) ^ 6) • ambientVolume r θ := by
  have h := congrArg
    (topBaseChange (S := FirstOverlap r θ) CycleQ2SurfaceOverlapVolume.differentialBasis)
    CycleQ2SurfaceOverlapVolume.differential_volume_change
  simpa only [CycleQ2SurfaceOverlapVolume.ambientVolume, map_smulₛₗ,
    topBaseChange_wedge, map_neg, map_pow, firstAmbientAlgebraMap,
    ambientMap_inverse, ambientVolume, changedVolume] using h

end CycleQ2SurfaceOverlapConormal

end

end


section

/-!
# Canonical comparison of the retained ambient modules

Tensor cancellation identifies the literal presentation cotangent space
with polynomial differentials after scalar extension. The genuine
localization equivalence then identifies it with localized ambient
differentials. Every comparison is characterized on the actual tensor
of the universal differential of every polynomial.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceAmbientComparison

open Module MvPolynomial TensorProduct
open CycleQ2GeometricSurfaceAdjunction CycleQ2SurfaceAffineOverlap
open CycleQ2GeometricSurfaceDehomogenizedCharts
open scoped TensorProduct

abbrev AmbientRing := CycleQ2SurfaceOverlapVolume.AmbientOverlap
abbrev PolynomialDifferentials := KaehlerDifferential ℂ SurfacePoly
abbrev LocalizedDifferentials := KaehlerDifferential ℂ AmbientRing

section CommonScalars

variable (v : Fin 2 → SurfacePoly) (S : Type*) [CommRing S]
  [Algebra (SurfaceChartRing v) S] [Algebra SurfacePoly S]
  [IsScalarTower SurfacePoly (SurfaceChartRing v) S]
  [Algebra AmbientRing S] [IsScalarTower SurfacePoly AmbientRing S]

/-- The comparison is a composite of canonical tensor cancellation and
the actual localization map on universal Kähler differentials. -/
def presentationAmbientEquiv :
    S ⊗[SurfaceChartRing v] AmbientDifferentials v ≃ₗ[S]
      S ⊗[AmbientRing] LocalizedDifferentials :=
  (AlgebraTensorModule.cancelBaseChange SurfacePoly (SurfaceChartRing v)
    S S PolynomialDifferentials).trans
      ((AlgebraTensorModule.cancelBaseChange SurfacePoly AmbientRing
        S S PolynomialDifferentials).symm.trans
          (CycleQ2SurfaceOverlapVolume.localizedDifferentialEquiv.baseChange AmbientRing S _ _))

@[simp] theorem presentationAmbientEquiv_tmul_D (s : S) (p : SurfacePoly) :
    presentationAmbientEquiv v S (s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p) =
      s ⊗ₜ[AmbientRing]
        KaehlerDifferential.D ℂ AmbientRing (CycleQ2SurfaceOverlapVolume.polynomialMap p) := by
  change ((1 : SurfaceChartRing v) • s) ⊗ₜ[AmbientRing]
    CycleQ2SurfaceOverlapVolume.localizedDifferentialEquiv
      ((1 : AmbientRing) ⊗ₜ[SurfacePoly] KaehlerDifferential.D ℂ SurfacePoly p) = _
  exact congrArg₂ (fun (a : S) (m : LocalizedDifferentials) => a ⊗ₜ[AmbientRing] m)
    (one_smul (SurfaceChartRing v) s)
    (CycleQ2SurfaceOverlapVolume.localizedDifferentialEquiv_tmul_D p)

variable (n t : SurfacePoly) [Algebra (AdjunctionPatch v n t) S]
  [IsScalarTower (SurfaceChartRing v) (AdjunctionPatch v n t) S]

/-- The same canonical comparison begins with the actual rank-four
ambient module of an augmented-Jacobian patch. -/
def patchAmbientEquiv :
    S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t ≃ₗ[S]
      S ⊗[AmbientRing] LocalizedDifferentials :=
  (AlgebraTensorModule.cancelBaseChange (SurfaceChartRing v) (AdjunctionPatch v n t)
    S S (AmbientDifferentials v)).trans (presentationAmbientEquiv v S)

@[simp] theorem patchAmbientEquiv_tmul_D (s : S) (p : SurfacePoly) :
    patchAmbientEquiv v S n t
        (s ⊗ₜ[AdjunctionPatch v n t]
          ((1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v] ambientDifferential v p)) =
      s ⊗ₜ[AmbientRing]
        KaehlerDifferential.D ℂ AmbientRing (CycleQ2SurfaceOverlapVolume.polynomialMap p) := by
  simp only [patchAmbientEquiv, LinearEquiv.trans_apply,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul, presentationAmbientEquiv_tmul_D]

end CommonScalars

/-- On the actual localized surface ring, the ambient scalar action is
the map already constructed from its quotient and localization. -/
@[instance_reducible]
def chartAmbientAlgebra (v : Fin 2 → SurfacePoly) : Algebra AmbientRing (ChartOverlap v) :=
  (ambientMap v).toRingHom.toAlgebra

attribute [local instance] chartAmbientAlgebra

@[simp] theorem chartAmbientAlgebraMap (v : Fin 2 → SurfacePoly) (a : AmbientRing) :
    algebraMap AmbientRing (ChartOverlap v) a = ambientMap v a := rfl

local instance chartAmbientTower (v : Fin 2 → SurfacePoly) :
    IsScalarTower SurfacePoly AmbientRing (ChartOverlap v) := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  change polynomialMap v p = ambientMap v (CycleQ2SurfaceOverlapVolume.polynomialMap p)
  exact (ambientMap_polynomial v p).symm

abbrev ChartRetainedAmbient (v : Fin 2 → SurfacePoly) :=
  ChartOverlap v ⊗[AmbientRing] LocalizedDifferentials

/-- A closed comparison on the actual surface chart overlap; no module
comparison, compatibility, or localization premise is supplied. -/
def chartAmbientEquiv (v : Fin 2 → SurfacePoly) :
    ChartOverlap v ⊗[SurfaceChartRing v] AmbientDifferentials v ≃ₗ[ChartOverlap v]
      ChartRetainedAmbient v :=
  presentationAmbientEquiv v (ChartOverlap v)

@[simp] theorem chartAmbientEquiv_tmul_D (v : Fin 2 → SurfacePoly)
    (s : ChartOverlap v) (p : SurfacePoly) :
    chartAmbientEquiv v (s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p) =
      s ⊗ₜ[AmbientRing]
        KaehlerDifferential.D ℂ AmbientRing (CycleQ2SurfaceOverlapVolume.polynomialMap p) :=
  presentationAmbientEquiv_tmul_D v (ChartOverlap v) s p

/-- The codomain is exactly the concrete retained-ambient module used
for the already proved first-overlap conormal and volume formulas. -/
def firstAmbientEquiv (r θ : ℂ) :
    FirstOverlap r θ ⊗[SurfaceChartRing (firstEquations r θ)]
      AmbientDifferentials (firstEquations r θ) ≃ₗ[FirstOverlap r θ]
        CycleQ2SurfaceOverlapConormal.RestrictedAmbientDifferentials r θ :=
  chartAmbientEquiv (firstEquations r θ)

@[simp] theorem firstAmbientEquiv_differential (r θ : ℂ) (p : SurfacePoly) :
    firstAmbientEquiv r θ
        ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (firstEquations r θ)]
          ambientDifferential (firstEquations r θ) p) =
      CycleQ2SurfaceOverlapConormal.tensorD r θ
        (CycleQ2SurfaceOverlapVolume.polynomialMap p) :=
  chartAmbientEquiv_tmul_D (firstEquations r θ) 1 p

end CycleQ2SurfaceAmbientComparison

end

end


section

/-!
# The actual changed-coordinate map on retained ambient differentials

The two polynomial scalar actions on the first overlap are distinct.
The source uses the actual second-chart quotient map; the target uses
the actual ambient localization followed by the first-chart quotient.
The weighted coordinate evaluation supplies their commuting square.
The resulting map is the scalar extension of the universal Kähler map.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceChangedAmbient

open Module MvPolynomial TensorProduct
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2SurfaceAffineOverlap CycleQ2SurfaceAmbientComparison
open scoped TensorProduct

section GenericMap

variable (v : Fin 2 → SurfacePoly) (A S : Type*) [CommRing A] [CommRing S]
  [Algebra ℂ A] [Algebra SurfacePoly A] [IsScalarTower ℂ SurfacePoly A]
  [Algebra (SurfaceChartRing v) S] [Algebra SurfacePoly S]
  [IsScalarTower SurfacePoly (SurfaceChartRing v) S]
  [Algebra A S] [IsScalarTower SurfacePoly A S]

/-- Canonical tensor cancellation followed by the actual universal
Kähler map. This construction is valid for any compatible ring square. -/
def presentationAmbientMap :
    S ⊗[SurfaceChartRing v] AmbientDifferentials v →ₗ[S]
      S ⊗[A] KaehlerDifferential ℂ A :=
  ((KaehlerDifferential.mapBaseChange ℂ SurfacePoly A).baseChange S).comp
    ((AlgebraTensorModule.cancelBaseChange SurfacePoly A S S
      (KaehlerDifferential ℂ SurfacePoly)).symm.toLinearMap.comp
        (AlgebraTensorModule.cancelBaseChange SurfacePoly (SurfaceChartRing v) S S
          (KaehlerDifferential ℂ SurfacePoly)).toLinearMap)

@[simp] theorem presentationAmbientMap_tmul_D (s : S) (p : SurfacePoly) :
    presentationAmbientMap v A S (s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p) =
      s ⊗ₜ[A] KaehlerDifferential.D ℂ A (algebraMap SurfacePoly A p) := by
  change ((1 : SurfaceChartRing v) • s) ⊗ₜ[A]
    KaehlerDifferential.mapBaseChange ℂ SurfacePoly A
      ((1 : A) ⊗ₜ[SurfacePoly] KaehlerDifferential.D ℂ SurfacePoly p) = _
  exact congrArg₂ (fun (a : S) (m : KaehlerDifferential ℂ A) => a ⊗ₜ[A] m)
    (one_smul (SurfaceChartRing v) s)
    ((KaehlerDifferential.mapBaseChange_tmul ℂ SurfacePoly A 1
      (KaehlerDifferential.D ℂ SurfacePoly p)).trans
        ((one_smul A _).trans (KaehlerDifferential.map_D ℂ ℂ SurfacePoly A p)))

variable [Algebra ℂ S] [IsScalarTower ℂ A S]
  [IsScalarTower ℂ (SurfaceChartRing v) S]

/-- The genuine presentation quotient map followed by the universal
Kähler map along the supplied scalar extension. -/
def presentationToKaehler :
    S ⊗[SurfaceChartRing v] AmbientDifferentials v →ₗ[S] KaehlerDifferential ℂ S :=
  (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing v) S).comp
    ((presentation v).toExtension.toKaehler.baseChange S)

@[simp] theorem presentationToKaehler_tmul_D (s : S) (p : SurfacePoly) :
    presentationToKaehler v S (s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p) =
      s • KaehlerDifferential.D ℂ S (algebraMap SurfacePoly S p) := by
  have h : ((presentation v).toExtension.toKaehler.baseChange S)
      (s ⊗ₜ[SurfaceChartRing v] ambientDifferential v p) =
      s ⊗ₜ[SurfaceChartRing v] KaehlerDifferential.D ℂ (SurfaceChartRing v)
        (algebraMap SurfacePoly (SurfaceChartRing v) p) :=
    congrArg (fun m : KaehlerDifferential ℂ (SurfaceChartRing v) =>
      s ⊗ₜ[SurfaceChartRing v] m) (ambientToKaehler_polynomial v p)
  exact (congrArg (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing v) S) h).trans
    ((KaehlerDifferential.mapBaseChange_tmul ℂ (SurfaceChartRing v) S s _).trans
      ((congrArg (fun m : KaehlerDifferential ℂ S => s • m)
        (KaehlerDifferential.map_D ℂ ℂ (SurfaceChartRing v) S
          (algebraMap SurfacePoly (SurfaceChartRing v) p))).trans
        (congrArg (fun x : S => s • KaehlerDifferential.D ℂ S x)
          (IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing v) S p).symm)))

/-- The ambient coordinate map and the actual presentation quotient
commute after every compatible scalar extension. Compatibility is the
literal algebra-map square; no differential comparison is assumed. -/
theorem presentationAmbientMap_toKaehler :
    (KaehlerDifferential.mapBaseChange ℂ A S).comp (presentationAmbientMap v A S) =
      presentationToKaehler v S := by
  apply ((presentation v).cotangentSpaceBasis.baseChange S).ext
  intro j
  rw [Basis.baseChange_apply, Algebra.Generators.cotangentSpaceBasis_apply]
  change KaehlerDifferential.mapBaseChange ℂ A S
      (presentationAmbientMap v A S
        ((1 : S) ⊗ₜ[SurfaceChartRing v] ambientDifferential v (X j))) =
    presentationToKaehler v S
      ((1 : S) ⊗ₜ[SurfaceChartRing v] ambientDifferential v (X j))
  rw [presentationAmbientMap_tmul_D, KaehlerDifferential.mapBaseChange_tmul,
    KaehlerDifferential.map_D, presentationToKaehler_tmul_D,
    ← IsScalarTower.algebraMap_apply SurfacePoly A S]

end GenericMap

abbrev AmbientRing := CycleQ2SurfaceOverlapVolume.AmbientOverlap

/-- This polynomial action is the literal changed evaluation, not the
ordinary inclusion into the ambient localization. -/
@[instance_reducible]
def changedAmbientAlgebra : Algebra SurfacePoly AmbientRing :=
  CycleQ2SurfaceOverlapVolume.changeEvaluation.toRingHom.toAlgebra

attribute [local instance] changedAmbientAlgebra

local instance changedAmbientSMul : SMul SurfacePoly AmbientRing :=
  changedAmbientAlgebra.toSMul

local instance changedAmbientModule : Module SurfacePoly AmbientRing :=
  @Algebra.toModule SurfacePoly AmbientRing _ _ changedAmbientAlgebra

local instance changedAmbientComplexTower : IsScalarTower ℂ SurfacePoly AmbientRing :=
  IsScalarTower.of_algHom CycleQ2SurfaceOverlapVolume.changeEvaluation

/-- The scalar action of the second surface chart on the first overlap
comes from its actual quotient lift. -/
@[instance_reducible]
def secondChartAlgebra (r θ : ℂ) :
    Algebra (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) :=
  (quotientLift (secondEquations r θ) (firstEquations r θ)
    (second_relations_change_zero r θ)).toRingHom.toAlgebra

@[instance_reducible]
def secondPolynomialAlgebra (r θ : ℂ) : Algebra SurfacePoly (FirstOverlap r θ) :=
  (changeEvaluation (firstEquations r θ)).toRingHom.toAlgebra

attribute [local instance] secondChartAlgebra secondPolynomialAlgebra
  CycleQ2SurfaceOverlapConormal.firstAmbientAlgebra

local instance secondPolynomialSMul (r θ : ℂ) : SMul SurfacePoly (FirstOverlap r θ) :=
  (secondPolynomialAlgebra r θ).toSMul

local instance secondPolynomialModule (r θ : ℂ) : Module SurfacePoly (FirstOverlap r θ) :=
  @Algebra.toModule SurfacePoly (FirstOverlap r θ) _ _ (secondPolynomialAlgebra r θ)

local instance secondChartTower (r θ : ℂ) :
    IsScalarTower SurfacePoly (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) := by
  constructor
  intro p q s
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  change changeEvaluation (firstEquations r θ) (p * a) * s =
    changeEvaluation (firstEquations r θ) p *
      (changeEvaluation (firstEquations r θ) a * s)
  rw [map_mul, mul_assoc]

local instance changedAmbientTower (r θ : ℂ) :
    IsScalarTower SurfacePoly AmbientRing (FirstOverlap r θ) := by
  apply IsScalarTower.of_algebraMap_eq
  intro p
  rfl

local instance ambientSurfaceComplexTower (r θ : ℂ) :
    IsScalarTower ℂ AmbientRing (FirstOverlap r θ) :=
  IsScalarTower.of_algHom (ambientMap (firstEquations r θ))

local instance secondChartComplexTower (r θ : ℂ) :
    IsScalarTower ℂ (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) :=
  IsScalarTower.of_algHom (quotientLift (secondEquations r θ) (firstEquations r θ)
    (second_relations_change_zero r θ))

/-- The second-chart scalar action agrees with the already constructed
literal quotient-ring overlap equivalence. -/
theorem secondChartAlgebraMap (r θ : ℂ)
    (x : SurfaceChartRing (secondEquations r θ)) :
    algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) x =
      overlapEquiv r θ
        (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ) x) := by
  change quotientLift _ _ _ x = IsLocalization.lift _
    (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ) x)
  rw [IsLocalization.lift_eq]
  rfl

abbrev SecondRetainedAmbient (r θ : ℂ) :=
  FirstOverlap r θ ⊗[SurfaceChartRing (secondEquations r θ)]
    AmbientDifferentials (secondEquations r θ)

/-- The actual universal ambient differential map between the two
surface presentations, expressed over the first overlap ring. -/
def secondAmbientMap (r θ : ℂ) :
    SecondRetainedAmbient r θ →ₗ[FirstOverlap r θ]
      CycleQ2SurfaceOverlapConormal.RestrictedAmbientDifferentials r θ :=
  presentationAmbientMap (secondEquations r θ) AmbientRing (FirstOverlap r θ)

@[simp] theorem secondAmbientMap_tmul_D (r θ : ℂ) (s : FirstOverlap r θ)
    (p : SurfacePoly) :
    secondAmbientMap r θ
        (s ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
          ambientDifferential (secondEquations r θ) p) =
      s ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing
        (CycleQ2SurfaceOverlapVolume.changeEvaluation p) :=
  presentationAmbientMap_tmul_D (secondEquations r θ) AmbientRing (FirstOverlap r θ) s p

@[simp] theorem secondAmbientMap_one_D (r θ : ℂ) (p : SurfacePoly) :
    secondAmbientMap r θ
        ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
          ambientDifferential (secondEquations r θ) p) =
      CycleQ2SurfaceOverlapConormal.tensorD r θ
        (CycleQ2SurfaceOverlapVolume.changeEvaluation p) :=
  secondAmbientMap_tmul_D r θ 1 p

theorem secondAmbientMap_surface_conormal (r θ : ℂ) :
    secondAmbientMap r θ
        ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
          ambientDifferential (secondEquations r θ) (secondEquations r θ 0)) =
      inverse (firstEquations r θ) ^ 6 •
        firstAmbientEquiv r θ
          ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (firstEquations r θ)]
            ambientDifferential (firstEquations r θ) (firstEquations r θ 0)) := by
  rw [secondAmbientMap_one_D, firstAmbientEquiv_differential,
    CycleQ2SurfaceOverlapConormal.surface_conormal_change]

theorem secondAmbientMap_cubic_conormal (r θ : ℂ) :
    secondAmbientMap r θ
        ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
          ambientDifferential (secondEquations r θ) (secondEquations r θ 1)) =
      inverse (firstEquations r θ) ^ 3 •
        firstAmbientEquiv r θ
          ((1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (firstEquations r θ)]
            ambientDifferential (firstEquations r θ) (firstEquations r θ 1)) := by
  rw [secondAmbientMap_one_D, firstAmbientEquiv_differential,
    CycleQ2SurfaceOverlapConormal.cubic_conormal_change]

/-- The actual quotient map from retained ambient differentials to the
universal differentials of the first surface overlap. -/
def retainedToKaehler (r θ : ℂ) :
    CycleQ2SurfaceOverlapConormal.RestrictedAmbientDifferentials r θ →ₗ[FirstOverlap r θ]
      KaehlerDifferential ℂ (FirstOverlap r θ) :=
  KaehlerDifferential.mapBaseChange ℂ AmbientRing (FirstOverlap r θ)

@[simp] theorem retainedToKaehler_tmul_D (r θ : ℂ) (s : FirstOverlap r θ)
    (a : AmbientRing) :
    retainedToKaehler r θ (s ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing a) =
      s • KaehlerDifferential.D ℂ (FirstOverlap r θ) (ambientMap (firstEquations r θ) a) := by
  rw [retainedToKaehler, KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D]
  rfl

/-- The cotangent map from the second surface presentation uses its
actual quotient map followed by its actual overlap ring map. -/
def secondPresentationToKaehler (r θ : ℂ) :
    SecondRetainedAmbient r θ →ₗ[FirstOverlap r θ]
      KaehlerDifferential ℂ (FirstOverlap r θ) :=
  (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing (secondEquations r θ))
    (FirstOverlap r θ)).comp
      ((presentation (secondEquations r θ)).toExtension.toKaehler.baseChange (FirstOverlap r θ))

@[simp] theorem secondPresentationToKaehler_tmul_D (r θ : ℂ) (s : FirstOverlap r θ)
    (p : SurfacePoly) :
    secondPresentationToKaehler r θ
        (s ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
          ambientDifferential (secondEquations r θ) p) =
      s • KaehlerDifferential.D ℂ (FirstOverlap r θ)
        (changeEvaluation (firstEquations r θ) p) := by
  exact presentationToKaehler_tmul_D (secondEquations r θ) (FirstOverlap r θ) s p

/-- The ambient coordinate change commutes with the genuine surface
cotangent quotient maps. The equality is proved on the actual free
presentation basis, using the universal differential formula. -/
theorem secondAmbientMap_toKaehler (r θ : ℂ) :
    (retainedToKaehler r θ).comp (secondAmbientMap r θ) =
      secondPresentationToKaehler r θ := by
  exact presentationAmbientMap_toKaehler (secondEquations r θ) AmbientRing (FirstOverlap r θ)

/-- The source is the actual ordered polynomial ambient volume of the
second presentation after scalar extension. -/
def secondAmbientVolume (r θ : ℂ) :
    ⋀[FirstOverlap r θ]^4 (SecondRetainedAmbient r θ) :=
  exteriorPower.ιMulti (FirstOverlap r θ) 4 (fun j : Fin 4 =>
    (1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
      ambientDifferential (secondEquations r θ) (X (finSuccEquiv 3 j)))

theorem secondAmbientMap_volume (r θ : ℂ) :
    exteriorPower.map 4 (secondAmbientMap r θ) (secondAmbientVolume r θ) =
      -(inverse (firstEquations r θ) ^ 6) •
        CycleQ2SurfaceOverlapConormal.ambientVolume r θ := by
  rw [secondAmbientVolume, exteriorPower.map_apply_ιMulti]
  have h : (secondAmbientMap r θ) ∘
      (fun j : Fin 4 => (1 : FirstOverlap r θ) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
        ambientDifferential (secondEquations r θ) (X (finSuccEquiv 3 j))) =
      fun j : Fin 4 => (1 : FirstOverlap r θ) ⊗ₜ[AmbientRing]
        CycleQ2SurfaceOverlapVolume.changedDifferentials j := by
    funext j
    exact secondAmbientMap_tmul_D r θ 1 (X (finSuccEquiv 3 j))
  rw [h]
  exact CycleQ2SurfaceOverlapConormal.restricted_volume_change r θ

end CycleQ2SurfaceChangedAmbient

end

end


section

/-!
# A concrete common localization of two augmented-Jacobian patches

The ring is the first affine surface overlap with the product of the two
actual augmented Jacobians inverted. The second Jacobian is transported
by the proved quotient-ring overlap map. Both patch maps are constructed
by the localization universal property, and both extensions are proved
formally étale. No differential-module comparison is assumed.

The standard polynomial action is the first-chart action. A separately
named second polynomial action is available only by explicit local
installation; the two coordinate actions are never identified.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceCommonLocalization

open MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2SurfaceAffineOverlap

abbrev AmbientRing := CycleQ2SurfaceOverlapVolume.AmbientOverlap

attribute [local instance] CycleQ2SurfaceChangedAmbient.secondChartAlgebra
  CycleQ2SurfaceOverlapConormal.firstAmbientAlgebra

local instance secondChartComplexTower (r θ : ℂ) :
    IsScalarTower ℂ (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) :=
  IsScalarTower.of_algHom (quotientLift (secondEquations r θ) (firstEquations r θ)
    (second_relations_change_zero r θ))

local instance ambientComplexTower (r θ : ℂ) :
    IsScalarTower ℂ AmbientRing (FirstOverlap r θ) :=
  IsScalarTower.of_algHom (CycleQ2SurfaceAffineOverlap.ambientMap (firstEquations r θ))

def firstJacobianImage (r θ : ℂ) (n t : SurfacePoly) : FirstOverlap r θ :=
  algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ)
    (augmentedJacobian (firstEquations r θ) n t)

def secondJacobianImage (r θ : ℂ) (n t : SurfacePoly) : FirstOverlap r θ :=
  algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ)
    (augmentedJacobian (secondEquations r θ) n t)

def commonDenominator (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) : FirstOverlap r θ :=
  firstJacobianImage r θ n₁ t₁ * secondJacobianImage r θ n₂ t₂

abbrev CommonPatch (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :=
  Localization.Away (commonDenominator r θ n₁ t₁ n₂ t₂)

variable (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)

def firstOverlapMap : FirstOverlap r θ →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  IsScalarTower.toAlgHom ℂ (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂)

def firstChartMap :
    SurfaceChartRing (firstEquations r θ) →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  (firstOverlapMap r θ n₁ t₁ n₂ t₂).comp
    (IsScalarTower.toAlgHom ℂ (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))

def secondChartMap :
    SurfaceChartRing (secondEquations r θ) →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  (firstOverlapMap r θ n₁ t₁ n₂ t₂).comp
    (quotientLift (secondEquations r θ) (firstEquations r θ)
      (second_relations_change_zero r θ))

def ambientMap : AmbientRing →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  (firstOverlapMap r θ n₁ t₁ n₂ t₂).comp
    (CycleQ2SurfaceAffineOverlap.ambientMap (firstEquations r θ))

/-- This action is the composite of the actual second-chart quotient
map with the canonical common localization. -/
@[instance_reducible]
def commonSecondChartAlgebra :
    Algebra (SurfaceChartRing (secondEquations r θ)) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstanceAs (Algebra (SurfaceChartRing (secondEquations r θ))
    (Localization.Away (commonDenominator r θ n₁ t₁ n₂ t₂)))

/-- The ambient action uses the ordinary first-coordinate quotient map. -/
@[instance_reducible]
def commonAmbientAlgebra : Algebra AmbientRing (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstanceAs (Algebra AmbientRing
    (Localization.Away (commonDenominator r θ n₁ t₁ n₂ t₂)))

attribute [local instance] commonSecondChartAlgebra commonAmbientAlgebra

theorem commonSecondChartTower :
    IsScalarTower (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ)
      (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstance

theorem commonSecondComplexTower :
    IsScalarTower ℂ (SurfaceChartRing (secondEquations r θ))
      (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstance

theorem commonAmbientTower :
    IsScalarTower AmbientRing (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstance

theorem commonAmbientComplexTower :
    IsScalarTower ℂ AmbientRing (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  inferInstance

attribute [local instance] commonSecondChartTower commonSecondComplexTower
  commonAmbientTower commonAmbientComplexTower

@[simp] theorem firstChartMap_apply (a : SurfaceChartRing (firstEquations r θ)) :
    firstChartMap r θ n₁ t₁ n₂ t₂ a =
      algebraMap (SurfaceChartRing (firstEquations r θ)) (CommonPatch r θ n₁ t₁ n₂ t₂) a := rfl

@[simp] theorem secondChartMap_apply (a : SurfaceChartRing (secondEquations r θ)) :
    secondChartMap r θ n₁ t₁ n₂ t₂ a =
      algebraMap (SurfaceChartRing (secondEquations r θ)) (CommonPatch r θ n₁ t₁ n₂ t₂) a := rfl

@[simp] theorem ambientMap_apply (a : AmbientRing) :
    ambientMap r θ n₁ t₁ n₂ t₂ a =
      algebraMap AmbientRing (CommonPatch r θ n₁ t₁ n₂ t₂) a := rfl

theorem secondChartMap_overlap (a : SurfaceChartRing (secondEquations r θ)) :
    secondChartMap r θ n₁ t₁ n₂ t₂ a =
      firstOverlapMap r θ n₁ t₁ n₂ t₂
        (overlapEquiv r θ (algebraMap (SurfaceChartRing (secondEquations r θ))
          (SecondOverlap r θ) a)) :=
  congrArg (firstOverlapMap r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceChangedAmbient.secondChartAlgebraMap r θ a)

theorem firstJacobian_isUnit :
    IsUnit (firstChartMap r θ n₁ t₁ n₂ t₂
      (augmentedJacobian (firstEquations r θ) n₁ t₁)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := CommonPatch r θ n₁ t₁ n₂ t₂) (commonDenominator r θ n₁ t₁ n₂ t₂)
  change IsUnit (firstOverlapMap r θ n₁ t₁ n₂ t₂
    (firstJacobianImage r θ n₁ t₁ * secondJacobianImage r θ n₂ t₂)) at h
  rw [map_mul, IsUnit.mul_iff] at h
  exact h.1

theorem secondJacobian_isUnit :
    IsUnit (secondChartMap r θ n₁ t₁ n₂ t₂
      (augmentedJacobian (secondEquations r θ) n₂ t₂)) := by
  have h := IsLocalization.Away.algebraMap_isUnit
    (S := CommonPatch r θ n₁ t₁ n₂ t₂) (commonDenominator r θ n₁ t₁ n₂ t₂)
  change IsUnit (firstOverlapMap r θ n₁ t₁ n₂ t₂
    (firstJacobianImage r θ n₁ t₁ * secondJacobianImage r θ n₂ t₂)) at h
  rw [map_mul, IsUnit.mul_iff] at h
  exact h.2

def firstPatchMap :
    AdjunctionPatch (firstEquations r θ) n₁ t₁ →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  IsLocalization.Away.liftAlgHom (augmentedJacobian (firstEquations r θ) n₁ t₁)
    (f := firstChartMap r θ n₁ t₁ n₂ t₂) (firstJacobian_isUnit r θ n₁ t₁ n₂ t₂)

def secondPatchMap :
    AdjunctionPatch (secondEquations r θ) n₂ t₂ →ₐ[ℂ] CommonPatch r θ n₁ t₁ n₂ t₂ :=
  IsLocalization.Away.liftAlgHom (augmentedJacobian (secondEquations r θ) n₂ t₂)
    (f := secondChartMap r θ n₁ t₁ n₂ t₂) (secondJacobian_isUnit r θ n₁ t₁ n₂ t₂)

@[simp] theorem firstPatchMap_base (a : SurfaceChartRing (firstEquations r θ)) :
    firstPatchMap r θ n₁ t₁ n₂ t₂
        (algebraMap (SurfaceChartRing (firstEquations r θ))
          (AdjunctionPatch (firstEquations r θ) n₁ t₁) a) =
      firstChartMap r θ n₁ t₁ n₂ t₂ a :=
  IsLocalization.Away.lift_eq _ (firstJacobian_isUnit r θ n₁ t₁ n₂ t₂) a

@[simp] theorem secondPatchMap_base (a : SurfaceChartRing (secondEquations r θ)) :
    secondPatchMap r θ n₁ t₁ n₂ t₂
        (algebraMap (SurfaceChartRing (secondEquations r θ))
          (AdjunctionPatch (secondEquations r θ) n₂ t₂) a) =
      secondChartMap r θ n₁ t₁ n₂ t₂ a :=
  IsLocalization.Away.lift_eq _ (secondJacobian_isUnit r θ n₁ t₁ n₂ t₂) a

/-- The first patch map and the ordinary ambient map agree on every
actual polynomial, not only on the four coordinate generators. -/
theorem firstPatchMap_polynomial (p : SurfacePoly) :
    firstPatchMap r θ n₁ t₁ n₂ t₂
        (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁) p) =
      ambientMap r θ n₁ t₁ n₂ t₂ (CycleQ2SurfaceOverlapVolume.polynomialMap p) := by
  change firstPatchMap r θ n₁ t₁ n₂ t₂
    (algebraMap (SurfaceChartRing (firstEquations r θ))
      (AdjunctionPatch (firstEquations r θ) n₁ t₁)
      (chartMap (firstEquations r θ) p)) = _
  rw [firstPatchMap_base]
  exact congrArg (firstOverlapMap r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceAffineOverlap.ambientMap_polynomial (firstEquations r θ) p).symm

/-- The second patch uses the changed polynomial evaluation. This
identity records the distinction between the two polynomial actions. -/
theorem secondPatchMap_polynomial (p : SurfacePoly) :
    secondPatchMap r θ n₁ t₁ n₂ t₂
        (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂) p) =
      ambientMap r θ n₁ t₁ n₂ t₂ (CycleQ2SurfaceOverlapVolume.changeEvaluation p) := by
  change secondPatchMap r θ n₁ t₁ n₂ t₂
    (algebraMap (SurfaceChartRing (secondEquations r θ))
      (AdjunctionPatch (secondEquations r θ) n₂ t₂)
      (chartMap (secondEquations r θ) p)) = _
  rw [secondPatchMap_base]
  rfl

@[instance_reducible]
def firstPatchAlgebra :
    Algebra (AdjunctionPatch (firstEquations r θ) n₁ t₁) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  (firstPatchMap r θ n₁ t₁ n₂ t₂).toRingHom.toAlgebra

@[instance_reducible]
def secondPatchAlgebra :
    Algebra (AdjunctionPatch (secondEquations r θ) n₂ t₂) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  (secondPatchMap r θ n₁ t₁ n₂ t₂).toRingHom.toAlgebra

attribute [local instance] firstPatchAlgebra secondPatchAlgebra

theorem firstPatchComplexTower :
    IsScalarTower ℂ (AdjunctionPatch (firstEquations r θ) n₁ t₁)
      (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  IsScalarTower.of_algHom (firstPatchMap r θ n₁ t₁ n₂ t₂)

theorem secondPatchComplexTower :
    IsScalarTower ℂ (AdjunctionPatch (secondEquations r θ) n₂ t₂)
      (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  IsScalarTower.of_algHom (secondPatchMap r θ n₁ t₁ n₂ t₂)

theorem firstPatchChartTower :
    IsScalarTower (SurfaceChartRing (firstEquations r θ))
      (AdjunctionPatch (firstEquations r θ) n₁ t₁) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  IsScalarTower.of_algebraMap_eq fun a => (firstPatchMap_base r θ n₁ t₁ n₂ t₂ a).symm

theorem secondPatchChartTower :
    IsScalarTower (SurfaceChartRing (secondEquations r θ))
      (AdjunctionPatch (secondEquations r θ) n₂ t₂) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
  IsScalarTower.of_algebraMap_eq fun a => (secondPatchMap_base r θ n₁ t₁ n₂ t₂ a).symm

attribute [local instance] firstPatchComplexTower secondPatchComplexTower
  firstPatchChartTower secondPatchChartTower

/-- The same literal overlap equivalence, now viewed over the second
surface quotient through its proved scalar-action formula. -/
def secondOverlapEquiv :
    SecondOverlap r θ ≃ₐ[SurfaceChartRing (secondEquations r θ)] FirstOverlap r θ :=
  { (overlapEquiv r θ).toRingEquiv with
    commutes' := fun a => (CycleQ2SurfaceChangedAmbient.secondChartAlgebraMap r θ a).symm }

theorem secondChart_overlap_formallyEtale :
    Algebra.FormallyEtale (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ) := by
  have : Algebra.FormallyEtale (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (middle (secondEquations r θ)))
  exact Algebra.FormallyEtale.of_equiv (secondOverlapEquiv r θ)

theorem firstChart_formallyEtale :
    Algebra.FormallyEtale (SurfaceChartRing (firstEquations r θ))
      (CommonPatch r θ n₁ t₁ n₂ t₂) := by
  have : Algebra.FormallyEtale (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (middle (firstEquations r θ)))
  have : Algebra.FormallyEtale (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (commonDenominator r θ n₁ t₁ n₂ t₂))
  exact Algebra.FormallyEtale.comp (SurfaceChartRing (firstEquations r θ))
    (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂)

theorem secondChart_formallyEtale :
    Algebra.FormallyEtale (SurfaceChartRing (secondEquations r θ))
      (CommonPatch r θ n₁ t₁ n₂ t₂) := by
  have := secondChart_overlap_formallyEtale r θ
  have : Algebra.FormallyEtale (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (commonDenominator r θ n₁ t₁ n₂ t₂))
  exact Algebra.FormallyEtale.comp (SurfaceChartRing (secondEquations r θ))
    (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂)

theorem firstPatch_formallyEtale :
    Algebra.FormallyEtale (AdjunctionPatch (firstEquations r θ) n₁ t₁)
      (CommonPatch r θ n₁ t₁ n₂ t₂) := by
  have := firstChart_formallyEtale r θ n₁ t₁ n₂ t₂
  have : Algebra.FormallyEtale (SurfaceChartRing (firstEquations r θ))
      (AdjunctionPatch (firstEquations r θ) n₁ t₁) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (augmentedJacobian (firstEquations r θ) n₁ t₁))
  exact Algebra.FormallyEtale.of_restrictScalars
    (R := SurfaceChartRing (firstEquations r θ))

theorem secondPatch_formallyEtale :
    Algebra.FormallyEtale (AdjunctionPatch (secondEquations r θ) n₂ t₂)
      (CommonPatch r θ n₁ t₁ n₂ t₂) := by
  have := secondChart_formallyEtale r θ n₁ t₁ n₂ t₂
  have : Algebra.FormallyEtale (SurfaceChartRing (secondEquations r θ))
      (AdjunctionPatch (secondEquations r θ) n₂ t₂) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (augmentedJacobian (secondEquations r θ) n₂ t₂))
  exact Algebra.FormallyEtale.of_restrictScalars
    (R := SurfaceChartRing (secondEquations r θ))

end CycleQ2SurfaceCommonLocalization
end

end


section

/-!
# The two genuine ambient maps over the common surface patch

Only the ordinary first-coordinate ambient action is used on the common
ring. The changed-coordinate map is extended from the already proved
map over FirstOverlap, through canonical tensor cancellation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2SurfaceCommonAmbient

open Module MvPolynomial TensorProduct
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2SurfaceAffineOverlap CycleQ2SurfaceCommonLocalization
open CycleQ2SurfacePatchCotangentBinding CycleQ2SurfaceEtaleResidueLifts
open CycleQ2ExteriorTopBaseChange CycleQ2SurfaceResidueScalarExtension
open scoped TensorProduct

namespace RetainedTransport

variable (Q A L S : Type*) [CommRing Q] [CommRing A] [CommRing L] [CommRing S]
  [Algebra Q L] [Algebra A L] [Algebra L S] [Algebra Q S] [Algebra A S]
  [IsScalarTower Q L S] [IsScalarTower A L S]
  {M N : Type*} [AddCommGroup M] [Module Q M] [AddCommGroup N] [Module A N]

def map (f : L ⊗[Q] M →ₗ[L] L ⊗[A] N) : S ⊗[Q] M →ₗ[S] S ⊗[A] N :=
  (AlgebraTensorModule.cancelBaseChange A L S S N).toLinearMap.comp
    ((f.baseChange S).comp
      (AlgebraTensorModule.cancelBaseChange Q L S S M).symm.toLinearMap)

def equiv (e : L ⊗[Q] M ≃ₗ[L] L ⊗[A] N) : S ⊗[Q] M ≃ₗ[S] S ⊗[A] N :=
  (AlgebraTensorModule.cancelBaseChange Q L S S M).symm.trans
    ((e.baseChange L S _ _).trans (AlgebraTensorModule.cancelBaseChange A L S S N))

theorem map_tmul (f : L ⊗[Q] M →ₗ[L] L ⊗[A] N) (m : M) (n : N)
    (h : f ((1 : L) ⊗ₜ[Q] m) = (1 : L) ⊗ₜ[A] n) (s : S) :
    map Q A L S f (s ⊗ₜ[Q] m) = s ⊗ₜ[A] n := by
  change AlgebraTensorModule.cancelBaseChange A L S S N
    (s ⊗ₜ[L] f ((1 : L) ⊗ₜ[Q] m)) = _
  exact (congrArg (fun x : L ⊗[A] N =>
    AlgebraTensorModule.cancelBaseChange A L S S N (s ⊗ₜ[L] x)) h).trans
      (congrArg (fun a : S => a ⊗ₜ[A] n) (one_smul L s))

theorem equiv_tmul (e : L ⊗[Q] M ≃ₗ[L] L ⊗[A] N) (m : M) (n : N)
    (h : e ((1 : L) ⊗ₜ[Q] m) = (1 : L) ⊗ₜ[A] n) (s : S) :
    equiv Q A L S e (s ⊗ₜ[Q] m) = s ⊗ₜ[A] n :=
  map_tmul Q A L S e.toLinearMap m n h s

end RetainedTransport

namespace ExteriorTransport

variable {R T M N : Type*} [CommRing R] [CommRing T] [Algebra R T]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module T N] {d : ℕ}

def image (b : Basis (Fin d) R M) (f : T ⊗[R] M →ₗ[T] N)
    (v : ⋀[R]^d M) : ⋀[T]^d N :=
  exteriorPower.map d f (topBaseChange (S := T) b v)

theorem image_basis (b : Basis (Fin d) R M) (f : T ⊗[R] M →ₗ[T] N)
    (w : Fin d → N) (h : ∀ j, f ((1 : T) ⊗ₜ[R] b j) = w j) :
    image b f (exteriorPower.ιMulti R d b) = exteriorPower.ιMulti T d w := by
  rw [image, topBaseChange_wedge, exteriorPower.map_apply_ιMulti]
  exact congrArg (exteriorPower.ιMulti T d) (funext h)

end ExteriorTransport

abbrev AmbientRing := CycleQ2SurfaceOverlapVolume.AmbientOverlap
abbrev AmbientKaehler := KaehlerDifferential ℂ AmbientRing

attribute [local instance] CycleQ2SurfaceChangedAmbient.secondChartAlgebra
  CycleQ2SurfaceOverlapConormal.firstAmbientAlgebra
  commonSecondChartAlgebra commonAmbientAlgebra
  commonSecondChartTower commonSecondComplexTower commonAmbientTower commonAmbientComplexTower
  firstPatchAlgebra secondPatchAlgebra firstPatchComplexTower secondPatchComplexTower
  firstPatchChartTower secondPatchChartTower firstPatch_formallyEtale secondPatch_formallyEtale

variable (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)

local notation "Common" => CommonPatch r θ n₁ t₁ n₂ t₂
local notation "L" => FirstOverlap r θ
local notation "Q₁" => SurfaceChartRing (firstEquations r θ)
local notation "Q₂" => SurfaceChartRing (secondEquations r θ)
local notation "P₁" => AdjunctionPatch (firstEquations r θ) n₁ t₁
local notation "P₂" => AdjunctionPatch (secondEquations r θ) n₂ t₂

abbrev CommonAmbient := Common ⊗[AmbientRing] AmbientKaehler

abbrev FirstPatchAmbient := Common ⊗[P₁] LocalAmbientDifferentials (firstEquations r θ) n₁ t₁

abbrev SecondPatchAmbient := Common ⊗[P₂] LocalAmbientDifferentials (secondEquations r θ) n₂ t₂

/-- The first comparison consists entirely of canonical equivalences. -/
def firstRetainedEquiv : FirstPatchAmbient r θ n₁ t₁ n₂ t₂ ≃ₗ[Common]
    CommonAmbient r θ n₁ t₁ n₂ t₂ :=
  (patchPresentationEquiv (firstEquations r θ) n₁ t₁ Common).trans
    (RetainedTransport.equiv Q₁ AmbientRing L Common
      (CycleQ2SurfaceAmbientComparison.firstAmbientEquiv r θ))

/-- The second map is the scalar extension of the genuine universal
changed-coordinate differential map over FirstOverlap. -/
def secondRetainedMap : SecondPatchAmbient r θ n₁ t₁ n₂ t₂ →ₗ[Common]
    CommonAmbient r θ n₁ t₁ n₂ t₂ :=
  (RetainedTransport.map Q₂ AmbientRing L Common
    (CycleQ2SurfaceChangedAmbient.secondAmbientMap r θ)).comp
      (patchPresentationEquiv (secondEquations r θ) n₂ t₂ Common).toLinearMap

@[simp] theorem firstRetainedEquiv_tmul_D (s : Common) (p : SurfacePoly) :
    firstRetainedEquiv r θ n₁ t₁ n₂ t₂
        (s ⊗ₜ[P₁] ((1 : P₁) ⊗ₜ[Q₁] ambientDifferential (firstEquations r θ) p)) =
      s ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing
        (CycleQ2SurfaceOverlapVolume.polynomialMap p) := by
  exact (congrArg (RetainedTransport.equiv Q₁ AmbientRing L Common
    (CycleQ2SurfaceAmbientComparison.firstAmbientEquiv r θ))
      (patchPresentationEquiv_tmul_D (firstEquations r θ) n₁ t₁ Common s p)).trans
        (RetainedTransport.equiv_tmul Q₁ AmbientRing L Common
          (CycleQ2SurfaceAmbientComparison.firstAmbientEquiv r θ)
          (ambientDifferential (firstEquations r θ) p) _
          (CycleQ2SurfaceAmbientComparison.firstAmbientEquiv_differential r θ p) s)

@[simp] theorem secondRetainedMap_tmul_D (s : Common) (p : SurfacePoly) :
    secondRetainedMap r θ n₁ t₁ n₂ t₂
        (s ⊗ₜ[P₂] ((1 : P₂) ⊗ₜ[Q₂] ambientDifferential (secondEquations r θ) p)) =
      s ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing
        (CycleQ2SurfaceOverlapVolume.changeEvaluation p) := by
  exact (congrArg (RetainedTransport.map Q₂ AmbientRing L Common
    (CycleQ2SurfaceChangedAmbient.secondAmbientMap r θ))
      (patchPresentationEquiv_tmul_D (secondEquations r θ) n₂ t₂ Common s p)).trans
        (RetainedTransport.map_tmul Q₂ AmbientRing L Common
          (CycleQ2SurfaceChangedAmbient.secondAmbientMap r θ)
          (ambientDifferential (secondEquations r θ) p) _
          (CycleQ2SurfaceChangedAmbient.secondAmbientMap_one_D r θ p) s)

def quotient : CommonAmbient r θ n₁ t₁ n₂ t₂ →ₗ[Common] KaehlerDifferential ℂ Common :=
  KaehlerDifferential.mapBaseChange ℂ AmbientRing Common

@[simp] theorem quotient_tmul_D (s : Common) (a : AmbientRing) :
    quotient r θ n₁ t₁ n₂ t₂ (s ⊗ₜ[AmbientRing] KaehlerDifferential.D ℂ AmbientRing a) =
      s • KaehlerDifferential.D ℂ Common
        (CycleQ2SurfaceCommonLocalization.ambientMap r θ n₁ t₁ n₂ t₂ a) :=
  (KaehlerDifferential.mapBaseChange_tmul ℂ AmbientRing Common s
    (KaehlerDifferential.D ℂ AmbientRing a)).trans
      (congrArg (fun m : KaehlerDifferential ℂ Common => s • m)
        (KaehlerDifferential.map_D ℂ ℂ AmbientRing Common a))

theorem first_quotient_polynomial (s : Common) (p : SurfacePoly) :
    quotient r θ n₁ t₁ n₂ t₂
        (firstRetainedEquiv r θ n₁ t₁ n₂ t₂
          (s ⊗ₜ[P₁] ((1 : P₁) ⊗ₜ[Q₁] ambientDifferential (firstEquations r θ) p))) =
      etaleToKaehler (firstEquations r θ) n₁ t₁ Common
        (s ⊗ₜ[P₁] ((1 : P₁) ⊗ₜ[Q₁] ambientDifferential (firstEquations r θ) p)) := by
  rw [firstRetainedEquiv_tmul_D, quotient_tmul_D, etaleToKaehler_polynomial]
  exact congrArg (fun a : Common => s • KaehlerDifferential.D ℂ Common a)
    (firstPatchMap_polynomial r θ n₁ t₁ n₂ t₂ p).symm

theorem second_quotient_polynomial (s : Common) (p : SurfacePoly) :
    quotient r θ n₁ t₁ n₂ t₂
        (secondRetainedMap r θ n₁ t₁ n₂ t₂
          (s ⊗ₜ[P₂] ((1 : P₂) ⊗ₜ[Q₂] ambientDifferential (secondEquations r θ) p))) =
      etaleToKaehler (secondEquations r θ) n₂ t₂ Common
        (s ⊗ₜ[P₂] ((1 : P₂) ⊗ₜ[Q₂] ambientDifferential (secondEquations r θ) p)) := by
  rw [secondRetainedMap_tmul_D, quotient_tmul_D, etaleToKaehler_polynomial]
  exact congrArg (fun a : Common => s • KaehlerDifferential.D ℂ Common a)
    (secondPatchMap_polynomial r θ n₁ t₁ n₂ t₂ p).symm

/-- The first comparison commutes with the actual surface cotangent map. -/
theorem first_quotient_square :
    (quotient r θ n₁ t₁ n₂ t₂).comp (firstRetainedEquiv r θ n₁ t₁ n₂ t₂).toLinearMap =
      etaleToKaehler (firstEquations r θ) n₁ t₁ Common := by
  apply ((localAmbientBasis (firstEquations r θ) n₁ t₁).baseChange Common).ext
  intro j
  simp only [Basis.baseChange_apply, localAmbientBasis, ambientBasis,
    Basis.reindex_apply, Algebra.Generators.cotangentSpaceBasis_apply]
  exact first_quotient_polynomial r θ n₁ t₁ n₂ t₂ 1 (X (ambientIndexEquiv j))

/-- The second comparison has the same actual quotient map to Ω of Common. -/
theorem second_quotient_square :
    (quotient r θ n₁ t₁ n₂ t₂).comp (secondRetainedMap r θ n₁ t₁ n₂ t₂) =
      etaleToKaehler (secondEquations r θ) n₂ t₂ Common := by
  apply ((localAmbientBasis (secondEquations r θ) n₂ t₂).baseChange Common).ext
  intro j
  simp only [Basis.baseChange_apply, localAmbientBasis, ambientBasis,
    Basis.reindex_apply, Algebra.Generators.cotangentSpaceBasis_apply]
  exact second_quotient_polynomial r θ n₁ t₁ n₂ t₂ 1 (X (ambientIndexEquiv j))

def inverseCoordinate : Common := algebraMap L Common (inverse (firstEquations r θ))

def pushRetained (x : CycleQ2SurfaceOverlapConormal.RestrictedAmbientDifferentials r θ) :
    CommonAmbient r θ n₁ t₁ n₂ t₂ :=
  AlgebraTensorModule.cancelBaseChange AmbientRing L Common Common AmbientKaehler ((1 : Common) ⊗ₜ[L] x)

theorem pushRetained_tmul (m : AmbientKaehler) :
    pushRetained r θ n₁ t₁ n₂ t₂ ((1 : L) ⊗ₜ[AmbientRing] m) =
      (1 : Common) ⊗ₜ[AmbientRing] m :=
  congrArg (fun a : Common => a ⊗ₜ[AmbientRing] m) (one_smul L (1 : Common))

theorem pushRetained_smul (a : L)
    (x : CycleQ2SurfaceOverlapConormal.RestrictedAmbientDifferentials r θ) :
    pushRetained r θ n₁ t₁ n₂ t₂ (a • x) =
      algebraMap L Common a • pushRetained r θ n₁ t₁ n₂ t₂ x := by
  have h : (1 : Common) ⊗ₜ[L] (a • x) =
      algebraMap L Common a • ((1 : Common) ⊗ₜ[L] x) :=
    (TensorProduct.tmul_smul a (1 : Common) x).trans
      (IsScalarTower.algebraMap_smul Common a ((1 : Common) ⊗ₜ[L] x)).symm
  exact (congrArg (AlgebraTensorModule.cancelBaseChange AmbientRing L Common Common AmbientKaehler) h).trans
    ((AlgebraTensorModule.cancelBaseChange AmbientRing L Common Common AmbientKaehler).map_smul _ _)

theorem surface_conormal_factor :
    secondRetainedMap r θ n₁ t₁ n₂ t₂
        ((1 : Common) ⊗ₜ[P₂] ((1 : P₂) ⊗ₜ[Q₂]
          ambientDifferential (secondEquations r θ) (secondEquations r θ 0))) =
      inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6 •
        firstRetainedEquiv r θ n₁ t₁ n₂ t₂
          ((1 : Common) ⊗ₜ[P₁] ((1 : P₁) ⊗ₜ[Q₁]
            ambientDifferential (firstEquations r θ) (firstEquations r θ 0))) := by
  rw [secondRetainedMap_tmul_D, firstRetainedEquiv_tmul_D]
  have h := congrArg (pushRetained r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceOverlapConormal.surface_conormal_change r θ)
  simpa only [CycleQ2SurfaceOverlapConormal.tensorD, pushRetained_smul,
    pushRetained_tmul, map_pow, inverseCoordinate] using h

theorem cubic_conormal_factor :
    secondRetainedMap r θ n₁ t₁ n₂ t₂
        ((1 : Common) ⊗ₜ[P₂] ((1 : P₂) ⊗ₜ[Q₂]
          ambientDifferential (secondEquations r θ) (secondEquations r θ 1))) =
      inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 3 •
        firstRetainedEquiv r θ n₁ t₁ n₂ t₂
          ((1 : Common) ⊗ₜ[P₁] ((1 : P₁) ⊗ₜ[Q₁]
            ambientDifferential (firstEquations r θ) (firstEquations r θ 1))) := by
  rw [secondRetainedMap_tmul_D, firstRetainedEquiv_tmul_D]
  have h := congrArg (pushRetained r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceOverlapConormal.cubic_conormal_change r θ)
  simpa only [CycleQ2SurfaceOverlapConormal.tensorD, pushRetained_smul,
    pushRetained_tmul, map_pow, inverseCoordinate] using h

@[simp] theorem ambient_inverse :
    algebraMap AmbientRing Common CycleQ2SurfaceOverlapVolume.inverse =
      inverseCoordinate r θ n₁ t₁ n₂ t₂ :=
  congrArg (firstOverlapMap r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceAffineOverlap.ambientMap_inverse (firstEquations r θ))

/-- The scalar extension of the actual ordered coordinate volume. -/
def commonVolume : ⋀[Common]^4 (CommonAmbient r θ n₁ t₁ n₂ t₂) :=
  exteriorPower.ιMulti Common 4 (fun j : Fin 4 =>
    (1 : Common) ⊗ₜ[AmbientRing] CycleQ2SurfaceOverlapVolume.differentialBasis j)

def commonChangedVolume : ⋀[Common]^4 (CommonAmbient r θ n₁ t₁ n₂ t₂) :=
  exteriorPower.ιMulti Common 4 (fun j : Fin 4 =>
    (1 : Common) ⊗ₜ[AmbientRing] CycleQ2SurfaceOverlapVolume.changedDifferentials j)

/-- This is the genuine semilinear exterior scalar extension of the
four-dimensional universal differential calculation. -/
theorem common_volume_change :
    commonChangedVolume r θ n₁ t₁ n₂ t₂ =
      -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6) • commonVolume r θ n₁ t₁ n₂ t₂ := by
  have h := congrArg
    (topBaseChange (S := Common) CycleQ2SurfaceOverlapVolume.differentialBasis)
    CycleQ2SurfaceOverlapVolume.differential_volume_change
  simpa only [CycleQ2SurfaceOverlapVolume.ambientVolume, map_smulₛₗ,
    topBaseChange_wedge, map_neg, map_pow, ambient_inverse,
    commonVolume, commonChangedVolume] using h

theorem ambientOrderedBasis_polynomial (v : Fin 2 → SurfacePoly)
    (n t : SurfacePoly) (j : Fin 4) :
    ambientOrderedBasis v n t j = (1 : AdjunctionPatch v n t) ⊗ₜ[SurfaceChartRing v]
      ambientDifferential v (X (finSuccEquiv 3 j)) := by
  simp only [ambientOrderedBasis, Basis.reindex_apply, localAmbientBasis,
    Basis.baseChange_apply, ambientBasis, Equiv.symm_symm,
    Algebra.Generators.cotangentSpaceBasis_apply, ambientIndexEquiv,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

def firstMappedVolume : ⋀[Common]^4 (CommonAmbient r θ n₁ t₁ n₂ t₂) :=
  ExteriorTransport.image (ambientOrderedBasis (firstEquations r θ) n₁ t₁)
    (firstRetainedEquiv r θ n₁ t₁ n₂ t₂).toLinearMap
    (CycleQ2SurfaceResidueWedge.ambientVolume (firstEquations r θ) n₁ t₁)

def secondMappedVolume : ⋀[Common]^4 (CommonAmbient r θ n₁ t₁ n₂ t₂) :=
  ExteriorTransport.image (ambientOrderedBasis (secondEquations r θ) n₂ t₂)
    (secondRetainedMap r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceResidueWedge.ambientVolume (secondEquations r θ) n₂ t₂)

theorem first_volume :
    firstMappedVolume r θ n₁ t₁ n₂ t₂ = commonVolume r θ n₁ t₁ n₂ t₂ := by
  apply ExteriorTransport.image_basis
  intro j
  exact (congrArg (firstRetainedEquiv r θ n₁ t₁ n₂ t₂)
    (congrArg (fun m : LocalAmbientDifferentials (firstEquations r θ) n₁ t₁ =>
      (1 : Common) ⊗ₜ[P₁] m)
      (ambientOrderedBasis_polynomial (firstEquations r θ) n₁ t₁ j))).trans
        ((firstRetainedEquiv_tmul_D r θ n₁ t₁ n₂ t₂ 1 (X (finSuccEquiv 3 j))).trans
          (congrArg (fun m : AmbientKaehler => (1 : Common) ⊗ₜ[AmbientRing] m)
            (CycleQ2SurfaceOverlapVolume.differentialBasis_apply j).symm))

theorem second_volume :
    secondMappedVolume r θ n₁ t₁ n₂ t₂ = commonChangedVolume r θ n₁ t₁ n₂ t₂ := by
  apply ExteriorTransport.image_basis
  intro j
  exact (congrArg (secondRetainedMap r θ n₁ t₁ n₂ t₂)
    (congrArg (fun m : LocalAmbientDifferentials (secondEquations r θ) n₂ t₂ =>
      (1 : Common) ⊗ₜ[P₂] m)
      (ambientOrderedBasis_polynomial (secondEquations r θ) n₂ t₂ j))).trans
        (secondRetainedMap_tmul_D r θ n₁ t₁ n₂ t₂ 1 (X (finSuccEquiv 3 j)))

/-- The actual ordered patch volumes have factor −b⁻⁶ in the common
retained ambient module. This is the volume premise of the proved
conormal-first residue comparison, with both source volumes unchanged. -/
theorem volume_factor :
    secondMappedVolume r θ n₁ t₁ n₂ t₂ =
      -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6) •
        firstMappedVolume r θ n₁ t₁ n₂ t₂ :=
  (second_volume r θ n₁ t₁ n₂ t₂).trans
    ((common_volume_change r θ n₁ t₁ n₂ t₂).trans
      (congrArg (fun w : ⋀[Common]^4 (CommonAmbient r θ n₁ t₁ n₂ t₂) =>
        -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6) • w)
        (first_volume r θ n₁ t₁ n₂ t₂).symm))

end CycleQ2SurfaceCommonAmbient

end

end


section

/-! Exact unit and weighted-section coefficients on the actual common
surface localization. These identities supply the residue normalization
factor and its cancellation against a cubic section. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceCommonCoefficients

open MvPolynomial CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SurfaceAffineOverlap
  CycleQ2SurfaceCommonLocalization

variable (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)

def commonCoordinate : CommonPatch r θ n₁ t₁ n₂ t₂ :=
  firstOverlapMap r θ n₁ t₁ n₂ t₂ (coordinate (firstEquations r θ) (some 1))

def commonInverse : CommonPatch r θ n₁ t₁ n₂ t₂ :=
  firstOverlapMap r θ n₁ t₁ n₂ t₂ (inverse (firstEquations r θ))

theorem commonCoordinate_mul_inverse :
    commonCoordinate r θ n₁ t₁ n₂ t₂ * commonInverse r θ n₁ t₁ n₂ t₂ = 1 := by
  exact ((firstOverlapMap r θ n₁ t₁ n₂ t₂).map_mul _ _).symm.trans
    ((congrArg (firstOverlapMap r θ n₁ t₁ n₂ t₂)
      (coordinate_mul_inverse (firstEquations r θ))).trans (map_one _))

theorem normalizing_inverse :
    commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 *
        (commonInverse r θ n₁ t₁ n₂ t₂ ^ 6 * commonInverse r θ n₁ t₁ n₂ t₂ ^ 3) = 1 := by
  rw [← pow_add]
  change commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 * commonInverse r θ n₁ t₁ n₂ t₂ ^ 9 = 1
  rw [← mul_pow, commonCoordinate_mul_inverse, one_pow]

theorem normalizing_factor :
    commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 * -(commonInverse r θ n₁ t₁ n₂ t₂ ^ 6) =
      -(commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) := by
  calc
    _ = -(commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3 *
        (commonCoordinate r θ n₁ t₁ n₂ t₂ * commonInverse r θ n₁ t₁ n₂ t₂) ^ 6) := by ring
    _ = _ := by rw [commonCoordinate_mul_inverse, one_pow, mul_one]

@[simp] theorem ambient_inverse :
    CycleQ2SurfaceCommonLocalization.ambientMap r θ n₁ t₁ n₂ t₂
        CycleQ2SurfaceOverlapVolume.inverse = commonInverse r θ n₁ t₁ n₂ t₂ :=
  congrArg (firstOverlapMap r θ n₁ t₁ n₂ t₂)
    (CycleQ2SurfaceAffineOverlap.ambientMap_inverse (firstEquations r θ))

def firstSectionCoefficient (p : MvPolynomial (Fin 5) ℂ) : CommonPatch r θ n₁ t₁ n₂ t₂ :=
  firstPatchMap r θ n₁ t₁ n₂ t₂
    (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁)
      (firstSurfaceDehomogenize p))

def secondSectionCoefficient (p : MvPolynomial (Fin 5) ℂ) : CommonPatch r θ n₁ t₁ n₂ t₂ :=
  secondPatchMap r θ n₁ t₁ n₂ t₂
    (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂)
      (secondSurfaceDehomogenize p))

/-- Every actual weighted homogeneous section has the expected coefficient
on the concrete common ring. Both coefficients use the actual patch maps. -/
theorem secondSectionCoefficient_weighted (p : MvPolynomial (Fin 5) ℂ) {d : ℕ}
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight d) :
    secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p =
      commonInverse r θ n₁ t₁ n₂ t₂ ^ d * firstSectionCoefficient r θ n₁ t₁ n₂ t₂ p := by
  rw [firstSectionCoefficient, secondSectionCoefficient,
    firstPatchMap_polynomial, secondPatchMap_polynomial,
    Volume.homogeneous_change p hp, map_mul, map_pow, ambient_inverse]

theorem cubic_section_residue_factor (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p * commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3 =
      firstSectionCoefficient r θ n₁ t₁ n₂ t₂ p := by
  rw [secondSectionCoefficient_weighted r θ n₁ t₁ n₂ t₂ p hp]
  calc
    _ = firstSectionCoefficient r θ n₁ t₁ n₂ t₂ p *
        (commonCoordinate r θ n₁ t₁ n₂ t₂ * commonInverse r θ n₁ t₁ n₂ t₂) ^ 3 := by ring
    _ = _ := by rw [commonCoordinate_mul_inverse, one_pow, mul_one]

end CycleQ2SurfaceCommonCoefficients
end

end


section

/-! The actual residue transition on the concrete common localization.
Both forms live in the genuine exterior power of Ω over that ring.
The sign and power are forced by the proved ambient, conormal and volume
maps. Cubic sections then cancel the power with the fixed coordinate
orientation. This is a local form identity, not a global support theorem. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceCommonResidue

open Module MvPolynomial
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2SurfaceCommonLocalization CycleQ2SurfaceCommonAmbient
  CycleQ2SurfaceCommonCoefficients CycleQ2SurfaceResidueScalarExtension
  CycleQ2SurfaceResidueComparisonCriterion
  CycleQ2SurfaceResidueWedge CycleQ2ExteriorTopBaseChange CycleQ2SurfaceEtaleResidueLifts
open scoped TensorProduct

section NamedComparison

variable (v₁ v₂ : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra ℂ S]
  [Algebra (AdjunctionPatch v₁ n₁ t₁) S] [Algebra (AdjunctionPatch v₂ n₂ t₂) S]
  [IsScalarTower ℂ (AdjunctionPatch v₁ n₁ t₁) S]
  [IsScalarTower ℂ (AdjunctionPatch v₂ n₂ t₂) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₁ n₁ t₁) S]
  [Algebra.FormallyEtale (AdjunctionPatch v₂ n₂ t₂) S]

theorem compared_residue_transition_named
    (N : Type*) [AddCommGroup N] [Module S N]
    (e : S ⊗[AdjunctionPatch v₁ n₁ t₁] LocalAmbientDifferentials v₁ n₁ t₁ ≃ₗ[S] N)
    (f : S ⊗[AdjunctionPatch v₂ n₂ t₂] LocalAmbientDifferentials v₂ n₂ t₂ →ₗ[S] N)
    (q : N →ₗ[S] KaehlerDifferential ℂ S)
    (a b k d : S) (hd : d * (a * b) = 1)
    (hfirst : ∀ x, q (e x) = etaleToKaehler v₁ n₁ t₁ S x)
    (hsecond : ∀ x, q (f x) = etaleToKaehler v₂ n₂ t₂ S x)
    (hc : ∀ j : Fin 2,
      f ((1 : S) ⊗ₜ[AdjunctionPatch v₂ n₂ t₂]
          ((1 : AdjunctionPatch v₂ n₂ t₂) ⊗ₜ[SurfaceChartRing v₂]
            ambientDifferential v₂ (v₂ j))) =
        ![a,b] j • e ((1 : S) ⊗ₜ[AdjunctionPatch v₁ n₁ t₁]
          ((1 : AdjunctionPatch v₁ n₁ t₁) ⊗ₜ[SurfaceChartRing v₁]
            ambientDifferential v₁ (v₁ j))))
    (hvolume : ExteriorTransport.image (ambientOrderedBasis v₂ n₂ t₂) f (ambientVolume v₂ n₂ t₂) =
      k • ExteriorTransport.image (ambientOrderedBasis v₁ n₁ t₁) e.toLinearMap
        (ambientVolume v₁ n₁ t₁)) :
    etaleResidue v₂ n₂ t₂ S = (d * k) • etaleResidue v₁ n₁ t₁ S :=
  compared_residue_transition v₁ v₂ n₁ t₁ n₂ t₂ S N e f q a b k d hd
    hfirst hsecond hc hvolume

end NamedComparison

theorem negative_product_smul {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (s a : R) (w : M) : (s * a) • w = -(s • ((-a) • w)) := by
  simp only [mul_smul, neg_smul, smul_neg, neg_neg]

attribute [local instance] CycleQ2SurfaceChangedAmbient.secondChartAlgebra
  CycleQ2SurfaceOverlapConormal.firstAmbientAlgebra
  commonSecondChartAlgebra commonAmbientAlgebra
  commonSecondChartTower commonSecondComplexTower commonAmbientTower commonAmbientComplexTower
  firstPatchAlgebra secondPatchAlgebra firstPatchComplexTower secondPatchComplexTower
  firstPatchChartTower secondPatchChartTower firstPatch_formallyEtale secondPatch_formallyEtale

variable (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)

local notation "Common" => CommonPatch r θ n₁ t₁ n₂ t₂

/-- The actual first-chart residue after its genuine formally étale map. -/
def firstResidue : ⋀[Common]^2 (KaehlerDifferential ℂ Common) :=
  etaleResidue (firstEquations r θ) n₁ t₁ Common

/-- The actual second-chart residue after its genuine formally étale map. -/
def secondResidue : ⋀[Common]^2 (KaehlerDifferential ℂ Common) :=
  etaleResidue (secondEquations r θ) n₂ t₂ Common

theorem inverseCoordinate_eq : inverseCoordinate r θ n₁ t₁ n₂ t₂ =
    commonInverse r θ n₁ t₁ n₂ t₂ := rfl

theorem inverse_normalization :
    commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 *
      (inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6 *
        inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) = 1 := by
  rw [inverseCoordinate_eq]
  exact normalizing_inverse r θ n₁ t₁ n₂ t₂

theorem residue_factor_normalization :
    commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 *
      -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6) =
        -(commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) := by
  rw [inverseCoordinate_eq]
  exact normalizing_factor r θ n₁ t₁ n₂ t₂

theorem mappedVolume_comparison :
    ExteriorTransport.image (T := Common) (N := CommonAmbient r θ n₁ t₁ n₂ t₂)
        (ambientOrderedBasis (secondEquations r θ) n₂ t₂)
        (secondRetainedMap r θ n₁ t₁ n₂ t₂)
        (ambientVolume (secondEquations r θ) n₂ t₂) =
      -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6) •
        ExteriorTransport.image (T := Common) (N := CommonAmbient r θ n₁ t₁ n₂ t₂)
          (ambientOrderedBasis (firstEquations r θ) n₁ t₁)
          (firstRetainedEquiv r θ n₁ t₁ n₂ t₂).toLinearMap
          (ambientVolume (firstEquations r θ) n₁ t₁) :=
  volume_factor r θ n₁ t₁ n₂ t₂

theorem conormal_comparison (j : Fin 2) :
    secondRetainedMap r θ n₁ t₁ n₂ t₂
        ((1 : Common) ⊗ₜ[AdjunctionPatch (secondEquations r θ) n₂ t₂]
          ((1 : AdjunctionPatch (secondEquations r θ) n₂ t₂) ⊗ₜ[SurfaceChartRing (secondEquations r θ)]
            ambientDifferential (secondEquations r θ) (secondEquations r θ j))) =
      ![inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6,
        inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 3] j •
        firstRetainedEquiv r θ n₁ t₁ n₂ t₂
          ((1 : Common) ⊗ₜ[AdjunctionPatch (firstEquations r θ) n₁ t₁]
            ((1 : AdjunctionPatch (firstEquations r θ) n₁ t₁) ⊗ₜ[SurfaceChartRing (firstEquations r θ)]
              ambientDifferential (firstEquations r θ) (firstEquations r θ j))) := by
  fin_cases j
  · exact surface_conormal_factor r θ n₁ t₁ n₂ t₂
  · exact cubic_conormal_factor r θ n₁ t₁ n₂ t₂

/-- Specialization of the proved comparison to the actual ring and maps.
Its remaining arguments are precisely the proved comparison identities. -/
def concreteResidueComparison :=
  compared_residue_transition_named
    (firstEquations r θ) (secondEquations r θ) n₁ t₁ n₂ t₂ Common
    (CommonAmbient r θ n₁ t₁ n₂ t₂)
    (firstRetainedEquiv r θ n₁ t₁ n₂ t₂)
    (secondRetainedMap r θ n₁ t₁ n₂ t₂)
    (quotient r θ n₁ t₁ n₂ t₂)
    (inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6)
    (inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 3)
    (-(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6))
    (commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9)


theorem rawResidue_factor :
    secondResidue r θ n₁ t₁ n₂ t₂ =
      (commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 9 *
        -(inverseCoordinate r θ n₁ t₁ n₂ t₂ ^ 6)) • firstResidue r θ n₁ t₁ n₂ t₂ :=
  concreteResidueComparison r θ n₁ t₁ n₂ t₂
    (inverse_normalization r θ n₁ t₁ n₂ t₂)
    (fun x => LinearMap.congr_fun (first_quotient_square r θ n₁ t₁ n₂ t₂) x)
    (fun x => LinearMap.congr_fun (second_quotient_square r θ n₁ t₁ n₂ t₂) x)
    (conormal_comparison r θ n₁ t₁ n₂ t₂)
    (mappedVolume_comparison r θ n₁ t₁ n₂ t₂)

/-- Closed transition of the actual residues. All quotient and ambient
comparison identities are proved for the literal common localization. -/
theorem rawResidue_transition :
    secondResidue r θ n₁ t₁ n₂ t₂ =
      -(commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) • firstResidue r θ n₁ t₁ n₂ t₂ :=
  (rawResidue_factor r θ n₁ t₁ n₂ t₂).trans
    (congrArg (fun a : Common => a • firstResidue r θ n₁ t₁ n₂ t₂)
      (residue_factor_normalization r θ n₁ t₁ n₂ t₂))

def firstCubicForm (p : MvPolynomial (Fin 5) ℂ) : ⋀[Common]^2 (KaehlerDifferential ℂ Common) :=
  firstSectionCoefficient r θ n₁ t₁ n₂ t₂ p • firstResidue r θ n₁ t₁ n₂ t₂

def secondCubicForm (p : MvPolynomial (Fin 5) ℂ) : ⋀[Common]^2 (KaehlerDifferential ℂ Common) :=
  -(secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p • secondResidue r θ n₁ t₁ n₂ t₂)

/-- With the fixed alternating coordinate orientation, every weighted
cubic gives the same actual two-form on this common localization. -/
theorem orientedCubicForms_agree (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3) :
    firstCubicForm r θ n₁ t₁ n₂ t₂ p = secondCubicForm r θ n₁ t₁ n₂ t₂ p := by
  calc
    _ = (secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p *
        commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) • firstResidue r θ n₁ t₁ n₂ t₂ :=
      congrArg (fun a : Common => a • firstResidue r θ n₁ t₁ n₂ t₂)
        (cubic_section_residue_factor r θ n₁ t₁ n₂ t₂ p hp).symm
    _ = -(secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p •
        (-(commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) • firstResidue r θ n₁ t₁ n₂ t₂)) :=
      negative_product_smul (R := Common) (M := ⋀[Common]^2 (KaehlerDifferential ℂ Common))
        (secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p)
        (commonCoordinate r θ n₁ t₁ n₂ t₂ ^ 3) (firstResidue r θ n₁ t₁ n₂ t₂)
    _ = _ := (congrArg
      (fun w : ⋀[Common]^2 (KaehlerDifferential ℂ Common) =>
        -(secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p • w))
      (rawResidue_transition r θ n₁ t₁ n₂ t₂)).symm

end CycleQ2SurfaceCommonResidue
end

end


section

/-! Independence of the actual surface residue from the chosen augmented
Jacobian frame. Both choices are compared after their genuine formally
étale maps to one algebra, retaining the original ambient presentation. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceResidueRefinement

open Module TensorProduct CycleQ2GeometricSurfaceAdjunction
  CycleQ2SurfaceResidueWedge CycleQ2SurfaceResidueScalarExtension
  CycleQ2SurfacePatchCotangentBinding CycleQ2SurfaceEtaleResidueLifts
  CycleQ2SurfaceResidueComparisonCriterion CycleQ2ExteriorTopBaseChange
open scoped TensorProduct

section Exterior

variable {R T M N : Type*} [CommRing R] [CommRing T] [Algebra R T]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module T N] {d : ℕ}

theorem mapped_baseChange_basis (b : Basis (Fin d) R M)
    (f : T ⊗[R] M →ₗ[T] N) (w : Fin d → N)
    (h : ∀ j, f ((1 : T) ⊗ₜ[R] b j) = w j) :
    exteriorPower.map d f (topBaseChange (S := T) b
        (exteriorPower.ιMulti R d b)) = exteriorPower.ιMulti T d w := by
  rw [topBaseChange_wedge, exteriorPower.map_apply_ιMulti]
  exact congrArg (exteriorPower.ιMulti T d) (funext h)

end Exterior

variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (S : Type*) [CommRing S] [Algebra (SurfaceChartRing v) S]
  [Algebra (AdjunctionPatch v n t) S]
  [IsScalarTower (SurfaceChartRing v) (AdjunctionPatch v n t) S]

/-- The common ambient volume retains the original polynomial coordinates. -/
def retainedVolume : ⋀[S]^4 (S ⊗[SurfaceChartRing v] AmbientDifferentials v) :=
  exteriorPower.ιMulti S 4 (fun j =>
    (1 : S) ⊗ₜ[SurfaceChartRing v]
      ((ambientBasis v).reindex (finSumFinEquiv : AmbientIndex ≃ Fin 4)) j)

theorem patchPresentationEquiv_basis (j : AmbientIndex) :
    patchPresentationEquiv v n t S
      ((1 : S) ⊗ₜ[AdjunctionPatch v n t] localAmbientBasis v n t j) =
        (1 : S) ⊗ₜ[SurfaceChartRing v] ambientBasis v j := by
  simp only [localAmbientBasis, Basis.baseChange_apply, patchPresentationEquiv,
    AlgebraTensorModule.cancelBaseChange_tmul, one_smul]

theorem patchPresentationEquiv_volume :
    exteriorPower.map 4 (patchPresentationEquiv v n t S).toLinearMap
        (topBaseChange (S := S) (ambientOrderedBasis v n t) (ambientVolume v n t)) =
      retainedVolume v S := by
  apply mapped_baseChange_basis
  intro j
  simpa only [Function.comp_apply, ambientOrderedBasis, Basis.reindex_apply,
    LinearEquiv.coe_coe] using
    patchPresentationEquiv_basis v n t S
      ((finSumFinEquiv : AmbientIndex ≃ Fin 4).symm j)

variable [Algebra ℂ S] [IsScalarTower ℂ (SurfaceChartRing v) S]

/-- The quotient to actual differentials depends on the original surface
presentation and the common algebra, independently of either Jacobian patch. -/
def retainedQuotient : (S ⊗[SurfaceChartRing v] AmbientDifferentials v) →ₗ[S]
    KaehlerDifferential ℂ S :=
  (KaehlerDifferential.mapBaseChange ℂ (SurfaceChartRing v) S).comp
    ((presentation v).toExtension.toKaehler.baseChange S)

theorem retainedQuotient_square
    [IsScalarTower ℂ (AdjunctionPatch v n t) S]
    [Algebra.FormallyEtale (AdjunctionPatch v n t) S]
    (x : S ⊗[AdjunctionPatch v n t] LocalAmbientDifferentials v n t) :
    retainedQuotient v S (patchPresentationEquiv v n t S x) =
      etaleToKaehler v n t S x :=
  (LinearMap.congr_fun (etaleToKaehler_eq_presentation v n t S) x).symm

variable (n₁ t₁ n₂ t₂ : SurfacePoly)
  [Algebra (AdjunctionPatch v n₁ t₁) S]
  [Algebra (AdjunctionPatch v n₂ t₂) S]
  [IsScalarTower (SurfaceChartRing v) (AdjunctionPatch v n₁ t₁) S]
  [IsScalarTower (SurfaceChartRing v) (AdjunctionPatch v n₂ t₂) S]
  [IsScalarTower ℂ (AdjunctionPatch v n₁ t₁) S]
  [IsScalarTower ℂ (AdjunctionPatch v n₂ t₂) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n₁ t₁) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n₂ t₂) S]

/-- The genuine residue in Ω² of a common étale algebra is independent of
the pair used to invert an augmented Jacobian determinant. -/
theorem etaleResidue_independent :
    etaleResidue v n₂ t₂ S = etaleResidue v n₁ t₁ S := by
  have h := compared_residue_transition v v n₁ t₁ n₂ t₂ S
    (S ⊗[SurfaceChartRing v] AmbientDifferentials v)
    (patchPresentationEquiv v n₁ t₁ S)
    (patchPresentationEquiv v n₂ t₂ S).toLinearMap
    (retainedQuotient v S) 1 1 1 1 (by simp only [mul_one])
    (retainedQuotient_square v n₁ t₁ S)
    (retainedQuotient_square v n₂ t₂ S)
    (by
      intro j
      change patchPresentationEquiv v n₂ t₂ S _ =
        ![(1 : S), 1] j • patchPresentationEquiv v n₁ t₁ S _
      rw [patchPresentationEquiv_tmul_D, patchPresentationEquiv_tmul_D]
      fin_cases j <;> exact (one_smul S _).symm)
    (by
      exact (patchPresentationEquiv_volume v n₂ t₂ S).trans
        ((patchPresentationEquiv_volume v n₁ t₁ S).symm.trans
          (one_smul S _).symm))
  simpa only [mul_one, one_smul] using h

end CycleQ2SurfaceResidueRefinement
end

end


section

/-!
# The actual common surface localization as a projective open

The canonical projective overlap is compared with the literal overlap
used by the retained ambient calculation. The common augmented-Jacobian
localization then presents the intersection of the two actual patch opens.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceCommonOpen

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading
open CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2SurfaceAffineOverlap CycleQ2SurfaceCommonLocalization

attribute [local instance] CycleQ2SurfaceChangedAmbient.secondChartAlgebra

theorem projective_coordinate_eq (v : Fin 2 → SurfacePoly) (j : Option (Fin 3)) :
    CycleQ2GeometricSurfaceOverlap.coordinate v j = coordinate v j := rfl

/-- Both definitions invert the actual middle coordinate. -/
theorem projective_inverse_eq (v : Fin 2 → SurfacePoly) :
    CycleQ2GeometricSurfaceOverlap.inverse v = inverse v := by
  have hu : IsUnit (coordinate v (some 1)) := by
    simpa only [middleUnit_val] using (middleUnit v).isUnit
  apply hu.mul_left_cancel
  exact (CycleQ2GeometricSurfaceOverlap.coordinate_mul_inverse v).trans
    (coordinate_mul_inverse v).symm

/-- The canonical Proj overlap map is exactly the literal map used by
our universal differential and conormal calculations. -/
theorem projective_overlapEquiv_eq (r θ : ℂ) :
    CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ = overlapEquiv r θ := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply coordinate_algHom_ext (secondEquations r θ)
  intro j
  change CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
    (CycleQ2GeometricSurfaceOverlap.coordinate (secondEquations r θ) j) =
      overlapEquiv r θ (polynomialMap (secondEquations r θ) (X j))
  rw [overlapEquiv_polynomialMap]
  cases j with
  | none =>
      rw [changeEvaluation_normal]
      exact (CycleQ2GeometricSurfaceOverlap.overlapEquiv_normalCoordinate r θ).trans (by
        rw [projective_coordinate_eq, projective_inverse_eq]
        rfl)
  | some i =>
      fin_cases i
      · change CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
          (CycleQ2GeometricSurfaceOverlap.coordinate (secondEquations r θ) (some 0)) =
            changeEvaluation (firstEquations r θ) (X (some 0))
        rw [changeEvaluation_first]
        exact (CycleQ2GeometricSurfaceOverlap.overlapEquiv_coordinate0 r θ).trans (by
          rw [projective_coordinate_eq, projective_inverse_eq]
          rfl)
      · change CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
          (CycleQ2GeometricSurfaceOverlap.coordinate (secondEquations r θ) (some 1)) =
            changeEvaluation (firstEquations r θ) (X (some 1))
        rw [changeEvaluation_middle]
        exact (CycleQ2GeometricSurfaceOverlap.overlapEquiv_coordinate1 r θ).trans
          (projective_inverse_eq _)
      · change CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
          (CycleQ2GeometricSurfaceOverlap.coordinate (secondEquations r θ) (some 2)) =
            changeEvaluation (firstEquations r θ) (X (some 2))
        rw [changeEvaluation_last]
        exact (CycleQ2GeometricSurfaceOverlap.overlapEquiv_coordinate2 r θ).trans (by
          rw [projective_coordinate_eq, projective_inverse_eq]
          rfl)

theorem first_projective_restriction (r θ : ℂ) :
    (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom.comp
        (CycleQ2GeometricSurfaceOverlap.firstRestriction r θ) =
      (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ)).comp
        (firstChartEquiv r θ).toRingHom := by
  ext a
  exact CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv_restriction r θ a

theorem second_projective_restriction (r θ : ℂ) :
    (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom.comp
        (CycleQ2GeometricSurfaceOverlap.secondRestriction r θ) =
      (algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ)).comp
        (secondChartEquiv r θ).toRingHom := by
  ext a
  change CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ
      (CycleQ2GeometricSurfaceOverlap.secondRestriction r θ a) =
    algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ)
      (secondChartEquiv r θ a)
  calc
    _ = CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
        (CycleQ2GeometricSurfaceOverlap.secondOverlapEquiv r θ
          (CycleQ2GeometricSurfaceOverlap.secondRestriction r θ a)) := by
      simp only [CycleQ2GeometricSurfaceOverlap.overlapEquiv, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply]
    _ = CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ
        (algebraMap (SurfaceChartRing (secondEquations r θ)) (SecondOverlap r θ)
          (secondChartEquiv r θ a)) :=
      congrArg (CycleQ2GeometricSurfaceOverlap.overlapEquiv r θ)
        (CycleQ2GeometricSurfaceOverlap.secondOverlapEquiv_restriction r θ a)
    _ = _ := by
      rw [projective_overlapEquiv_eq]
      exact (CycleQ2SurfaceChangedAmbient.secondChartAlgebraMap r θ
        (secondChartEquiv r θ a)).symm

def overlapChart (r θ : ℂ) :
    (CycleQ2GeometricSurfaceOverlap.overlapPatch r θ).toScheme ≅
      Spec (CommRingCat.of (FirstOverlap r θ)) :=
  Proj.basicOpenIsoSpec (surfaceGrade r θ)
      (CycleQ2GeometricSurfaceOverlap.overlapDen r θ)
      (CycleQ2GeometricSurfaceOverlap.overlapDen_mem_grade r θ) (by decide) ≪≫
    Scheme.Spec.mapIso
      (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingEquiv.toCommRingCatIso.symm.op

def overlapEmbedding (r θ : ℂ) :
    Spec (CommRingCat.of (FirstOverlap r θ)) ⟶ projectiveSurface r θ :=
  (overlapChart r θ).inv ≫ (CycleQ2GeometricSurfaceOverlap.overlapPatch r θ).ι

instance overlapEmbedding_isOpenImmersion (r θ : ℂ) :
    IsOpenImmersion (overlapEmbedding r θ) := by
  unfold overlapEmbedding
  infer_instance

theorem overlapEmbedding_range (r θ : ℂ) :
    (overlapEmbedding r θ).opensRange = coordinatePatch r θ 1 ⊓ coordinatePatch r θ 2 :=
  ((Scheme.Hom.opensRange_comp_of_isIso (overlapChart r θ).inv
      (CycleQ2GeometricSurfaceOverlap.overlapPatch r θ).ι).trans
    (CycleQ2GeometricSurfaceOverlap.overlapPatch r θ).opensRange_ι).trans
      (CycleQ2GeometricSurfaceOverlap.overlapPatch_eq r θ)

theorem overlapEmbedding_product (r θ : ℂ) :
    overlapEmbedding r θ =
      Spec.map (CommRingCat.ofHom
          (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom) ≫
        Proj.awayι (surfaceGrade r θ) (CycleQ2GeometricSurfaceOverlap.overlapDen r θ)
          (CycleQ2GeometricSurfaceOverlap.overlapDen_mem_grade r θ) (by decide) :=
  CycleQ2GeometricSurfaceCurveCharts.basicOpenChart_inv_ι (surfaceGrade r θ)
    (CycleQ2GeometricSurfaceOverlap.overlapDen r θ)
    (CycleQ2GeometricSurfaceOverlap.overlapDen_mem_grade r θ) (by decide)
    (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingEquiv

def firstCoordinateEmbedding (r θ : ℂ) :
    Spec (CommRingCat.of (SurfaceChartRing (firstEquations r θ))) ⟶ projectiveSurface r θ :=
  (firstAffineChart r θ).inv ≫ (coordinatePatch r θ 1).ι

def secondCoordinateEmbedding (r θ : ℂ) :
    Spec (CommRingCat.of (SurfaceChartRing (secondEquations r θ))) ⟶ projectiveSurface r θ :=
  (secondAffineChart r θ).inv ≫ (coordinatePatch r θ 2).ι

instance firstCoordinateEmbedding_isOpenImmersion (r θ : ℂ) :
    IsOpenImmersion (firstCoordinateEmbedding r θ) := by
  unfold firstCoordinateEmbedding
  infer_instance

instance secondCoordinateEmbedding_isOpenImmersion (r θ : ℂ) :
    IsOpenImmersion (secondCoordinateEmbedding r θ) := by
  unfold secondCoordinateEmbedding
  infer_instance

section SpecHelpers

variable {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  {X : Scheme}

theorem spec_factorization (f : A →+* B) (g : B →+* D)
    (f' : A →+* C) (g' : C →+* D) (h : g.comp f = g'.comp f')
    (u : Spec (CommRingCat.of A) ⟶ X) :
    Spec.map (CommRingCat.ofHom g) ≫ (Spec.map (CommRingCat.ofHom f) ≫ u) =
      Spec.map (CommRingCat.ofHom g') ≫ (Spec.map (CommRingCat.ofHom f') ≫ u) := by
  simp only [← Category.assoc, ← Spec.map_comp]
  exact congrArg (fun k : A →+* D => Spec.map (CommRingCat.ofHom k) ≫ u) h

theorem localization_range (a : A) :
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))).opensRange =
      PrimeSpectrum.basicOpen a := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (Localization.Away a) a

theorem spec_algHom_overComplex [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (u : Spec (CommRingCat.of A) ⟶ X)
    (c : X ⟶ Spec (CommRingCat.of ℂ))
    (hu : u ≫ c = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ u) ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ B)) := by
  rw [Category.assoc, hu, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext z
  exact f.commutes z

end SpecHelpers

theorem overlapEmbedding_first (r θ : ℂ) :
    overlapEmbedding r θ =
      Spec.map (CommRingCat.ofHom
          (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))) ≫
        firstCoordinateEmbedding r θ := by
  have h := Proj.SpecMap_awayMap_awayι (surfaceGrade r θ)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2)
    (x := CycleQ2GeometricSurfaceOverlap.overlapDen r θ) rfl
  have hmap := spec_factorization
    (CycleQ2GeometricSurfaceOverlap.firstRestriction r θ)
    (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom
    (firstChartEquiv r θ).toRingHom
    (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))
    (first_projective_restriction r θ)
    (Proj.awayι (surfaceGrade r θ)
      (CycleQ2GeometricSurfaceOverlap.coordinateDen r θ 1)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1) (by decide))
  exact (overlapEmbedding_product r θ).trans
    ((congrArg (fun k => Spec.map (CommRingCat.ofHom
        (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom) ≫ k) h).symm.trans
      (hmap.trans (congrArg (fun k => Spec.map (CommRingCat.ofHom
        (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))) ≫ k)
        (CycleQ2GeometricSurfaceCurveCharts.firstSurfaceAffineChart_inv_ι r θ).symm)))

theorem overlapEmbedding_second (r θ : ℂ) :
    overlapEmbedding r θ =
      Spec.map (CommRingCat.ofHom
          (algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ))) ≫
        secondCoordinateEmbedding r θ := by
  have h := Proj.SpecMap_awayMap_awayι (surfaceGrade r θ)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide)
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 1)
    (x := CycleQ2GeometricSurfaceOverlap.overlapDen r θ) (mul_comm _ _)
  have hmap := spec_factorization
    (CycleQ2GeometricSurfaceOverlap.secondRestriction r θ)
    (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom
    (secondChartEquiv r θ).toRingHom
    (algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ))
    (second_projective_restriction r θ)
    (Proj.awayι (surfaceGrade r θ)
      (CycleQ2GeometricSurfaceOverlap.coordinateDen r θ 2)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade r θ 2) (by decide))
  exact (overlapEmbedding_product r θ).trans
    ((congrArg (fun k => Spec.map (CommRingCat.ofHom
        (CycleQ2GeometricSurfaceOverlap.firstOverlapEquiv r θ).toRingHom) ≫ k) h).symm.trans
      (hmap.trans (congrArg (fun k => Spec.map (CommRingCat.ofHom
        (algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ))) ≫ k)
        (CycleQ2GeometricSurfaceCurveCharts.secondSurfaceAffineChart_inv_ι r θ).symm)))

def firstPatchEmbedding (r θ : ℂ) (n t : SurfacePoly) :
    Spec (CommRingCat.of (AdjunctionPatch (firstEquations r θ) n t)) ⟶ projectiveSurface r θ :=
  principalImmersion (firstAffineChart r θ) (augmentedJacobian (firstEquations r θ) n t)

def secondPatchEmbedding (r θ : ℂ) (n t : SurfacePoly) :
    Spec (CommRingCat.of (AdjunctionPatch (secondEquations r θ) n t)) ⟶ projectiveSurface r θ :=
  principalImmersion (secondAffineChart r θ) (augmentedJacobian (secondEquations r θ) n t)

instance firstPatchEmbedding_isOpenImmersion (r θ : ℂ) (n t : SurfacePoly) :
    IsOpenImmersion (firstPatchEmbedding r θ n t) := by
  unfold firstPatchEmbedding
  infer_instance

instance secondPatchEmbedding_isOpenImmersion (r θ : ℂ) (n t : SurfacePoly) :
    IsOpenImmersion (secondPatchEmbedding r θ n t) := by
  unfold secondPatchEmbedding
  infer_instance

def firstPatchOpen (r θ : ℂ) (n t : SurfacePoly) : (projectiveSurface r θ).Opens :=
  principalOpen (firstAffineChart r θ) (augmentedJacobian (firstEquations r θ) n t)

def secondPatchOpen (r θ : ℂ) (n t : SurfacePoly) : (projectiveSurface r θ).Opens :=
  principalOpen (secondAffineChart r θ) (augmentedJacobian (secondEquations r θ) n t)

def firstPatchChart (r θ : ℂ) (n t : SurfacePoly) :
    (firstPatchOpen r θ n t).toScheme ≅
      Spec (CommRingCat.of (AdjunctionPatch (firstEquations r θ) n t)) :=
  principalChart (firstAffineChart r θ) (augmentedJacobian (firstEquations r θ) n t)

def secondPatchChart (r θ : ℂ) (n t : SurfacePoly) :
    (secondPatchOpen r θ n t).toScheme ≅
      Spec (CommRingCat.of (AdjunctionPatch (secondEquations r θ) n t)) :=
  principalChart (secondAffineChart r θ) (augmentedJacobian (secondEquations r θ) n t)

theorem firstPatchChart_inv_ι (r θ : ℂ) (n t : SurfacePoly) :
    (firstPatchChart r θ n t).inv ≫ (firstPatchOpen r θ n t).ι =
      firstPatchEmbedding r θ n t := principalChart_inv_ι _ _

theorem secondPatchChart_inv_ι (r θ : ℂ) (n t : SurfacePoly) :
    (secondPatchChart r θ n t).inv ≫ (secondPatchOpen r θ n t).ι =
      secondPatchEmbedding r θ n t := principalChart_inv_ι _ _

theorem firstPatchOpen_le (r θ : ℂ) (n t : SurfacePoly) :
    firstPatchOpen r θ n t ≤ coordinatePatch r θ 1 :=
  CycleQ2GeometricPrincipalChartSections.principalOpen_le _ _

theorem secondPatchOpen_le (r θ : ℂ) (n t : SurfacePoly) :
    secondPatchOpen r θ n t ≤ coordinatePatch r θ 2 :=
  CycleQ2GeometricPrincipalChartSections.principalOpen_le _ _

theorem firstPatchOpen_image (r θ : ℂ) (n t : SurfacePoly) :
    firstPatchOpen r θ n t = firstCoordinateEmbedding r θ ''ᵁ
      PrimeSpectrum.basicOpen (augmentedJacobian (firstEquations r θ) n t) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (SurfaceChartRing (firstEquations r θ))
      (AdjunctionPatch (firstEquations r θ) n t))) ≫ firstCoordinateEmbedding r θ).opensRange = _
  rw [Scheme.Hom.opensRange_comp, localization_range]

theorem secondPatchOpen_image (r θ : ℂ) (n t : SurfacePoly) :
    secondPatchOpen r θ n t = secondCoordinateEmbedding r θ ''ᵁ
      PrimeSpectrum.basicOpen (augmentedJacobian (secondEquations r θ) n t) := by
  change (Spec.map (CommRingCat.ofHom
    (algebraMap (SurfaceChartRing (secondEquations r θ))
      (AdjunctionPatch (secondEquations r θ) n t))) ≫ secondCoordinateEmbedding r θ).opensRange = _
  rw [Scheme.Hom.opensRange_comp, localization_range]

theorem overlap_preimage_firstPatch (r θ : ℂ) (n t : SurfacePoly) :
    overlapEmbedding r θ ⁻¹ᵁ firstPatchOpen r θ n t =
      PrimeSpectrum.basicOpen (firstJacobianImage r θ n t) := by
  rw [overlapEmbedding_first, firstPatchOpen_image]
  change Spec.map (CommRingCat.ofHom
    (algebraMap (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))) ⁻¹ᵁ
      (firstCoordinateEmbedding r θ ⁻¹ᵁ (firstCoordinateEmbedding r θ ''ᵁ
        PrimeSpectrum.basicOpen (augmentedJacobian (firstEquations r θ) n t))) = _
  erw [Scheme.Hom.preimage_image_eq]
  exact SpecMap_preimage_basicOpen _ _

theorem overlap_preimage_secondPatch (r θ : ℂ) (n t : SurfacePoly) :
    overlapEmbedding r θ ⁻¹ᵁ secondPatchOpen r θ n t =
      PrimeSpectrum.basicOpen (secondJacobianImage r θ n t) := by
  rw [overlapEmbedding_second, secondPatchOpen_image]
  change Spec.map (CommRingCat.ofHom
    (algebraMap (SurfaceChartRing (secondEquations r θ)) (FirstOverlap r θ))) ⁻¹ᵁ
      (secondCoordinateEmbedding r θ ⁻¹ᵁ (secondCoordinateEmbedding r θ ''ᵁ
        PrimeSpectrum.basicOpen (augmentedJacobian (secondEquations r θ) n t))) = _
  erw [Scheme.Hom.preimage_image_eq]
  exact SpecMap_preimage_basicOpen _ _

def commonEmbedding (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    Spec (CommRingCat.of (CommonPatch r θ n₁ t₁ n₂ t₂)) ⟶ projectiveSurface r θ :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂))) ≫
    overlapEmbedding r θ

instance commonEmbedding_isOpenImmersion (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    IsOpenImmersion (commonEmbedding r θ n₁ t₁ n₂ t₂) := by
  unfold commonEmbedding
  infer_instance

theorem commonEmbedding_first (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    commonEmbedding r θ n₁ t₁ n₂ t₂ =
      Spec.map (CommRingCat.ofHom (firstPatchMap r θ n₁ t₁ n₂ t₂).toRingHom) ≫
        firstPatchEmbedding r θ n₁ t₁ := by
  rw [commonEmbedding, overlapEmbedding_first]
  apply spec_factorization
  apply RingHom.ext
  intro a
  exact (firstPatchMap_base r θ n₁ t₁ n₂ t₂ a).symm

theorem commonEmbedding_second (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    commonEmbedding r θ n₁ t₁ n₂ t₂ =
      Spec.map (CommRingCat.ofHom (secondPatchMap r θ n₁ t₁ n₂ t₂).toRingHom) ≫
        secondPatchEmbedding r θ n₂ t₂ := by
  rw [commonEmbedding, overlapEmbedding_second]
  apply spec_factorization
  apply RingHom.ext
  intro a
  exact (secondPatchMap_base r θ n₁ t₁ n₂ t₂ a).symm

/-- The common localization presents precisely the actual intersection,
without a supplied comparison isomorphism or open-cover assumption. -/
theorem commonEmbedding_range (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonEmbedding r θ n₁ t₁ n₂ t₂).opensRange =
      firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂ := by
  have hp : overlapEmbedding r θ ⁻¹ᵁ
      (firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂) =
      PrimeSpectrum.basicOpen (commonDenominator r θ n₁ t₁ n₂ t₂) := by
    rw [Scheme.Hom.preimage_inf, overlap_preimage_firstPatch, overlap_preimage_secondPatch]
    exact (PrimeSpectrum.basicOpen_mul _ _).symm
  have hi : (coordinatePatch r θ 1 ⊓ coordinatePatch r θ 2) ⊓
      (firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂) =
      firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂ :=
    inf_eq_right.mpr (le_inf
      (inf_le_left.trans (firstPatchOpen_le r θ n₁ t₁))
      (inf_le_right.trans (secondPatchOpen_le r θ n₂ t₂)))
  calc
    (commonEmbedding r θ n₁ t₁ n₂ t₂).opensRange =
        overlapEmbedding r θ ''ᵁ
          PrimeSpectrum.basicOpen (commonDenominator r θ n₁ t₁ n₂ t₂) :=
      (Scheme.Hom.opensRange_comp (Spec.map (CommRingCat.ofHom
        (algebraMap (FirstOverlap r θ) (CommonPatch r θ n₁ t₁ n₂ t₂))))
        (overlapEmbedding r θ)).trans
        (congrArg (fun U => overlapEmbedding r θ ''ᵁ U)
          (localization_range (commonDenominator r θ n₁ t₁ n₂ t₂)))
    _ = overlapEmbedding r θ ''ᵁ (overlapEmbedding r θ ⁻¹ᵁ
        (firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂)) :=
      congrArg (fun U => overlapEmbedding r θ ''ᵁ U) hp.symm
    _ = (overlapEmbedding r θ).opensRange ⊓
        (firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂) :=
      Scheme.Hom.image_preimage_eq_opensRange_inf _ _
    _ = _ := (congrArg (fun U => U ⊓
      (firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂))
      (overlapEmbedding_range r θ)).trans hi

def commonOpen (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) : (projectiveSurface r θ).Opens :=
  firstPatchOpen r θ n₁ t₁ ⊓ secondPatchOpen r θ n₂ t₂

def commonChart (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonOpen r θ n₁ t₁ n₂ t₂).toScheme ≅
      Spec (CommRingCat.of (CommonPatch r θ n₁ t₁ n₂ t₂)) :=
  IsOpenImmersion.isoOfRangeEq (commonOpen r θ n₁ t₁ n₂ t₂).ι
    (commonEmbedding r θ n₁ t₁ n₂ t₂) (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (commonEmbedding_range r θ n₁ t₁ n₂ t₂).symm)

theorem commonChart_inv_ι (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonChart r θ n₁ t₁ n₂ t₂).inv ≫ (commonOpen r θ n₁ t₁ n₂ t₂).ι =
      commonEmbedding r θ n₁ t₁ n₂ t₂ :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

theorem commonChart_first (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonChart r θ n₁ t₁ n₂ t₂).inv ≫ (commonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (firstPatchMap r θ n₁ t₁ n₂ t₂).toRingHom) ≫
        (firstPatchChart r θ n₁ t₁).inv ≫ (firstPatchOpen r θ n₁ t₁).ι := by
  rw [commonChart_inv_ι, commonEmbedding_first, firstPatchChart_inv_ι]

theorem commonChart_second (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonChart r θ n₁ t₁ n₂ t₂).inv ≫ (commonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (secondPatchMap r θ n₁ t₁ n₂ t₂).toRingHom) ≫
        (secondPatchChart r θ n₂ t₂).inv ≫ (secondPatchOpen r θ n₂ t₂).ι := by
  rw [commonChart_inv_ι, commonEmbedding_second, secondPatchChart_inv_ι]

theorem overlapEmbedding_overComplex (r θ : ℂ) :
    overlapEmbedding r θ ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (FirstOverlap r θ))) := by
  rw [overlapEmbedding_first]
  apply spec_algHom_overComplex
    (IsScalarTower.toAlgHom ℂ (SurfaceChartRing (firstEquations r θ)) (FirstOverlap r θ))
  simpa only [firstCoordinateEmbedding, Category.assoc] using
    CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ

theorem commonEmbedding_overComplex (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    commonEmbedding r θ n₁ t₁ n₂ t₂ ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CommonPatch r θ n₁ t₁ n₂ t₂))) :=
  spec_algHom_overComplex (firstOverlapMap r θ n₁ t₁ n₂ t₂)
    (overlapEmbedding r θ) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (overlapEmbedding_overComplex r θ)

theorem commonChart_overComplex (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (commonChart r θ n₁ t₁ n₂ t₂).inv ≫ (commonOpen r θ n₁ t₁ n₂ t₂).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CommonPatch r θ n₁ t₁ n₂ t₂))) := by
  rw [← Category.assoc, commonChart_inv_ι]
  exact commonEmbedding_overComplex r θ n₁ t₁ n₂ t₂

/-- On every actual subopen, the first patch ring map is the same as
restriction through the common affine chart. -/
theorem commonChart_first_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (a : AdjunctionPatch (firstEquations r θ) n₁ t₁) :
    CycleQ2GeometricAffineChartSections.chartSection (commonChart r θ n₁ t₁ n₂ t₂) V
        (firstPatchMap r θ n₁ t₁ n₂ t₂ a) =
      CycleQ2GeometricAffineChartSections.chartSection (firstPatchChart r θ n₁ t₁)
        (Over.mk (V.hom ≫ homOfLE
          (show commonOpen r θ n₁ t₁ n₂ t₂ ≤ firstPatchOpen r θ n₁ t₁ from inf_le_left))) a :=
  CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (firstPatchChart r θ n₁ t₁) (commonChart r θ n₁ t₁ n₂ t₂)
    inf_le_left (firstPatchMap r θ n₁ t₁ n₂ t₂).toRingHom
    (commonChart_first r θ n₁ t₁ n₂ t₂) V a

/-- The second patch uses its genuine changed-coordinate ring map on
the same actual structure-sheaf restrictions. -/
theorem commonChart_second_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (a : AdjunctionPatch (secondEquations r θ) n₂ t₂) :
    CycleQ2GeometricAffineChartSections.chartSection (commonChart r θ n₁ t₁ n₂ t₂) V
        (secondPatchMap r θ n₁ t₁ n₂ t₂ a) =
      CycleQ2GeometricAffineChartSections.chartSection (secondPatchChart r θ n₂ t₂)
        (Over.mk (V.hom ≫ homOfLE
          (show commonOpen r θ n₁ t₁ n₂ t₂ ≤ secondPatchOpen r θ n₂ t₂ from inf_le_right))) a :=
  CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (secondPatchChart r θ n₂ t₂) (commonChart r θ n₁ t₁ n₂ t₂)
    inf_le_right (secondPatchMap r θ n₁ t₁ n₂ t₂).toRingHom
    (commonChart_second r θ n₁ t₁ n₂ t₂) V a

end CycleQ2SurfaceCommonOpen
end

end


section

/-!
# Actual intersections of two Jacobian patches in one surface chart

The common ring is the localization at the product of the two actual
augmented Jacobians. Both patch maps, their scalar towers and formal
étaleness are constructed from the localization universal property.
The two actual surface residues therefore agree in its Kähler exterior
power. Its spectrum is the genuine intersection of the two projective
patch opens, with compatible complex and section maps.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceSameChartOverlap

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2SurfaceResidueScalarExtension

namespace PrincipalProduct

variable {A : Type} [CommRing A] [Algebra ℂ A]

abbrev CommonRing (a b : A) := Localization.Away (a * b)

omit [Algebra ℂ A] in
theorem left_isUnit (a b : A) : IsUnit (algebraMap A (CommonRing a b) a) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := CommonRing a b) (a * b)
  rw [map_mul, IsUnit.mul_iff] at h
  exact h.1

omit [Algebra ℂ A] in
theorem right_isUnit (a b : A) : IsUnit (algebraMap A (CommonRing a b) b) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := CommonRing a b) (a * b)
  rw [map_mul, IsUnit.mul_iff] at h
  exact h.2

def leftMap (a b : A) : Localization.Away a →ₐ[ℂ] CommonRing a b :=
  IsLocalization.Away.liftAlgHom a
    (f := IsScalarTower.toAlgHom ℂ A (CommonRing a b)) (left_isUnit a b)

def rightMap (a b : A) : Localization.Away b →ₐ[ℂ] CommonRing a b :=
  IsLocalization.Away.liftAlgHom b
    (f := IsScalarTower.toAlgHom ℂ A (CommonRing a b)) (right_isUnit a b)

@[simp] theorem leftMap_base (a b x : A) :
    leftMap a b (algebraMap A (Localization.Away a) x) =
      algebraMap A (CommonRing a b) x :=
  IsLocalization.Away.lift_eq _ (left_isUnit a b) x

@[simp] theorem rightMap_base (a b x : A) :
    rightMap a b (algebraMap A (Localization.Away b) x) =
      algebraMap A (CommonRing a b) x :=
  IsLocalization.Away.lift_eq _ (right_isUnit a b) x

@[instance_reducible]
def leftAlgebra (a b : A) : Algebra (Localization.Away a) (CommonRing a b) :=
  (leftMap a b).toRingHom.toAlgebra

@[instance_reducible]
def rightAlgebra (a b : A) : Algebra (Localization.Away b) (CommonRing a b) :=
  (rightMap a b).toRingHom.toAlgebra

attribute [local instance] leftAlgebra rightAlgebra

theorem leftChartTower (a b : A) : IsScalarTower A (Localization.Away a) (CommonRing a b) :=
  IsScalarTower.of_algebraMap_eq fun x => (leftMap_base a b x).symm

theorem rightChartTower (a b : A) : IsScalarTower A (Localization.Away b) (CommonRing a b) :=
  IsScalarTower.of_algebraMap_eq fun x => (rightMap_base a b x).symm

theorem leftComplexTower (a b : A) : IsScalarTower ℂ (Localization.Away a) (CommonRing a b) :=
  IsScalarTower.of_algHom (leftMap a b)

theorem rightComplexTower (a b : A) : IsScalarTower ℂ (Localization.Away b) (CommonRing a b) :=
  IsScalarTower.of_algHom (rightMap a b)

attribute [local instance] leftChartTower rightChartTower leftComplexTower rightComplexTower

theorem left_formallyEtale (a b : A) :
    Algebra.FormallyEtale (Localization.Away a) (CommonRing a b) := by
  have : Algebra.FormallyEtale A (CommonRing a b) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (a * b))
  have : Algebra.FormallyEtale A (Localization.Away a) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  exact Algebra.FormallyEtale.of_restrictScalars (R := A)

theorem right_formallyEtale (a b : A) :
    Algebra.FormallyEtale (Localization.Away b) (CommonRing a b) := by
  have : Algebra.FormallyEtale A (CommonRing a b) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (a * b))
  have : Algebra.FormallyEtale A (Localization.Away b) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers b)
  exact Algebra.FormallyEtale.of_restrictScalars (R := A)

section Geometry

variable {X : Scheme.{0}} {U : X.Opens}
  (e : U.toScheme ≅ Spec (CommRingCat.of A))

omit [Algebra ℂ A] in
private theorem principalOpen_image (a : A) :
    principalOpen e a = (e.inv ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen a :=
  (Scheme.Hom.opensRange_comp
    (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away a)))) (e.inv ≫ U.ι)).trans
    (congrArg (fun V => (e.inv ≫ U.ι) ''ᵁ V)
      (CycleQ2SurfaceCommonOpen.localization_range a))

omit [Algebra ℂ A] in
/-- Product localization is the actual intersection of the principal opens. -/
theorem principalOpen_mul (a b : A) :
    principalOpen e (a * b) = principalOpen e a ⊓ principalOpen e b := by
  calc
    _ = (e.inv ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen (a * b) := principalOpen_image e _
    _ = (e.inv ≫ U.ι) ''ᵁ (PrimeSpectrum.basicOpen a ⊓ PrimeSpectrum.basicOpen b) :=
      congrArg (fun V => (e.inv ≫ U.ι) ''ᵁ V) (PrimeSpectrum.basicOpen_mul a b)
    _ = ((e.inv ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen a) ⊓
        ((e.inv ≫ U.ι) ''ᵁ PrimeSpectrum.basicOpen b) :=
      TopologicalSpace.Opens.ext (Set.image_inter (e.inv ≫ U.ι).isOpenEmbedding.injective)
    _ = _ := congrArg₂ (· ⊓ ·) (principalOpen_image e a).symm (principalOpen_image e b).symm

omit [Algebra ℂ A] in
private theorem spec_lift_factorization {B C : Type} [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (h : ψ.comp φ = χ)
    (u : Spec (CommRingCat.of A) ⟶ X) :
    Spec.map (CommRingCat.ofHom χ) ≫ u =
      Spec.map (CommRingCat.ofHom ψ) ≫ (Spec.map (CommRingCat.ofHom φ) ≫ u) :=
  (congrArg (fun k : A →+* C => Spec.map (CommRingCat.ofHom k) ≫ u) h.symm).trans
    ((congrArg (fun k => k ≫ u)
      (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ))).trans
      (Category.assoc _ _ _))

theorem productImmersion_left (a b : A) :
    principalImmersion e (a * b) =
      Spec.map (CommRingCat.ofHom (leftMap a b).toRingHom) ≫ principalImmersion e a :=
  spec_lift_factorization (algebraMap A (Localization.Away a)) (leftMap a b).toRingHom
    (algebraMap A (CommonRing a b)) (RingHom.ext (leftMap_base a b)) (e.inv ≫ U.ι)

theorem productImmersion_right (a b : A) :
    principalImmersion e (a * b) =
      Spec.map (CommRingCat.ofHom (rightMap a b).toRingHom) ≫ principalImmersion e b :=
  spec_lift_factorization (algebraMap A (Localization.Away b)) (rightMap a b).toRingHom
    (algebraMap A (CommonRing a b)) (RingHom.ext (rightMap_base a b)) (e.inv ≫ U.ι)

def intersectionChart (a b : A) :
    (principalOpen e a ⊓ principalOpen e b).toScheme ≅ Spec (CommRingCat.of (CommonRing a b)) :=
  IsOpenImmersion.isoOfRangeEq (principalOpen e a ⊓ principalOpen e b).ι
    (principalImmersion e (a * b)) (by
      rw [Scheme.Opens.range_ι]
      exact congrArg SetLike.coe (principalOpen_mul e a b).symm)

omit [Algebra ℂ A] in
theorem intersectionChart_inv_ι (a b : A) :
    (intersectionChart e a b).inv ≫ (principalOpen e a ⊓ principalOpen e b).ι =
      principalImmersion e (a * b) :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

theorem intersectionChart_left (a b : A) :
    (intersectionChart e a b).inv ≫ (principalOpen e a ⊓ principalOpen e b).ι =
      Spec.map (CommRingCat.ofHom (leftMap a b).toRingHom) ≫
        (principalChart e a).inv ≫ (principalOpen e a).ι :=
  (intersectionChart_inv_ι e a b).trans ((productImmersion_left e a b).trans
    (congrArg (fun k => Spec.map (CommRingCat.ofHom (leftMap a b).toRingHom) ≫ k)
      (principalChart_inv_ι e a).symm))

theorem intersectionChart_right (a b : A) :
    (intersectionChart e a b).inv ≫ (principalOpen e a ⊓ principalOpen e b).ι =
      Spec.map (CommRingCat.ofHom (rightMap a b).toRingHom) ≫
        (principalChart e b).inv ≫ (principalOpen e b).ι :=
  (intersectionChart_inv_ι e a b).trans ((productImmersion_right e a b).trans
    (congrArg (fun k => Spec.map (CommRingCat.ofHom (rightMap a b).toRingHom) ≫ k)
      (principalChart_inv_ι e b).symm))

theorem intersectionChart_overComplex (a b : A)
    (f : X ⟶ Spec (CommRingCat.of ℂ))
    (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A))) :
    (intersectionChart e a b).inv ≫ (principalOpen e a ⊓ principalOpen e b).ι ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (CommonRing a b))) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ f) (intersectionChart_inv_ι e a b)).trans
      (principalImmersion_overComplex e (a * b) f h))

theorem intersectionChart_left_section (a b : A)
    (V : Over (principalOpen e a ⊓ principalOpen e b)) (x : Localization.Away a) :
    CycleQ2GeometricAffineChartSections.chartSection (intersectionChart e a b) V (leftMap a b x) =
      CycleQ2GeometricAffineChartSections.chartSection (principalChart e a)
        (Over.mk (V.hom ≫ homOfLE (show principalOpen e a ⊓ principalOpen e b ≤ principalOpen e a
          from inf_le_left))) x :=
  CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (principalChart e a) (intersectionChart e a b) inf_le_left (leftMap a b).toRingHom
    (intersectionChart_left e a b) V x

theorem intersectionChart_right_section (a b : A)
    (V : Over (principalOpen e a ⊓ principalOpen e b)) (x : Localization.Away b) :
    CycleQ2GeometricAffineChartSections.chartSection (intersectionChart e a b) V (rightMap a b x) =
      CycleQ2GeometricAffineChartSections.chartSection (principalChart e b)
        (Over.mk (V.hom ≫ homOfLE (show principalOpen e a ⊓ principalOpen e b ≤ principalOpen e b
          from inf_le_right))) x :=
  CycleQ2GeometricPrincipalChartSections.chartSection_compatible
    (principalChart e b) (intersectionChart e a b) inf_le_right (rightMap a b).toRingHom
    (intersectionChart_right e a b) V x

end Geometry
end PrincipalProduct

attribute [local instance] PrincipalProduct.leftAlgebra PrincipalProduct.rightAlgebra
  PrincipalProduct.leftChartTower PrincipalProduct.rightChartTower
  PrincipalProduct.leftComplexTower PrincipalProduct.rightComplexTower
  PrincipalProduct.left_formallyEtale PrincipalProduct.right_formallyEtale

abbrev SameChartRing (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :=
  PrincipalProduct.CommonRing (augmentedJacobian v n₁ t₁) (augmentedJacobian v n₂ t₂)

def leftPatchMap (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    AdjunctionPatch v n₁ t₁ →ₐ[ℂ] SameChartRing v n₁ t₁ n₂ t₂ :=
  PrincipalProduct.leftMap _ _

def rightPatchMap (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    AdjunctionPatch v n₂ t₂ →ₐ[ℂ] SameChartRing v n₁ t₁ n₂ t₂ :=
  PrincipalProduct.rightMap _ _

def leftResidue (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    ⋀[SameChartRing v n₁ t₁ n₂ t₂]^2 (KaehlerDifferential ℂ (SameChartRing v n₁ t₁ n₂ t₂)) :=
  etaleResidue v n₁ t₁ (SameChartRing v n₁ t₁ n₂ t₂)

def rightResidue (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    ⋀[SameChartRing v n₁ t₁ n₂ t₂]^2 (KaehlerDifferential ℂ (SameChartRing v n₁ t₁ n₂ t₂)) :=
  etaleResidue v n₂ t₂ (SameChartRing v n₁ t₁ n₂ t₂)

/-- Both normalized residues agree after the actual two localization maps. -/
theorem residue_independent (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    rightResidue v n₁ t₁ n₂ t₂ = leftResidue v n₁ t₁ n₂ t₂ :=
  CycleQ2SurfaceResidueRefinement.etaleResidue_independent
    (v := v) (S := SameChartRing v n₁ t₁ n₂ t₂)
    (n₁ := n₁) (t₁ := t₁) (n₂ := n₂) (t₂ := t₂)

def firstCommonOpen (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (CycleQ2CartierProjectiveCover.projectiveSurface r θ).Opens :=
  CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₁ t₁ ⊓
    CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₂ t₂

def firstCommonChart (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (firstCommonOpen r θ n₁ t₁ n₂ t₂).toScheme ≅
      Spec (CommRingCat.of (SameChartRing (firstEquations r θ) n₁ t₁ n₂ t₂)) :=
  PrincipalProduct.intersectionChart (firstAffineChart r θ)
    (augmentedJacobian (firstEquations r θ) n₁ t₁)
    (augmentedJacobian (firstEquations r θ) n₂ t₂)

theorem firstCommonChart_overComplex (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (firstCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (firstCommonOpen r θ n₁ t₁ n₂ t₂).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (SameChartRing (firstEquations r θ) n₁ t₁ n₂ t₂))) :=
  PrincipalProduct.intersectionChart_overComplex (firstAffineChart r θ) _ _
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ)

theorem first_residue_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    rightResidue (firstEquations r θ) n₁ t₁ n₂ t₂ =
      leftResidue (firstEquations r θ) n₁ t₁ n₂ t₂ :=
  residue_independent _ _ _ _ _

theorem firstCommonChart_left (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (firstCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (firstCommonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (leftPatchMap (firstEquations r θ) n₁ t₁ n₂ t₂).toRingHom) ≫
        (CycleQ2SurfaceCommonOpen.firstPatchChart r θ n₁ t₁).inv ≫
          (CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₁ t₁).ι :=
  PrincipalProduct.intersectionChart_left (firstAffineChart r θ) _ _

theorem firstCommonChart_left_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (firstCommonOpen r θ n₁ t₁ n₂ t₂))
    (x : AdjunctionPatch (firstEquations r θ) n₁ t₁) :
    CycleQ2GeometricAffineChartSections.chartSection (firstCommonChart r θ n₁ t₁ n₂ t₂) V
        (leftPatchMap (firstEquations r θ) n₁ t₁ n₂ t₂ x) =
      CycleQ2GeometricAffineChartSections.chartSection
        (CycleQ2SurfaceCommonOpen.firstPatchChart r θ n₁ t₁)
        (Over.mk (V.hom ≫ homOfLE (show firstCommonOpen r θ n₁ t₁ n₂ t₂ ≤
          CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₁ t₁ from inf_le_left))) x :=
  PrincipalProduct.intersectionChart_left_section (firstAffineChart r θ) _ _ V x

theorem firstCommonChart_right (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (firstCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (firstCommonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (rightPatchMap (firstEquations r θ) n₁ t₁ n₂ t₂).toRingHom) ≫
        (CycleQ2SurfaceCommonOpen.firstPatchChart r θ n₂ t₂).inv ≫
          (CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₂ t₂).ι :=
  PrincipalProduct.intersectionChart_right (firstAffineChart r θ) _ _

theorem firstCommonChart_right_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (firstCommonOpen r θ n₁ t₁ n₂ t₂))
    (x : AdjunctionPatch (firstEquations r θ) n₂ t₂) :
    CycleQ2GeometricAffineChartSections.chartSection (firstCommonChart r θ n₁ t₁ n₂ t₂) V
        (rightPatchMap (firstEquations r θ) n₁ t₁ n₂ t₂ x) =
      CycleQ2GeometricAffineChartSections.chartSection
        (CycleQ2SurfaceCommonOpen.firstPatchChart r θ n₂ t₂)
        (Over.mk (V.hom ≫ homOfLE (show firstCommonOpen r θ n₁ t₁ n₂ t₂ ≤
          CycleQ2SurfaceCommonOpen.firstPatchOpen r θ n₂ t₂ from inf_le_right))) x :=
  PrincipalProduct.intersectionChart_right_section (firstAffineChart r θ) _ _ V x

def secondCommonOpen (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (CycleQ2CartierProjectiveCover.projectiveSurface r θ).Opens :=
  CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₁ t₁ ⊓
    CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₂ t₂

def secondCommonChart (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (secondCommonOpen r θ n₁ t₁ n₂ t₂).toScheme ≅
      Spec (CommRingCat.of (SameChartRing (secondEquations r θ) n₁ t₁ n₂ t₂)) :=
  PrincipalProduct.intersectionChart (secondAffineChart r θ)
    (augmentedJacobian (secondEquations r θ) n₁ t₁)
    (augmentedJacobian (secondEquations r θ) n₂ t₂)

theorem secondCommonChart_overComplex (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (secondCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (secondCommonOpen r θ n₁ t₁ n₂ t₂).ι ≫
        CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom
        (algebraMap ℂ (SameChartRing (secondEquations r θ) n₁ t₁ n₂ t₂))) :=
  PrincipalProduct.intersectionChart_overComplex (secondAffineChart r θ) _ _
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ)

theorem second_residue_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    rightResidue (secondEquations r θ) n₁ t₁ n₂ t₂ =
      leftResidue (secondEquations r θ) n₁ t₁ n₂ t₂ :=
  residue_independent _ _ _ _ _

theorem secondCommonChart_left (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (secondCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (secondCommonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (leftPatchMap (secondEquations r θ) n₁ t₁ n₂ t₂).toRingHom) ≫
        (CycleQ2SurfaceCommonOpen.secondPatchChart r θ n₁ t₁).inv ≫
          (CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₁ t₁).ι :=
  PrincipalProduct.intersectionChart_left (secondAffineChart r θ) _ _

theorem secondCommonChart_left_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (secondCommonOpen r θ n₁ t₁ n₂ t₂))
    (x : AdjunctionPatch (secondEquations r θ) n₁ t₁) :
    CycleQ2GeometricAffineChartSections.chartSection (secondCommonChart r θ n₁ t₁ n₂ t₂) V
        (leftPatchMap (secondEquations r θ) n₁ t₁ n₂ t₂ x) =
      CycleQ2GeometricAffineChartSections.chartSection
        (CycleQ2SurfaceCommonOpen.secondPatchChart r θ n₁ t₁)
        (Over.mk (V.hom ≫ homOfLE (show secondCommonOpen r θ n₁ t₁ n₂ t₂ ≤
          CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₁ t₁ from inf_le_left))) x :=
  PrincipalProduct.intersectionChart_left_section (secondAffineChart r θ) _ _ V x

theorem secondCommonChart_right (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly) :
    (secondCommonChart r θ n₁ t₁ n₂ t₂).inv ≫ (secondCommonOpen r θ n₁ t₁ n₂ t₂).ι =
      Spec.map (CommRingCat.ofHom (rightPatchMap (secondEquations r θ) n₁ t₁ n₂ t₂).toRingHom) ≫
        (CycleQ2SurfaceCommonOpen.secondPatchChart r θ n₂ t₂).inv ≫
          (CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₂ t₂).ι :=
  PrincipalProduct.intersectionChart_right (secondAffineChart r θ) _ _

theorem secondCommonChart_right_section (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (secondCommonOpen r θ n₁ t₁ n₂ t₂))
    (x : AdjunctionPatch (secondEquations r θ) n₂ t₂) :
    CycleQ2GeometricAffineChartSections.chartSection (secondCommonChart r θ n₁ t₁ n₂ t₂) V
        (rightPatchMap (secondEquations r θ) n₁ t₁ n₂ t₂ x) =
      CycleQ2GeometricAffineChartSections.chartSection
        (CycleQ2SurfaceCommonOpen.secondPatchChart r θ n₂ t₂)
        (Over.mk (V.hom ≫ homOfLE (show secondCommonOpen r θ n₁ t₁ n₂ t₂ ≤
          CycleQ2SurfaceCommonOpen.secondPatchOpen r θ n₂ t₂ from inf_le_right))) x :=
  PrincipalProduct.intersectionChart_right_section (secondAffineChart r θ) _ _ V x

end CycleQ2SurfaceSameChartOverlap
end

end


section

/-! Canonical affine exterior forms as sections of the genuine exterior
module sheaf. Restriction and change of affine coordinates commute with
this construction on every form, without a local-freeness assumption. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ExteriorSectionNaturality

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricAffineOverlap CycleQ2GeometricExteriorSheaf

section AffineMap

variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

/-- The original universal differential map, with its actual coefficient map. -/
def differentialSemilinearMap (φ : A →ₐ[ℂ] B) :
    KaehlerDifferential ℂ A →ₛₗ[φ.toRingHom] KaehlerDifferential ℂ B where
  toFun := differentialMap φ
  map_add' := (differentialMap φ).map_add
  map_smul' := differentialMap_smul φ

def exteriorDifferentialMap (φ : A →ₐ[ℂ] B) (n : ℕ) :
    (⋀[A]^n (KaehlerDifferential ℂ A)) →ₛₗ[φ.toRingHom]
      (⋀[B]^n (KaehlerDifferential ℂ B)) :=
  exteriorMap φ.toRingHom (differentialSemilinearMap φ) n

theorem exteriorDifferentialMap_wedge (φ : A →ₐ[ℂ] B) (n : ℕ)
    (w : Fin n → KaehlerDifferential ℂ A) :
    exteriorDifferentialMap φ n (exteriorPower.ιMulti A n w) =
      exteriorPower.ιMulti B n (fun j => differentialMap φ (w j)) :=
  exteriorMap_wedge φ.toRingHom (differentialSemilinearMap φ) n w

end AffineMap

section Lift

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))
  (d : M.val.Derivation' (coefficientMap R c))
  (O : Opens X) {A : Type} [CommRing A] [Algebra ℂ A]
  (f : A →+* R.obj.obj (op O))
  (hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z)

def sectionLiftSemilinear : KaehlerDifferential ℂ A →ₛₗ[f] M.val.obj (op O) where
  toFun := sectionLift R c M d O f hf
  map_add' := (sectionLift R c M d O f hf).map_add
  map_smul' := sectionLift_smul R c M d O f hf

/-- Affine exterior forms map into the actual exterior sheaf through its
canonical sheafification unit. No coordinate functional selects the result. -/
def exteriorSectionLift (n : ℕ) :
    (⋀[A]^n (KaehlerDifferential ℂ A)) →ₛₗ[f]
      (exteriorSheaf R M.val n).val.obj (op O) :=
  (exteriorSection R M.val n O).comp
    (exteriorMap f (sectionLiftSemilinear R c M d O f hf) n)

theorem exteriorSectionLift_wedge (n : ℕ) (w : Fin n → KaehlerDifferential ℂ A) :
    exteriorSectionLift R c M d O f hf n (exteriorPower.ιMulti A n w) =
      wedgeSection R M.val n O (fun j => sectionLift R c M d O f hf (w j)) := by
  change exteriorSection R M.val n O
      (exteriorMap f (sectionLiftSemilinear R c M d O f hf) n
        (exteriorPower.ιMulti A n w)) = _
  rw [exteriorMap_wedge]
  rfl

theorem sectionLift_restriction_differentialMap
    {B : Type} [CommRing B] [Algebra ℂ B]
    (P : Opens X) (hPO : P ≤ O)
    (g : B →+* R.obj.obj (op P))
    (hg : ∀ z : ℂ, g (algebraMap ℂ B z) = coefficientOn R c P z)
    (φ : A →ₐ[ℂ] B)
    (hfg : ∀ a, R.obj.map (homOfLE hPO).op (f a) = g (φ a))
    (ω : KaehlerDifferential ℂ A) :
    M.val.map (homOfLE hPO).op (sectionLift R c M d O f hf ω) =
      sectionLift R c M d P g hg (differentialMap φ ω) := by
  have hcomp : ∀ z : ℂ, (g.comp φ.toRingHom) (algebraMap ℂ A z) =
      coefficientOn R c P z := fun z => (congrArg g (φ.commutes z)).trans (hg z)
  exact (sectionLift_restriction R c M d O f hf P hPO
    (g.comp φ.toRingHom) hcomp hfg ω).trans
      (sectionLift_differentialMap R c M d P (g.comp φ.toRingHom) hcomp
        g hg φ (fun _ => rfl) ω).symm

/-- Restricting an actual exterior-sheaf section agrees with the genuine
affine differential pullback, for every degree and every exterior form. -/
theorem exteriorSectionLift_restriction
    {B : Type} [CommRing B] [Algebra ℂ B]
    (P : Opens X) (hPO : P ≤ O)
    (g : B →+* R.obj.obj (op P))
    (hg : ∀ z : ℂ, g (algebraMap ℂ B z) = coefficientOn R c P z)
    (φ : A →ₐ[ℂ] B)
    (hfg : ∀ a, R.obj.map (homOfLE hPO).op (f a) = g (φ a))
    (n : ℕ) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (exteriorSheaf R M.val n).val.map (homOfLE hPO).op
        (exteriorSectionLift R c M d O f hf n ω) =
      exteriorSectionLift R c M d P g hg n (exteriorDifferentialMap φ n ω) := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      rw [exteriorSectionLift_wedge, exteriorDifferentialMap_wedge,
        exteriorSectionLift_wedge, wedgeSection_restrict]
      apply congrArg (wedgeSection R M.val n P)
      funext j
      exact sectionLift_restriction_differentialMap R c M d O f hf P hPO g hg φ hfg (w j)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      simp only [map_smulₛₗ]
      change R.obj.map (homOfLE hPO).op (f a) •
          (exteriorSheaf R M.val n).val.map (homOfLE hPO).op
            (exteriorSectionLift R c M d O f hf n x) =
        g (φ a) • exteriorSectionLift R c M d P g hg n (exteriorDifferentialMap φ n x)
      rw [hfg, hx]

end Lift

end CycleQ2ExteriorSectionNaturality
end

end


section

/-! The genuine formally étale exterior pullback is the canonical
semilinear exterior map of the universal differential. This identifies
the actual normalized residue with its actual affine pullback. -/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2EtaleExteriorMapBinding

open Module CycleQ2GeometricAffineOverlap CycleQ2ExteriorSectionNaturality
  CycleQ2SurfaceResidueScalarExtension CycleQ2ExteriorTopBaseChange
open scoped TensorProduct

section Affine

variable {A B : Type} [CommRing A] [CommRing B]
  [Algebra ℂ A] [Algebra ℂ B] [Algebra A B] [IsScalarTower ℂ A B]

theorem differentialMap_algebraMap (ω : KaehlerDifferential ℂ A) :
    differentialMap (IsScalarTower.toAlgHom ℂ A B) ω =
      KaehlerDifferential.map ℂ ℂ A B ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact (differentialMap_D (IsScalarTower.toAlgHom ℂ A B) a).trans
        (KaehlerDifferential.map_D ℂ ℂ A B a).symm
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      rw [differentialMap_smul, map_smul, hx]
      exact IsScalarTower.algebraMap_smul B a (KaehlerDifferential.map ℂ ℂ A B x)

variable [Algebra.FormallyEtale A B]

theorem tensorKaehlerEquiv_one (ω : KaehlerDifferential ℂ A) :
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ A B ((1 : B) ⊗ₜ[A] ω) =
      differentialMap (IsScalarTower.toAlgHom ℂ A B) ω := by
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul]
  exact (differentialMap_algebraMap ω).symm

def etaleExteriorExtension {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential ℂ A)) :
    (⋀[A]^n (KaehlerDifferential ℂ A)) →ₛₗ[algebraMap A B]
      (⋀[B]^n (KaehlerDifferential ℂ B)) :=
  (exteriorLinearEquiv n (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ A B)).toLinearMap.comp
    (topBaseChange (S := B) b)

theorem etaleExteriorExtension_wedge {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential ℂ A))
    (w : Fin n → KaehlerDifferential ℂ A) :
    etaleExteriorExtension (B := B) b (exteriorPower.ιMulti A n w) =
      exteriorPower.ιMulti B n
        (fun j => differentialMap (IsScalarTower.toAlgHom ℂ A B) (w j)) := by
  change exteriorPower.map n
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ A B).toLinearMap
      (topBaseChange (S := B) b (exteriorPower.ιMulti A n w)) = _
  rw [topBaseChange_wedge, exteriorPower.map_apply_ιMulti]
  exact congrArg (exteriorPower.ιMulti B n) (funext fun j => tensorKaehlerEquiv_one (w j))

theorem exteriorDifferentialMap_eq_extension {n : ℕ}
    (b : Basis (Fin n) A (KaehlerDifferential ℂ A))
    (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ A B) n ω =
      etaleExteriorExtension (B := B) b ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      exact (exteriorDifferentialMap_wedge (IsScalarTower.toAlgHom ℂ A B) n w).trans
        (etaleExteriorExtension_wedge b w).symm
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx =>
      simp only [map_smulₛₗ, hx]
      rfl

end Affine

section Residue

open CycleQ2GeometricSurfaceAdjunction
variable (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (S : Type) [CommRing S] [Algebra (AdjunctionPatch v n t) S]
  [Algebra ℂ S] [IsScalarTower ℂ (AdjunctionPatch v n t) S]
  [Algebra.FormallyEtale (AdjunctionPatch v n t) S]

/-- The same normalized actual residue is obtained by the universal
exterior pullback along the actual coefficient algebra map. -/
theorem etaleResidue_eq_exteriorDifferentialMap :
    etaleResidue v n t S =
      exteriorDifferentialMap (IsScalarTower.toAlgHom ℂ (AdjunctionPatch v n t) S) 2
        (localSurfaceResidueForm v n t) := by
  exact (exteriorDifferentialMap_eq_extension (B := S) (localSurfaceKaehlerBasis v n t)
    (localSurfaceResidueForm v n t)).symm

end Residue
end CycleQ2EtaleExteriorMapBinding
end

end


section

/-! The existing affine chart exterior map is the canonical exterior
map of its actual Kähler section lift. Its image in the genuine exterior
sheaf therefore obeys change of affine chart on every smaller open. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ChartExteriorBinding

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricAffineOverlap CycleQ2GeometricExteriorSheaf
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2GeometricSurfaceExteriorSections CycleQ2ExteriorSectionNaturality

section Composition

variable {X : TopCat.{0}} (R : X.Sheaf CommRingCat.{0})
  (c : ℂ →+* R.obj.obj (op ⊤))
  (M : SheafOfModules.{0} (ringSheaf R))
  (d : M.val.Derivation' (coefficientMap R c)) (O : Opens X)
  {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  (f : A →+* R.obj.obj (op O))
  (hf : ∀ z : ℂ, f (algebraMap ℂ A z) = coefficientOn R c O z)
  (g : B →+* R.obj.obj (op O))
  (hg : ∀ z : ℂ, g (algebraMap ℂ B z) = coefficientOn R c O z)

theorem exteriorSectionLift_differentialMap (φ : A →ₐ[ℂ] B)
    (hfg : ∀ a : A, g (φ a) = f a)
    (n : ℕ) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    exteriorSectionLift R c M d O g hg n (exteriorDifferentialMap φ n ω) =
      exteriorSectionLift R c M d O f hf n ω := by
  change exteriorSection R M.val n O
      (exteriorMap g (sectionLiftSemilinear R c M d O g hg) n
        (exteriorMap φ.toRingHom (differentialSemilinearMap φ) n ω)) =
    exteriorSection R M.val n O
      (exteriorMap f (sectionLiftSemilinear R c M d O f hf) n ω)
  apply congrArg (exteriorSection R M.val n O)
  exact (exteriorMap_composition φ.toRingHom g f
    (differentialSemilinearMap φ) (sectionLiftSemilinear R c M d O g hg)
    (sectionLiftSemilinear R c M d O f hf) (fun a => (hfg a).symm)
    (fun η => (sectionLift_differentialMap R c M d O f hf g hg φ hfg η).symm)
    n ω).symm

end Composition

section Chart

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem chartExteriorSection_eq_exteriorMap
    (b : Basis (Fin 2) A (KaehlerDifferential ℂ A)) (V : Over U)
    (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    chartExteriorSection e f h b V ω =
      exteriorMap (chartSection e V)
        (sectionLiftSemilinear X.sheaf (schemeCoefficient f)
          (differentialSheaf X.sheaf (schemeCoefficient f))
          (universalDifferential X.sheaf (schemeCoefficient f)) V.left
          (chartSection e V) (chartSection_complex e f h V)) 2 ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      have ha : a = ![a 0,a 1] := by funext j; fin_cases j <;> rfl
      rw [ha,chartExteriorSection_wedge,exteriorMap_wedge]
      apply congrArg (exteriorPower.ιMulti Γ(X,V.left) 2)
      funext j
      fin_cases j <;> rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx => simp only [map_smulₛₗ,hx]

/-- The canonical actual chart form in the exterior-power sheaf. -/
def chartExteriorSheafSection (n : ℕ) (V : Over U) :
    (⋀[A]^n (KaehlerDifferential ℂ A)) →ₛₗ[chartSection e V]
      (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val n).val.obj
        (op V.left) :=
  exteriorSectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e V) (chartSection_complex e f h V) n

theorem chartExteriorSheafSection_eq (b : Basis (Fin 2) A (KaehlerDifferential ℂ A))
    (V : Over U) (ω : ⋀[A]^2 (KaehlerDifferential ℂ A)) :
    exteriorSection X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val 2 V.left
        (chartExteriorSection e f h b V ω) =
      chartExteriorSheafSection e f h 2 V ω := by
  rw [chartExteriorSection_eq_exteriorMap]
  rfl

theorem chartExteriorSheafSection_restrict {V W : Over U} (k : V ⟶ W)
    (n : ℕ) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val n).val.map
        k.left.op (chartExteriorSheafSection e f h n W ω) =
      chartExteriorSheafSection e f h n V ω := by
  have hω : ω ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A n)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a,rfl⟩ := hx
      change _ = exteriorSectionLift _ _ _ _ _ _ _ n _
      rw [chartExteriorSheafSection,exteriorSectionLift_wedge,
        exteriorSectionLift_wedge,wedgeSection_restrict]
      apply congrArg (wedgeSection X.sheaf
        (differentialSheaf X.sheaf (schemeCoefficient f)).val n V.left)
      funext j
      exact sectionLift_restriction X.sheaf (schemeCoefficient f)
        (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) W.left
        (chartSection e W) (chartSection_complex e f h W) V.left k.left.le
        (chartSection e V) (chartSection_complex e f h V)
        (chartSection_naturality e k) (a j)
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add,hx,hy]
  | smul a x _ hx =>
      simp only [map_smulₛₗ]
      change X.presheaf.map k.left.op (chartSection e W a) •
          (exteriorSheaf X.sheaf
            (differentialSheaf X.sheaf (schemeCoefficient f)).val n).val.map
              k.left.op (chartExteriorSheafSection e f h n W x) =
        chartSection e V a • chartExteriorSheafSection e f h n V x
      rw [chartSection_naturality,hx]

end Chart

section ChangeChart

variable {X : Scheme.{0}} {U W : X.Opens}
  {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (e' : W.toScheme ≅ Spec (CommRingCat.of B)) (hWU : W ≤ U)
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (h' : e'.inv ≫ W.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
  (φ : A →ₐ[ℂ] B)
  (hc : e'.inv ≫ W.ι = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ e.inv ≫ U.ι)

include hc in
theorem chartExteriorSheafSection_differentialMap (V : Over W)
    (n : ℕ) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    chartExteriorSheafSection e' f h' n V (exteriorDifferentialMap φ n ω) =
      chartExteriorSheafSection e f h n (Over.mk (V.hom ≫ homOfLE hWU)) ω :=
  exteriorSectionLift_differentialMap X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f))
    (universalDifferential X.sheaf (schemeCoefficient f)) V.left
    (chartSection e (Over.mk (V.hom ≫ homOfLE hWU)))
    (chartSection_complex e f h (Over.mk (V.hom ≫ homOfLE hWU)))
    (chartSection e' V) (chartSection_complex e' f h' V) φ
    (CycleQ2GeometricPrincipalChartSections.chartSection_compatible e e' hWU φ.toRingHom hc V)
    n ω

end ChangeChart

section Residue

open CycleQ2GeometricSurfaceAdjunction
variable {X : Scheme.{0}} {U : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ)) (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (h : e.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

theorem chartResidueSheafSection_eq_canonical (V : Over U) :
    chartResidueSheafSection f v n t e h V =
      chartExteriorSheafSection e f h 2 V (localSurfaceResidueForm v n t) :=
  chartExteriorSheafSection_eq e f h (localSurfaceKaehlerBasis v n t) V
    (localSurfaceResidueForm v n t)

end Residue

end CycleQ2ChartExteriorBinding
end

end


section

/-! A genuine formally étale affine refinement transports the normalized
surface residue into the very same exterior-sheaf section. This binds the
algebraic residue to the actual chart maps on each subopen. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ChartResidueTransport

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineChartSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2SurfaceResidueScalarExtension CycleQ2ExteriorSectionNaturality
  CycleQ2EtaleExteriorMapBinding CycleQ2ChartExteriorBinding

variable {X : Scheme.{0}} {U W : X.Opens}
  (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  {B : Type} [CommRing B] [Algebra ℂ B] [Algebra (AdjunctionPatch v n t) B]
  [IsScalarTower ℂ (AdjunctionPatch v n t) B]
  [Algebra.FormallyEtale (AdjunctionPatch v n t) B]
  (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (e' : W.toScheme ≅ Spec (CommRingCat.of B)) (hWU : W ≤ U)
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))
  (h' : e'.inv ≫ W.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
  (hc : e'.inv ≫ W.ι =
    Spec.map (CommRingCat.ofHom (algebraMap (AdjunctionPatch v n t) B)) ≫ e.inv ≫ U.ι)

include hc

theorem chartResidueSheafSection_etale (V : Over W) :
    chartExteriorSheafSection e' f h' 2 V (etaleResidue v n t B) =
      chartResidueSheafSection f v n t e h (Over.mk (V.hom ≫ homOfLE hWU)) := by
  rw [etaleResidue_eq_exteriorDifferentialMap]
  exact (chartExteriorSheafSection_differentialMap e e' hWU f h h'
    (IsScalarTower.toAlgHom ℂ (AdjunctionPatch v n t) B) hc V 2
    (localSurfaceResidueForm v n t)).trans
      (chartResidueSheafSection_eq_canonical f v n t e h
        (Over.mk (V.hom ≫ homOfLE hWU))).symm

theorem chartResidueSheafSection_etale_coefficient
    (V : Over W) (a : AdjunctionPatch v n t) :
    chartExteriorSheafSection e' f h' 2 V
        (algebraMap (AdjunctionPatch v n t) B a • etaleResidue v n t B) =
      chartSection e (Over.mk (V.hom ≫ homOfLE hWU)) a •
        chartResidueSheafSection f v n t e h (Over.mk (V.hom ≫ homOfLE hWU)) := by
  rw [map_smulₛₗ,chartResidueSheafSection_etale v n t e e' hWU f h h' hc]
  exact congrArg (fun s => s • chartResidueSheafSection f v n t e h
    (Over.mk (V.hom ≫ homOfLE hWU)))
      (CycleQ2GeometricPrincipalChartSections.chartSection_compatible e e' hWU
        (algebraMap (AdjunctionPatch v n t) B) hc V a)

end CycleQ2ChartResidueTransport
end

end


section

/-! The oriented cubic residues agree as actual sections of the genuine
exterior differential sheaf on the intersection of the projective
augmented-Jacobian charts, and on every subopen of that intersection. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SurfaceResidueSheafOverlap

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module MvPolynomial
  CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricAffineChartSections CycleQ2GeometricExteriorSheaf
  CycleQ2SurfaceCommonLocalization CycleQ2SurfaceCommonOpen
  CycleQ2SurfaceCommonCoefficients CycleQ2SurfaceCommonResidue
  CycleQ2ChartExteriorBinding CycleQ2ChartResidueTransport

attribute [local instance] CycleQ2SurfaceChangedAmbient.secondChartAlgebra
  CycleQ2SurfaceOverlapConormal.firstAmbientAlgebra
  commonSecondChartAlgebra commonAmbientAlgebra
  commonSecondChartTower commonSecondComplexTower commonAmbientTower commonAmbientComplexTower
  firstPatchAlgebra secondPatchAlgebra firstPatchComplexTower secondPatchComplexTower
  firstPatchChartTower secondPatchChartTower firstPatch_formallyEtale secondPatch_formallyEtale

variable (r θ : ℂ)

def surfaceExteriorSheaf :=
  exteriorSheaf (projectiveSurface r θ).sheaf
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).val 2

theorem firstPatchChart_overComplex (n t : SurfacePoly) :
    (firstPatchChart r θ n t).inv ≫ (firstPatchOpen r θ n t).ι ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch (firstEquations r θ) n t))) :=
  principalChart_overComplex (firstAffineChart r θ)
    (augmentedJacobian (firstEquations r θ) n t) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (firstAffineChart_overComplex r θ)

theorem secondPatchChart_overComplex (n t : SurfacePoly) :
    (secondPatchChart r θ n t).inv ≫ (secondPatchOpen r θ n t).ι ≫ CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch (secondEquations r θ) n t))) :=
  principalChart_overComplex (secondAffineChart r θ)
    (augmentedJacobian (secondEquations r θ) n t) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (secondAffineChart_overComplex r θ)

def firstCubicSection (n t : SurfacePoly) (p : MvPolynomial (Fin 5) ℂ)
    (V : Over (firstPatchOpen r θ n t)) : (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  chartSection (firstPatchChart r θ n t) V
      (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n t)
        (firstSurfaceDehomogenize p)) •
    chartResidueSheafSection (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (firstEquations r θ) n t
      (firstPatchChart r θ n t) (firstPatchChart_overComplex r θ n t) V

def secondCubicSection (n t : SurfacePoly) (p : MvPolynomial (Fin 5) ℂ)
    (V : Over (secondPatchOpen r θ n t)) : (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  -(chartSection (secondPatchChart r θ n t) V
      (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n t)
        (secondSurfaceDehomogenize p)) •
    chartResidueSheafSection (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (secondEquations r θ) n t
      (secondPatchChart r θ n t) (secondPatchChart_overComplex r θ n t) V)

variable (n₁ t₁ n₂ t₂ : SurfacePoly)

def commonExteriorSection (V : Over (commonOpen r θ n₁ t₁ n₂ t₂)) :
    (⋀[CommonPatch r θ n₁ t₁ n₂ t₂]^2
      (KaehlerDifferential ℂ (CommonPatch r θ n₁ t₁ n₂ t₂))) →ₛₗ[
        chartSection (commonChart r θ n₁ t₁ n₂ t₂) V]
      (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  chartExteriorSheafSection (commonChart r θ n₁ t₁ n₂ t₂) (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (commonChart_overComplex r θ n₁ t₁ n₂ t₂) 2 V

def firstCommonSubopen (V : Over (commonOpen r θ n₁ t₁ n₂ t₂)) :
    Over (firstPatchOpen r θ n₁ t₁) :=
  Over.mk (V.hom ≫ homOfLE
    (show commonOpen r θ n₁ t₁ n₂ t₂ ≤ firstPatchOpen r θ n₁ t₁ from inf_le_left))

def secondCommonSubopen (V : Over (commonOpen r θ n₁ t₁ n₂ t₂)) :
    Over (secondPatchOpen r θ n₂ t₂) :=
  Over.mk (V.hom ≫ homOfLE
    (show commonOpen r θ n₁ t₁ n₂ t₂ ≤ secondPatchOpen r θ n₂ t₂ from inf_le_right))

def firstSectionOnCommon (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (p : MvPolynomial (Fin 5) ℂ) : (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  firstCubicSection r θ n₁ t₁ p (firstCommonSubopen r θ n₁ t₁ n₂ t₂ V)

def secondSectionOnCommon (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (p : MvPolynomial (Fin 5) ℂ) : (surfaceExteriorSheaf r θ).val.obj (op V.left) :=
  secondCubicSection r θ n₂ t₂ p (secondCommonSubopen r θ n₁ t₁ n₂ t₂ V)

theorem commonExteriorSection_first (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (p : MvPolynomial (Fin 5) ℂ) :
    commonExteriorSection r θ n₁ t₁ n₂ t₂ V (firstCubicForm r θ n₁ t₁ n₂ t₂ p) =
      firstCubicSection r θ n₁ t₁ p (firstCommonSubopen r θ n₁ t₁ n₂ t₂ V) :=
  chartResidueSheafSection_etale_coefficient (firstEquations r θ) n₁ t₁
    (firstPatchChart r θ n₁ t₁) (commonChart r θ n₁ t₁ n₂ t₂) inf_le_left
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (firstPatchChart_overComplex r θ n₁ t₁)
    (commonChart_overComplex r θ n₁ t₁ n₂ t₂) (commonChart_first r θ n₁ t₁ n₂ t₂) V
    (algebraMap SurfacePoly (AdjunctionPatch (firstEquations r θ) n₁ t₁)
      (firstSurfaceDehomogenize p))

theorem commonExteriorSection_second (V : Over (commonOpen r θ n₁ t₁ n₂ t₂))
    (p : MvPolynomial (Fin 5) ℂ) :
    commonExteriorSection r θ n₁ t₁ n₂ t₂ V (secondCubicForm r θ n₁ t₁ n₂ t₂ p) =
      secondCubicSection r θ n₂ t₂ p (secondCommonSubopen r θ n₁ t₁ n₂ t₂ V) := by
  change commonExteriorSection r θ n₁ t₁ n₂ t₂ V
      (-(secondSectionCoefficient r θ n₁ t₁ n₂ t₂ p • secondResidue r θ n₁ t₁ n₂ t₂)) = _
  rw [map_neg]
  exact congrArg Neg.neg
    (chartResidueSheafSection_etale_coefficient (secondEquations r θ) n₂ t₂
      (secondPatchChart r θ n₂ t₂) (commonChart r θ n₁ t₁ n₂ t₂) inf_le_right
      (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (secondPatchChart_overComplex r θ n₂ t₂)
      (commonChart_overComplex r θ n₁ t₁ n₂ t₂) (commonChart_second r θ n₁ t₁ n₂ t₂) V
      (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂)
        (secondSurfaceDehomogenize p)))

theorem commonCubicSections_agree (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (V : Over (commonOpen r θ n₁ t₁ n₂ t₂)) :
    commonExteriorSection r θ n₁ t₁ n₂ t₂ V (firstCubicForm r θ n₁ t₁ n₂ t₂ p) =
      commonExteriorSection r θ n₁ t₁ n₂ t₂ V (secondCubicForm r θ n₁ t₁ n₂ t₂ p) :=
  congrArg (commonExteriorSection r θ n₁ t₁ n₂ t₂ V)
    (orientedCubicForms_agree r θ n₁ t₁ n₂ t₂ p hp)

/-- Every weighted cubic gives the same actual exterior-sheaf section
through the two projective charts, with the fixed coordinate orientation. -/
theorem orientedCubicSections_agree (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (V : Over (commonOpen r θ n₁ t₁ n₂ t₂)) :
    firstSectionOnCommon r θ n₁ t₁ n₂ t₂ V p =
      secondSectionOnCommon r θ n₁ t₁ n₂ t₂ V p := by
  calc
    _ = commonExteriorSection r θ n₁ t₁ n₂ t₂ V (firstCubicForm r θ n₁ t₁ n₂ t₂ p) :=
      (commonExteriorSection_first r θ n₁ t₁ n₂ t₂ V p).symm
    _ = commonExteriorSection r θ n₁ t₁ n₂ t₂ V (secondCubicForm r θ n₁ t₁ n₂ t₂ p) :=
      commonCubicSections_agree r θ n₁ t₁ n₂ t₂ p hp V
    _ = _ := commonExteriorSection_second r θ n₁ t₁ n₂ t₂ V p

end CycleQ2SurfaceResidueSheafOverlap
end

end


section

/-!
# Same-chart residue agreement in the actual exterior sheaf

The two Jacobian frames are compared on their genuine projective
intersection. The ring-level equality is transported by the universal
chart exterior-section map, including any common polynomial coefficient.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceSameChartResidueSections

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricAffineChartSections
open CycleQ2GeometricExteriorSheaf CycleQ2ChartExteriorBinding CycleQ2ChartResidueTransport
open CycleQ2SurfaceSameChartOverlap

attribute [local instance] PrincipalProduct.leftAlgebra PrincipalProduct.rightAlgebra
  PrincipalProduct.leftChartTower PrincipalProduct.rightChartTower
  PrincipalProduct.leftComplexTower PrincipalProduct.rightComplexTower
  PrincipalProduct.left_formallyEtale PrincipalProduct.right_formallyEtale

theorem leftPatchMap_polynomial (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ p : SurfacePoly) :
    leftPatchMap v n₁ t₁ n₂ t₂ (algebraMap SurfacePoly (AdjunctionPatch v n₁ t₁) p) =
      algebraMap SurfacePoly (SameChartRing v n₁ t₁ n₂ t₂) p :=
  PrincipalProduct.leftMap_base (augmentedJacobian v n₁ t₁) (augmentedJacobian v n₂ t₂)
    (algebraMap SurfacePoly (SurfaceChartRing v) p)

theorem rightPatchMap_polynomial (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ p : SurfacePoly) :
    rightPatchMap v n₁ t₁ n₂ t₂ (algebraMap SurfacePoly (AdjunctionPatch v n₂ t₂) p) =
      algebraMap SurfacePoly (SameChartRing v n₁ t₁ n₂ t₂) p :=
  PrincipalProduct.rightMap_base (augmentedJacobian v n₁ t₁) (augmentedJacobian v n₂ t₂)
    (algebraMap SurfacePoly (SurfaceChartRing v) p)

section Chart

variable {X : Scheme.{0}} {U : X.Opens}
  (v : Fin 2 → SurfacePoly) (n₁ t₁ n₂ t₂ : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (SurfaceChartRing v)))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ (SurfaceChartRing v))))

local notation "J₁" => augmentedJacobian v n₁ t₁
local notation "J₂" => augmentedJacobian v n₂ t₂
local notation "W" => principalOpen e J₁ ⊓ principalOpen e J₂

private abbrev sectionType (O : X.Opens) :=
  (exteriorSheaf X.sheaf
    (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
      (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.obj (op O)

local instance (O : X.Opens) : Module Γ(X, O) (sectionType f O) :=
  (exteriorSheaf X.sheaf
    (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
      (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.obj (op O) |>.isModule

def leftSection (V : Over W) : sectionType f V.left :=
  chartResidueSheafSection f v n₁ t₁ (principalChart e J₁)
    (principalChart_overComplex e J₁ f h) (Over.mk (V.hom ≫ homOfLE inf_le_left))

def rightSection (V : Over W) : sectionType f V.left :=
  chartResidueSheafSection f v n₂ t₂ (principalChart e J₂)
    (principalChart_overComplex e J₂ f h) (Over.mk (V.hom ≫ homOfLE inf_le_right))

def commonSectionMap (V : Over W) :
    (⋀[SameChartRing v n₁ t₁ n₂ t₂]^2
      (KaehlerDifferential ℂ (SameChartRing v n₁ t₁ n₂ t₂))) →ₛₗ[
        chartSection (PrincipalProduct.intersectionChart e J₁ J₂) V] sectionType f V.left :=
  chartExteriorSheafSection (PrincipalProduct.intersectionChart e J₁ J₂) f
    (PrincipalProduct.intersectionChart_overComplex e J₁ J₂ f h) 2 V

/-- Actual sheaf sections from either Jacobian frame agree on every subopen. -/
theorem section_independent (V : Over W) :
    rightSection v n₁ t₁ n₂ t₂ e f h V = leftSection v n₁ t₁ n₂ t₂ e f h V := by
  have hL := chartResidueSheafSection_etale (B := SameChartRing v n₁ t₁ n₂ t₂) v n₁ t₁
    (principalChart e J₁) (PrincipalProduct.intersectionChart e J₁ J₂) inf_le_left f
    (principalChart_overComplex e J₁ f h)
    (PrincipalProduct.intersectionChart_overComplex e J₁ J₂ f h)
    (PrincipalProduct.intersectionChart_left e J₁ J₂) V
  have hR := chartResidueSheafSection_etale (B := SameChartRing v n₁ t₁ n₂ t₂) v n₂ t₂
    (principalChart e J₂) (PrincipalProduct.intersectionChart e J₁ J₂) inf_le_right f
    (principalChart_overComplex e J₂ f h)
    (PrincipalProduct.intersectionChart_overComplex e J₁ J₂ f h)
    (PrincipalProduct.intersectionChart_right e J₁ J₂) V
  exact hR.symm.trans ((congrArg
    (fun ω => commonSectionMap v n₁ t₁ n₂ t₂ e f h V ω)
    (residue_independent v n₁ t₁ n₂ t₂)).trans hL)

def leftCoefficientSection (V : Over W) (p : SurfacePoly) : sectionType f V.left :=
  (show Γ(X, V.left) from chartSection (principalChart e J₁)
      (Over.mk (V.hom ≫ homOfLE inf_le_left))
      (algebraMap SurfacePoly (AdjunctionPatch v n₁ t₁) p)) •
    leftSection v n₁ t₁ n₂ t₂ e f h V

def rightCoefficientSection (V : Over W) (p : SurfacePoly) : sectionType f V.left :=
  (show Γ(X, V.left) from chartSection (principalChart e J₂)
      (Over.mk (V.hom ≫ homOfLE inf_le_right))
      (algebraMap SurfacePoly (AdjunctionPatch v n₂ t₂) p)) •
    rightSection v n₁ t₁ n₂ t₂ e f h V

/-- Multiplying by the same genuine chart polynomial preserves the agreement. -/
theorem coefficient_section_independent (V : Over W) (p : SurfacePoly) :
    rightCoefficientSection v n₁ t₁ n₂ t₂ e f h V p =
      leftCoefficientSection v n₁ t₁ n₂ t₂ e f h V p := by
  have hL := chartResidueSheafSection_etale_coefficient
    (B := SameChartRing v n₁ t₁ n₂ t₂) v n₁ t₁
    (principalChart e J₁) (PrincipalProduct.intersectionChart e J₁ J₂) inf_le_left f
    (principalChart_overComplex e J₁ f h)
    (PrincipalProduct.intersectionChart_overComplex e J₁ J₂ f h)
    (PrincipalProduct.intersectionChart_left e J₁ J₂) V
    (algebraMap SurfacePoly (AdjunctionPatch v n₁ t₁) p)
  have hR := chartResidueSheafSection_etale_coefficient
    (B := SameChartRing v n₁ t₁ n₂ t₂) v n₂ t₂
    (principalChart e J₂) (PrincipalProduct.intersectionChart e J₁ J₂) inf_le_right f
    (principalChart_overComplex e J₂ f h)
    (PrincipalProduct.intersectionChart_overComplex e J₁ J₂ f h)
    (PrincipalProduct.intersectionChart_right e J₁ J₂) V
    (algebraMap SurfacePoly (AdjunctionPatch v n₂ t₂) p)
  have he : rightPatchMap v n₁ t₁ n₂ t₂
        (algebraMap SurfacePoly (AdjunctionPatch v n₂ t₂) p) • rightResidue v n₁ t₁ n₂ t₂ =
      leftPatchMap v n₁ t₁ n₂ t₂
        (algebraMap SurfacePoly (AdjunctionPatch v n₁ t₁) p) • leftResidue v n₁ t₁ n₂ t₂ := by
    rw [rightPatchMap_polynomial, leftPatchMap_polynomial, residue_independent]
  exact hR.symm.trans ((congrArg
    (fun ω => commonSectionMap v n₁ t₁ n₂ t₂ e f h V ω) he).trans hL)

end Chart

theorem first_section_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (firstCommonOpen r θ n₁ t₁ n₂ t₂)) :
    rightSection (firstEquations r θ) n₁ t₁ n₂ t₂ (firstAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ) V =
      leftSection (firstEquations r θ) n₁ t₁ n₂ t₂ (firstAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ) V :=
  section_independent _ _ _ _ _ _ _ _ V

theorem first_coefficient_section_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ p : SurfacePoly)
    (V : Over (firstCommonOpen r θ n₁ t₁ n₂ t₂)) :
    rightCoefficientSection (firstEquations r θ) n₁ t₁ n₂ t₂ (firstAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ) V p =
      leftCoefficientSection (firstEquations r θ) n₁ t₁ n₂ t₂ (firstAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.firstAffineChart_overComplex r θ) V p :=
  coefficient_section_independent _ _ _ _ _ _ _ _ V p

theorem second_section_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ : SurfacePoly)
    (V : Over (secondCommonOpen r θ n₁ t₁ n₂ t₂)) :
    rightSection (secondEquations r θ) n₁ t₁ n₂ t₂ (secondAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ) V =
      leftSection (secondEquations r θ) n₁ t₁ n₂ t₂ (secondAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ) V :=
  section_independent _ _ _ _ _ _ _ _ V

theorem second_coefficient_section_independent (r θ : ℂ) (n₁ t₁ n₂ t₂ p : SurfacePoly)
    (V : Over (secondCommonOpen r θ n₁ t₁ n₂ t₂)) :
    rightCoefficientSection (secondEquations r θ) n₁ t₁ n₂ t₂ (secondAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ) V p =
      leftCoefficientSection (secondEquations r θ) n₁ t₁ n₂ t₂ (secondAffineChart r θ)
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ) (CycleQ2GeometricSurfaceCoefficients.secondAffineChart_overComplex r θ) V p :=
  coefficient_section_independent _ _ _ _ _ _ _ _ V p

end CycleQ2SurfaceSameChartResidueSections
end

end


section

/-!
# Cubic two-forms on the actual normal-chart neighborhood

Twelve actual Jacobian opens give a neighborhood of the literal curve.
Compatible local cubic residue sections glue in the genuine exterior
square of the surface differential sheaf. No claim is made that these
opens cover the entire surface.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2SurfaceCubicGluing

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry MvPolynomial
open CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceAdjunction
open CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2GeometricSurfaceJacobianCharts
open CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricSurfaceCoefficients CycleQ2GeometricAffineChartSections
open CycleQ2GeometricExteriorSheaf CycleQ2ChartExteriorBinding
open CycleQ2SurfaceResidueSheafOverlap CycleQ2SurfaceCommonOpen
open CycleQ2SurfaceSameChartOverlap CycleQ2SurfaceSameChartResidueSections

abbrev PatchIndex := (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3)
abbrev CubicPolynomial := MvPolynomial (Fin 5) ℂ
abbrev WeightedCubic := ↥(weightedHomogeneousSubmodule ℂ CycleQ2CartierSurfaceGrading.weight 3)

def patchOpen (r θ : ℂ) : PatchIndex → (projectiveSurface r θ).Opens
  | .inl (i, j) => firstNormalOpen r θ i j
  | .inr (i, j) => secondNormalOpen r θ i j

/-- The precise domain of the glued form is the union of the twelve opens. -/
def neighborhood (r θ : ℂ) : (projectiveSurface r θ).Opens := ⨆ k, patchOpen r θ k

abbrev additiveExteriorSheaf (r θ : ℂ) :
    TopCat.Sheaf AddCommGrpCat.{0} (projectiveSurface r θ) :=
  (SheafOfModules.toSheaf _).obj (surfaceExteriorSheaf r θ)

theorem literal_neighborhood_preimage :
    CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ⁻¹ᵁ neighborhood 57 1 = ⊤ := by
  simp only [neighborhood, iSup_sum, iSup_prod, patchOpen,
    Scheme.Hom.preimage_sup, Scheme.Hom.preimage_iSup]
  exact CycleQ2GeometricSurfaceNormalCover.normalSurfaceOpen_preimage_cover

theorem literal_curve_range_subset_neighborhood :
    Set.range (CycleQ2GeometricLiteralSurface.curveToSurface 57 1) ⊆
      (neighborhood 57 1 : Set (projectiveSurface 57 1)) := by
  rintro _ ⟨x, rfl⟩
  change x ∈ CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ⁻¹ᵁ neighborhood 57 1
  rw [literal_neighborhood_preimage]
  trivial

section Restriction

variable {X : Scheme.{0}} {U : X.Opens}
  (f : X ⟶ Spec (CommRingCat.of ℂ)) (v : Fin 2 → SurfacePoly) (n t : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch v n t)))
  (h : e.inv ≫ U.ι ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch v n t))))

local instance (O : X.Opens) : Module Γ(X, O)
    ((CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
      (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
        (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.obj (op O)) :=
  (CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
    (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
      (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.obj (op O) |>.isModule

private theorem chartResidue_restrict {V W : Over U} (k : V ⟶ W) :
    (CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
      (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
        (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.map k.left.op
        (chartResidueSheafSection f v n t e h W) =
      chartResidueSheafSection f v n t e h V :=
  (congrArg (fun s => (CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
      (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
        (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.map k.left.op s)
    (chartResidueSheafSection_eq_canonical f v n t e h W)).trans
    ((chartExteriorSheafSection_restrict e f h k 2 (localSurfaceResidueForm v n t)).trans
      (chartResidueSheafSection_eq_canonical f v n t e h V).symm)

private theorem chartPolynomialResidue_restrict {V W : Over U} (k : V ⟶ W) (p : SurfacePoly) :
    (CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
      (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
        (CycleQ2GeometricAffineChartSections.schemeCoefficient f)).val 2).val.map k.left.op
        (chartSection e W (algebraMap SurfacePoly (AdjunctionPatch v n t) p) •
          chartResidueSheafSection f v n t e h W) =
      chartSection e V (algebraMap SurfacePoly (AdjunctionPatch v n t) p) •
        chartResidueSheafSection f v n t e h V := by
  exact ((CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
      (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
        (schemeCoefficient f)).val 2).val.map_smul k.left.op
          (chartSection e W (algebraMap SurfacePoly (AdjunctionPatch v n t) p))
          (chartResidueSheafSection f v n t e h W)).trans
    (congrArg₂ (fun (a : Γ(X, V.left)) (s :
      (CycleQ2GeometricExteriorSheaf.exteriorSheaf X.sheaf
        (CycleQ2GeometricDifferentialSheaf.differentialSheaf X.sheaf
          (schemeCoefficient f)).val 2).val.obj (op V.left)) => a • s)
      (chartSection_naturality e k _) (chartResidue_restrict f v n t e h k))

end Restriction

theorem firstCubicSection_restrict (r θ : ℂ) (n t : SurfacePoly) (p : CubicPolynomial)
    {V W : Over (firstPatchOpen r θ n t)} (k : V ⟶ W) :
    (surfaceExteriorSheaf r θ).val.map k.left.op (firstCubicSection r θ n t p W) =
      firstCubicSection r θ n t p V :=
  chartPolynomialResidue_restrict (projectiveToComplex r θ) (firstEquations r θ) n t
    (firstPatchChart r θ n t) (firstPatchChart_overComplex r θ n t) k (firstSurfaceDehomogenize p)

theorem secondCubicSection_restrict (r θ : ℂ) (n t : SurfacePoly) (p : CubicPolynomial)
    {V W : Over (secondPatchOpen r θ n t)} (k : V ⟶ W) :
    (surfaceExteriorSheaf r θ).val.map k.left.op (secondCubicSection r θ n t p W) =
      secondCubicSection r θ n t p V := by
  exact (map_neg ((surfaceExteriorSheaf r θ).val.map k.left.op).hom _).trans
    (congrArg Neg.neg
      (chartPolynomialResidue_restrict (projectiveToComplex r θ) (secondEquations r θ) n t
        (secondPatchChart r θ n t) (secondPatchChart_overComplex r θ n t) k
        (secondSurfaceDehomogenize p)))

def localSectionOn (r θ : ℂ) (p : CubicPolynomial) (k : PatchIndex)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ patchOpen r θ k) :
    (surfaceExteriorSheaf r θ).val.obj (op O) := by
  rcases k with ⟨i, j⟩ | ⟨i, j⟩
  · exact firstCubicSection r θ (normalPolynomial (firstQuadric r) i)
      (includeCurve (X j)) p (Over.mk (homOfLE hO))
  · exact secondCubicSection r θ (normalPolynomial (secondQuadric r) i)
      (includeCurve (X j)) p (Over.mk (homOfLE hO))

def localSection (r θ : ℂ) (p : CubicPolynomial) (k : PatchIndex) :=
  localSectionOn r θ p k (patchOpen r θ k) le_rfl

theorem localSectionOn_restrict (r θ : ℂ) (p : CubicPolynomial) (k : PatchIndex)
    {O P : (projectiveSurface r θ).Opens} (hPO : P ≤ O) (hO : O ≤ patchOpen r θ k) :
    (surfaceExteriorSheaf r θ).val.map (homOfLE hPO).op (localSectionOn r θ p k O hO) =
      localSectionOn r θ p k P (hPO.trans hO) := by
  cases k with
  | inl k =>
      rcases k with ⟨i, j⟩
      exact firstCubicSection_restrict r θ (normalPolynomial (firstQuadric r) i)
        (includeCurve (X j)) p
        (V := Over.mk (homOfLE (hPO.trans hO))) (W := Over.mk (homOfLE hO))
        (Over.homMk (homOfLE hPO))
  | inr k =>
      rcases k with ⟨i, j⟩
      exact secondCubicSection_restrict r θ (normalPolynomial (secondQuadric r) i)
        (includeCurve (X j)) p
        (V := Over.mk (homOfLE (hPO.trans hO))) (W := Over.mk (homOfLE hO))
        (Over.homMk (homOfLE hPO))

private theorem firstLocalSections_agree (r θ : ℂ) (p : CubicPolynomial)
    (i i' : Fin 2) (j j' : Fin 3) (O : (projectiveSurface r θ).Opens)
    (hk : O ≤ patchOpen r θ (.inl (i,j))) (hl : O ≤ patchOpen r θ (.inl (i',j'))) :
    localSectionOn r θ p (.inl (i,j)) O hk = localSectionOn r θ p (.inl (i',j')) O hl :=
  (first_coefficient_section_independent r θ
    (normalPolynomial (firstQuadric r) i) (includeCurve (X j))
    (normalPolynomial (firstQuadric r) i') (includeCurve (X j'))
    (firstSurfaceDehomogenize p) (Over.mk (homOfLE (le_inf hk hl)))).symm

private theorem crossLocalSections_agree (r θ : ℂ) (p : CubicPolynomial)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (i i' : Fin 2) (j j' : Fin 3) (O : (projectiveSurface r θ).Opens)
    (hk : O ≤ patchOpen r θ (.inl (i,j))) (hl : O ≤ patchOpen r θ (.inr (i',j'))) :
    localSectionOn r θ p (.inl (i,j)) O hk = localSectionOn r θ p (.inr (i',j')) O hl :=
  orientedCubicSections_agree r θ
    (normalPolynomial (firstQuadric r) i) (includeCurve (X j))
    (normalPolynomial (secondQuadric r) i') (includeCurve (X j')) p hp
    (Over.mk (homOfLE (le_inf hk hl)))

private theorem secondLocalSections_agree (r θ : ℂ) (p : CubicPolynomial)
    (i i' : Fin 2) (j j' : Fin 3) (O : (projectiveSurface r θ).Opens)
    (hk : O ≤ patchOpen r θ (.inr (i,j))) (hl : O ≤ patchOpen r θ (.inr (i',j'))) :
    localSectionOn r θ p (.inr (i,j)) O hk = localSectionOn r θ p (.inr (i',j')) O hl :=
  congrArg (fun s : (surfaceExteriorSheaf r θ).val.obj (op O) => -s)
    (second_coefficient_section_independent r θ
      (normalPolynomial (secondQuadric r) i) (includeCurve (X j))
      (normalPolynomial (secondQuadric r) i') (includeCurve (X j'))
      (secondSurfaceDehomogenize p) (Over.mk (homOfLE (le_inf hk hl)))).symm

/-- Every two local cubic sections agree on every subopen of their intersection. -/
theorem localSectionOn_pairwise (r θ : ℂ) (p : CubicPolynomial)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3)
    (k l : PatchIndex) (O : (projectiveSurface r θ).Opens)
    (hk : O ≤ patchOpen r θ k) (hl : O ≤ patchOpen r θ l) :
    localSectionOn r θ p k O hk = localSectionOn r θ p l O hl := by
  rcases k with ⟨i, j⟩ | ⟨i, j⟩
  · rcases l with ⟨i', j'⟩ | ⟨i', j'⟩
    · exact firstLocalSections_agree r θ p i i' j j' O hk hl
    · exact crossLocalSections_agree r θ p hp i i' j j' O hk hl
  · rcases l with ⟨i', j'⟩ | ⟨i', j'⟩
    · exact (crossLocalSections_agree r θ p hp i' i j' j O hl hk).symm
    · exact secondLocalSections_agree r θ p i i' j j' O hk hl

theorem localSections_compatible (r θ : ℂ) (p : WeightedCubic) :
    TopCat.Presheaf.IsCompatible (additiveExteriorSheaf r θ).obj (patchOpen r θ)
      (localSection r θ p.val) := by
  intro k l
  exact (localSectionOn_restrict r θ p.val k inf_le_left le_rfl).trans
    ((localSectionOn_pairwise r θ p.val p.property k l _ inf_le_left inf_le_right).trans
      (localSectionOn_restrict r θ p.val l inf_le_right le_rfl).symm)

/-- Existence and uniqueness use the actual exterior sheaf's gluing property. -/
theorem existsUnique_cubicSection (r θ : ℂ) (p : WeightedCubic) :
    ∃! s : (surfaceExteriorSheaf r θ).val.obj (op (neighborhood r θ)),
      ∀ k : PatchIndex, (surfaceExteriorSheaf r θ).val.map
        (homOfLE (show patchOpen r θ k ≤ neighborhood r θ from le_iSup (patchOpen r θ) k)).op s =
          localSection r θ p.val k := by
  have h := (additiveExteriorSheaf r θ).existsUnique_gluing' (patchOpen r θ) (neighborhood r θ)
    (fun k => homOfLE (le_iSup (patchOpen r θ) k)) le_rfl
    (localSection r θ p.val) (localSections_compatible r θ p)
  exact h

def gluedCubicSection (r θ : ℂ) (p : WeightedCubic) :
    (surfaceExteriorSheaf r θ).val.obj (op (neighborhood r θ)) :=
  Classical.choose (existsUnique_cubicSection r θ p)

theorem gluedCubicSection_restrict (r θ : ℂ) (p : WeightedCubic) (k : PatchIndex) :
    (surfaceExteriorSheaf r θ).val.map
        (homOfLE (show patchOpen r θ k ≤ neighborhood r θ from le_iSup (patchOpen r θ) k)).op
        (gluedCubicSection r θ p) = localSection r θ p.val k :=
  (Classical.choose_spec (existsUnique_cubicSection r θ p)).1 k

theorem gluedCubicSection_unique (r θ : ℂ) (p : WeightedCubic)
    (s : (surfaceExteriorSheaf r θ).val.obj (op (neighborhood r θ)))
    (hs : ∀ k : PatchIndex, (surfaceExteriorSheaf r θ).val.map
      (homOfLE (show patchOpen r θ k ≤ neighborhood r θ from le_iSup (patchOpen r θ) k)).op s =
        localSection r θ p.val k) : s = gluedCubicSection r θ p :=
  (Classical.choose_spec (existsUnique_cubicSection r θ p)).2 s hs

theorem gluedCubicSection_subopen (r θ : ℂ) (p : WeightedCubic) (k : PatchIndex)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ patchOpen r θ k) :
    (surfaceExteriorSheaf r θ).val.map
        (homOfLE (hO.trans (le_iSup (patchOpen r θ) k))).op (gluedCubicSection r θ p) =
      localSectionOn r θ p.val k O hO := by
  have hc := (surfaceExteriorSheaf r θ).val.map_comp_apply
    (homOfLE (le_iSup (patchOpen r θ) k)).op (homOfLE hO).op (gluedCubicSection r θ p)
  exact hc.trans ((congrArg (fun s => (surfaceExteriorSheaf r θ).val.map (homOfLE hO).op s)
    (gluedCubicSection_restrict r θ p k)).trans
    (localSectionOn_restrict r θ p.val k hO le_rfl))

local instance (r θ : ℂ) (O : (projectiveSurface r θ).Opens) :
    Module Γ(projectiveSurface r θ, O) ((surfaceExteriorSheaf r θ).val.obj (op O)) :=
  ((surfaceExteriorSheaf r θ).val.obj (op O)).isModule

theorem localSectionOn_zero (r θ : ℂ) (k : PatchIndex)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ patchOpen r θ k) :
    localSectionOn r θ 0 k O hO = 0 := by
  rcases k with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [localSectionOn, firstCubicSection, map_zero]
    exact zero_smul Γ(projectiveSurface r θ, O) _
  · simp only [localSectionOn, secondCubicSection, map_zero]
    exact (congrArg Neg.neg (zero_smul Γ(projectiveSurface r θ, O) _)).trans neg_zero

theorem localSectionOn_add (r θ : ℂ) (p q : CubicPolynomial) (k : PatchIndex)
    (O : (projectiveSurface r θ).Opens) (hO : O ≤ patchOpen r θ k) :
    localSectionOn r θ (p + q) k O hO =
      localSectionOn r θ p k O hO + localSectionOn r θ q k O hO := by
  rcases k with ⟨i, j⟩ | ⟨i, j⟩
  · simp only [localSectionOn, firstCubicSection, map_add]
    exact add_smul (R := Γ(projectiveSurface r θ, O)) _ _ _
  · simp only [localSectionOn, secondCubicSection, map_add]
    exact (congrArg Neg.neg (add_smul (R := Γ(projectiveSurface r θ, O)) _ _ _)).trans (neg_add _ _)

theorem gluedCubicSection_zero (r θ : ℂ) : gluedCubicSection r θ 0 = 0 := by
  symm
  apply gluedCubicSection_unique r θ 0
  intro k
  exact (map_zero _).trans (localSectionOn_zero r θ k _ le_rfl).symm

theorem gluedCubicSection_add (r θ : ℂ) (p q : WeightedCubic) :
    gluedCubicSection r θ (p + q) = gluedCubicSection r θ p + gluedCubicSection r θ q := by
  symm
  apply gluedCubicSection_unique r θ (p + q)
  intro k
  rw [map_add, gluedCubicSection_restrict, gluedCubicSection_restrict]
  exact (localSectionOn_add r θ p.val q.val k _ le_rfl).symm

/-- Weighted cubics give actual exterior-sheaf sections additively. -/
def gluedCubicAddHom (r θ : ℂ) :
    WeightedCubic →+ (surfaceExteriorSheaf r θ).val.obj (op (neighborhood r θ)) where
  toFun := gluedCubicSection r θ
  map_zero' := gluedCubicSection_zero r θ
  map_add' := gluedCubicSection_add r θ

end CycleQ2SurfaceCubicGluing
end

end
