import Proposal.GeometricThirdSurfaceChart
import Proposal.GeometricSurfaceResidueSections

/-!
# The actual first-to-third ambient coordinate change

Status: source-only proof draft; verification is deferred at the user's request.
The substitution is (z,a,b,c) ↦ (z/c²,a/c,1/c,b/c). Its Jacobian determinant
is positive c⁻⁶. Differentiating the original weighted equations before
passing to a quotient gives their conormal factors c⁻⁶ and c⁻³. The mixed
Jacobian identity is then proved for every actual ring map out of this
ambient localization which kills the two original first-chart equations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceFirstThirdTransition

open MvPolynomial Module
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceAdjunction
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2ThirdSurfaceChart

namespace Ambient

abbrev AmbientOverlap := Localization.Away (X (some (2 : Fin 3)) : SurfacePoly)

def base : SurfacePoly →ₐ[ℂ] AmbientOverlap :=
  IsScalarTower.toAlgHom ℂ SurfacePoly AmbientOverlap

def ambientCoordinate (j : Option (Fin 3)) : AmbientOverlap := base (X j)

def ambientInverse : AmbientOverlap :=
  IsLocalization.Away.invSelf (X (some (2 : Fin 3)) : SurfacePoly)

theorem coordinate_mul_inverse : ambientCoordinate (some 2) * ambientInverse = 1 :=
  IsLocalization.Away.mul_invSelf (X (some (2 : Fin 3)) : SurfacePoly)

def coordinateUnit : AmbientOverlapˣ :=
  Units.mkOfMulEqOne (ambientCoordinate (some 2)) ambientInverse coordinate_mul_inverse

def ambientPartial (j : Option (Fin 3)) : Derivation ℂ AmbientOverlap AmbientOverlap :=
  CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)

theorem ambientPartial_base (j : Option (Fin 3)) (p : SurfacePoly) :
    ambientPartial j (base p) = base (pderiv j p) := by
  change CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)
      (algebraMap SurfacePoly AmbientOverlap p) = _
  rw [CycleQ2GeometricFunctionalDifferentials.localizedDerivation_algebraMap]
  simp only [Basis.coord_apply, KaehlerDifferential.mvPolynomialBasis_repr_apply]

theorem ambientPartial_coordinate (j k : Option (Fin 3)) :
    ambientPartial j (ambientCoordinate k) = if k = j then 1 else 0 := by
  rw [ambientCoordinate, ambientPartial_base]
  by_cases h : k = j <;> simp [pderiv_X, h]

theorem ambientPartial_inverse (j : Option (Fin 3)) :
    ambientPartial j ambientInverse =
      -(ambientInverse ^ 2) * ambientPartial j (ambientCoordinate (some 2)) :=
  CycleQ2GeometricResidueFrames.derivation_unit_inverse (ambientPartial j) coordinateUnit

def ambientChangeCoordinate : Option (Fin 3) → AmbientOverlap :=
  fun j => match j with
    | none => ambientCoordinate none * ambientInverse ^ 2
    | some k => ![ambientCoordinate (some 0) * ambientInverse,
        ambientInverse, ambientCoordinate (some 1) * ambientInverse] k

def ambientChangeEvaluate : SurfacePoly →ₐ[ℂ] AmbientOverlap :=
  aeval ambientChangeCoordinate

private theorem thirdEvaluate_dehomogenize {R : Type*} [CommRing R] [Algebra ℂ R]
    (z a b c : R) (p : WeightedPoly) :
    CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate z a b c (thirdDehomogenize p) =
      aeval ![a,b,c,1,z-c^2] p := by
  have h : (CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate z a b c).comp
      thirdDehomogenize = aeval ![a,b,c,1,z-c^2] := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [thirdDehomogenize_eq]
    fin_cases j <;> simp [CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate]
  exact AlgHom.congr_fun h p

private theorem dehomogenize_scaling {R : Type*} [CommRing R] [Algebra ℂ R]
    (z a b c t : R) (ht : c*t = 1)
    (p : WeightedPoly) (n : ℕ) (hp : p.IsWeightedHomogeneous weight n) :
    CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate
        (z*t^2) (a*t) t (b*t) (thirdDehomogenize p) =
      t^n * CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate
        z a b c (firstSurfaceDehomogenize p) := by
  rw [thirdEvaluate_dehomogenize,
    CycleQ2GeometricSurfaceWeightedChange.firstEvaluate_dehomogenize]
  have hv : (![a*t,t,b*t,1,z*t^2-(b*t)^2] : Fin 5 → R) =
      fun j => t ^ weight j * (![a,1,b,c,z-b^2] : Fin 5 → R) j := by
    funext j
    fin_cases j
    · simp [weight, mul_comm]
    · simp [weight]
    · simp [weight, mul_comm]
    · simpa [weight, mul_comm] using ht.symm
    · simp only [weight, Matrix.cons_val_succ, Matrix.cons_val_zero]
      ring
  rw [hv]
  exact weighted_homogeneous_eval_scale (algebraMap ℂ R) ![a,1,b,c,z-b^2] t p n hp

private theorem base_evaluate (p : SurfacePoly) :
    CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate
        (ambientCoordinate none) (ambientCoordinate (some 0))
        (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) p = base p := by
  have h : CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate
      (ambientCoordinate none) (ambientCoordinate (some 0))
      (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) = base := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp [CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate, ambientCoordinate]
    | some j => fin_cases j <;>
      simp [CycleQ2GeometricSurfaceWeightedChange.surfaceEvaluate, ambientCoordinate]
  exact AlgHom.congr_fun h p

/-- The coefficient change is computed from the original weighted polynomial. -/
theorem homogeneous_change (p : WeightedPoly) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    ambientChangeEvaluate (thirdDehomogenize p) =
      ambientInverse ^ n * base (firstSurfaceDehomogenize p) := by
  have h := dehomogenize_scaling (ambientCoordinate none) (ambientCoordinate (some 0))
    (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) ambientInverse
    coordinate_mul_inverse p n hp
  rw [base_evaluate] at h
  exact h

def ambientJacobian : Matrix (Option (Fin 3)) (Option (Fin 3)) AmbientOverlap :=
  fun j k => ambientPartial k (ambientChangeCoordinate j)

theorem gradient_change (p : WeightedPoly) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) (i : Option (Fin 3)) :
    ambientPartial i (ambientChangeEvaluate (thirdDehomogenize p)) =
      ambientInverse ^ n * base (pderiv i (firstSurfaceDehomogenize p)) +
        base (firstSurfaceDehomogenize p) *
          (n • ambientInverse ^ (n-1) * ambientPartial i ambientInverse) := by
  rw [homogeneous_change p hp, Derivation.leibniz, ambientPartial_base,
    Derivation.leibniz_pow]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_assoc]

private theorem derivative_mul_square {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (z c t : R) (ht : D t = -(t^2) * D c) :
    D (z*t^2) = t^2 * D z - (2*z*t^3) * D c := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, ht]
  simp only [Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  ring

private theorem derivative_mul_linear {R : Type*} [CommRing R] [Algebra ℂ R]
    (D : Derivation ℂ R R) (a c t : R) (ht : D t = -(t^2) * D c) :
    D (a*t) = t * D a - (a*t^2) * D c := by
  rw [Derivation.leibniz, ht]
  simp only [smul_eq_mul]
  ring

theorem ambientJacobian_none (j : Option (Fin 3)) :
    ambientJacobian none j = ambientInverse^2 * (if none=j then 1 else 0) -
      (2*ambientCoordinate none*ambientInverse^3) * (if some 2=j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate none*ambientInverse^2) = _
  rw [derivative_mul_square (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some0 (j : Option (Fin 3)) :
    ambientJacobian (some 0) j = ambientInverse * (if some 0=j then 1 else 0) -
      (ambientCoordinate (some 0)*ambientInverse^2) * (if some 2=j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 0)*ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some1 (j : Option (Fin 3)) :
    ambientJacobian (some 1) j = -(ambientInverse^2) * (if some 2=j then 1 else 0) := by
  change ambientPartial j ambientInverse = _
  rw [ambientPartial_inverse, ambientPartial_coordinate]

theorem ambientJacobian_some2 (j : Option (Fin 3)) :
    ambientJacobian (some 2) j = ambientInverse * (if some 1=j then 1 else 0) -
      (ambientCoordinate (some 1)*ambientInverse^2) * (if some 2=j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 1)*ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

def jacobianFin : Matrix (Fin 4) (Fin 4) AmbientOverlap :=
  fun i j => ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)

private theorem coordinateIndex (i : Fin 4) :
    _root_.finSuccEquiv 3 i = (![none,some 0,some 1,some 2] : Fin 4 → Option (Fin 3)) i := by
  fin_cases i <;> rfl

theorem jacobianFin_eq :
    jacobianFin =
      !![ambientInverse^2, 0, 0, -2*ambientCoordinate none*ambientInverse^3;
         0, ambientInverse, 0, -ambientCoordinate (some 0)*ambientInverse^2;
         0, 0, 0, -ambientInverse^2;
         0, 0, ambientInverse, -ambientCoordinate (some 1)*ambientInverse^2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [jacobianFin, coordinateIndex, ambientJacobian_none, ambientJacobian_some0,
      ambientJacobian_some1, ambientJacobian_some2]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4),2,3; 0,2,3; 0,1,3; 0,1,2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The sign is positive for the first-to-third coordinate permutation. -/
theorem jacobianFin_det : jacobianFin.det = ambientInverse^6 := by
  rw [jacobianFin_eq]
  simp [Matrix.det_succ_row_zero, Matrix.submatrix_apply,
    Fin.sum_univ_succ, succAbove_four]
  ring

/-- The actual Kähler module of the ambient localization has its coordinate basis. -/
def ambientKaehlerBasis :
    Basis (Option (Fin 3)) AmbientOverlap (KaehlerDifferential ℂ AmbientOverlap) := by
  letI : Algebra.FormallyEtale SurfacePoly AmbientOverlap :=
    Algebra.FormallyEtale.of_isLocalization
      (Rₘ := AmbientOverlap) (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly))
  exact ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).baseChange AmbientOverlap).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℂ SurfacePoly AmbientOverlap)

theorem ambientKaehlerBasis_apply (j : Option (Fin 3)) :
    ambientKaehlerBasis j = KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j) := by
  letI : Algebra.FormallyEtale SurfacePoly AmbientOverlap :=
    Algebra.FormallyEtale.of_isLocalization
      (Rₘ := AmbientOverlap) (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly))
  simp only [ambientKaehlerBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
    KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
  rfl

def ambientFunctional (j : Option (Fin 3)) :
    KaehlerDifferential ℂ AmbientOverlap →ₗ[AmbientOverlap] AmbientOverlap :=
  CycleQ2GeometricFunctionalDifferentials.localFunctional
    (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)

theorem ambientFunctional_D (j : Option (Fin 3)) (a : AmbientOverlap) :
    ambientFunctional j (KaehlerDifferential.D ℂ AmbientOverlap a) = ambientPartial j a := rfl

theorem ambientKaehlerBasis_coord (j : Option (Fin 3)) :
    ambientKaehlerBasis.coord j = ambientFunctional j := by
  apply ambientKaehlerBasis.ext
  intro k
  rw [Basis.coord_apply, Basis.repr_self, ambientKaehlerBasis_apply, ambientFunctional_D,
    ambientPartial_coordinate]
  simp only [Finsupp.single_apply]

theorem ambient_D_expand (p : AmbientOverlap) :
    KaehlerDifferential.D ℂ AmbientOverlap p =
      ∑ j : Option (Fin 3), ambientPartial j p •
        KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j) := by
  have h := ambientKaehlerBasis.sum_repr (KaehlerDifferential.D ℂ AmbientOverlap p)
  have hc (j : Option (Fin 3)) :
      ambientKaehlerBasis.repr (KaehlerDifferential.D ℂ AmbientOverlap p) j =
        ambientPartial j p := by
    change ambientKaehlerBasis.coord j _ = _
    rw [ambientKaehlerBasis_coord]
    rfl
  simpa only [hc, ambientKaehlerBasis_apply] using h.symm

end Ambient

open Ambient

variable {R : Type*} [CommRing R]

def firstGradient (φ : AmbientOverlap →+* R) (p : SurfacePoly) (j : Fin 4) : R :=
  φ (base (pderiv (_root_.finSuccEquiv 3 j) p))

def pulledGradient (φ : AmbientOverlap →+* R) (p : SurfacePoly) (j : Fin 4) : R :=
  φ (ambientPartial (_root_.finSuccEquiv 3 j) (ambientChangeEvaluate p))

def thirdGradient (φ : AmbientOverlap →+* R) (p : SurfacePoly) (j : Fin 4) : R :=
  φ (ambientChangeEvaluate (pderiv (_root_.finSuccEquiv 3 j) p))

def sourcePolynomialMap (φ : AmbientOverlap →+* R) : SurfacePoly →+* R :=
  φ.comp base.toRingHom

def targetPolynomialMap (φ : AmbientOverlap →+* R) : SurfacePoly →+* R :=
  φ.comp ambientChangeEvaluate.toRingHom

def mixedGradientMatrix (φ : AmbientOverlap →+* R) (r θ : ℂ)
    (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) R :=
  ![firstGradient φ (firstEquations r θ 0),
    firstGradient φ (firstEquations r θ 1), pulledGradient φ p, pulledGradient φ q]

def changedGradientMatrix (φ : AmbientOverlap →+* R) (r θ : ℂ)
    (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => thirdGradient φ (augmentedPolynomialRows (thirdEquations r θ) p q i) j

theorem pulledGradient_chain (φ : AmbientOverlap →+* R) (p : SurfacePoly) (j : Fin 4) :
    pulledGradient φ p j = ∑ k : Fin 4,
      thirdGradient φ p k * φ (jacobianFin k j) := by
  unfold pulledGradient
  change φ (ambientPartial (_root_.finSuccEquiv 3 j) (aeval ambientChangeCoordinate p)) = _
  rw [CycleQ2GeometricSurfaceWeightedChange.derivation_aeval, map_sum]
  calc
    _ = ∑ k : Option (Fin 3), φ (ambientChangeEvaluate (pderiv k p)) *
        φ (ambientJacobian k (_root_.finSuccEquiv 3 j)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact map_mul φ _ _
    _ = _ := (Equiv.sum_comp (_root_.finSuccEquiv 3) _).symm

theorem pulledGradient_firstEquation (r θ : ℂ) (φ : AmbientOverlap →+* R)
    (hF : φ (base (firstEquations r θ 0)) = 0) (j : Fin 4) :
    pulledGradient φ (thirdEquations r θ 0) j =
      φ ambientInverse ^ 6 * firstGradient φ (firstEquations r θ 0) j := by
  have hf : firstSurfaceDehomogenize (actualSeedEquation r θ) = firstEquations r θ 0 := by
    simp only [firstEquations, Matrix.cons_val_zero]
    exact firstSurfaceDehomogenize_equation r θ
  have h := congrArg φ (gradient_change (actualSeedEquation r θ) 6
    (actualSeedEquation_homogeneous r θ) (_root_.finSuccEquiv 3 j))
  rw [hf] at h
  simpa only [thirdEquations, dehomogenizedEquations, Matrix.cons_val_zero,
    map_add, map_mul, map_pow, hF, zero_mul, add_zero,
    pulledGradient, firstGradient, thirdDehomogenize] using h

theorem pulledGradient_secondEquation (r θ : ℂ) (φ : AmbientOverlap →+* R)
    (hh : φ (base (firstEquations r θ 1)) = 0) (j : Fin 4) :
    pulledGradient φ (thirdEquations r θ 1) j =
      φ ambientInverse ^ 3 * firstGradient φ (firstEquations r θ 1) j := by
  have hf : firstSurfaceDehomogenize (thetaH θ) = firstEquations r θ 1 := by
    simp only [firstEquations, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact firstSurfaceDehomogenize_h θ
  have h := congrArg φ (gradient_change (thetaH θ) 3
    (thetaH_homogeneous θ) (_root_.finSuccEquiv 3 j))
  rw [hf] at h
  simpa only [thirdEquations, dehomogenizedEquations, Matrix.cons_val_one,
    Matrix.cons_val_zero, map_add, map_mul, map_pow, hh, zero_mul, add_zero,
    pulledGradient, firstGradient, thirdDehomogenize] using h

private theorem weightedDiagonal_det (t : R) :
    (Matrix.diagonal (![t^6,t^3,1,1] : Fin 4 → R)).det = t^9 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

/-- The actual positive first-to-third residue factor, before any choice
of surface section or cohomology class. -/
theorem mixedJacobian_transition (r θ : ℂ) (φ : AmbientOverlap →+* R)
    (hF : φ (base (firstEquations r θ 0)) = 0)
    (hh : φ (base (firstEquations r θ 1)) = 0) (p q : SurfacePoly) :
    Matrix.det ![firstGradient φ (firstEquations r θ 0),
      firstGradient φ (firstEquations r θ 1), pulledGradient φ p, pulledGradient φ q] =
      φ (ambientCoordinate (some 2)) ^ 3 *
        Matrix.det (fun i j : Fin 4 =>
          thirdGradient φ (augmentedPolynomialRows (thirdEquations r θ) p q i) j) := by
  let T : Matrix (Fin 4) (Fin 4) R := fun i j =>
    thirdGradient φ (augmentedPolynomialRows (thirdEquations r θ) p q i) j
  let J : Matrix (Fin 4) (Fin 4) R := fun i j => φ (jacobianFin i j)
  let B : Matrix (Fin 4) (Fin 4) R :=
    ![firstGradient φ (firstEquations r θ 0),
      firstGradient φ (firstEquations r θ 1), pulledGradient φ p, pulledGradient φ q]
  have hmul : T*J = Matrix.diagonal ![φ ambientInverse^6,φ ambientInverse^3,1,1]*B := by
    ext i j
    rw [Matrix.diagonal_mul]
    change (∑ k : Fin 4, thirdGradient φ
      (augmentedPolynomialRows (thirdEquations r θ) p q i) k * φ (jacobianFin k j)) = _
    rw [← pulledGradient_chain]
    fin_cases i <;> simp only [augmentedPolynomialRows, B,
      Matrix.cons_val_zero', Matrix.cons_val_succ', one_mul]
    · exact pulledGradient_firstEquation r θ φ hF j
    · exact pulledGradient_secondEquation r θ φ hh j
  have hdetJ : J.det = φ ambientInverse^6 := by
    change (φ.mapMatrix jacobianFin).det = _
    rw [← RingHom.map_det, jacobianFin_det, map_pow]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, hdetJ, Matrix.det_mul, weightedDiagonal_det] at hdet
  have ht : φ (ambientCoordinate (some 2)) * φ ambientInverse = 1 := by
    rw [← map_mul, coordinate_mul_inverse, map_one]
  have hu : IsUnit (φ ambientInverse) :=
    isUnit_iff_exists_inv.mpr ⟨φ (ambientCoordinate (some 2)), (mul_comm _ _).trans ht⟩
  apply (hu.pow 9).mul_left_cancel
  have h3 : φ (ambientCoordinate (some 2))^3 * φ ambientInverse^3 = 1 := by
    rw [← mul_pow, ht, one_pow]
  calc
    φ ambientInverse^9 * B.det = T.det * φ ambientInverse^6 := hdet.symm
    _ = T.det * φ ambientInverse^6 *
        (φ (ambientCoordinate (some 2))^3 * φ ambientInverse^3) := by rw [h3, mul_one]
    _ = φ ambientInverse^9 * (φ (ambientCoordinate (some 2))^3 * T.det) := by ring

/-- The cubic coefficient cancels the actual positive residue factor. -/
theorem cubic_scalar_balance (φ : AmbientOverlap →+* R) (p : WeightedPoly)
    (hp : p.IsWeightedHomogeneous weight 3) :
    targetPolynomialMap φ (thirdDehomogenize p) *
        φ (ambientCoordinate (some 2))^3 =
      sourcePolynomialMap φ (firstSurfaceDehomogenize p) := by
  change φ (ambientChangeEvaluate (thirdDehomogenize p)) * _ = _
  rw [homogeneous_change p hp, map_mul, map_pow]
  have h3 : φ ambientInverse^3 * φ (ambientCoordinate (some 2))^3 = 1 := by
    rw [← mul_pow, ← map_mul, mul_comm ambientInverse, coordinate_mul_inverse,
      map_one, one_pow]
  calc
    _ = sourcePolynomialMap φ (firstSurfaceDehomogenize p) *
        (φ ambientInverse^3 * φ (ambientCoordinate (some 2))^3) := by
      change _ = φ (base (firstSurfaceDehomogenize p)) * _
      ring
    _ = _ := by rw [h3, mul_one]

#print axioms Ambient.homogeneous_change
#print axioms Ambient.jacobianFin_det
#print axioms Ambient.ambient_D_expand
#print axioms mixedJacobian_transition

end CycleQ2SurfaceFirstThirdTransition

end
