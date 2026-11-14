import Proposal.GeometricThirdSurfaceChart
import Proposal.GeometricSurfaceResidueSections
import Proposal.GeometricCrossChartResidueSections
import Proposal.GeometricSurfaceCoordinateSections

/-!
# The literal x₂/x₃ surface transition

The x₂-chart coordinates `(z,a,b,c)` pull the x₃-chart coordinates back to
`(z/c²,a/c,b/c,1/c)`. The actual ambient Jacobian determinant is `-c⁻⁶`;
the two conormal rows have factors `c⁻⁶,c⁻³`. Thus the raw determinant
residue has factor `-c³`, and projective cubic orientations `(-,+)` agree.

All statements have explicit proof bodies. This source has not been compiled;
the user requested that validation be deferred to a subsequent turn.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfaceSecondThirdTransition

open MvPolynomial Module
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2CartierSurfaceGrading CycleQ2ThirdSurfaceChart
open CycleQ2GeometricSurfaceWeightedChange (surfaceEvaluate derivation_aeval)

section Evaluation

variable {R : Type*} [CommRing R] [Algebra ℂ R]

theorem thirdEvaluate_dehomogenize (z a b c : R) (p : MvPolynomial (Fin 5) ℂ) :
    surfaceEvaluate z a b c (thirdDehomogenize p) =
      aeval ![a,b,c,1,z-c^2] p := by
  have h : (surfaceEvaluate z a b c).comp thirdDehomogenize =
      aeval ![a,b,c,1,z-c^2] := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [thirdDehomogenize_eq]
    fin_cases j <;> simp [surfaceEvaluate]
  exact AlgHom.congr_fun h p

/-- Weighted scaling before any surface equation is imposed. -/
theorem dehomogenize_scaling (z a b c t : R) (ht : c * t = 1)
    (p : MvPolynomial (Fin 5) ℂ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) :
    surfaceEvaluate (z*t^2) (a*t) (b*t) t (thirdDehomogenize p) =
      t^n * surfaceEvaluate z a b c (secondSurfaceDehomogenize p) := by
  rw [thirdEvaluate_dehomogenize,
    CycleQ2GeometricSurfaceWeightedChange.secondEvaluate_dehomogenize]
  have hv : (![a*t,b*t,t,1,z*t^2-t^2] : Fin 5 → R) =
      fun j => t ^ weight j * (![a,b,1,c,z-1] : Fin 5 → R) j := by
    funext j
    fin_cases j
    · simp [weight, mul_comm]
    · simp [weight, mul_comm]
    · simp [weight]
    · simpa [weight, mul_comm] using ht.symm
    · simp only [weight, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_succ, pow_one]
      ring
  rw [hv]
  exact weighted_homogeneous_eval_scale (algebraMap ℂ R)
    ![a,b,1,c,z-1] t p n hp

end Evaluation

section Matrix

variable {R : Type*} [CommRing R]

/-- Both axes use the original ambient order `(z,a,b,c)`. -/
def coordinateJacobian (z a b t : R) : Matrix (Fin 4) (Fin 4) R :=
  !![t^2, 0, 0, -2*z*t^3;
     0, t, 0, -a*t^2;
     0, 0, t, -b*t^2;
     0, 0, 0, -t^2]

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4),2,3; 0,2,3; 0,1,3; 0,1,2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

theorem coordinateJacobian_det (z a b t : R) :
    (coordinateJacobian z a b t).det = -t^6 := by
  simp [coordinateJacobian, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.submatrix_apply, Fin.sum_univ_succ, succAbove_four]
  ring

end Matrix

namespace Ambient

abbrev AmbientOverlap := Localization.Away (X (some (2 : Fin 3)) : SurfacePoly)

def polynomialMap : SurfacePoly →ₐ[ℂ] AmbientOverlap :=
  IsScalarTower.toAlgHom ℂ SurfacePoly AmbientOverlap

def ambientCoordinate (j : Option (Fin 3)) : AmbientOverlap := polynomialMap (X j)

def ambientInverse : AmbientOverlap :=
  IsLocalization.Away.invSelf (X (some (2 : Fin 3)) : SurfacePoly)

@[simp] theorem coordinate_mul_inverse :
    ambientCoordinate (some 2) * ambientInverse = 1 :=
  IsLocalization.Away.mul_invSelf (X (some (2 : Fin 3)) : SurfacePoly)

@[simp] theorem inverse_mul_coordinate :
    ambientInverse * ambientCoordinate (some 2) = 1 := by
  rw [mul_comm, coordinate_mul_inverse]

def ambientLastUnit : AmbientOverlapˣ :=
  Units.mkOfMulEqOne (ambientCoordinate (some 2)) ambientInverse coordinate_mul_inverse

def ambientPartial (j : Option (Fin 3)) : Derivation ℂ AmbientOverlap AmbientOverlap :=
  CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)

theorem ambientPartial_base (j : Option (Fin 3)) (p : SurfacePoly) :
    ambientPartial j (polynomialMap p) = polynomialMap (pderiv j p) := by
  change CycleQ2GeometricFunctionalDifferentials.localizedDerivation
    (Submonoid.powers (X (some (2 : Fin 3)) : SurfacePoly)) AmbientOverlap
    ((KaehlerDifferential.mvPolynomialBasis ℂ (Option (Fin 3))).coord j)
      (algebraMap SurfacePoly AmbientOverlap p) =
        algebraMap SurfacePoly AmbientOverlap (pderiv j p)
  rw [CycleQ2GeometricFunctionalDifferentials.localizedDerivation_algebraMap]
  simp only [Basis.coord_apply, KaehlerDifferential.mvPolynomialBasis_repr_apply]

theorem ambientPartial_coordinate (j k : Option (Fin 3)) :
    ambientPartial j (ambientCoordinate k) = if k = j then 1 else 0 := by
  rw [ambientCoordinate, ambientPartial_base]
  by_cases h : k = j <;> simp [pderiv_X, h]

theorem ambientPartial_inverse (j : Option (Fin 3)) :
    ambientPartial j ambientInverse =
      -(ambientInverse^2) * ambientPartial j (ambientCoordinate (some 2)) :=
  CycleQ2GeometricResidueFrames.derivation_unit_inverse (ambientPartial j) ambientLastUnit

theorem ambient_originalEvaluate (p : SurfacePoly) :
    surfaceEvaluate (ambientCoordinate none) (ambientCoordinate (some 0))
        (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) p = polynomialMap p := by
  have h : surfaceEvaluate (ambientCoordinate none) (ambientCoordinate (some 0))
      (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) = polynomialMap := by
    apply MvPolynomial.algHom_ext
    intro j
    cases j with
    | none => simp only [surfaceEvaluate, aeval_X]; rfl
    | some j => fin_cases j <;> simp only [surfaceEvaluate, aeval_X] <;> rfl
  exact AlgHom.congr_fun h p

def ambientChangeCoordinate : Option (Fin 3) → AmbientOverlap :=
  fun j => match j with
    | none => ambientCoordinate none * ambientInverse^2
    | some k => ![ambientCoordinate (some 0) * ambientInverse,
        ambientCoordinate (some 1) * ambientInverse, ambientInverse] k

def ambientChangeEvaluate : SurfacePoly →ₐ[ℂ] AmbientOverlap := aeval ambientChangeCoordinate

/-- Every weighted polynomial has its actual x₂/x₃ factor. -/
theorem homogeneous_change (p : MvPolynomial (Fin 5) ℂ) {n : ℕ}
    (hp : p.IsWeightedHomogeneous weight n) :
    ambientChangeEvaluate (thirdDehomogenize p) =
      ambientInverse^n * polynomialMap (secondSurfaceDehomogenize p) := by
  have h := dehomogenize_scaling (ambientCoordinate none) (ambientCoordinate (some 0))
    (ambientCoordinate (some 1)) (ambientCoordinate (some 2)) ambientInverse
    coordinate_mul_inverse p n hp
  rw [ambient_originalEvaluate] at h
  exact h

def ambientJacobian : Matrix (Option (Fin 3)) (Option (Fin 3)) AmbientOverlap :=
  fun j k => ambientPartial k (ambientChangeCoordinate j)

/-- The derivative of the denominator factor is kept until the defining
polynomial is sent to zero in the actual surface section ring. -/
theorem ambient_gradient_change (p : MvPolynomial (Fin 5) ℂ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n) (i : Option (Fin 3)) :
    (∑ j : Option (Fin 3), ambientChangeEvaluate (pderiv j (thirdDehomogenize p)) *
      ambientJacobian j i) =
      ambientInverse^n * polynomialMap (pderiv i (secondSurfaceDehomogenize p)) +
        polynomialMap (secondSurfaceDehomogenize p) *
          (n • ambientInverse^(n-1) * ambientPartial i ambientInverse) := by
  have h := congrArg (ambientPartial i) (homogeneous_change p hp)
  change ambientPartial i (aeval ambientChangeCoordinate (thirdDehomogenize p)) = _ at h
  rw [derivation_aeval, Derivation.leibniz, ambientPartial_base,
    Derivation.leibniz_pow] at h
  simpa only [ambientChangeEvaluate, ambientJacobian, smul_eq_mul, nsmul_eq_mul,
    mul_assoc] using h

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
    ambientJacobian none j = ambientInverse^2 * (if none = j then 1 else 0) -
      (2*ambientCoordinate none*ambientInverse^3) * (if some 2 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate none * ambientInverse^2) = _
  rw [derivative_mul_square (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some0 (j : Option (Fin 3)) :
    ambientJacobian (some 0) j = ambientInverse * (if some 0 = j then 1 else 0) -
      (ambientCoordinate (some 0)*ambientInverse^2) * (if some 2 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 0) * ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some1 (j : Option (Fin 3)) :
    ambientJacobian (some 1) j = ambientInverse * (if some 1 = j then 1 else 0) -
      (ambientCoordinate (some 1)*ambientInverse^2) * (if some 2 = j then 1 else 0) := by
  change ambientPartial j (ambientCoordinate (some 1) * ambientInverse) = _
  rw [derivative_mul_linear (ambientPartial j) _ _ _ (ambientPartial_inverse j),
    ambientPartial_coordinate, ambientPartial_coordinate]

theorem ambientJacobian_some2 (j : Option (Fin 3)) :
    ambientJacobian (some 2) j = -(ambientInverse^2) * (if some 2 = j then 1 else 0) := by
  change ambientPartial j ambientInverse = _
  rw [ambientPartial_inverse, ambientPartial_coordinate]

private theorem coordinateIndex (i : Fin 4) :
    _root_.finSuccEquiv 3 i = (![none,some 0,some 1,some 2] : Fin 4 → Option (Fin 3)) i := by
  fin_cases i <;> rfl

theorem ambientJacobian_fin :
    (fun i j : Fin 4 => ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)) =
      coordinateJacobian (ambientCoordinate none) (ambientCoordinate (some 0))
        (ambientCoordinate (some 1)) ambientInverse := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coordinateIndex, ambientJacobian_none, ambientJacobian_some0,
      ambientJacobian_some1, ambientJacobian_some2, coordinateJacobian]

theorem ambientJacobian_det : ambientJacobian.det = -ambientInverse^6 := by
  rw [← Matrix.det_reindex_self (_root_.finSuccEquiv 3).symm]
  change Matrix.det (fun i j : Fin 4 =>
    ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j)) = _
  rw [ambientJacobian_fin, coordinateJacobian_det]

/-- The genuine ambient Kähler basis, used to transport the calculation
through any actual ring-to-sheaf section map. -/
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
  rw [Basis.coord_apply, Basis.repr_self, ambientKaehlerBasis_apply,
    ambientFunctional_D, ambientPartial_coordinate]
  simp only [Finsupp.single_apply]

theorem ambient_D_expand (a : AmbientOverlap) :
    KaehlerDifferential.D ℂ AmbientOverlap a =
      ∑ j : Option (Fin 3), ambientPartial j a •
        KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j) := by
  have h := ambientKaehlerBasis.sum_repr (KaehlerDifferential.D ℂ AmbientOverlap a)
  have hc (j : Option (Fin 3)) : ambientKaehlerBasis.repr
      (KaehlerDifferential.D ℂ AmbientOverlap a) j = ambientPartial j a := by
    change ambientKaehlerBasis.coord j (KaehlerDifferential.D ℂ AmbientOverlap a) = _
    rw [ambientKaehlerBasis_coord, ambientFunctional_D]
  simpa only [hc, ambientKaehlerBasis_apply] using h.symm

theorem ambientPartial_changeEvaluate (i : Option (Fin 3)) (p : SurfacePoly) :
    ambientPartial i (ambientChangeEvaluate p) =
      ∑ j : Option (Fin 3), ambientChangeEvaluate (pderiv j p) * ambientJacobian j i := by
  change ambientPartial i (aeval ambientChangeCoordinate p) = _
  rw [derivation_aeval]
  rfl

end Ambient

section TargetRing

open Ambient

variable {R : Type*} [CommRing R] (φ : AmbientOverlap →+* R)

def sourcePolynomialMap : SurfacePoly →+* R := φ.comp polynomialMap.toRingHom

def targetPolynomialMap : SurfacePoly →+* R := φ.comp ambientChangeEvaluate.toRingHom

def targetJacobian : Matrix (Fin 4) (Fin 4) R :=
  fun i j => φ (ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j))

theorem targetJacobian_det : (targetJacobian φ).det = -(φ ambientInverse)^6 := by
  change (φ.mapMatrix (fun i j : Fin 4 =>
    ambientJacobian (_root_.finSuccEquiv 3 i) (_root_.finSuccEquiv 3 j))).det = _
  rw [← RingHom.map_det, ambientJacobian_fin, coordinateJacobian_det, map_neg, map_pow]

def pulledGradient (p : SurfacePoly) (j : Fin 4) : R :=
  φ (ambientPartial (_root_.finSuccEquiv 3 j) (ambientChangeEvaluate p))

theorem pulledGradient_eq_sum (p : SurfacePoly) (j : Fin 4) :
    pulledGradient φ p j = ∑ k : Fin 4,
      targetPolynomialMap φ (pderiv (_root_.finSuccEquiv 3 k) p) * targetJacobian φ k j := by
  rw [pulledGradient, ambientPartial_changeEvaluate, map_sum]
  symm
  change (∑ k : Fin 4,
    (fun k : Option (Fin 3) => φ (ambientChangeEvaluate (pderiv k p)) *
      φ (ambientJacobian k (_root_.finSuccEquiv 3 j))) (_root_.finSuccEquiv 3 k)) = _
  refine (Equiv.sum_comp (_root_.finSuccEquiv 3) _).trans ?_
  apply Finset.sum_congr rfl
  intro k hk
  exact (map_mul φ _ _).symm

/-- Differentiate first; only then use the original equation's zero image. -/
theorem target_gradient_change (p : MvPolynomial (Fin 5) ℂ) (n : ℕ)
    (hp : p.IsWeightedHomogeneous weight n)
    (hz : sourcePolynomialMap φ (secondSurfaceDehomogenize p) = 0) (j : Fin 4) :
    pulledGradient φ (thirdDehomogenize p) j =
      (φ ambientInverse)^n * sourcePolynomialMap φ
        (pderiv (_root_.finSuccEquiv 3 j) (secondSurfaceDehomogenize p)) := by
  have h := congrArg φ (ambient_gradient_change p n hp (_root_.finSuccEquiv 3 j))
  rw [← ambientPartial_changeEvaluate] at h
  simp only [map_add, map_mul, map_pow] at h
  change pulledGradient φ (thirdDehomogenize p) j =
    (φ ambientInverse)^n * sourcePolynomialMap φ
      (pderiv (_root_.finSuccEquiv 3 j) (secondSurfaceDehomogenize p)) +
    sourcePolynomialMap φ (secondSurfaceDehomogenize p) * _ at h
  simpa only [hz, zero_mul, add_zero] using h

variable (r θ : ℂ)

theorem source_equation_zero_of_map (ψ : SurfaceChartRing (secondEquations r θ) →+* R)
    (hψ : sourcePolynomialMap φ = ψ.comp (Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ))))
    (j : Fin 2) : sourcePolynomialMap φ (secondEquations r θ j) = 0 := by
  rw [hψ, RingHom.comp_apply]
  have hj : Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ))
      (secondEquations r θ j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j, rfl⟩)
  rw [hj, map_zero]

theorem pulledGradient_equation_zero
    (hF : sourcePolynomialMap φ (secondEquations r θ 0) = 0) (j : Fin 4) :
    pulledGradient φ (thirdEquations r θ 0) j =
      (φ ambientInverse)^6 * sourcePolynomialMap φ
        (pderiv (_root_.finSuccEquiv 3 j) (secondEquations r θ 0)) := by
  have hs : secondSurfaceDehomogenize (CycleQ2NormalConnecting.actualSeedEquation r θ) =
      secondEquations r θ 0 := by
    simp only [secondEquations, Matrix.cons_val_zero]
    exact secondSurfaceDehomogenize_equation r θ
  have ht : thirdDehomogenize (CycleQ2NormalConnecting.actualSeedEquation r θ) =
      thirdEquations r θ 0 := rfl
  have h := target_gradient_change φ (CycleQ2NormalConnecting.actualSeedEquation r θ) 6
    (actualSeedEquation_homogeneous r θ) (by simpa only [hs] using hF) j
  simpa only [hs, ht] using h

theorem pulledGradient_equation_one
    (hh : sourcePolynomialMap φ (secondEquations r θ 1) = 0) (j : Fin 4) :
    pulledGradient φ (thirdEquations r θ 1) j =
      (φ ambientInverse)^3 * sourcePolynomialMap φ
        (pderiv (_root_.finSuccEquiv 3 j) (secondEquations r θ 1)) := by
  have hs : secondSurfaceDehomogenize (CycleQ2NormalConnecting.thetaH θ) =
      secondEquations r θ 1 := by
    simp only [secondEquations, Matrix.cons_val_one, Matrix.cons_val_zero]
    exact secondSurfaceDehomogenize_h θ
  have ht : thirdDehomogenize (CycleQ2NormalConnecting.thetaH θ) =
      thirdEquations r θ 1 := rfl
  have h := target_gradient_change φ (CycleQ2NormalConnecting.thetaH θ) 3
    (thetaH_homogeneous θ) (by simpa only [hs] using hh) j
  simpa only [hs, ht] using h

def changedGradientMatrix (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) R :=
  fun i j => targetPolynomialMap φ
    (pderiv (_root_.finSuccEquiv 3 j) (augmentedPolynomialRows (thirdEquations r θ) p q i))

def mixedGradientMatrix (p q : SurfacePoly) : Matrix (Fin 4) (Fin 4) R :=
  ![(fun j => sourcePolynomialMap φ (pderiv (_root_.finSuccEquiv 3 j) (secondEquations r θ 0))),
    (fun j => sourcePolynomialMap φ (pderiv (_root_.finSuccEquiv 3 j) (secondEquations r θ 1))),
    pulledGradient φ p, pulledGradient φ q]

theorem gradientMatrix_mul
    (hF : sourcePolynomialMap φ (secondEquations r θ 0) = 0)
    (hh : sourcePolynomialMap φ (secondEquations r θ 1) = 0) (p q : SurfacePoly) :
    changedGradientMatrix φ r θ p q * targetJacobian φ =
      Matrix.diagonal ![(φ ambientInverse)^6, (φ ambientInverse)^3, 1, 1] *
        mixedGradientMatrix φ r θ p q := by
  ext i j
  rw [Matrix.diagonal_mul]
  simp only [Matrix.mul_apply, changedGradientMatrix, augmentedPolynomialRows,
    mixedGradientMatrix]
  fin_cases i <;> simp only [Matrix.cons_val_zero', Matrix.cons_val_succ']
  · exact (pulledGradient_eq_sum φ _ j).symm.trans
      (pulledGradient_equation_zero φ r θ hF j)
  · exact (pulledGradient_eq_sum φ _ j).symm.trans
      (pulledGradient_equation_one φ r θ hh j)
  · rw [one_mul]
    exact (pulledGradient_eq_sum φ _ j).symm
  · rw [one_mul]
    exact (pulledGradient_eq_sum φ _ j).symm

private theorem weightedDiagonal_det (t : R) :
    (Matrix.diagonal (![t^6,t^3,1,1] : Fin 4 → R)).det = t^9 := by
  simp [Matrix.det_diagonal, Fin.prod_univ_succ]
  ring

theorem actualJacobian_determinant_balance
    (hF : sourcePolynomialMap φ (secondEquations r θ 0) = 0)
    (hh : sourcePolynomialMap φ (secondEquations r θ 1) = 0) (p q : SurfacePoly) :
    (changedGradientMatrix φ r θ p q).det * -(φ ambientInverse)^6 =
      (φ ambientInverse)^9 * (mixedGradientMatrix φ r θ p q).det := by
  have h := congrArg Matrix.det (gradientMatrix_mul φ r θ hF hh p q)
  rw [Matrix.det_mul, targetJacobian_det, Matrix.det_mul, weightedDiagonal_det] at h
  exact h

private theorem cancel_weighted_determinant (a d c t : R) (ht : c*t=1)
    (h : a * -(t^6) = t^9 * d) : d = -(c^3) * a := by
  have hu : IsUnit t := isUnit_iff_exists_inv.mpr ⟨c, by rw [mul_comm]; exact ht⟩
  apply (hu.pow 9).mul_left_cancel
  have h3 : c^3*t^3=1 := by rw [← mul_pow, ht, one_pow]
  calc
    t^9*d = a * -(t^6) := h.symm
    _ = -(a*t^6*(c^3*t^3)) := by rw [h3, mul_one]; ring
    _ = t^9 * (-(c^3)*a) := by ring

/-- The actual transformed determinant, with the original equation
rows retained, has the raw factor `-c³`. -/
theorem mixedJacobian_transition
    (hF : sourcePolynomialMap φ (secondEquations r θ 0) = 0)
    (hh : sourcePolynomialMap φ (secondEquations r θ 1) = 0) (p q : SurfacePoly) :
    (mixedGradientMatrix φ r θ p q).det =
      -((φ (ambientCoordinate (some 2)))^3) * (changedGradientMatrix φ r θ p q).det := by
  apply cancel_weighted_determinant _ _ _ _
  · exact (map_mul φ _ _).symm.trans ((congrArg φ coordinate_mul_inverse).trans (map_one φ))
  · exact actualJacobian_determinant_balance φ r θ hF hh p q

/-- The coefficient factor cancels the raw residue factor with the
fixed second-chart minus sign and third-chart plus sign. -/
theorem cubic_scalar_balance (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3) :
    targetPolynomialMap φ (thirdDehomogenize p) *
      -((φ (ambientCoordinate (some 2)))^3) =
      -(sourcePolynomialMap φ (secondSurfaceDehomogenize p)) := by
  change φ (ambientChangeEvaluate (thirdDehomogenize p)) * _ = _
  rw [homogeneous_change p hp, map_mul, map_pow]
  have h3 : (φ ambientInverse)^3 * (φ (ambientCoordinate (some 2)))^3 = 1 := by
    rw [← mul_pow, ← map_mul, inverse_mul_coordinate, map_one, one_pow]
  calc
    _ = -(sourcePolynomialMap φ (secondSurfaceDehomogenize p)) *
        ((φ ambientInverse)^3 * (φ (ambientCoordinate (some 2)))^3) := by
      simp only [sourcePolynomialMap, RingHom.comp_apply, AlgHom.coe_toRingHom]
      ring
    _ = _ := by rw [h3, mul_one]

end TargetRing

section ActualSections

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
open CycleQ2GeometricExteriorSheaf
open CycleQ2GeometricSurfaceResidueSections CycleQ2SurfaceCommonOpen
open CycleQ2SurfaceResidueSheafOverlap CycleQ2GeometricSurfaceCoefficients
open CycleQ2CrossChartResidueSections
open Ambient

variable (r θ : ℂ) (n₂ t₂ n₃ t₃ : SurfacePoly)
  (V : (projectiveSurface r θ).Opens)
  (h₂ : V ≤ secondPatchOpen r θ n₂ t₂)
  (h₃ : V ≤ thirdPatchOpen r θ n₃ t₃)

def secondPolynomialSection : SurfacePoly →+* Γ(projectiveSurface r θ,V) :=
  (chartSection (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂))).comp
    (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂))

def thirdPolynomialSection : SurfacePoly →+* Γ(projectiveSurface r θ,V) :=
  (chartSection (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))).comp
    (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations r θ) n₃ t₃))

theorem secondPolynomialSection_equation (j : Fin 2) :
    secondPolynomialSection r θ n₂ t₂ V h₂ (secondEquations r θ j) = 0 := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _)
    (secondEquations r θ j)) = 0
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (secondEquations r θ))
    (AdjunctionPatch (secondEquations r θ) n₂ t₂)]
  have hj : algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
      (secondEquations r θ j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  rw [hj, map_zero, map_zero]

theorem secondPolynomialSection_base (p : SurfacePoly) :
    secondPolynomialSection r θ n₂ t₂ V h₂ p =
      chartSurfaceSectionMap (secondEquations r θ) n₂ t₂
        (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂))
        (Ideal.Quotient.mk (surfaceChartIdeal (secondEquations r θ)) p) := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _) p) = _
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (secondEquations r θ))
    (AdjunctionPatch (secondEquations r θ) n₂ t₂)]
  rfl

theorem thirdPolynomialSection_base (p : SurfacePoly) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ p =
      chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
        (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
        (Ideal.Quotient.mk (surfaceChartIdeal (thirdEquations r θ)) p) := by
  change chartSection _ _ (algebraMap SurfacePoly (AdjunctionPatch _ _ _) p) = _
  rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (thirdEquations r θ))
    (AdjunctionPatch (thirdEquations r θ) n₃ t₃)]
  rfl

variable (φ : AmbientOverlap →+* Γ(projectiveSurface r θ,V))
  (hsource : ∀ p : SurfacePoly, φ (polynomialMap p) =
    secondPolynomialSection r θ n₂ t₂ V h₂ p)
  (htarget : ∀ p : SurfacePoly, φ (ambientChangeEvaluate p) =
    thirdPolynomialSection r θ n₃ t₃ V h₃ p)

include hsource in
theorem ambientSectionMap_complex (c : ℂ) :
    φ (algebraMap ℂ AmbientOverlap c) =
      coefficientOn (projectiveSurface r θ).sheaf
        (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)) V c := by
  have hc : algebraMap ℂ AmbientOverlap c = polynomialMap (C c) := by
    exact (polynomialMap.commutes c).symm
  rw [hc, hsource]
  change chartSection (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂))
    (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂) (C c)) = _
  have hC : algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂) (C c) =
      algebraMap ℂ (AdjunctionPatch (secondEquations r θ) n₂ t₂) c := by
    exact (IsScalarTower.algebraMap_apply ℂ SurfacePoly
      (AdjunctionPatch (secondEquations r θ) n₂ t₂) c).symm
  rw [hC]
  exact chartSection_complex (secondPatchChart r θ n₂ t₂)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (secondPatchChart_overComplex r θ n₂ t₂) _ c

def ambientDifferentialSection : KaehlerDifferential ℂ AmbientOverlap →+
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).val.obj (op V) :=
  sectionLift (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₂ t₂ V h₂ φ hsource)

include hsource in
theorem ambientDifferentialSection_D (a : AmbientOverlap) :
    ambientDifferentialSection r θ n₂ t₂ V h₂ φ hsource
        (KaehlerDifferential.D ℂ AmbientOverlap a) =
      (universalDifferential (projectiveSurface r θ).sheaf
        (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
        (X := op V) (φ a) :=
  sectionLift_D (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₂ t₂ V h₂ φ hsource) a

include hsource in
theorem ambientDifferentialSection_smul (a : AmbientOverlap)
    (ω : KaehlerDifferential ℂ AmbientOverlap) :
    ambientDifferentialSection r θ n₂ t₂ V h₂ φ hsource (a • ω) =
      φ a • ambientDifferentialSection r θ n₂ t₂ V h₂ φ hsource ω :=
  sectionLift_smul (projectiveSurface r θ).sheaf
    (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))
    (differentialSheaf (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    (universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)))
    V φ (ambientSectionMap_complex r θ n₂ t₂ V h₂ φ hsource) a ω

include hsource htarget in
theorem thirdPolynomialDifferential_expansion (p : SurfacePoly) :
    polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (Over.mk (homOfLE h₃)) p =
      chartAmbientDifferential
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (secondEquations r θ) n₂ t₂ (secondPatchChart r θ n₂ t₂)
        (Over.mk (homOfLE h₂)) (pulledGradient φ p) := by
  let L := ambientDifferentialSection r θ n₂ t₂ V h₂ φ hsource
  have hsourceD (j : Option (Fin 3)) :
      L (KaehlerDifferential.D ℂ AmbientOverlap (ambientCoordinate j)) =
        polynomialDifferentialSection_common
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (secondEquations r θ) n₂ t₂ (secondPatchChart r θ n₂ t₂)
          (Over.mk (homOfLE h₂)) (X j) := by
    rw [ambientDifferentialSection_D]
    apply congrArg ((universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
      (X := op V))
    exact hsource (X j)
  have htargetD : L (KaehlerDifferential.D ℂ AmbientOverlap (ambientChangeEvaluate p)) =
      polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (Over.mk (homOfLE h₃)) p := by
    rw [ambientDifferentialSection_D]
    apply congrArg ((universalDifferential (projectiveSurface r θ).sheaf
      (schemeCoefficient (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ))).d
      (X := op V))
    exact htarget p
  rw [← htargetD, ambient_D_expand, map_sum]
  simp only [L, ambientDifferentialSection_smul, hsourceD]
  symm
  exact Equiv.sum_comp (_root_.finSuccEquiv 3)
    (fun j : Option (Fin 3) => φ (ambientPartial j (ambientChangeEvaluate p)) •
      polynomialDifferentialSection_common
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (secondEquations r θ) n₂ t₂ (secondPatchChart r θ n₂ t₂)
        (Over.mk (homOfLE h₂)) (X j))

include hsource htarget in
theorem actual_mixed_determinant (p q : SurfacePoly) :
    Matrix.det ![
      chartEquationGradient (secondEquations r θ) n₂ t₂
        (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂)) 0,
      chartEquationGradient (secondEquations r θ) n₂ t₂
        (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂)) 1,
      pulledGradient φ p, pulledGradient φ q] =
      -((φ (ambientCoordinate (some 2)))^3) *
        chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
          (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
          (augmentedJacobian (thirdEquations r θ) p q) := by
  have hF : sourcePolynomialMap φ (secondEquations r θ 0) = 0 :=
    (hsource _).trans (secondPolynomialSection_equation r θ n₂ t₂ V h₂ 0)
  have hh : sourcePolynomialMap φ (secondEquations r θ 1) = 0 :=
    (hsource _).trans (secondPolynomialSection_equation r θ n₂ t₂ V h₂ 1)
  have hleft : ![
      chartEquationGradient (secondEquations r θ) n₂ t₂
        (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂)) 0,
      chartEquationGradient (secondEquations r θ) n₂ t₂
        (secondPatchChart r θ n₂ t₂) (Over.mk (homOfLE h₂)) 1,
      pulledGradient φ p, pulledGradient φ q] = mixedGradientMatrix φ r θ p q := by
    ext i j
    fin_cases i <;> simp only [mixedGradientMatrix, Matrix.cons_val_zero', Matrix.cons_val_succ']
    · exact ((hsource _).trans (secondPolynomialSection_base r θ n₂ t₂ V h₂ _)).symm
    · exact ((hsource _).trans (secondPolynomialSection_base r θ n₂ t₂ V h₂ _)).symm
    · rfl
    · rfl
  have hright : (changedGradientMatrix φ r θ p q).det =
      chartSurfaceSectionMap (thirdEquations r θ) n₃ t₃
        (thirdPatchChart r θ n₃ t₃) (Over.mk (homOfLE h₃))
        (augmentedJacobian (thirdEquations r θ) p q) := by
    rw [augmentedJacobian_polynomial, RingHom.map_det]
    congr 1
    ext i j
    exact (htarget _).trans (thirdPolynomialSection_base r θ n₃ t₃ V h₃ _)
  rw [hleft, mixedJacobian_transition φ r θ hF hh p q, hright]

/-- The determinant calculation is now an equality of the genuine
exterior-sheaf sections on the actual projective overlap. -/
include hsource htarget in
theorem residueSheafSection_transition_of_maps :
    chartResidueSheafSection
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (thirdPatchChart_overComplex r θ n₃ t₃) (Over.mk (homOfLE h₃)) =
      -((φ (ambientCoordinate (some 2)))^3) •
        chartResidueSheafSection
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (secondEquations r θ) n₂ t₂ (secondPatchChart r θ n₂ t₂)
          (secondPatchChart_overComplex r θ n₂ t₂) (Over.mk (homOfLE h₂)) :=
  CycleQ2CrossChartResidueSections.residueSheafSection_transition
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
    (secondEquations r θ) (thirdEquations r θ) n₂ t₂ n₃ t₃
    (secondPatchChart r θ n₂ t₂) (thirdPatchChart r θ n₃ t₃)
    (secondPatchChart_overComplex r θ n₂ t₂) (thirdPatchChart_overComplex r θ n₃ t₃)
    V h₂ h₃ (pulledGradient φ) (-((φ (ambientCoordinate (some 2)))^3))
    (thirdPolynomialDifferential_expansion r θ n₂ t₂ n₃ t₃ V h₂ h₃ φ hsource htarget)
    (actual_mixed_determinant r θ n₂ t₂ n₃ t₃ V h₂ h₃ φ hsource htarget)

include hsource htarget in
theorem orientedCubicSections_agree_of_maps (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3) :
    secondCubicSection r θ n₂ t₂ p (Over.mk (homOfLE h₂)) =
      thirdCubicSection r θ n₃ t₃ p (Over.mk (homOfLE h₃)) := by
  have hcoeff : thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) *
      -((φ (ambientCoordinate (some 2)))^3) =
      -(secondPolynomialSection r θ n₂ t₂ V h₂ (secondSurfaceDehomogenize p)) := by
    rw [← htarget, ← hsource]
    exact cubic_scalar_balance φ p hp
  unfold secondCubicSection thirdCubicSection
  rw [residueSheafSection_transition_of_maps r θ n₂ t₂ n₃ t₃ V h₂ h₃ φ hsource htarget,
    ← mul_smul]
  change -(secondPolynomialSection r θ n₂ t₂ V h₂ (secondSurfaceDehomogenize p) • _) =
    (thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) * _) • _
  rw [hcoeff, neg_smul]

end ActualSections

section LiteralMapBinding

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2GeometricAffineChartSections
open CycleQ2GeometricSurfaceJacobianCharts CycleQ2GeometricPrincipalChartSections
open CycleQ2SurfaceCommonOpen CycleQ2SurfaceResidueSheafOverlap
open CycleQ2SurfaceCoordinateSections CycleQ2SeedTrace
open Ambient

variable (r θ : ℂ) (n₂ t₂ n₃ t₃ : SurfacePoly)
  (V : (projectiveSurface r θ).Opens)
  (h₂ : V ≤ secondPatchOpen r θ n₂ t₂)
  (h₃ : V ≤ thirdPatchOpen r θ n₃ t₃)

/-- An arbitrary augmented patch uses the unchanged second chart's
actual homogeneous coefficient sections. -/
theorem secondPolynomialSection_homogeneous (n : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight n) :
    secondPolynomialSection r θ n₂ t₂ V h₂ (secondSurfaceDehomogenize p) =
      coordinatePolynomialSection r θ 2 V (h₂.trans (secondPatchOpen_le r θ n₂ t₂)) p := by
  calc
    _ = chartSection (secondAffineChart r θ)
        (Over.mk (homOfLE (h₂.trans (secondPatchOpen_le r θ n₂ t₂))))
        (algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
          (secondSurfaceDehomogenize p)) := by
      change chartSection
        (principalChart (secondAffineChart r θ) (augmentedJacobian (secondEquations r θ) n₂ t₂))
        (Over.mk (homOfLE h₂))
        (algebraMap SurfacePoly (AdjunctionPatch (secondEquations r θ) n₂ t₂)
          (secondSurfaceDehomogenize p)) = _
      rw [IsScalarTower.algebraMap_apply SurfacePoly (SurfaceChartRing (secondEquations r θ))
        (AdjunctionPatch (secondEquations r θ) n₂ t₂)]
      simpa only [Over.mk_hom, homOfLE_comp] using
        (principal_chartSection (secondAffineChart r θ)
          (augmentedJacobian (secondEquations r θ) n₂ t₂) (Over.mk (homOfLE h₂))
          (algebraMap SurfacePoly (SurfaceChartRing (secondEquations r θ))
            (secondSurfaceDehomogenize p)))
    _ = _ := second_chart_polynomial_section r θ V
      (h₂.trans (secondPatchOpen_le r θ n₂ t₂)) n p hp

/-- On the third chart the generic coordinate map is the literal map. -/
theorem thirdPolynomialSection_weighted (p : MvPolynomial (Fin 5) ℂ) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) =
      coordinatePolynomialSection r θ 3 V (h₃.trans (thirdPatchOpen_le r θ n₃ t₃)) p := by
  calc
    _ = chartSection (thirdAffineChart r θ)
        (Over.mk (homOfLE (h₃.trans (thirdPatchOpen_le r θ n₃ t₃))))
        (algebraMap SurfacePoly (ThirdChartRing r θ) (thirdDehomogenize p)) := by
      change chartSection
        (principalChart (thirdAffineChart r θ) (augmentedJacobian (thirdEquations r θ) n₃ t₃))
        (Over.mk (homOfLE h₃))
        (algebraMap SurfacePoly (AdjunctionPatch (thirdEquations r θ) n₃ t₃)
          (thirdDehomogenize p)) = _
      rw [IsScalarTower.algebraMap_apply SurfacePoly (ThirdChartRing r θ)
        (AdjunctionPatch (thirdEquations r θ) n₃ t₃)]
      simpa only [Over.mk_hom, homOfLE_comp] using
        (principal_chartSection (thirdAffineChart r θ)
          (augmentedJacobian (thirdEquations r θ) n₃ t₃) (Over.mk (homOfLE h₃))
          (algebraMap SurfacePoly (ThirdChartRing r θ) (thirdDehomogenize p)))
    _ = _ := rfl

/-- The inverse ratio and every coefficient are actual structure-sheaf
sections; this is the projective weighted identity on the given open. -/
theorem homogeneous_section_change (n : ℕ) (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight n) :
    thirdPolynomialSection r θ n₃ t₃ V h₃ (thirdDehomogenize p) =
      (thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 2)))^n *
        secondPolynomialSection r θ n₂ t₂ V h₂ (secondSurfaceDehomogenize p) := by
  have h := coordinatePolynomialSection_change r θ 2 3 V
    (h₂.trans (secondPatchOpen_le r θ n₂ t₂))
    (h₃.trans (thirdPatchOpen_le r θ n₃ t₃)) n p hp
  rw [← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ p,
    ← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ (X (2 : Fin 5)),
    ← secondPolynomialSection_homogeneous r θ n₂ t₂ V h₂ n p hp] at h
  simpa only [thirdDehomogenize_eq, aeval_X, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_succ] using h

theorem literal_ratio_inverse :
    secondPolynomialSection r θ n₂ t₂ V h₂ (X (some 2)) *
      thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 2)) = 1 := by
  have hX : (X (3 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
    simpa only [weight_castSucc] using
      isWeightedHomogeneous_X ℂ weight (3 : Fin 4).castSucc
  have h := coordinateRatio_inverse r θ 2 3 V
    (h₂.trans (secondPatchOpen_le r θ n₂ t₂))
    (h₃.trans (thirdPatchOpen_le r θ n₃ t₃))
  rw [← secondPolynomialSection_homogeneous r θ n₂ t₂ V h₂ 1 (X (3 : Fin 5)) hX,
    ← thirdPolynomialSection_weighted r θ n₃ t₃ V h₃ (X (2 : Fin 5))] at h
  simpa only [secondSurfaceDehomogenize, thirdDehomogenize_eq, aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using h

theorem source_last_isUnit :
    IsUnit (secondPolynomialSection r θ n₂ t₂ V h₂ (X (some 2))) :=
  isUnit_iff_exists_inv.mpr ⟨thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 2)),
    literal_ratio_inverse r θ n₂ t₂ n₃ t₃ V h₂ h₃⟩

/-- The actual ambient map into the common section ring. Its inverse
coordinate is justified by the actual projective ratio identity. -/
def literalAmbientSectionMap : AmbientOverlap →+* Γ(projectiveSurface r θ,V) :=
  Localization.awayLift (secondPolynomialSection r θ n₂ t₂ V h₂)
    (X (some (2 : Fin 3))) (source_last_isUnit r θ n₂ t₂ n₃ t₃ V h₂ h₃)

theorem literalAmbientSectionMap_source (p : SurfacePoly) :
    literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃ (polynomialMap p) =
      secondPolynomialSection r θ n₂ t₂ V h₂ p :=
  IsLocalization.Away.lift_eq _ (source_last_isUnit r θ n₂ t₂ n₃ t₃ V h₂ h₃) p

theorem literalAmbientSectionMap_inverse :
    literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃ ambientInverse =
      thirdPolynomialSection r θ n₃ t₃ V h₃ (X (some 2)) := by
  apply (source_last_isUnit r θ n₂ t₂ n₃ t₃ V h₂ h₃).mul_left_cancel
  have h := congrArg (literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃)
    coordinate_mul_inverse
  rw [map_mul, ambientCoordinate, literalAmbientSectionMap_source, map_one] at h
  exact h.trans (literal_ratio_inverse r θ n₂ t₂ n₃ t₃ V h₂ h₃).symm

/-- The ambient substitution agrees with the actual third chart on
every polynomial, proved from the four homogeneous coordinate sections. -/
theorem literalAmbientSectionMap_target (p : SurfacePoly) :
    literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃ (ambientChangeEvaluate p) =
      thirdPolynomialSection r θ n₃ t₃ V h₃ p := by
  have hmaps :
      (literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃).comp ambientChangeEvaluate.toRingHom =
        thirdPolynomialSection r θ n₃ t₃ V h₃ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have h := homogeneous_section_change r θ n₂ t₂ n₃ t₃ V h₂ h₃
        0 (C c) (isWeightedHomogeneous_C weight c)
      have hC : ambientChangeEvaluate (C c) = polynomialMap (C c) := by simp
      change literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃
        (ambientChangeEvaluate (C c)) = _
      rw [hC, literalAmbientSectionMap_source]
      simpa only [thirdDehomogenize, dehomogenize, secondSurfaceDehomogenize,
        aeval_C, pow_zero, one_mul] using h.symm
    · intro j
      change literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃
        (ambientChangeEvaluate (X j)) = _
      cases j with
      | none =>
          have h := homogeneous_section_change r θ n₂ t₂ n₃ t₃ V h₂ h₃
            2 originalF2 originalF2_homogeneous
          have hthird : thirdDehomogenize originalF2 = X none := dehomogenize_f2 3
          rw [hthird, secondSurfaceDehomogenize_f2] at h
          simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
            map_mul, map_pow, literalAmbientSectionMap_inverse, ambientCoordinate,
            literalAmbientSectionMap_source]
          exact (mul_comm _ _).trans h.symm
      | some j =>
          fin_cases j
          · have hX : (X (0 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
              simpa only [weight_castSucc] using
                isWeightedHomogeneous_X ℂ weight (0 : Fin 4).castSucc
            have h := homogeneous_section_change r θ n₂ t₂ n₃ t₃ V h₂ h₃ 1 (X (0 : Fin 5)) hX
            simp only [thirdDehomogenize_eq, secondSurfaceDehomogenize, aeval_X,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, pow_one] at h
            simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, map_mul, literalAmbientSectionMap_inverse, ambientCoordinate,
              literalAmbientSectionMap_source]
            exact (mul_comm _ _).trans h.symm
          · have hX : (X (1 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous weight 1 := by
              simpa only [weight_castSucc] using
                isWeightedHomogeneous_X ℂ weight (1 : Fin 4).castSucc
            have h := homogeneous_section_change r θ n₂ t₂ n₃ t₃ V h₂ h₃ 1 (X (1 : Fin 5)) hX
            simp only [thirdDehomogenize_eq, secondSurfaceDehomogenize, aeval_X,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ, pow_one] at h
            simp only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, Matrix.cons_val_one, map_mul, literalAmbientSectionMap_inverse,
              ambientCoordinate, literalAmbientSectionMap_source]
            exact (mul_comm _ _).trans h.symm
          · simpa only [ambientChangeEvaluate, aeval_X, ambientChangeCoordinate,
              Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_succ] using
              literalAmbientSectionMap_inverse r θ n₂ t₂ n₃ t₃ V h₂ h₃
  exact RingHom.congr_fun hmaps p

/-- The raw determinant frame comparison on every actual common subopen.
This coefficient formula is independent of any cubic and therefore also
compares arbitrary local coefficients in the canonical line bundle. -/
theorem literal_residueSheafSection_transition :
    CycleQ2GeometricExteriorSheaf.chartResidueSheafSection
        (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
        (thirdEquations r θ) n₃ t₃ (thirdPatchChart r θ n₃ t₃)
        (thirdPatchChart_overComplex r θ n₃ t₃) (Over.mk (homOfLE h₃)) =
      -((secondPolynomialSection r θ n₂ t₂ V h₂ (X (some 2)))^3) •
        CycleQ2GeometricExteriorSheaf.chartResidueSheafSection
          (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex r θ)
          (secondEquations r θ) n₂ t₂ (secondPatchChart r θ n₂ t₂)
          (secondPatchChart_overComplex r θ n₂ t₂) (Over.mk (homOfLE h₂)) := by
  have h := residueSheafSection_transition_of_maps r θ n₂ t₂ n₃ t₃ V h₂ h₃
    (literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃)
    (literalAmbientSectionMap_source r θ n₂ t₂ n₃ t₃ V h₂ h₃)
    (literalAmbientSectionMap_target r θ n₂ t₂ n₃ t₃ V h₂ h₃)
  simpa only [ambientCoordinate, literalAmbientSectionMap_source] using h

/-- Closed signed cubic compatibility on every actual common subopen.
There is no supplied extension or residue compatibility premise. -/
theorem orientedCubicSections_agree_on_open (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3) :
    secondCubicSection r θ n₂ t₂ p (Over.mk (homOfLE h₂)) =
      thirdCubicSection r θ n₃ t₃ p (Over.mk (homOfLE h₃)) :=
  orientedCubicSections_agree_of_maps r θ n₂ t₂ n₃ t₃ V h₂ h₃
    (literalAmbientSectionMap r θ n₂ t₂ n₃ t₃ V h₂ h₃)
    (literalAmbientSectionMap_source r θ n₂ t₂ n₃ t₃ V h₂ h₃)
    (literalAmbientSectionMap_target r θ n₂ t₂ n₃ t₃ V h₂ h₃) p hp

end LiteralMapBinding

section OverCompatibility

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2CartierProjectiveCover CycleQ2SurfaceCommonOpen
open CycleQ2SurfaceResidueSheafOverlap

variable (r θ : ℂ) (n₂ t₂ n₃ t₃ : SurfacePoly)

def secondCommonSubopen (V : Over (secondPatchOpen r θ n₂ t₂ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    Over (secondPatchOpen r θ n₂ t₂) :=
  Over.mk (V.hom ≫ homOfLE inf_le_left)

def thirdCommonSubopen (V : Over (secondPatchOpen r θ n₂ t₂ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    Over (thirdPatchOpen r θ n₃ t₃) :=
  Over.mk (V.hom ≫ homOfLE inf_le_right)

/-- The exact overlap API consumed by global cubic gluing. The second
chart carries the existing minus orientation and the third the plus orientation. -/
theorem orientedCubicSections_agree (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous weight 3)
    (V : Over (secondPatchOpen r θ n₂ t₂ ⊓ thirdPatchOpen r θ n₃ t₃)) :
    secondCubicSection r θ n₂ t₂ p (secondCommonSubopen r θ n₂ t₂ n₃ t₃ V) =
      thirdCubicSection r θ n₃ t₃ p (thirdCommonSubopen r θ n₂ t₂ n₃ t₃ V) := by
  simpa only [secondCommonSubopen, thirdCommonSubopen, homOfLE_comp] using
    orientedCubicSections_agree_on_open r θ n₂ t₂ n₃ t₃ V.left
      ((leOfHom V.hom).trans inf_le_left) ((leOfHom V.hom).trans inf_le_right) p hp

#print axioms orientedCubicSections_agree

end OverCompatibility

end CycleQ2SurfaceSecondThirdTransition

end
