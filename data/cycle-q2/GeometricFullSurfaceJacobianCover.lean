import Proposal.GeometricSeedSurfaceGradient
import Proposal.GeometricSurfaceProjectiveCoefficients
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Full coordinate-minor cover of the three literal surface charts

SOURCE-ONLY DRAFT. No compilation or replay has been run, at the user's
request. All proposed declarations below have proof bodies; no new axiom,
admission, or global-extension hypothesis is introduced. The finite
polynomial reductions and elaboration remain to be checked in a later turn.

The old twelve normal patches need not cover D. This file instead uses
all augmented coordinate pairs on each of X1, X2, X3. The key polynomial
identity is the weighted Euler identity after the genuine shifted
dehomogenization Z = (w + X2^2)/Xi^2. Its explicit coefficient matrices
transport the original five-column Jacobian to the four chart columns.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2FullSurfaceJacobianCover

open MvPolynomial
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
open CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricSurfaceDehomogenizedCharts
open CycleQ2IncidenceEquations CycleQ2CartierSurfaceGrading
open scoped BigOperators

/-- The three projective charts are X1, X2, X3, in that order. -/
def projectiveIndex (i : Fin 3) : Fin 4 := i.succ

def variableIndex (j : Fin 4) : Option (Fin 3) := ![none, some 0, some 1, some 2] j

private theorem finSuccEquiv_eq (j : Fin 4) :
    _root_.finSuccEquiv 3 j = variableIndex j := by
  fin_cases j <;> rfl

abbrev Chart (i : Fin 3) := DehomogenizedRing 57 1 (projectiveIndex i)

def equations (i : Fin 3) : Fin 2 → SurfacePoly :=
  dehomogenizedEquations 57 1 (projectiveIndex i)

def chartGradient (i : Fin 3) (a : Fin 2) (j : Fin 4) : Chart i :=
  dehomogenizedMap 57 1 (projectiveIndex i)
    (pderiv (variableIndex j) (equations i a))

def coneGradient (i : Fin 3) (a : Fin 2) (j : Fin 5) : Chart i :=
  dehomogenizedMap 57 1 (projectiveIndex i)
    (dehomogenize (projectiveIndex i) (pderiv j (surfaceEquations 57 1 a)))

/-- Rows express the five original derivatives in the four chart derivatives.
The row deleted by dehomogenization follows from weighted Euler; the extra
2b/2c term comes from w = Z - X2^2. -/
def gradientLift (i : Fin 3) : Matrix (Fin 5) (Fin 4) SurfacePoly :=
  let z : SurfacePoly := X none
  let a : SurfacePoly := X (some 0)
  let b : SurfacePoly := X (some 1)
  let c : SurfacePoly := X (some 2)
  ![!![0, 1, 0, 0;
        -2*z, -a, -b, -c;
        2*b, 0, 1, 0;
        0, 0, 0, 1;
        1, 0, 0, 0],
    !![0, 1, 0, 0;
        0, 0, 1, 0;
        -2*(z-1), -a, -b, -c;
        0, 0, 0, 1;
        1, 0, 0, 0],
    !![0, 1, 0, 0;
        0, 0, 1, 0;
        2*c, 0, 0, 1;
        -2*z, -a, -b, -c;
        1, 0, 0, 0]] i

def equationDegree (a : Fin 2) : ℕ := ![6,3] a

/-- Explicit weighted Euler and chain-rule identity before taking the quotient.
The finite reductions use exactly the original equations at (57,1). -/
theorem gradientLift_polynomial (i : Fin 3) (a : Fin 2) (j : Fin 5) :
    dehomogenize (projectiveIndex i) (pderiv j (surfaceEquations 57 1 a)) =
      (∑ k : Fin 4, gradientLift i j k *
        pderiv (variableIndex k) (equations i a)) +
      if j = (projectiveIndex i).castSucc then
        (equationDegree a : SurfacePoly) * equations i a else 0 := by
  fin_cases i <;> fin_cases a <;> fin_cases j <;>
    simp [gradientLift, equationDegree, equations, projectiveIndex, variableIndex,
      surfaceEquations, dehomogenizedEquations, dehomogenize, linearCoordinate,
      Fin.insertNth, Fin.succAboveCases, Fin.sum_univ_succ,
      actualSeedEquation_eq_smoothF, smoothF, seedG,
      CycleQ2SegreSeed.seedG_expanded, smoothH, smoothK, smoothB, smoothA,
      thetaH, originalH, originalB, Derivation.leibniz, Pi.single_apply] <;> ring

/-- In the actual chart quotient, the equation term in Euler vanishes. -/
theorem coneGradient_eq_sum (i : Fin 3) (a : Fin 2) (j : Fin 5) :
    coneGradient i a j =
      ∑ k : Fin 4,
        dehomogenizedMap 57 1 (projectiveIndex i) (gradientLift i j k) *
          chartGradient i a k := by
  have h := congrArg (dehomogenizedMap 57 1 (projectiveIndex i))
    (gradientLift_polynomial i a j)
  simpa [coneGradient, chartGradient, equations, map_sum,
    dehomogenizedMap_equation] using h

section LinearAlgebra

variable {R : Type*} [CommRing R]

/-- Vanishing of all two-column minors is preserved by arbitrary column
linear combinations. This is the two-row Cauchy--Binet identity. -/
theorem minors_linearCombination {ι : Type*} [Fintype ι]
    (u v c d : ι → R)
    (h : ∀ a b, u a * v b - u b * v a = 0) :
    (∑ a, c a * u a) * (∑ b, d b * v b) -
      (∑ a, d a * u a) * (∑ b, c b * v b) = 0 := by
  apply sub_eq_zero.mpr
  calc
    _ = ∑ a, ∑ b, (c a * d b) * (u a * v b) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ∑ a, ∑ b, (c a * d b) * (u b * v a) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [sub_eq_zero.mp (h a b)]
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro a _
      ring

private theorem succAbove_four (i : Fin 4) (j : Fin 3) :
    i.succAbove j = (!![(1 : Fin 4), 2, 3; 0, 2, 3; 0, 1, 3; 0, 1, 2] i j) := by
  fin_cases i <;> fin_cases j <;> rfl

/-- Appending every coordinate pair to the two equation rows detects all
six ordinary Jacobian minors, with their forced determinant signs. -/
theorem minors_zero_of_augmented (v : Fin 2 → SurfacePoly)
    (φ : SurfaceChartRing v →+* R)
    (h : ∀ a b : Fin 4,
      φ (augmentedJacobian v (X (variableIndex a)) (X (variableIndex b))) = 0)
    (a b : Fin 4) :
    φ (Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (variableIndex a) (v 0))) *
        φ (Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (variableIndex b) (v 1))) -
      φ (Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (variableIndex b) (v 0))) *
        φ (Ideal.Quotient.mk (surfaceChartIdeal v) (pderiv (variableIndex a) (v 1))) = 0 := by
  have h01 := h 0 1
  have h02 := h 0 2
  have h03 := h 0 3
  have h12 := h 1 2
  have h13 := h 1 3
  have h23 := h 2 3
  simp only [augmentedJacobian_polynomial, RingHom.map_det] at h01 h02 h03 h12 h13 h23
  simp [Matrix.det_succ_row_zero, Matrix.det_fin_three, Matrix.det_fin_two,
    Matrix.submatrix_apply, Fin.sum_univ_succ, succAbove_four,
    augmentedPolynomialRows, finSuccEquiv_eq, variableIndex,
    pderiv_X, Pi.single_apply] at h01 h02 h03 h12 h13 h23
  fin_cases a <;> fin_cases b <;>
    simp only [variableIndex, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    first
    | ring
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h02
    | linear_combination -h02
    | linear_combination h03
    | linear_combination -h03
    | linear_combination h12
    | linear_combination -h12
    | linear_combination h13
    | linear_combination -h13
    | linear_combination h23
    | linear_combination -h23

end LinearAlgebra

/-- Every field-valued point of each genuine chart has a nonzero augmented
coordinate determinant. This uses the existing characteristic-zero certificate. -/
theorem field_augmented_cover (i : Fin 3) {K : Type*} [Field K]
    (φ : Chart i →+* K) :
    ∃ a b : Fin 4,
      φ (augmentedJacobian (equations i)
        (X (variableIndex a)) (X (variableIndex b))) ≠ 0 := by
  by_contra h
  push_neg at h
  have hchart : ∀ a b : Fin 4,
      φ (chartGradient i 0 a) * φ (chartGradient i 1 b) -
        φ (chartGradient i 0 b) * φ (chartGradient i 1 a) = 0 := by
    intro a b
    exact minors_zero_of_augmented (equations i) φ h a b
  have hcone : ∀ a b : Fin 5,
      φ (coneGradient i 0 a) * φ (coneGradient i 1 b) -
        φ (coneGradient i 0 b) * φ (coneGradient i 1 a) = 0 := by
    intro a b
    simp only [coneGradient_eq_sum, map_sum, map_mul]
    exact minors_linearCombination
      (fun k => φ (chartGradient i 0 k)) (fun k => φ (chartGradient i 1 k))
      (fun k => φ (dehomogenizedMap 57 1 (projectiveIndex i) (gradientLift i a k)))
      (fun k => φ (dehomogenizedMap 57 1 (projectiveIndex i) (gradientLift i b k)))
      hchart
  let Φ : WeightedPoly →+* K :=
    (φ.comp (dehomogenizedMap 57 1 (projectiveIndex i))).comp
      (dehomogenize (projectiveIndex i)).toRingHom
  have hF : Φ (actualSeedEquation 57 1) = 0 := by
    change φ (dehomogenizedMap 57 1 (projectiveIndex i)
      (dehomogenizedEquations 57 1 (projectiveIndex i) 0)) = 0
    rw [dehomogenizedMap_equation, map_zero]
  have hh : Φ (thetaH 1) = 0 := by
    change φ (dehomogenizedMap 57 1 (projectiveIndex i)
      (dehomogenizedEquations 57 1 (projectiveIndex i) 1)) = 0
    rw [dehomogenizedMap_equation, map_zero]
  have hx : ∃ j : Fin 5, Φ (X j) ≠ 0 := by
    refine ⟨(projectiveIndex i).castSucc, ?_⟩
    simp [Φ]
  obtain ⟨a,b,hu⟩ := CycleQ2SeedSurfaceGradient.actual_field_normal_cover Φ hF hh hx
  apply (isUnit_iff_ne_zero.mp hu)
  simpa only [CycleQ2SeedSurfaceGradient.actualNormalMinor, Matrix.det_fin_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, map_sub, map_mul, Φ,
    RingHom.comp_apply, coneGradient, surfaceEquations] using hcone a b

def augmentedCoordinateIdeal (i : Fin 3) : Ideal (Chart i) :=
  Ideal.span (Set.range (fun ab : Fin 4 × Fin 4 =>
    augmentedJacobian (equations i) (X (variableIndex ab.1)) (X (variableIndex ab.2))))

/-- The full coordinate determinants generate the unit ideal in each of the
actual three affine equation rings. No surface-cover assumption is used. -/
theorem augmentedCoordinateIdeal_eq_top (i : Fin 3) :
    augmentedCoordinateIdeal i = ⊤ := by
  by_contra h
  obtain ⟨M,hM,hle⟩ := Ideal.exists_le_maximal (augmentedCoordinateIdeal i) h
  letI : M.IsMaximal := hM
  obtain ⟨a,b,hab⟩ := field_augmented_cover i (Ideal.Quotient.mk M)
  apply hab
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply hle
  exact Ideal.subset_span ⟨(a,b), rfl⟩

#print axioms gradientLift_polynomial
#print axioms coneGradient_eq_sum
#print axioms field_augmented_cover
#print axioms augmentedCoordinateIdeal_eq_top

end CycleQ2FullSurfaceJacobianCover

end
