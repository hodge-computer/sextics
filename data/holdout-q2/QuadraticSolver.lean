import HodgeComputer.Constructions.CubicSurfaces.LineContact
import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootSpecialization
import HodgeComputer.Constructions.FiniteAlgebra.PolynomialMatrixMap
import HodgeComputer.Constructions.FiniteAlgebra.MatrixHomogeneous
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.LinearCombination

/-! Arbitrary quadratic sources on the holdout cubic, using four constant
coordinate fields and six coefficient functionals on a degree-27 line algebra.
The determinant and adjugate descent are reused from the accepted proof. -/
noncomputable section
open scoped BigOperators Matrix
set_option maxHeartbeats 2000000
namespace HoldoutQ2.QuadraticSolver
open MvPolynomial HodgeTestbed HodgeComputer.CubicSurfaces.LineContact QuadricContact

variable {K E : Type*} [CommRing K] [IsDomain K] [CommRing E] [Algebra K E]
abbrev Poly := MvPolynomial (Fin 4) K
abbrev Rep := E →ₐ[K] Matrix (Fin 27) (Fin 27) K

def matrixPole (ρ : Rep (K := K) (E := E)) (e f : E) :
    Matrix (Fin 27) (Fin 27) (Poly (K := K)) :=
  polynomialMatrixMap ρ.toRingHom (pole e f)

def matrixNumerator (ρ : Rep (K := K) (E := E)) (d : K) (e f g h : E) :
    Fin 4 → Matrix (Fin 27) (Fin 27) (Poly (K := K)) :=
  fun i => polynomialMatrixMap ρ.toRingHom (numerator (algebraMap K E d) e f g h i)

def denominator (ρ : Rep (K := K) (E := E)) (e f : E) : Poly (K := K) :=
  (matrixPole ρ e f).det

def contactNumerators (ρ : Rep (K := K) (E := E)) (d : K) (e f g h : E)
    (weights : Fin 27 → K) : Fin 4 → Poly (K := K) := fun i =>
  columnFunctional (fun j => C (weights j)) 0
    (matrixNumerator ρ d e f g h i * (matrixPole ρ e f).adjugate)

def coefficientFunctional (ρ : Rep (K := K) (E := E)) (weights : Fin 27 → K)
    (z : E) : K := ∑ j, weights j * ρ z j 0

def contactSource (ρ : Rep (K := K) (E := E)) (d : K) (e f g h : E)
    (weights : Fin 27 → K) : Poly (K := K) :=
  ∑ j : Fin 10,
    C (coefficientFunctional ρ weights (sourceCoefficients (algebraMap K E d) e f g h j)) *
      quadraticMonomials j

theorem denominator_ne_zero (ρ : Rep (K := K) (E := E)) (e f : E) :
    denominator ρ e f ≠ 0 := by
  apply determinant_ne_zero_of_map_eq_one (matrixPole ρ e f)
    (MvPolynomial.eval (fun i : Fin 4 => if i = 2 then (1 : K) else 0))
  ext a b
  simp [matrixPole, pole, polynomialMatrixMap_X, polynomialMatrixMap_C,
    Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply,
    smul_eq_mul, map_sub, map_mul, map_sum]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem denominator_eval₂ {R : Type*} [CommRing R]
    (ρ : Rep (K := K) (E := E)) (e f : E) (φ : K →+* R) (v : Fin 4 → R) :
    MvPolynomial.eval₂Hom φ v (denominator ρ e f) =
      (v 2 • (1 : Matrix (Fin 27) (Fin 27) R) -
        v 0 • (ρ e).map φ - v 1 • (ρ f).map φ).det := by
  unfold denominator
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [matrixPole, pole, polynomialMatrixMap_X, polynomialMatrixMap_C,
    Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.mul_smul,
    Matrix.mul_one, smul_eq_mul, map_ofNat]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem denominator_norm_fiber {R : Type*} [CommRing R]
    (ρ : Rep (K := K) (E := E)) (e f : E) (φ : K →+* R) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp φ)
      ![1, 1, Polynomial.X, 0] (denominator ρ e f) =
      ((Polynomial.X : Polynomial R) • (1 : Matrix (Fin 27) (Fin 27) (Polynomial R)) -
        ((ρ (e+f)).map φ).map (Polynomial.C : R →+* Polynomial R)).det := by
  rw [denominator_eval₂]
  congr 1
  ext a b : 2
  simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
    RingHom.comp_apply, map_add, sub_sub]

theorem map_cubic (a b c d : K) :
    MvPolynomial.map (algebraMap K E) (cubic a b c d) =
      cubic (algebraMap K E a) (algebraMap K E b)
        (algebraMap K E c) (algebraMap K E d) := by
  simp [cubic, map_ofNat]

theorem columnFunctional_constant (ρ : Rep (K := K) (E := E))
    (weights : Fin 27 → K) (z : E) :
    columnFunctional (fun j => (C (weights j) : Poly (K := K))) 0 ((ρ z).map C) =
      C (coefficientFunctional ρ weights z) := by
  simp only [columnFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    coefficientFunctional, Matrix.map_apply, map_sum, map_mul]

theorem source_target (ρ : Rep (K := K) (E := E)) (d : K) (e f g h : E)
    (weights : Fin 27 → K) :
    columnFunctional (fun j => C (weights j)) 0
      (polynomialMatrixMap ρ.toRingHom (source (algebraMap K E d) e f g h)) =
      contactSource ρ d e f g h weights := by
  have hm (i : Fin 10) : polynomialMatrixMap ρ.toRingHom
      (quadraticMonomials (R := E) i) =
      quadraticMonomials (R := K) i • (1 : Matrix (Fin 27) (Fin 27) (Poly (K := K))) := by
    have hmap : MvPolynomial.map (algebraMap K E) (quadraticMonomials (R := K) i) =
        quadraticMonomials (R := E) i := by
      fin_cases i <;> simp [quadraticMonomials]
    rw [← hmap, polynomialMatrixMap_base]
  rw [source_expansion, map_sum]
  simp_rw [map_mul, polynomialMatrixMap_C, hm, Matrix.mul_smul, Matrix.mul_one]
  simp only [map_sum, map_smul, smul_eq_mul, columnFunctional_constant, contactSource]
  apply Finset.sum_congr rfl
  intro i _
  change quadraticMonomials i *
    columnFunctional (fun j => (C (weights j) : Poly (K := K))) 0
      ((ρ (sourceCoefficients (algebraMap K E d) e f g h i)).map C) = _
  rw [columnFunctional_constant]
  ring

theorem contact_equations (ρ : Rep (K := K) (E := E)) (a b c d : K) (e f g h : E)
    (weights : Fin 27 → K)
    (h0 : rel0 (algebraMap K E a) e g = 0)
    (h1 : rel1 (algebraMap K E c) e f g h = 0)
    (h2 : rel2 (algebraMap K E d) e f g h = 0)
    (h3 : rel3 (algebraMap K E b) (algebraMap K E d) f h = 0) :
    Equations (cubic a b c d) (contactSource ρ d e f g h weights)
      (denominator ρ e f) (contactNumerators ρ d e f g h weights) 0 := by
  let L := matrixPole ρ e f
  let U := matrixNumerator ρ d e f g h
  let J := polynomialMatrixMap ρ.toRingHom (source (algebraMap K E d) e f g h)
  have hdiv : (∑ i, matrixDeriv (pderiv i) (U i)) = 0 := by
    apply polynomialMatrixMap_divergence ρ.toRingHom
    exact numerator_divergence _ _ _ _ _
  have htan : (∑ i, U i * matrixDeriv (pderiv i) L) = 0 := by
    apply polynomialMatrixMap_tangency ρ.toRingHom
    simpa only [directional, mul_comm] using
      numerator_tangency (algebraMap K E d) e f g h
  have hsource : (∑ i, pderiv i (cubic a b c d) • U i) = J * L := by
    apply polynomialMatrixMap_source ρ
    rw [map_cubic]
    have hs := source_with_residual (algebraMap K E a) (algebraMap K E b)
      (algebraMap K E c) (algebraMap K E d) e f g h
    rw [h0, h1, h2, h3] at hs
    simpa only [directional, map_zero, mul_zero, zero_mul, add_zero, sub_zero,
      mul_comm] using hs
  have hcomm (i : Fin 4) : U i * L.adjugate = L.adjugate * U i := by
    apply commute_adjugate_of_regular_det
    · exact (IsRegular.of_ne_zero (denominator_ne_zero ρ e f)).left
    · exact polynomialMatrixMap_commute ρ.toRingHom _ _
  have hh := pderiv_contact_column L J U weights 0 (cubic a b c d)
    (contactSource ρ d e f g h weights) hcomm hdiv htan hsource (source_target ρ d e f g h weights)
  apply strict_to_equations
  · simpa only [directional, contactNumerators, denominator, L, U, mul_comm] using hh.1
  · unfold divergenceNumerator divergence directional
    have hh2 := hh.2
    change denominator ρ e f * (∑ i, pderiv i (contactNumerators ρ d e f g h weights i)) =
      ∑ i, contactNumerators ρ d e f g h weights i * pderiv i (denominator ρ e f) at hh2
    rw [hh2]
    simp only [mul_comm, sub_self]

theorem matrixPole_homogeneous (ρ : Rep (K := K) (E := E)) (e f : E) (i j : Fin 27) :
    (matrixPole ρ e f i j).IsHomogeneous 1 :=
  polynomialMatrixMap_homogeneous ρ (pole e f) 1 (pole_homogeneous e f) i j

theorem matrixNumerator_homogeneous (ρ : Rep (K := K) (E := E)) (d : K)
    (e f g h : E) (i : Fin 4) (j k : Fin 27) :
    (matrixNumerator ρ d e f g h i j k).IsHomogeneous 1 :=
  polynomialMatrixMap_homogeneous ρ (numerator (algebraMap K E d) e f g h i) 1
    (numerator_homogeneous _ _ _ _ _ i) j k

theorem denominator_homogeneous (ρ : Rep (K := K) (E := E)) (e f : E) :
    (denominator ρ e f).IsHomogeneous 27 := by
  simpa [denominator] using determinant_homogeneous (matrixPole ρ e f) 1
    (matrixPole_homogeneous ρ e f)

theorem contactNumerators_homogeneous (ρ : Rep (K := K) (E := E)) (d : K)
    (e f g h : E) (weights : Fin 27 → K) (i : Fin 4) :
    (contactNumerators ρ d e f g h weights i).IsHomogeneous 27 := by
  have hh := column_contact_numerator_homogeneous (matrixPole ρ e f)
    (matrixNumerator ρ d e f g h i) weights 0 1
    (matrixPole_homogeneous ρ e f) (matrixNumerator_homogeneous ρ d e f g h i)
  simpa only [contactNumerators, columnFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Fintype.card_fin, Nat.mul_one] using hh

/-- Ten columns: four coordinate fields, then the first six power-basis functionals. -/
def sourceMinor (basis : Module.Basis (Fin 27) K E) (a b c d : K) (e f g h : E) :
    Matrix (Fin 10) (Fin 10) K := fun i =>
  Fin.addCases (motive := fun _ => K)
    (fun j : Fin 4 => gradientCoefficients a b c d i j)
    (fun j : Fin 6 => basis.repr (sourceCoefficients (algebraMap K E d) e f g h i)
      (Fin.castAdd 21 j))

theorem sourceMinor_map {S : Type*} [CommRing S] [IsDomain S] (φ : K →+* S)
    (p : Polynomial K) (hp : p.Monic) (hn : p.natDegree = 27)
    (hm : (p.map φ).natDegree = 27) (a b c d : K) (e f g h : AdjoinRoot p) :
    (sourceMinor (AdjoinRootSpecialization.basis p hp hn) a b c d e f g h).map φ =
      sourceMinor (AdjoinRootSpecialization.basis (p.map φ) (hp.map φ) hm)
        (φ a) (φ b) (φ c) (φ d)
        (AdjoinRootSpecialization.specialize φ p e) (AdjoinRootSpecialization.specialize φ p f)
        (AdjoinRootSpecialization.specialize φ p g) (AdjoinRootSpecialization.specialize φ p h) := by
  ext i j
  cases j using Fin.addCases (m := 4) (n := 6) with
  | left j =>
    simp only [Matrix.map_apply, sourceMinor, Fin.addCases_left]
    exact gradientCoefficients_map φ a b c d i j
  | right j =>
    simp only [Matrix.map_apply, sourceMinor, Fin.addCases_right,
      AdjoinRootSpecialization.basis_repr]
    rw [AdjoinRootSpecialization.map_coordinate]
    congr 2
    rw [sourceCoefficients_map]
    simp [AdjoinRoot.algebraMap_eq]

/-- Same specialization lemma, allowing a separately named target polynomial. -/
theorem sourceMinor_map_named {S : Type*} [CommRing S] [IsDomain S] (φ : K →+* S)
    (p : Polynomial K) (hp : p.Monic) (hn : p.natDegree = 27)
    (q : Polynomial S) (hq : q = p.map φ) (hqm : q.Monic) (hqn : q.natDegree = 27)
    (hdiv : q ∣ p.map φ) (a b c d : K) (e f g h : AdjoinRoot p) :
    (sourceMinor (AdjoinRootSpecialization.basis p hp hn) a b c d e f g h).map φ =
      sourceMinor (AdjoinRootSpecialization.basis q hqm hqn)
        (φ a) (φ b) (φ c) (φ d)
        (AdjoinRoot.map φ p q hdiv e) (AdjoinRoot.map φ p q hdiv f)
        (AdjoinRoot.map φ p q hdiv g) (AdjoinRoot.map φ p q hdiv h) := by
  subst q
  exact sourceMinor_map φ p hp hn hqn a b c d e f g h

def solveCoefficients (M : Matrix (Fin 10) (Fin 10) K) (target : Fin 10 → K) : Fin 10 → K :=
  M⁻¹ *ᵥ target

def gradientWeights (solution : Fin 10 → K) : Fin 4 → K := fun i => solution (Fin.castAdd 6 i)

def contactWeights (solution : Fin 10 → K) : Fin 27 → K :=
  Fin.addCases (motive := fun _ => K)
    (fun i : Fin 6 => solution (Fin.natAdd 4 i)) (fun _ : Fin 21 => 0)

theorem solveCoefficients_correct (M : Matrix (Fin 10) (Fin 10) K) (target : Fin 10 → K)
    (hM : IsUnit M.det) : M *ᵥ solveCoefficients M target = target := by
  rw [solveCoefficients, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hM,
    Matrix.one_mulVec]

theorem coefficient_decomposition (basis : Module.Basis (Fin 27) K E)
    (a b c d : K) (e f g h : E) (target : Fin 10 → K)
    (hM : IsUnit (sourceMinor basis a b c d e f g h).det) (i : Fin 10) :
    let sol := solveCoefficients (sourceMinor basis a b c d e f g h) target
    (∑ j : Fin 4, gradientCoefficients a b c d i j * gradientWeights sol j) +
      (∑ j : Fin 27, contactWeights sol j *
        basis.repr (sourceCoefficients (algebraMap K E d) e f g h i) j) = target i := by
  dsimp
  have hm := congrFun (solveCoefficients_correct
    (sourceMinor basis a b c d e f g h) target hM) i
  simp only [Matrix.mulVec, dotProduct] at hm
  rw [Fin.sum_univ_add (a := 4) (b := 6)] at hm
  rw [Fin.sum_univ_add (a := 6) (b := 21)]
  simp only [sourceMinor, gradientWeights, contactWeights,
    Fin.addCases_left, Fin.addCases_right, zero_mul, Finset.sum_const_zero, add_zero] at *
  simpa only [mul_comm] using hm


def quadratic (target : Fin 10 → K) : Poly (K := K) :=
  ∑ j : Fin 10, C (target j) * quadraticMonomials j

def combinedNumerators (ρ : Rep (K := K) (E := E)) (d : K) (e f g h : E)
    (solution : Fin 10 → K) : Fin 4 → Poly (K := K) := fun i =>
  contactNumerators ρ d e f g h (contactWeights solution) i +
    denominator ρ e f * C (gradientWeights solution i)

theorem representation_functional (basis : Module.Basis (Fin 27) K E)
    (hB : basis 0 = 1) (weights : Fin 27 → K) (z : E) :
    coefficientFunctional (Algebra.leftMulMatrix basis) weights z =
      ∑ j, weights j * basis.repr z j := by
  simp only [coefficientFunctional, Algebra.leftMulMatrix_eq_repr_mul, hB, mul_one]

theorem gradient_source_expansion (a b c d : K) (weights : Fin 4 → K) :
    directional (cubic a b c d) (fun i => C (weights i)) =
      ∑ j : Fin 10, C (∑ i : Fin 4, gradientCoefficients a b c d j i * weights i) *
        quadraticMonomials j := by
  unfold directional
  simp_rw [gradient_expansion, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [map_sum, map_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem target_decomposition (basis : Module.Basis (Fin 27) K E) (hB : basis 0 = 1)
    (a b c d : K) (e f g h : E) (target : Fin 10 → K)
    (hM : IsUnit (sourceMinor basis a b c d e f g h).det) :
    let sol := solveCoefficients (sourceMinor basis a b c d e f g h) target
    quadratic target =
      contactSource (Algebra.leftMulMatrix basis) d e f g h (contactWeights sol) +
        directional (cubic a b c d) (fun i => C (gradientWeights sol i)) := by
  dsimp
  rw [gradient_source_expansion]
  unfold quadratic contactSource
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [representation_functional basis hB]
  rw [← add_mul, ← map_add]
  congr 2
  exact (coefficient_decomposition basis a b c d e f g h target hM i).symm.trans
    (add_comm _ _)

/-- Adding a constant polynomial vector field preserves strictness. -/
theorem equations_add_constant {F A D : Poly (K := K)}
    {N : Fin 4 → Poly (K := K)} (h : Equations F A D N 0) (weights : Fin 4 → K) :
    Equations F (A + directional F (fun i => C (weights i))) D
      (fun i => N i + D * C (weights i)) 0 := by
  apply strict_to_equations
  · simp only [directional, mul_add, Finset.sum_add_distrib]
    have hsum : (∑ i, pderiv i F * (D * C (weights i))) =
        directional F (fun i => C (weights i)) * D := by
      simp only [directional, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hsum]
    change directional F N + directional F (fun i => C (weights i)) * D = _
    rw [h.e1]
    simp only [directional]
    ring
  · have hzero : divergenceNumerator D N = 0 := by simpa using h.e2
    unfold divergenceNumerator divergence directional at hzero ⊢
    simp only [map_add, pderiv_mul, pderiv_C, mul_zero, add_zero,
      Finset.sum_add_distrib, mul_add]
    rw [Finset.mul_sum, Finset.mul_sum]
    have hcancel : (∑ i, D * (pderiv i D * C (weights i))) =
        ∑ i, pderiv i D * (D * C (weights i)) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hcancel]
    rw [Finset.mul_sum] at hzero
    linear_combination hzero

theorem equations (basis : Module.Basis (Fin 27) K E) (hB : basis 0 = 1)
    (a b c d : K) (e f g h : E) (target : Fin 10 → K)
    (h0 : rel0 (algebraMap K E a) e g = 0)
    (h1 : rel1 (algebraMap K E c) e f g h = 0)
    (h2 : rel2 (algebraMap K E d) e f g h = 0)
    (h3 : rel3 (algebraMap K E b) (algebraMap K E d) f h = 0)
    (hM : IsUnit (sourceMinor basis a b c d e f g h).det) :
    Equations (cubic a b c d) (quadratic target)
      (denominator (Algebra.leftMulMatrix basis) e f)
      (combinedNumerators (Algebra.leftMulMatrix basis) d e f g h
        (solveCoefficients (sourceMinor basis a b c d e f g h) target)) 0 := by
  rw [target_decomposition basis hB a b c d e f g h target hM]
  exact equations_add_constant
    (contact_equations (Algebra.leftMulMatrix basis) a b c d e f g h _ h0 h1 h2 h3) _

theorem combinedNumerators_homogeneous (ρ : Rep (K := K) (E := E)) (d : K)
    (e f g h : E) (solution : Fin 10 → K) (i : Fin 4) :
    (combinedNumerators ρ d e f g h solution i).IsHomogeneous 27 := by
  apply (contactNumerators_homogeneous ρ d e f g h _ i).add
  simpa only [mul_comm] using
    (denominator_homogeneous ρ e f).C_mul (gradientWeights solution i)

end HoldoutQ2.QuadraticSolver
#print axioms HoldoutQ2.QuadraticSolver.contact_equations
#print axioms HoldoutQ2.QuadraticSolver.coefficient_decomposition
#print axioms HoldoutQ2.QuadraticSolver.equations
