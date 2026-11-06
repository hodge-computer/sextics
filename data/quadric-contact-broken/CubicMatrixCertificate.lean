import Proposal.ConcreteLine
import HodgeComputer.Constructions.FiniteAlgebra.PolynomialMatrixMap
import HodgeComputer.Constructions.FiniteAlgebra.MatrixHomogeneous

noncomputable section
open scoped BigOperators
namespace QuadricContact.CubicMatrixCertificate
open MvPolynomial HodgeTestbed ConcreteLine

variable {K E n : Type*} [CommRing K] [IsDomain K] [CommRing E] [Algebra K E]
variable [Fintype n] [DecidableEq n]

abbrev PM := MvPolynomial (Fin 4) K

def matrixPole (ρ : E →ₐ[K] Matrix n n K) (x y : E) : Matrix n n (PM (K := K)) :=
  polynomialMatrixMap ρ.toRingHom (pole x y)

def matrixNumerator (ρ : E →ₐ[K] Matrix n n K) (k : K) (x y z w : E) :
    Fin 4 → Matrix n n (PM (K := K)) :=
  fun i => polynomialMatrixMap ρ.toRingHom (numerator (algebraMap K E k) x y z w i)

def denominator (ρ : E →ₐ[K] Matrix n n K) (x y : E) : PM (K := K) :=
  (matrixPole ρ x y).det

def numerators (ρ : E →ₐ[K] Matrix n n K) (k : K) (x y z w : E)
    (weights : n → K) (j : n) : Fin 4 → PM (K := K) := fun i =>
  columnFunctional (fun a => C (weights a)) j
    (matrixNumerator ρ k x y z w i * (matrixPole ρ x y).adjugate)

 theorem denominator_ne_zero (ρ : E →ₐ[K] Matrix n n K) (x y : E) :
    denominator ρ x y ≠ 0 := by
  apply determinant_ne_zero_of_map_eq_one (matrixPole ρ x y)
    (MvPolynomial.eval (fun i : Fin 4 => if i = 0 then (1 : K) else 0))
  ext a b
  simp [matrixPole, pole, polynomialMatrixMap_X, polynomialMatrixMap_C,
    Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.sub_apply,
    smul_eq_mul, map_sub, map_mul, map_sum]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

 theorem map_cubic (p q s k u v : K) :
    MvPolynomial.map (algebraMap K E) (cubic p q s k u v) =
      cubic (algebraMap K E p) (algebraMap K E q) (algebraMap K E s)
        (algebraMap K E k) (algebraMap K E u) (algebraMap K E v) := by
  simp [cubic, map_ofNat]

 theorem equations_of_source_target
    (ρ : E →ₐ[K] Matrix n n K) (p q s k u v : K) (x y z w : E)
    (weights : n → K) (j : n)
    (h0 : rel0 (algebraMap K E p) (algebraMap K E u) x z = 0)
    (h1 : rel1 (algebraMap K E p) (algebraMap K E q) (algebraMap K E k) x y z w = 0)
    (h2 : rel2 (algebraMap K E q) (algebraMap K E s) (algebraMap K E k) x y z w = 0)
    (h3 : rel3 (algebraMap K E s) (algebraMap K E v) y w = 0)
    (hD : denominator ρ x y ≠ 0)
    (hA : columnFunctional (fun a => C (weights a)) j
      (polynomialMatrixMap ρ.toRingHom
        (source (algebraMap K E p) (algebraMap K E q) (algebraMap K E s)
          (algebraMap K E k) x y z w)) = X 1 * X 2) :
    Equations (cubic p q s k u v) (X 1 * X 2)
      (denominator ρ x y) (numerators ρ k x y z w weights j) 0 := by
  let L := matrixPole ρ x y
  let U := matrixNumerator ρ k x y z w
  let J := polynomialMatrixMap ρ.toRingHom
    (source (algebraMap K E p) (algebraMap K E q) (algebraMap K E s)
      (algebraMap K E k) x y z w)
  have hdiv : (∑ i, matrixDeriv (pderiv i) (U i)) = 0 := by
    apply polynomialMatrixMap_divergence ρ.toRingHom
    exact numerator_divergence _ _ _ _ _
  have htan : (∑ i, U i * matrixDeriv (pderiv i) L) = 0 := by
    apply polynomialMatrixMap_tangency ρ.toRingHom
    simpa only [directional, mul_comm] using
      numerator_tangency (algebraMap K E k) x y z w
  have hsource : (∑ i, pderiv i (cubic p q s k u v) • U i) = J * L := by
    apply polynomialMatrixMap_source ρ
    rw [map_cubic]
    have hs := source_with_residual (algebraMap K E p) (algebraMap K E q)
      (algebraMap K E s) (algebraMap K E k) (algebraMap K E u)
      (algebraMap K E v) x y z w
    rw [h0, h1, h2, h3] at hs
    simpa only [directional, map_zero, mul_zero, zero_mul, add_zero, sub_zero,
      mul_comm] using hs
  have hcomm (i : Fin 4) : U i * L.adjugate = L.adjugate * U i := by
    apply commute_adjugate_of_regular_det
    · exact (IsRegular.of_ne_zero hD).left
    · exact polynomialMatrixMap_commute ρ.toRingHom _ _
  have hh := pderiv_contact_column L J U weights j (cubic p q s k u v) (X 1 * X 2)
    hcomm hdiv htan hsource hA
  apply strict_to_equations
  · simpa only [directional, numerators, denominator, L, U, mul_comm] using hh.1
  · unfold divergenceNumerator divergence directional
    have hh2 := hh.2
    change denominator ρ x y * (∑ i, pderiv i (numerators ρ k x y z w weights j i)) =
      ∑ i, numerators ρ k x y z w weights j i * pderiv i (denominator ρ x y) at hh2
    rw [hh2]
    simp only [mul_comm, sub_self]

/-- Coefficient extraction from the column representing the element 1. -/
def coefficientFunctional (ρ : E →ₐ[K] Matrix n n K) (weights : n → K)
    (j : n) (a : E) : K := ∑ r, weights r * ρ a r j

 theorem columnFunctional_constant (ρ : E →ₐ[K] Matrix n n K)
    (weights : n → K) (j : n) (a : E) :
    columnFunctional (fun r => (C (weights r) : PM (K := K))) j ((ρ a).map C) =
      C (coefficientFunctional ρ weights j a) := by
  simp only [columnFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    coefficientFunctional, Matrix.map_apply, map_sum, map_mul]

 theorem source_target_of_coefficients
    (ρ : E →ₐ[K] Matrix n n K) (p q s k : K) (x y z w : E)
    (weights : n → K) (j : n)
    (hc : ∀ i : Fin 8,
      coefficientFunctional ρ weights j
        (sourceCoefficients (algebraMap K E p) (algebraMap K E q)
          (algebraMap K E s) (algebraMap K E k) x y z w i) =
      if i = 3 then 1 else 0) :
    columnFunctional (fun a => C (weights a)) j
      (polynomialMatrixMap ρ.toRingHom
        (source (algebraMap K E p) (algebraMap K E q) (algebraMap K E s)
          (algebraMap K E k) x y z w)) = X 1 * X 2 := by
  have hm (i : Fin 8) : polynomialMatrixMap ρ.toRingHom
      (quadraticMonomials (R := E) i) =
      quadraticMonomials (R := K) i • (1 : Matrix n n (PM (K := K))) := by
    have hmap : MvPolynomial.map (algebraMap K E) (quadraticMonomials (R := K) i) =
        quadraticMonomials (R := E) i := by
      fin_cases i <;> simp [quadraticMonomials]
    rw [← hmap, polynomialMatrixMap_base]
  have hconst (i : Fin 8) :
      columnFunctional (fun a => (C (weights a) : PM (K := K))) j
        ((ρ.toRingHom (sourceCoefficients (algebraMap K E p) (algebraMap K E q)
          (algebraMap K E s) (algebraMap K E k) x y z w i)).map C) =
      C (if i = 3 then (1 : K) else 0) := by
    change columnFunctional (fun a => (C (weights a) : PM (K := K))) j
        ((ρ (sourceCoefficients (algebraMap K E p) (algebraMap K E q)
          (algebraMap K E s) (algebraMap K E k) x y z w i)).map C) = _
    rw [columnFunctional_constant, hc]
  rw [source_expansion, map_sum]
  simp_rw [map_mul, polynomialMatrixMap_C, hm, Matrix.mul_smul, Matrix.mul_one]
  simp only [map_sum, map_smul, smul_eq_mul, hconst]
  simp [quadraticMonomials]

 theorem equations_of_coefficients
    (ρ : E →ₐ[K] Matrix n n K) (p q s k u v : K) (x y z w : E)
    (weights : n → K) (j : n)
    (h0 : rel0 (algebraMap K E p) (algebraMap K E u) x z = 0)
    (h1 : rel1 (algebraMap K E p) (algebraMap K E q) (algebraMap K E k) x y z w = 0)
    (h2 : rel2 (algebraMap K E q) (algebraMap K E s) (algebraMap K E k) x y z w = 0)
    (h3 : rel3 (algebraMap K E s) (algebraMap K E v) y w = 0)
    (hD : denominator ρ x y ≠ 0)
    (hc : ∀ i : Fin 8,
      coefficientFunctional ρ weights j
        (sourceCoefficients (algebraMap K E p) (algebraMap K E q)
          (algebraMap K E s) (algebraMap K E k) x y z w i) =
      if i = 3 then 1 else 0) :
    Equations (cubic p q s k u v) (X 1 * X 2)
      (denominator ρ x y) (numerators ρ k x y z w weights j) 0 :=
  equations_of_source_target ρ p q s k u v x y z w weights j h0 h1 h2 h3 hD
    (source_target_of_coefficients ρ p q s k x y z w weights j hc)

 theorem matrixPole_homogeneous (ρ : E →ₐ[K] Matrix n n K) (x y : E) (a b : n) :
    (matrixPole ρ x y a b).IsHomogeneous 1 :=
  polynomialMatrixMap_homogeneous ρ (pole x y) 1 (pole_homogeneous x y) a b

 theorem matrixNumerator_homogeneous (ρ : E →ₐ[K] Matrix n n K) (k : K)
    (x y z w : E) (i : Fin 4) (a b : n) :
    (matrixNumerator ρ k x y z w i a b).IsHomogeneous 1 :=
  polynomialMatrixMap_homogeneous ρ (numerator (algebraMap K E k) x y z w i) 1
    (numerator_homogeneous _ _ _ _ _ i) a b

 theorem denominator_homogeneous (ρ : E →ₐ[K] Matrix n n K) (x y : E) :
    (denominator ρ x y).IsHomogeneous (Fintype.card n) := by
  simpa [denominator] using determinant_homogeneous (matrixPole ρ x y) 1
    (matrixPole_homogeneous ρ x y)

 theorem numerators_homogeneous (ρ : E →ₐ[K] Matrix n n K) (k : K)
    (x y z w : E) (weights : n → K) (j : n) (i : Fin 4) :
    (numerators ρ k x y z w weights j i).IsHomogeneous (Fintype.card n) := by
  have hn : 1 ≤ Fintype.card n := Nat.succ_le_of_lt (Fintype.card_pos_iff.mpr ⟨j⟩)
  have hh := column_contact_numerator_homogeneous (matrixPole ρ x y)
    (matrixNumerator ρ k x y z w i) weights j 1
    (matrixPole_homogeneous ρ x y) (matrixNumerator_homogeneous ρ k x y z w i)
  simpa only [numerators, columnFunctional, LinearMap.coe_mk, AddHom.coe_mk,
    Nat.mul_one, Nat.add_comm 1, Nat.sub_add_cancel hn] using hh

end QuadricContact.CubicMatrixCertificate
#print axioms QuadricContact.CubicMatrixCertificate.equations_of_source_target

#print axioms QuadricContact.CubicMatrixCertificate.equations_of_coefficients

#print axioms QuadricContact.CubicMatrixCertificate.denominator_ne_zero
#print axioms QuadricContact.CubicMatrixCertificate.numerators_homogeneous
