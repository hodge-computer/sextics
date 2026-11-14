import Proposal.GeometricKoszulTrace
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Concrete denominator regularity for every curve parameter

The actual curve quotient is compared with a tower of monic quadratic and
cubic root algebras. Regularity is obtained from their explicit power bases.
The proofs in `At` allow every complex cubic parameter; the original sparse
curve endpoints are retained as specializations at parameter zero.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricCurveRegularPair

namespace At

section MonicModel
open Polynomial
variable {R S : Type*} [CommRing R] [CommRing S]

private theorem regular_map_adjoinRoot {p : R[X]} (hp : p.Monic) {z : R}
    (hz : IsSMulRegular R z) :
    IsSMulRegular (AdjoinRoot p) (algebraMap R (AdjoinRoot p) z) := by
  intro u v huv
  apply (AdjoinRoot.powerBasisAux' hp).repr.injective
  ext k
  apply hz
  have huv' : z • u = z • v := by
    simpa only [Algebra.smul_def, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply] using huv
  have hh := congrArg (fun w => (AdjoinRoot.powerBasisAux' hp).repr w k) huv'
  simpa only [map_smul, Finsupp.smul_apply, RingHom.id_apply] using hh

def quadratic (r x y : R) : R[X] := Polynomial.X ^ 2 - Polynomial.C (r * x * y)

theorem quadratic_monic (r x y : R) : (quadratic r x y).Monic :=
  Polynomial.monic_X_pow_sub_C _ (by decide)

abbrev Quadratic (r x y : R) := AdjoinRoot (quadratic r x y)

def quadraticRoot (r x y : R) : Quadratic r x y := AdjoinRoot.root _

theorem quadraticRoot_sq (r x y : R) :
    quadraticRoot r x y ^ 2 = algebraMap R (Quadratic r x y) (r * x * y) := by
  have hh := AdjoinRoot.mk_self (f := quadratic r x y)
  change AdjoinRoot.mk _ (Polynomial.X ^ 2 - Polynomial.C (r * x * y)) = 0 at hh
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  exact sub_eq_zero.mp hh

def cubic (r i θ x y : R) : (Quadratic r x y)[X] :=
  Polynomial.X ^ 3 +
    Polynomial.C ((quadraticRoot r x y + algebraMap R _ x) * algebraMap R _ y) *
      Polynomial.X +
    Polynomial.C (quadraticRoot r x y * algebraMap R _ (x ^ 2 + θ * r * x * y) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i θ x y : R) : (cubic r i θ x y).Monic := by
  unfold cubic
  rw [add_assoc]
  apply Polynomial.monic_X_pow_add
  apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (Polynomial.degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add Polynomial.degree_C_le Polynomial.degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt Polynomial.degree_C_le (by norm_num)

abbrev Tower (r i θ x y : R) := AdjoinRoot (cubic r i θ x y)

def towerX0 (r i θ x y : R) : Tower r i θ x y :=
  algebraMap (Quadratic r x y) _ (quadraticRoot r x y)

def towerX2 (r i θ x y : R) : Tower r i θ x y := AdjoinRoot.root _

def towerBase (r i θ x y : R) : R →+* Tower r i θ x y :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem towerX0_sq (r i θ x y : R) :
    towerX0 r i θ x y ^ 2 = towerBase r i θ x y (r * x * y) := by
  rw [towerX0, ← map_pow, quadraticRoot_sq]
  rfl

theorem towerX2_cubic (r i θ x y : R) :
    towerX2 r i θ x y ^ 3 + (towerX0 r i θ x y + towerBase r i θ x y x) *
        towerBase r i θ x y y * towerX2 r i θ x y +
      towerX0 r i θ x y * towerBase r i θ x y (x ^ 2 + θ * r * x * y) +
        towerBase r i θ x y ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i θ x y)
  change AdjoinRoot.mk _
    (Polynomial.X ^ 3 +
      Polynomial.C ((quadraticRoot r x y + algebraMap R _ x) * algebraMap R _ y) *
        Polynomial.X +
      Polynomial.C (quadraticRoot r x y * algebraMap R _ (x ^ 2 + θ * r * x * y) +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  rw [map_add, map_add, map_pow, AdjoinRoot.mk_X, map_mul,
    AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  rw [map_mul, map_add, map_add, map_mul] at hh
  change towerX2 r i θ x y ^ 3 +
    (towerX0 r i θ x y + towerBase r i θ x y x) *
      towerBase r i θ x y y * towerX2 r i θ x y +
    (towerX0 r i θ x y * towerBase r i θ x y (x ^ 2 + θ * r * x * y) +
      towerBase r i θ x y ((1 - i) * y ^ 3 - i * x ^ 3)) = 0 at hh
  simpa only [add_assoc] using hh

theorem towerBase_regular (r i θ x y z : R) (hz : IsSMulRegular R z) :
    IsSMulRegular (Tower r i θ x y) (towerBase r i θ x y z) :=
  regular_map_adjoinRoot (cubic_monic r i θ x y)
    (regular_map_adjoinRoot (quadratic_monic r x y) hz)

def binaryNorm (r i θ x y : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x * y * (x ^ 2 + θ * r * x * y) ^ 2

def inverseNumerator (r i θ x y : R) : Tower r i θ x y :=
  -(towerX2 r i θ x y ^ 2 +
      (towerX0 r i θ x y + towerBase r i θ x y x) * towerBase r i θ x y y) *
    (towerBase r i θ x y ((1 - i) * y ^ 3 - i * x ^ 3) -
      towerX0 r i θ x y * towerBase r i θ x y (x ^ 2 + θ * r * x * y))

theorem towerX2_mul_inverseNumerator (r i θ x y : R) :
    towerX2 r i θ x y * inverseNumerator r i θ x y = towerBase r i θ x y (binaryNorm r i θ x y) := by
  have h0 := towerX0_sq r i θ x y
  have h2 := towerX2_cubic r i θ x y
  unfold inverseNumerator binaryNorm
  simp only [map_sub, map_add, map_mul, map_pow, map_one] at h0 h2 ⊢
  linear_combination
    -((1 - towerBase r i θ x y i) * towerBase r i θ x y y ^ 3 -
      towerBase r i θ x y i * towerBase r i θ x y x ^ 3 -
      towerX0 r i θ x y * (towerBase r i θ x y x ^ 2 +
        towerBase r i θ x y θ * towerBase r i θ x y r *
          towerBase r i θ x y x * towerBase r i θ x y y)) * h2 -
    (towerBase r i θ x y x ^ 2 + towerBase r i θ x y θ * towerBase r i θ x y r *
      towerBase r i θ x y x * towerBase r i θ x y y) ^ 2 * h0

theorem towerX2_regular (r i θ x y : R) (hn : IsSMulRegular R (binaryNorm r i θ x y)) :
    IsSMulRegular (Tower r i θ x y) (towerX2 r i θ x y) := by
  have hh := towerBase_regular r i θ x y _ hn
  rw [← towerX2_mul_inverseNumerator, mul_comm] at hh
  exact IsLeftRegular.of_mul hh

end MonicModel

section ModelLift
variable {R S : Type*} [CommRing R] [CommRing S]

/-- The universal map out of the quadratic stage. -/
def liftQuadratic (r x y : R) (f : R →+* S) (a : S)
    (ha : a ^ 2 = f (r * x * y)) : Quadratic r x y →+* S :=
  AdjoinRoot.lift f a (by simpa [quadratic] using sub_eq_zero.mpr ha)

@[simp] theorem liftQuadratic_root (r x y : R) (f : R →+* S) (a : S)
    (ha : a ^ 2 = f (r * x * y)) : liftQuadratic r x y f a ha (quadraticRoot r x y) = a := by
  simp [liftQuadratic, quadraticRoot]

@[simp] theorem liftQuadratic_base (r x y z : R) (f : R →+* S) (a : S)
    (ha : a ^ 2 = f (r * x * y)) :
    liftQuadratic r x y f a ha (algebraMap R (Quadratic r x y) z) = f z := by
  simp [liftQuadratic, AdjoinRoot.algebraMap_eq]

/-- A homomorphism from the two-stage monic model, with the two actual
curve equations as its only input relations. -/
def liftTower (r i θ x y : R) (f : R →+* S) (a b : S)
    (ha : a ^ 2 = f (r * x * y))
    (hb : b ^ 3 + (a + f x) * f y * b + a * f (x ^ 2 + θ * r * x * y) +
      f ((1 - i) * y ^ 3 - i * x ^ 3) = 0) : Tower r i θ x y →+* S :=
  AdjoinRoot.lift (liftQuadratic r x y f a ha) b (by
    simp only [cubic, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_sub, Polynomial.eval₂_one, map_add, map_mul, map_pow, map_sub, map_one,
      liftQuadratic_root, liftQuadratic_base]
    simpa only [map_sub, map_add, map_mul, map_pow, map_one, add_assoc] using hb)

@[simp] theorem liftTower_x0 (r i θ x y : R) (f : R →+* S) (a b : S)
    (ha : a ^ 2 = f (r * x * y))
    (hb : b ^ 3 + (a + f x) * f y * b + a * f (x ^ 2 + θ * r * x * y) +
      f ((1 - i) * y ^ 3 - i * x ^ 3) = 0) :
    liftTower r i θ x y f a b ha hb (towerX0 r i θ x y) = a := by
  simp [liftTower, towerX0, AdjoinRoot.algebraMap_eq]

@[simp] theorem liftTower_x2 (r i θ x y : R) (f : R →+* S) (a b : S)
    (ha : a ^ 2 = f (r * x * y))
    (hb : b ^ 3 + (a + f x) * f y * b + a * f (x ^ 2 + θ * r * x * y) +
      f ((1 - i) * y ^ 3 - i * x ^ 3) = 0) :
    liftTower r i θ x y f a b ha hb (towerX2 r i θ x y) = b := by
  simp [liftTower, towerX2]

@[simp] theorem liftTower_base (r i θ x y z : R) (f : R →+* S) (a b : S)
    (ha : a ^ 2 = f (r * x * y))
    (hb : b ^ 3 + (a + f x) * f y * b + a * f (x ^ 2 + θ * r * x * y) +
      f ((1 - i) * y ^ 3 - i * x ^ 3) = 0) :
    liftTower r i θ x y f a b ha hb (towerBase r i θ x y z) = f z := by
  simp [liftTower, towerBase, liftQuadratic, AdjoinRoot.algebraMap_eq]

end ModelLift

section BinaryBase
open MvPolynomial

abbrev Base := MvPolynomial (Fin 2) ℂ

def baseProduct : Base := (X 0 * X 1) ^ 2

def baseNorm (r θ : ℂ) : Base := binaryNorm (C r) (C Complex.I) (C θ) (X 0) (X 1)

private theorem X_zero_not_dvd_norm (r θ : ℂ) : ¬ (X 0 : Base) ∣ baseNorm r θ := by
  rintro ⟨p, hp⟩
  have hh := congrArg (MvPolynomial.eval ![(0 : ℂ), 1]) hp
  norm_num [baseNorm, binaryNorm, Complex.ext_iff] at hh

private theorem X_one_not_dvd_norm (r θ : ℂ) : ¬ (X 1 : Base) ∣ baseNorm r θ := by
  rintro ⟨p, hp⟩
  have hh := congrArg (MvPolynomial.eval ![(1 : ℂ), 0]) hp
  norm_num [baseNorm, binaryNorm, Complex.ext_iff] at hh

/-- The binary norm remains a nonzerodivisor even after imposing the
nonreduced denominator equation (x1*x3)^2=0. -/
theorem baseProduct_dvd_of_dvd_norm_mul (r θ : ℂ) (p : Base)
    (hp : baseProduct ∣ baseNorm r θ * p) : baseProduct ∣ p := by
  have h0 : (X (0 : Fin 2) : Base) ^ 2 ∣ p :=
    (MvPolynomial.X_prime (i := (0 : Fin 2))).pow_dvd_of_dvd_mul_left 2
      (X_zero_not_dvd_norm r θ) ((show (X (0 : Fin 2) : Base) ^ 2 ∣ baseProduct by simp [baseProduct, mul_pow]).trans hp)
  obtain ⟨q, hq⟩ := h0
  have h1 : (X (1 : Fin 2) : Base) ^ 2 ∣ p :=
    (MvPolynomial.X_prime (i := (1 : Fin 2))).pow_dvd_of_dvd_mul_left 2
      (X_one_not_dvd_norm r θ) ((show (X (1 : Fin 2) : Base) ^ 2 ∣ baseProduct by simp [baseProduct, mul_pow]).trans hp)
  have h10 : ¬ (X (1 : Fin 2) : Base) ∣ (X (0 : Fin 2) : Base) ^ 2 := by
    intro hh
    have h := (MvPolynomial.X_prime (i := (1 : Fin 2))).dvd_of_dvd_pow hh
    exact (by decide : (1 : Fin 2) ≠ 0) (MvPolynomial.X_dvd_X.mp h)
  have hq1 : (X (1 : Fin 2) : Base) ^ 2 ∣ q :=
    (MvPolynomial.X_prime (i := (1 : Fin 2))).pow_dvd_of_dvd_mul_left 2 h10 (hq ▸ h1)
  obtain ⟨s, hs⟩ := hq1
  refine ⟨s, ?_⟩
  rw [hq, hs]
  simp [baseProduct, mul_pow, mul_assoc]

abbrev BaseQuotient := Base ⧸ Ideal.span {baseProduct}

def baseQuotientMap : Base →+* BaseQuotient := Ideal.Quotient.mk _

theorem baseQuotient_norm_regular (r θ : ℂ) :
    IsSMulRegular BaseQuotient (baseQuotientMap (baseNorm r θ)) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply baseProduct_dvd_of_dvd_norm_mul r θ p
  change baseQuotientMap (baseNorm r θ) * baseQuotientMap p = 0 at hz
  rw [← map_mul] at hz
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)

end BinaryBase

section Comparison
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
variable {R S : Type*} [CommRing R] [CommRing S]

def baseInclusion : Base →+* Poly := (rename ![(1 : Fin 4), 3]).toRingHom

@[simp] theorem baseInclusion_C (z : ℂ) : baseInclusion (C z) = C z := by simp [baseInclusion]
@[simp] theorem baseInclusion_X0 : baseInclusion (X 0) = X 1 := by simp [baseInclusion]
@[simp] theorem baseInclusion_X1 : baseInclusion (X 1) = X 3 := by simp [baseInclusion]

abbrev Model (r θ : ℂ) (f : Base →+* R) :=
  Tower (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))

def modelBase (r θ : ℂ) (f : Base →+* R) : R →+* Model r θ f :=
  towerBase (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))

def modelX0 (r θ : ℂ) (f : Base →+* R) : Model r θ f :=
  towerX0 (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))

def modelX2 (r θ : ℂ) (f : Base →+* R) : Model r θ f :=
  towerX2 (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))

def modelEval (r θ : ℂ) (f : Base →+* R) : Poly →+* Model r θ f :=
  eval₂Hom ((modelBase r θ f).comp (f.comp C))
    ![modelX0 r θ f, modelBase r θ f (f (X 0)), modelX2 r θ f, modelBase r θ f (f (X 1))]

@[simp] theorem modelEval_C (r θ : ℂ) (f : Base →+* R) (z : ℂ) :
    modelEval r θ f (C z) = modelBase r θ f (f (C z)) := by simp [modelEval]
@[simp] theorem modelEval_X0 (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (X 0) = modelX0 r θ f := by simp [modelEval]
@[simp] theorem modelEval_X1 (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (X 1) = modelBase r θ f (f (X 0)) := by simp [modelEval]
@[simp] theorem modelEval_X2 (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (X 2) = modelX2 r θ f := by simp [modelEval]
@[simp] theorem modelEval_X3 (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (X 3) = modelBase r θ f (f (X 1)) := by simp [modelEval]

theorem modelEval_quadric (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (relation r 0) = 0 := by
  have hh := towerX0_sq (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))
  change modelX0 r θ f ^ 2 = modelBase r θ f (f (C r) * f (X 0) * f (X 1)) at hh
  simp only [map_mul] at hh
  simpa only [relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    modelEval_X0, modelEval_X1, modelEval_X3, modelEval_C] using sub_eq_zero.mpr hh

theorem modelEval_cubic (r θ : ℂ) (f : Base →+* R) :
    modelEval r θ f (curveH θ) = 0 := by
  have hh := towerX2_cubic (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))
  have h0 := towerX0_sq (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1))
  change modelX0 r θ f ^ 2 =
    modelBase r θ f (f (C r) * f (X 0) * f (X 1)) at h0
  change modelX2 r θ f ^ 3 + (modelX0 r θ f + modelBase r θ f (f (X 0))) *
    modelBase r θ f (f (X 1)) * modelX2 r θ f +
    modelX0 r θ f * modelBase r θ f
      (f (X 0) ^ 2 + f (C θ) * f (C r) * f (X 0) * f (X 1)) +
    modelBase r θ f ((1 - f (C Complex.I)) * f (X 1) ^ 3 -
      f (C Complex.I) * f (X 0) ^ 3) = 0 at hh
  simp only [map_sub, map_add, map_mul, map_pow, map_one] at hh h0
  simp only [curveH, h, b, map_sub, map_add, map_mul, map_pow,
    modelEval_X0, modelEval_X1, modelEval_X2, modelEval_X3, modelEval_C]
  linear_combination hh + modelBase r θ f (f (C θ)) * modelX0 r θ f * h0

/-- The actual curve quotient maps to the monic model over any selected
base ring. This map preserves all four existing coordinate functions. -/
def curveToModel (r θ : ℂ) (f : Base →+* R) : CurveRing r θ →+* Model r θ f :=
  Ideal.Quotient.lift _ (modelEval r θ f) (by
    intro p hp
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hp
    rw [← hab, map_add, map_mul, map_mul, modelEval_quadric, modelEval_cubic]
    ring)

@[simp] theorem curveToModel_mk (r θ : ℂ) (f : Base →+* R) (p : Poly) :
    curveToModel r θ f (curveMap r θ p) = modelEval r θ f p := rfl

private theorem coordinate_quadratic (r : ℂ) (p : Poly →+* S)
    (hf : p (relation r 0) = 0) :
    p (X 0) ^ 2 = p (C r) * p (X 1) * p (X 3) := by
  simpa only [relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    sub_eq_zero] using hf

private theorem coordinate_cubic (r θ : ℂ) (p : Poly →+* S)
    (hf : p (relation r 0) = 0) (hh : p (curveH θ) = 0) :
    p (X 2) ^ 3 + (p (X 0) + p (X 1)) * p (X 3) * p (X 2) +
    p (X 0) * (p (X 1) ^ 2 + p (C θ) * p (C r) * p (X 1) * p (X 3)) +
    ((1 - p (C Complex.I)) * p (X 3) ^ 3 - p (C Complex.I) * p (X 1) ^ 3) = 0 := by
  have h0 := coordinate_quadratic r p hf
  simp only [curveH, h, b, map_sub, map_add, map_mul, map_pow] at hh
  linear_combination hh - p (C θ) * p (X 0) * h0

/-- A faithful reverse map is constructed whenever the base map factors
through the chosen concrete quotient. All curve relations are explicit. -/
def modelBack (r θ : ℂ) (f : Base →+* R) (p : Poly →+* S) (g : R →+* S)
    (hg : g.comp f = p.comp baseInclusion)
    (hf : p (relation r 0) = 0) (hh : p (curveH θ) = 0) : Model r θ f →+* S :=
  liftTower (f (C r)) (f (C Complex.I)) (f (C θ)) (f (X 0)) (f (X 1)) g (p (X 0)) (p (X 2))
    (by
      have hgf (z : Base) : g (f z) = p (baseInclusion z) := RingHom.congr_fun hg z
      simpa only [map_mul, hgf, baseInclusion_C, baseInclusion_X0, baseInclusion_X1]
        using coordinate_quadratic r p hf)
    (by
      have hgf (z : Base) : g (f z) = p (baseInclusion z) := RingHom.congr_fun hg z
      simpa only [map_sub, map_add, map_mul, map_pow, map_one, hgf,
        baseInclusion_C, baseInclusion_X0, baseInclusion_X1]
        using coordinate_cubic r θ p hf hh)

theorem modelBack_comp_eval (r θ : ℂ) (f : Base →+* R) (p : Poly →+* S) (g : R →+* S)
    (hg : g.comp f = p.comp baseInclusion)
    (hf : p (relation r 0) = 0) (hh : p (curveH θ) = 0) :
    (modelBack r θ f p g hg hf hh).comp (modelEval r θ f) = p := by
  have hgf (z : Base) : g (f z) = p (baseInclusion z) := RingHom.congr_fun hg z
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [modelBack, modelBase, hgf]
  · intro j
    fin_cases j <;> simp [modelBack, modelBase, modelX0, modelX2, hgf]

theorem model_injective (r θ : ℂ) (f : Base →+* R) (p : Poly →+* S)
    (hp : Function.Surjective p) (g : R →+* S)
    (hg : g.comp f = p.comp baseInclusion)
    (hf : p (relation r 0) = 0) (hh : p (curveH θ) = 0)
    (φ : S →+* Model r θ f) (hφ : φ.comp p = modelEval r θ f) : Function.Injective φ := by
  have hleft : Function.LeftInverse (modelBack r θ f p g hg hf hh) φ := by
    intro z
    obtain ⟨q, rfl⟩ := hp z
    have he := RingHom.congr_fun (modelBack_comp_eval r θ f p g hg hf hh) q
    rw [← hφ] at he
    exact he
  exact hleft.injective

end Comparison

section ActualRegularPair
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricKoszulTrace
open CycleQ2SeedCech (curveA curveB)

private theorem regular_of_injective {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Injective f) (z : R) (hz : IsSMulRegular S (f z)) :
    IsSMulRegular R z := by
  intro a b hab
  apply hf
  apply hz
  simpa only [smul_eq_mul, map_mul] using congrArg f hab

/-- The monic model is faithful to the literal four-variable quotient. -/
theorem curveToModel_injective (r θ : ℂ) :
    Function.Injective (curveToModel r θ (RingHom.id Base)) := by
  apply model_injective r θ (RingHom.id Base) (curveMap r θ) Ideal.Quotient.mk_surjective
    ((curveMap r θ).comp baseInclusion) (by rfl)
    (curveMap_f1 r θ) (curveMap_h r θ)
  rfl

theorem modelEval_baseInclusion (r θ : ℂ) {R : Type*} [CommRing R] (f : Base →+* R) (p : Base) :
    modelEval r θ f (baseInclusion p) = modelBase r θ f (f p) := by
  have hh : (modelEval r θ f).comp baseInclusion = (modelBase r θ f).comp f := by
    apply MvPolynomial.ringHom_ext
    · intro z
      simp
    · intro j
      fin_cases j <;> simp
  exact RingHom.congr_fun hh p

theorem curveToModel_g1 (r θ : ℂ) {R : Type*} [CommRing R] (f : Base →+* R) :
    curveToModel r θ f (curveG1 r θ) = modelBase r θ f (f (C (3 * r ^ 2) * baseProduct)) := by
  rw [curveG1, ambientCurveMap_g1, curveToModel_mk]
  have heq : C (3 * r ^ 2) * curveA ^ 2 = baseInclusion (C (3 * r ^ 2) * baseProduct) := by
    simp [baseProduct, curveA]
  rw [heq, modelEval_baseInclusion]

theorem curveToModel_g2 (r θ : ℂ) {R : Type*} [CommRing R] (f : Base →+* R) :
    curveToModel r θ f (curveG2 r θ) = modelBase r θ f (f (C 3)) * modelX2 r θ f ^ 4 := by
  rw [curveG2, ambientCurveMap_g2, curveToModel_mk]
  simp [curveB]

/-- The actual first quartic denominator is regular in the curve ring. -/
theorem curveG1_regular (r θ : ℂ) (hr : r ≠ 0) :
    IsSMulRegular (CurveRing r θ) (curveG1 r θ) := by
  apply regular_of_injective (curveToModel r θ (RingHom.id Base)) (curveToModel_injective r θ)
  rw [curveToModel_g1]
  apply towerBase_regular
  have hz : (C (3 * r ^ 2) * baseProduct : Base) ≠ 0 := by
    apply mul_ne_zero
    · exact C_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))
    · exact pow_ne_zero _ (mul_ne_zero (X_ne_zero _) (X_ne_zero _))
  intro a b hab
  exact mul_left_cancel₀ hz hab

abbrev DenominatorQuotient (r θ : ℂ) := CurveRing r θ ⧸ Ideal.span {curveG1 r θ}

def denominatorQuotientMap (r θ : ℂ) : CurveRing r θ →+* DenominatorQuotient r θ :=
  Ideal.Quotient.mk _

def denominatorPolyMap (r θ : ℂ) : Poly →+* DenominatorQuotient r θ :=
  (denominatorQuotientMap r θ).comp (curveMap r θ)

@[simp] theorem denominatorPolyMap_quadric (r θ : ℂ) :
    denominatorPolyMap r θ (relation r 0) = 0 := by
  simp [denominatorPolyMap]

@[simp] theorem denominatorPolyMap_cubic (r θ : ℂ) :
    denominatorPolyMap r θ (curveH θ) = 0 := by
  simp [denominatorPolyMap]

@[simp] theorem denominatorQuotientMap_g1 (r θ : ℂ) :
    denominatorQuotientMap r θ (curveG1 r θ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))

theorem denominatorPolyMap_baseProduct (r θ : ℂ) (hr : r ≠ 0) :
    denominatorPolyMap r θ (baseInclusion baseProduct) = 0 := by
  have hu : IsUnit (denominatorPolyMap r θ (C (3 * r ^ 2))) :=
    (isUnit_iff_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))).map
      ((denominatorPolyMap r θ).comp C)
  have hz : denominatorPolyMap r θ (C (3 * r ^ 2)) *
      denominatorPolyMap r θ (baseInclusion baseProduct) = 0 := by
    have heq : C (3 * r ^ 2) * baseInclusion baseProduct = firstQuartic r := by
      simp [firstQuartic, baseProduct, curveA]
    rw [← map_mul, heq]
    simp [denominatorPolyMap]
  apply (hu.isRegular.left : Function.Injective
    (fun z : DenominatorQuotient r θ => denominatorPolyMap r θ (C (3 * r ^ 2)) * z))
  exact hz.trans (mul_zero (denominatorPolyMap r θ (C (3 * r ^ 2)))).symm

/-- The reverse base map factors through the exact squared-denominator
quotient; cancellation uses only the explicit nonzero scalar 3*r^2. -/
def baseQuotientToDenominator (r θ : ℂ) (hr : r ≠ 0) : BaseQuotient →+* DenominatorQuotient r θ :=
  Ideal.Quotient.lift _ ((denominatorPolyMap r θ).comp baseInclusion) (by
    intro p hp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
    rw [hq, map_mul]
    simp only [RingHom.comp_apply, denominatorPolyMap_baseProduct r θ hr]
    ring)

theorem curveToModel_g1_zero (r θ : ℂ) :
    curveToModel r θ baseQuotientMap (curveG1 r θ) = 0 := by
  rw [curveToModel_g1, map_mul]
  have hz : baseQuotientMap baseProduct = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  rw [hz, mul_zero, map_zero]

def denominatorToModel (r θ : ℂ) : DenominatorQuotient r θ →+* Model r θ baseQuotientMap :=
  Ideal.Quotient.lift _ (curveToModel r θ baseQuotientMap) (by
    intro p hp
    obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hp
    rw [hq, map_mul, curveToModel_g1_zero, zero_mul])

@[simp] theorem denominatorToModel_mk (r θ : ℂ) (z : CurveRing r θ) :
    denominatorToModel r θ (denominatorQuotientMap r θ z) = curveToModel r θ baseQuotientMap z := rfl

/-- Faithfulness also holds after imposing the nonreduced first
quartic denominator. The proof supplies an actual reverse homomorphism. -/
theorem denominatorToModel_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (denominatorToModel r θ) := by
  exact model_injective (R := BaseQuotient) (S := DenominatorQuotient r θ)
    r θ baseQuotientMap (denominatorPolyMap r θ)
    (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)
    (baseQuotientToDenominator r θ hr) (by rfl)
    (denominatorPolyMap_quadric r θ) (denominatorPolyMap_cubic r θ)
    (denominatorToModel r θ) (by rfl)

private theorem modelX2_regular_mod_baseProduct (r θ : ℂ) :
    IsSMulRegular (Model r θ baseQuotientMap) (modelX2 r θ baseQuotientMap) := by
  apply towerX2_regular
  simpa only [baseNorm, binaryNorm, map_sub, map_add, map_mul, map_pow, map_one]
    using baseQuotient_norm_regular r θ

/-- The actual second quartic is regular modulo the first. Both
regular-pair hypotheses of the all-poles Koszul kernel are now proved. -/
theorem curveG2_regular_mod_curveG1 (r θ : ℂ) (hr : r ≠ 0) :
    IsSMulRegular (DenominatorQuotient r θ) (curveG2 r θ) := by
  change IsSMulRegular (DenominatorQuotient r θ) (denominatorQuotientMap r θ (curveG2 r θ))
  refine regular_of_injective (R := DenominatorQuotient r θ) (S := Model r θ baseQuotientMap)
    (denominatorToModel r θ) (denominatorToModel_injective r θ hr)
    (denominatorQuotientMap r θ (curveG2 r θ)) ?_
  rw [denominatorToModel_mk, curveToModel_g2]
  have hu : IsUnit (modelBase r θ baseQuotientMap (baseQuotientMap (C 3))) :=
    (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℂ) ≠ 0)).map
      ((modelBase r θ baseQuotientMap).comp (baseQuotientMap.comp C))
  exact hu.isRegular.left.mul (IsLeftRegular.pow 4 (modelX2_regular_mod_baseProduct r θ))

/-- Unconditional numerator-kernel criterion for every actual curve parameter.
The only parameter condition is the necessary nonzero coefficient r. -/
theorem degreeNineCechClass_zero_iff_fourGeneratorIdeal (r θ : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    CycleQ2GeometricProjectiveCurve.degreeNineCechClass r θ p hp = 0 ↔
      p ∈ fourGeneratorIdeal r θ :=
  degreeNineCechClass_eq_zero_iff r θ
    (curveG1_regular r θ hr) (curveG2_regular_mod_curveG1 r θ hr) p hp

end ActualRegularPair

end At

section SparseSpecializations
variable {R S : Type*} [CommRing R] [CommRing S]

abbrev quadratic (r x y : R) := At.quadratic r x y
abbrev quadratic_monic (r x y : R) := At.quadratic_monic r x y
abbrev Quadratic (r x y : R) := At.Quadratic r x y
abbrev quadraticRoot (r x y : R) := At.quadraticRoot r x y
abbrev quadraticRoot_sq (r x y : R) := At.quadraticRoot_sq r x y
abbrev liftQuadratic (r x y : R) := At.liftQuadratic (S := S) r x y
abbrev liftQuadratic_root (r x y : R) := At.liftQuadratic_root (S := S) r x y
abbrev liftQuadratic_base (r x y : R) := At.liftQuadratic_base (S := S) r x y

abbrev cubic (r i x y : R) := At.cubic r i 0 x y
abbrev cubic_monic (r i x y : R) := At.cubic_monic r i 0 x y
abbrev Tower (r i x y : R) := At.Tower r i 0 x y
abbrev towerX0 (r i x y : R) := At.towerX0 r i 0 x y
abbrev towerX2 (r i x y : R) := At.towerX2 r i 0 x y
abbrev towerBase (r i x y : R) := At.towerBase r i 0 x y
abbrev towerX0_sq (r i x y : R) := At.towerX0_sq r i 0 x y
abbrev towerX2_cubic (r i x y : R) := At.towerX2_cubic r i 0 x y
abbrev towerBase_regular (r i x y : R) := At.towerBase_regular r i 0 x y
abbrev binaryNorm (r i x y : R) := At.binaryNorm r i 0 x y
abbrev inverseNumerator (r i x y : R) := At.inverseNumerator r i 0 x y
abbrev towerX2_mul_inverseNumerator (r i x y : R) := At.towerX2_mul_inverseNumerator r i 0 x y
abbrev towerX2_regular (r i x y : R) := At.towerX2_regular r i 0 x y
abbrev liftTower (r i x y : R) := At.liftTower (S := S) r i 0 x y
abbrev liftTower_x0 (r i x y : R) := At.liftTower_x0 (S := S) r i 0 x y
abbrev liftTower_x2 (r i x y : R) := At.liftTower_x2 (S := S) r i 0 x y
abbrev liftTower_base (r i x y : R) := At.liftTower_base (S := S) r i 0 x y

abbrev Base := @At.Base
abbrev baseProduct := @At.baseProduct
abbrev BaseQuotient := @At.BaseQuotient
abbrev baseQuotientMap := @At.baseQuotientMap
abbrev baseInclusion := @At.baseInclusion
abbrev baseInclusion_C := @At.baseInclusion_C
abbrev baseInclusion_X0 := @At.baseInclusion_X0
abbrev baseInclusion_X1 := @At.baseInclusion_X1

abbrev baseNorm (r : ℂ) := At.baseNorm r 0
abbrev baseProduct_dvd_of_dvd_norm_mul (r : ℂ) := At.baseProduct_dvd_of_dvd_norm_mul r 0
abbrev baseQuotient_norm_regular (r : ℂ) := At.baseQuotient_norm_regular r 0
abbrev Model (r : ℂ) := At.Model (R := R) r 0
abbrev modelBase (r : ℂ) := At.modelBase (R := R) r 0
abbrev modelX0 (r : ℂ) := At.modelX0 (R := R) r 0
abbrev modelX2 (r : ℂ) := At.modelX2 (R := R) r 0
abbrev modelEval (r : ℂ) := At.modelEval (R := R) r 0
abbrev modelEval_C (r : ℂ) := At.modelEval_C (R := R) r 0
abbrev modelEval_X0 (r : ℂ) := At.modelEval_X0 (R := R) r 0
abbrev modelEval_X1 (r : ℂ) := At.modelEval_X1 (R := R) r 0
abbrev modelEval_X2 (r : ℂ) := At.modelEval_X2 (R := R) r 0
abbrev modelEval_X3 (r : ℂ) := At.modelEval_X3 (R := R) r 0
abbrev modelEval_quadric (r : ℂ) := At.modelEval_quadric (R := R) r 0
abbrev modelEval_cubic (r : ℂ) := At.modelEval_cubic (R := R) r 0
abbrev curveToModel (r : ℂ) := At.curveToModel (R := R) r 0
abbrev curveToModel_mk (r : ℂ) := At.curveToModel_mk (R := R) r 0
abbrev modelBack (r : ℂ) := At.modelBack (R := R) (S := S) r 0
abbrev modelBack_comp_eval (r : ℂ) := At.modelBack_comp_eval (R := R) (S := S) r 0
abbrev model_injective (r : ℂ) := At.model_injective (R := R) (S := S) r 0
abbrev curveToModel_injective (r : ℂ) := At.curveToModel_injective r 0
abbrev modelEval_baseInclusion (r : ℂ) := At.modelEval_baseInclusion (R := R) r 0
abbrev curveToModel_g1 (r : ℂ) := At.curveToModel_g1 (R := R) r 0
abbrev curveToModel_g2 (r : ℂ) := At.curveToModel_g2 (R := R) r 0
abbrev DenominatorQuotient (r : ℂ) := At.DenominatorQuotient r 0
abbrev denominatorQuotientMap (r : ℂ) := At.denominatorQuotientMap r 0
abbrev denominatorPolyMap (r : ℂ) := At.denominatorPolyMap r 0
abbrev denominatorPolyMap_quadric (r : ℂ) := At.denominatorPolyMap_quadric r 0
abbrev denominatorPolyMap_cubic (r : ℂ) := At.denominatorPolyMap_cubic r 0
abbrev denominatorQuotientMap_g1 (r : ℂ) := At.denominatorQuotientMap_g1 r 0
abbrev denominatorPolyMap_baseProduct (r : ℂ) := At.denominatorPolyMap_baseProduct r 0
abbrev baseQuotientToDenominator (r : ℂ) := At.baseQuotientToDenominator r 0
abbrev curveToModel_g1_zero (r : ℂ) := At.curveToModel_g1_zero r 0
abbrev denominatorToModel (r : ℂ) := At.denominatorToModel r 0
abbrev denominatorToModel_mk (r : ℂ) := At.denominatorToModel_mk r 0
abbrev denominatorToModel_injective (r : ℂ) := At.denominatorToModel_injective r 0

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricKoszulTrace

theorem curveG1_regular (r : ℂ) (hr : r ≠ 0) :
    IsSMulRegular (CurveRing r 0) (curveG1 r 0) := At.curveG1_regular r 0 hr

theorem curveG2_regular_mod_curveG1 (r : ℂ) (hr : r ≠ 0) :
    IsSMulRegular (DenominatorQuotient r) (curveG2 r 0) :=
  At.curveG2_regular_mod_curveG1 r 0 hr

theorem degreeNineCechClass_zero_iff_reducedIdeal (r : ℂ) (hr : r ≠ 0)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    CycleQ2GeometricProjectiveCurve.degreeNineCechClass r 0 p hp = 0 ↔ p ∈ reducedIdeal r :=
  degreeNineCechClass_eq_zero_iff_reducedIdeal r hr
    (curveG1_regular r hr) (curveG2_regular_mod_curveG1 r hr) p hp

end SparseSpecializations

#print axioms At.curveG1_regular
#print axioms At.curveG2_regular_mod_curveG1
#print axioms At.degreeNineCechClass_zero_iff_fourGeneratorIdeal
#print axioms degreeNineCechClass_zero_iff_reducedIdeal

end CycleQ2GeometricCurveRegularPair
end
