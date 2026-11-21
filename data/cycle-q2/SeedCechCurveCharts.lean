import Mathlib.RingTheory.LaurentSeries
import Proposal.IncidenceGradedNormalForms
import Proposal.ProtectedHypersurfaceCertificate
import Proposal.SparseSeedQuotientTrace

/-! # The sparse seed curve, its two charts and their coordinate rings -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SeedCechAlgebra.lean -/
section
/-!
# The actual sparse seed curve and its two residue charts

The two monic equations below are the equations obtained from the published
sparse seed after eliminating `w = -x₂²`.  This is deliberately not the smooth
Segre incidence seed, whose cubic has the additional term `x₀³`.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def quadratic (r x y : R) : R[X] := X ^ 2 - C (r * x * y)

theorem quadratic_monic (r x y : R) : (quadratic r x y).Monic :=
  monic_X_pow_sub_C _ (by decide)

abbrev Quadratic (r x y : R) := AdjoinRoot (quadratic r x y)

def a (r x y : R) : Quadratic r x y := AdjoinRoot.root _

theorem a_sq (r x y : R) :
    a r x y ^ 2 = algebraMap R (Quadratic r x y) (r * x * y) := by
  have hh := AdjoinRoot.mk_self (f := quadratic r x y)
  change AdjoinRoot.mk (quadratic r x y) (X ^ 2 - C (r * x * y)) = 0 at hh
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  exact sub_eq_zero.mp hh

def cubic (r i x y : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ (x ^ 2) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y : R) : (cubic r i x y).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y : R) := AdjoinRoot (cubic r i x y)

def x0 (r i x y : R) : CurveAlgebra r i x y :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y : R) : CurveAlgebra r i x y := AdjoinRoot.root _

def base (r i x y : R) : R →+* CurveAlgebra r i x y :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y : R) : x0 r i x y ^ 2 = base r i x y (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y : R) :
    x2 r i x y ^ 3 + (x0 r i x y + base r i x y x) *
        base r i x y y * x2 r i x y +
      x0 r i x y * base r i x y (x ^ 2) +
        base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y)
  change AdjoinRoot.mk (cubic r i x y)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ (x ^ 2) +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y : R) : CurveAlgebra r i x y →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y))).restrictScalars R))

theorem modByMonicHom_map (f : R →+* S) (p : R[X])
    (hp : p.Monic) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom (hp.map f)
      (AdjoinRoot.map f p (p.map f) (dvd_refl _) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  induction z using AdjoinRoot.induction_on
  rename_i z
  have hm : AdjoinRoot.map f p (p.map f) (dvd_refl _) (AdjoinRoot.mk p z) =
      AdjoinRoot.mk (p.map f) (z.map f) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
    exact AdjoinRoot.aeval_eq _
  rw [hm, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
    Polynomial.map_modByMonic _ hp]

theorem modByMonicHom_map_eq (f : R →+* S) (p : R[X]) (q : S[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : p.map f = q) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom hq
      (AdjoinRoot.map f p q (by rw [hpq]) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  subst q
  exact modByMonicHom_map f p hp z

theorem quadratic_map (f : R →+* S) (r x y : R) :
    (quadratic r x y).map f = quadratic (f r) (f x) (f y) := by
  simp [quadratic]

def quadraticMap (f : R →+* S) (r x y : R) :
    Quadratic r x y →+* Quadratic (f r) (f x) (f y) :=
  AdjoinRoot.map f _ _ (by rw [quadratic_map])

@[simp] theorem quadraticMap_a (f : R →+* S) (r x y : R) :
    quadraticMap f r x y (a r x y) = a (f r) (f x) (f y) := by
  simp [quadraticMap, a]

@[simp] theorem quadraticMap_base (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (algebraMap R (Quadratic r x y) z) =
      algebraMap S _ (f z) := by
  simp [quadraticMap, AdjoinRoot.algebraMap_eq]

@[simp] theorem quadraticMap_of (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (AdjoinRoot.of (quadratic r x y) z) =
      AdjoinRoot.of (quadratic (f r) (f x) (f y)) (f z) := by
  simp [quadraticMap]

theorem cubic_map (f : R →+* S) (r i x y : R) :
    (cubic r i x y).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y : R) :
    CurveAlgebra r i x y →+* CurveAlgebra (f r) (f i) (f x) (f y) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x0 r i x y) = x0 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x2 r i x y) = x2 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y z : R) :
    curveMap f r i x y (base r i x y z) = base (f r) (f i) (f x) (f y) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y : R)
    (z : CurveAlgebra r i x y) :
    coefficient (f r) (f i) (f x) (f y) (curveMap f r i x y z) =
      f (coefficient r i x y z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y)
      (cubic_monic (f r) (f i) (f x) (f y)) (cubic_map f r i x y) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x ^ 5 * y

def inverseNumerator (r i x y : R) : CurveAlgebra r i x y :=
  -(x2 r i x y ^ 2 + (x0 r i x y + base r i x y x) * base r i x y y) *
    (base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y * base r i x y (x ^ 2))

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y : R) :
    x2 r i x y * inverseNumerator r i x y = base r i x y (norm r i x y) := by
  have h0 := x0_sq r i x y
  have h2 := x2_cubic r i x y
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y i) * base r i x y y ^ 3 -
      base r i x y i * base r i x y x ^ 3 -
      x0 r i x y * base r i x y x ^ 2) * h2 -
    base r i x y x ^ 4 * h0

def x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (CurveAlgebra r i x y)ˣ where
  val := x2 r i x y
  inv := inverseNumerator r i x y * base r i x y (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (x2Unit r i x y u hu : CurveAlgebra r i x y) = x2 r i x y := rfl

end CycleQ2SeedCech
end
end

/- Component: continuation_3/SeedCechCover.lean -/
section
/-!
# The two actual projective seed charts cover the curve

The proof includes the perturbation by θ x₀³.  Consequently the same two
opens cover both the sparse trace seed (θ = 0) and the smooth incidence
seed (θ = 1).  No smoothness conclusion is inferred from this cover.
-/

namespace CycleQ2SeedCechCover

set_option backward.isDefEq.respectTransparency false

open MvPolynomial CycleQ2SeedTrace

theorem zero_of_chart_equations {R : Type*} [CommRing R] [NoZeroDivisors R]
    (r i θ : R) (hi : i ≠ 0) (h1 : 1 - i ≠ 0) (x : Fin 4 → R)
    (hf : x 0 ^ 2 - r * x 1 * x 3 = 0)
    (hh : x 3 ^ 3 + x 2 ^ 3 + x 1 * x 2 * x 3 + x 0 * x 2 * x 3 +
      x 0 * x 1 ^ 2 - i * (x 1 ^ 3 + x 3 ^ 3) + θ * x 0 ^ 3 = 0)
    (hA : x 1 * x 3 = 0) (hB : x 2 = 0) : x = 0 := by
  have hx0sq : x 0 ^ 2 = 0 := by
    rw [sub_eq_zero] at hf
    rw [hf, mul_assoc, hA, mul_zero]
  have hx0 : x 0 = 0 := eq_zero_of_pow_eq_zero hx0sq
  have hc : (1 - i) * x 3 ^ 3 - i * x 1 ^ 3 = 0 := by
    have hh' : x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) = 0 := by
      simpa only [hx0, hB, zero_pow (by decide : 3 ≠ 0), mul_zero,
        zero_mul, add_zero, zero_add] using hh
    calc
      _ = x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) := by ring
      _ = 0 := hh'
  have hx13 : x 1 = 0 ∧ x 3 = 0 := by
    rcases mul_eq_zero.mp hA with hx1 | hx3
    · have hz : (1 - i) * x 3 ^ 3 = 0 := by simpa [hx1] using hc
      exact ⟨hx1, eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left h1)⟩
    · have hz : i * x 1 ^ 3 = 0 := by simpa [hx3] using hc
      exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left hi), hx3⟩
  funext j
  fin_cases j
  · exact hx0
  · exact hx13.1
  · exact hB
  · exact hx13.2

/-- A nonzero homogeneous representative satisfying the actual curve
equations lies in D₊(x₁x₃) or D₊(x₂). -/
theorem projective_cover (r θ : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0)
    (hh : eval x (h + C θ * X 0 ^ 3) = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  by_contra hcover
  push Not at hcover
  apply hx
  apply zero_of_chart_equations r Complex.I θ Complex.I_ne_zero
    (by norm_num [Complex.ext_iff]) x
  · simpa [relation] using hf
  · simpa [h, b] using hh
  · exact hcover.1
  · exact hcover.2

theorem sparse_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x h = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 0 x hf (by simpa using hh) hx

theorem smooth_seed_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x (h + X 0 ^ 3) = 0)
    (hx : x ≠ 0) : x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 1 x hf (by simpa using hh) hx

/-- The same cover holds at every relevant prime ideal, including the
nonclosed points of the projective curve. -/
theorem prime_chart_cover (r θ : ℂ) (P : Ideal Poly) [P.IsPrime]
    (hf : relation r 0 ∈ P) (hh : h + C θ * X 0 ^ 3 ∈ P)
    (hrelevant : ∃ j : Fin 4, X j ∉ P) :
    X 1 * X 3 ∉ P ∨ X 2 ∉ P := by
  by_contra hcover
  push Not at hcover
  let π : Poly →+* Poly ⧸ P := Ideal.Quotient.mk P
  have hi : π (C Complex.I) ≠ 0 := by
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne Complex.I_ne_zero
    simpa only [RingHom.comp_apply, map_zero] using hn
  have h1 : 1 - π (C Complex.I) ≠ 0 := by
    have hc : (1 : ℂ) - Complex.I ≠ 0 := by norm_num [Complex.ext_iff]
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne hc
    simpa only [RingHom.comp_apply, map_sub, map_one, map_zero] using hn
  have hf' : π (relation r 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hh' : π (h + C θ * X 0 ^ 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hA : π (X 1 * X 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.1
  have hB : π (X 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.2
  have hz : (fun j : Fin 4 => π (X j)) = 0 := by
    apply zero_of_chart_equations (π (C r)) (π (C Complex.I)) (π (C θ)) hi h1
    · simpa [relation] using hf'
    · simpa [h, b] using hh'
    · simpa only [map_mul] using hA
    · exact hB
  obtain ⟨j, hj⟩ := hrelevant
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hz j))

section ProjectiveSpectrum

open CycleQ2SupportEquation
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_coordinate_exists (p : AmbientProjectiveSpace 3) :
    ∃ j : Fin 4, X j ∉ p.asHomogeneousIdeal.toIdeal := by
  by_contra hn
  push Not at hn
  have hvars : idealOfVars (Fin 4) ℂ ≤ p.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hn j
  apply p.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (ambientGrading 3)).mpr
  intro d hd q hq
  apply hvars
  have hqhom : q.IsHomogeneous d := hq
  have hmem : q ∈ idealOfVars (Fin 4) ℂ ^ 1 := by
    apply (mem_pow_idealOfVars_iff 1 q).mpr
    intro e he
    have heq : e.degree = d := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hqhom (mem_support_iff.mp he)
    rw [heq]
    exact hd
  simpa only [pow_one] using hmem

/-- The actual closed curve in the standard projective spectrum. -/
def projectiveCurve (r θ : ℂ) : Set (AmbientProjectiveSpace 3) :=
  ProjectiveSpectrum.zeroLocus (ambientGrading 3)
    ({relation r 0, h + C θ * X 0 ^ 3} : Set Poly)

/-- The two genuine standard opens cover the closed projective seed curve. -/
theorem projectiveCurve_covered (r θ : ℂ) :
    projectiveCurve r θ ⊆
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 1 * X 3) :
        Set (AmbientProjectiveSpace 3)) ∪
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 2) :
        Set (AmbientProjectiveSpace 3)) := by
  intro p hp
  have hf : relation r 0 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  have hh : h + C θ * X 0 ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  exact prime_chart_cover r θ p.asHomogeneousIdeal.toIdeal hf hh
    (projective_coordinate_exists p)

end ProjectiveSpectrum

end CycleQ2SeedCechCover

#print axioms CycleQ2SeedCechCover.projective_cover
#print axioms CycleQ2SeedCechCover.prime_chart_cover
#print axioms CycleQ2SeedCechCover.projectiveCurve_covered
end

/- Component: continuation_3/cylinder_bridge/SeedCechCharts.lean -/
section
/-!
# Honest power-series charts for the sparse curve Čech trace

At each endpoint of the finite map to P¹ with coordinates (x₁:x₃), x₂ is
already a unit over the power-series ring.  Thus every element of the x₂-open
has zero endpoint Laurent residue.  This is the first full coboundary check;
it applies to all powers of the denominator.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech

abbrev PS := PowerSeries ℂ
abbrev LS := LaurentSeries ℂ

def endpointX : Bool → PS
  | false => 1
  | true => PowerSeries.X

def endpointY : Bool → PS
  | false => PowerSeries.X
  | true => 1

def seriesMap : PS →+* LS := HahnSeries.ofPowerSeries ℤ ℂ

abbrev PowerChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

abbrev LaurentChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def chartEmbedding (r : ℂ) (e : Bool) : PowerChart r e →+* LaurentChart r e :=
  curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e)

def endpointResidue (r : ℂ) (e : Bool) : LaurentChart r e →+ ℂ :=
  (HahnSeries.coeff.addMonoidHom (-1 : ℤ)).comp
    ((coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
      (seriesMap (endpointX e)) (seriesMap (endpointY e))).toAddMonoidHom)

theorem endpointResidue_integral (r : ℂ) (e : Bool) (z : PowerChart r e) :
    endpointResidue r e (chartEmbedding r e z) = 0 := by
  change (coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))
    (curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) z)).coeff (-1) = 0
  rw [coefficient_curveMap]
  exact PowerSeries.coeff_coe _ _ |>.trans (by norm_num)

theorem endpointNorm_isUnit (r : ℂ) (e : Bool) :
    IsUnit (norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [isUnit_iff_ne_zero]
  cases e <;>
    norm_num [norm, endpointX, endpointY, Complex.ext_iff, Complex.I_sq]

def endpointNormUnit (r : ℂ) (e : Bool) : PSˣ := (endpointNorm_isUnit r e).unit

theorem endpointNormUnit_spec (r : ℂ) (e : Bool) :
    (endpointNormUnit r e : PS) = norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := (endpointNorm_isUnit r e).unit_spec

def powerX2Unit (r : ℂ) (e : Bool) : (PowerChart r e)ˣ :=
  x2Unit _ _ _ _ (endpointNormUnit r e) (endpointNormUnit_spec r e)

def laurentX2Unit (r : ℂ) (e : Bool) : (LaurentChart r e)ˣ :=
  Units.map (chartEmbedding r e) (powerX2Unit r e)

/-- Every x₂-localized polynomial expression is integral in both endpoint
charts, so its Laurent residue vanishes for arbitrary denominator powers. -/
theorem endpointResidue_x2_open (r : ℂ) (e : Bool) (z : PowerChart r e) (n : ℕ) :
    endpointResidue r e
      (chartEmbedding r e z * ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n) = 0 := by
  have heq : chartEmbedding r e z * ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n =
      chartEmbedding r e (z * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ n) := by
    simp [laurentX2Unit]
  rw [heq]
  exact endpointResidue_integral r e _

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.endpointResidue_x2_open
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechCoefficient.lean -/
section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open Polynomial

variable {R : Type*} [CommRing R] [Nontrivial R]

instance quadratic_nontrivial (r x y : R) : Nontrivial (Quadratic r x y) :=
  Ideal.Quotient.nontrivial_iff.mpr (by
    intro hh
    have he := (quadratic_monic r x y).eq_one_of_isUnit
      (Ideal.span_singleton_eq_top.mp hh)
    have hn := congrArg Polynomial.natDegree he
    rw [quadratic, natDegree_X_pow_sub_C, natDegree_one] at hn
    omega)

theorem cubic_degree (r i x y : R) : (cubic r i x y).degree = 3 := by
  unfold cubic
  rw [add_assoc]
  have hl : (C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ (x ^ 2) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))).degree < 3 := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  rw [degree_add_eq_left_of_degree_lt (by simpa using hl)]
  simp

theorem coefficient_small_monomial (r i x y z : R) (j k : ℕ)
    (hj : j < 2) (hk : k < 3) :
    coefficient r i x y (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k) =
      if j = 1 ∧ k = 2 then z else 0 := by
  have hc : AdjoinRoot.modByMonicHom (cubic_monic r i x y)
      (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k) =
      C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k := by
    have heq : base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k =
        AdjoinRoot.mk (cubic r i x y)
          (C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k) := by
      simp [base, x0, x2, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (cubic_monic r i x y)).mpr
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by
      rw [cubic_degree]
      exact_mod_cast hk)
  have hq : AdjoinRoot.modByMonicHom (quadratic_monic r x y)
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) = C z * X ^ j := by
    have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
        AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
      simp [a, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr
    apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
    rw [quadratic, degree_X_pow_sub_C (by decide)]
    exact_mod_cast hj
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y))
      (base r i x y z * x0 r i x y ^ j * x2 r i x y ^ k)).coeff 2)).coeff 1 = _
  rw [hc]
  simp only [coeff_C_mul_X_pow]
  by_cases hk2 : k = 2
  · subst k
    simp only [ite_true, hq, coeff_C_mul_X_pow]
    simp [eq_comm]
  · simp [hk2, eq_comm]

theorem coefficient_base_mul (r i x y z : R) (v : CurveAlgebra r i x y) :
    coefficient r i x y (base r i x y z * v) = z * coefficient r i x y v := by
  unfold base
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R
    (Quadratic r x y) (CurveAlgebra r i x y)]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (coefficient r i x y).map_smul z v

def quadraticCoefficient (r x y : R) : Quadratic r x y →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp (AdjoinRoot.modByMonicHom (quadratic_monic r x y))

theorem coefficient_quadratic (r i x y : R) (q : Quadratic r x y) (k : ℕ)
    (hk : k < 3) :
    coefficient r i x y
      (algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q * x2 r i x y ^ k) =
      if k = 2 then quadraticCoefficient r x y q else 0 := by
  have heq : algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q * x2 r i x y ^ k =
      AdjoinRoot.mk (cubic r i x y) (C q * X ^ k) := by
    simp [x2, AdjoinRoot.algebraMap_eq]
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y))
      (algebraMap (Quadratic r x y) (CurveAlgebra r i x y) q *
        x2 r i x y ^ k)).coeff 2)).coeff 1 = _
  rw [heq, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (cubic_monic r i x y)).mpr (by
      apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
      rw [cubic_degree]
      exact_mod_cast hk)]
  simp only [coeff_C_mul_X_pow]
  by_cases h : k = 2
  · subst k
    rfl
  · simp only [Ne.symm h, h, if_false, map_zero, coeff_zero]

theorem quadraticCoefficient_small (r x y z : R) (j : ℕ) (hj : j < 2) :
    quadraticCoefficient r x y
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) =
      if j = 1 then z else 0 := by
  have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
      AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
    simp [a, AdjoinRoot.algebraMap_eq]
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (algebraMap R (Quadratic r x y) z * a r x y ^ j)).coeff 1 = _
  rw [heq, AdjoinRoot.modByMonicHom_mk,
    (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr (by
      apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
      rw [quadratic, degree_X_pow_sub_C (by decide)]
      exact_mod_cast hj)]
  simp [coeff_C_mul_X_pow, eq_comm]

end CycleQ2SeedCech
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechNormal.lean -/
section
/-! Homogeneous normal forms for the actual published sparse curve. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace CycleQ2IncidenceNormalForm
open scoped MonomialOrder

@[simp] private lemma vec4_two {α : Type*} (a b c d : α) :
    ![a,b,c,d] (2 : Fin 4) = c := rfl
@[simp] private lemma vec4_three {α : Type*} (a b c d : α) :
    ![a,b,c,d] (3 : Fin 4) = d := rfl
@[simp] private lemma vec5_two {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (2 : Fin 5) = c := rfl
@[simp] private lemma vec5_three {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (3 : Fin 5) = d := rfl
@[simp] private lemma vec5_four {α : Type*} (a b c d e : α) :
    ![a,b,c,d,e] (4 : Fin 5) = e := rfl

def curveWeight : Exp →+ ℕ where
  toFun d := 3 * d 0 + d 1 + 3 * d 2 + d 3
  map_zero' := by simp
  map_add' d e := by simp only [Finsupp.add_apply]; omega

def curveOrder : MonomialOrder (Fin 4) := weightedOrder MonomialOrder.lex curveWeight

def curveF1 (r : ℂ) : Poly := relation r 0
def curveH : Poly := h
def curveIdeal (r : ℂ) : Ideal Poly := Ideal.span {curveF1 r, curveH}

def hTailExponent (j : Fin 5) : Exp :=
  ![exponent ![0,0,0,3], exponent ![0,1,1,1], exponent ![1,0,1,1],
    exponent ![1,2,0,0], exponent ![0,3,0,0]] j

def hTailCoefficient (j : Fin 5) : ℂ := ![1 - Complex.I, 1, 1, 1, -Complex.I] j

theorem curveF1_shape (r : ℂ) :
    curveF1 r = monomial (exponent ![2,0,0,0]) 1 +
      ∑ _j : Fin 1, monomial (exponent ![0,1,0,1]) (-r) := by
  simp only [Fin.sum_univ_one]
  rw [monomial_eq_C_mul_mon, monomial_eq_C_mul_mon]
  simp [curveF1, relation, mon] <;> ring

theorem curveH_shape :
    curveH = monomial (exponent ![0,0,3,0]) 1 +
      ∑ j : Fin 5, monomial (hTailExponent j) (hTailCoefficient j) := by
  simp only [Fin.sum_univ_succ, hTailExponent, hTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    Matrix.cons_val_succ, Fin.reduceSucc,
    monomial_eq_C_mul_mon]
  norm_num [curveH, h, b, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem curveF1_leading_data (r : ℂ) :
    curveOrder.degree (curveF1 r) = exponent ![2,0,0,0] ∧ curveOrder.Monic (curveF1 r) := by
  rw [curveF1_shape]
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    change (0 : ℕ) < 6
    decide
  · intro j
    apply weightedOrder_lt_of_weight_lt
    change (2 : ℕ) < 6
    decide

theorem curveH_leading_data :
    curveOrder.degree curveH = exponent ![0,0,3,0] ∧ curveOrder.Monic curveH := by
  rw [curveH_shape]
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    change (0 : ℕ) < 9
    decide
  · intro j
    apply weightedOrder_lt_of_weight_lt
    fin_cases j <;> norm_num [curveWeight, hTailExponent, Matrix.cons_val_succ, Fin.reduceSucc]

theorem curve_leading_coprime (r : ℂ) :
    ∀ j, curveOrder.degree (curveF1 r) j = 0 ∨ curveOrder.degree curveH j = 0 := by
  rw [(curveF1_leading_data r).1, curveH_leading_data.1]
  intro j
  fin_cases j <;> simp

theorem mon_homogeneous (a b c d : ℕ) : (mon a b c d).IsHomogeneous (a+b+c+d) := by
  rw [mon_eq_monomial]
  apply isHomogeneous_monomial
  norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc,
    Matrix.cons_val_succ, Fin.reduceSucc]

theorem curveF1_homogeneous (r : ℂ) : (curveF1 r).IsHomogeneous 2 := by
  have h0 : (mon 2 0 0 0).IsHomogeneous 2 := by simpa using mon_homogeneous 2 0 0 0
  have h1 : (mon 0 1 0 1).IsHomogeneous 2 := by simpa using mon_homogeneous 0 1 0 1
  simpa [curveF1, relation, mon, mul_assoc] using h0.sub (h1.C_mul r)

theorem curveH_homogeneous : curveH.IsHomogeneous 3 := by
  have hm (a b c d : ℕ) (hd : a+b+c+d=3) : (mon a b c d).IsHomogeneous 3 := by
    simpa only [hd] using mon_homogeneous a b c d
  have h1 := (hm 0 0 0 3 (by omega)).add (hm 0 0 3 0 (by omega))
  have h2 := h1.add (hm 0 1 1 1 (by omega))
  have h3 := h2.add (hm 1 0 1 1 (by omega))
  have h4 := h3.add (hm 1 2 0 0 (by omega))
  have h5 := h4.sub (((hm 0 3 0 0 (by omega)).add (hm 0 0 0 3 (by omega))).C_mul Complex.I)
  simpa [curveH, h, b, mon, mul_assoc] using h5

def CurveReduced (p : Poly) : Prop := ∀ d ∈ p.support, d 0 < 2 ∧ d 2 < 3

theorem curveReduced_iff (r : ℂ) (p : Poly) :
    CurveReduced p ↔ Reduced curveOrder (curveF1 r) curveH p := by
  simp only [CurveReduced, Reduced, (curveF1_leading_data r).1, curveH_leading_data.1]
  apply forall_congr'
  intro d
  apply forall_congr'
  intro hd
  have he0 : exponent ![2,0,0,0] = Finsupp.single (0 : Fin 4) 2 := by
    ext j; fin_cases j <;> simp
  have he2 : exponent ![0,0,3,0] = Finsupp.single (2 : Fin 4) 3 := by
    ext j; fin_cases j <;> simp
  rw [he0, he2, Finsupp.single_le_iff, Finsupp.single_le_iff]
  omega

/-- Every homogeneous function on the actual curve has a homogeneous
representative whose x₀ and x₂ exponents are respectively less than 2 and 3. -/
theorem exists_homogeneous_curve_normal (r : ℂ) (p : Poly) (d : ℕ)
    (hp : p.IsHomogeneous d) :
    ∃ q : Poly, CurveReduced q ∧ q.IsHomogeneous d ∧ p - q ∈ curveIdeal r := by
  obtain ⟨u,v,q,hpq,hq⟩ := exists_reduced_representation curveOrder (curveF1 r) curveH p
    (curveF1_leading_data r).2 curveH_leading_data.2
  refine ⟨q, (curveReduced_iff r q).mpr hq, ?_, ?_⟩
  · exact reduced_isHomogeneous curveOrder (curveF1_leading_data r).2
      curveH_leading_data.2 (curve_leading_coprime r)
      (curveF1_homogeneous r) curveH_homogeneous hp hq hpq
  · apply Ideal.mem_span_pair.mpr
    exact ⟨u,v,by rw [hpq]; ring⟩

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.exists_homogeneous_curve_normal
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechGeneralCubic.lean -/
section
/-! A monic cubic over the actual quadratic curve algebra, allowing an
arbitrary coefficient of x₀ in the constant term.  This covers the whole
family h+θx₀³ after reduction modulo x₀²-rx₁x₃. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2CechLinearCubic
open Polynomial CycleQ2SeedCech
variable {R S : Type*} [CommRing R] [CommRing S]

def cubic (r i x y q : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y q : R) : (cubic r i x y q).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y q : R) := AdjoinRoot (cubic r i x y q)

def x0 (r i x y q : R) : CurveAlgebra r i x y q :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y q : R) : CurveAlgebra r i x y q := AdjoinRoot.root _

def base (r i x y q : R) : R →+* CurveAlgebra r i x y q :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y q : R) : x0 r i x y q ^ 2 = base r i x y q (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y q : R) :
    x2 r i x y q ^ 3 + (x0 r i x y q + base r i x y q x) *
        base r i x y q y * x2 r i x y q +
      x0 r i x y q * base r i x y q q +
        base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y q)
  change AdjoinRoot.mk (cubic r i x y q)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ q +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y q : R) : CurveAlgebra r i x y q →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y q))).restrictScalars R))

theorem cubic_map (f : R →+* S) (r i x y q : R) :
    (cubic r i x y q).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) (f q) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y q : R) :
    CurveAlgebra r i x y q →+* CurveAlgebra (f r) (f i) (f x) (f y) (f q) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x0 r i x y q) = x0 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y q : R) :
    curveMap f r i x y q (x2 r i x y q) = x2 (f r) (f i) (f x) (f y) (f q) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y q z : R) :
    curveMap f r i x y q (base r i x y q z) = base (f r) (f i) (f x) (f y) (f q) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y q : R)
    (z : CurveAlgebra r i x y q) :
    coefficient (f r) (f i) (f x) (f y) (f q) (curveMap f r i x y q z) =
      f (coefficient r i x y q z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y) (f q)))
      (curveMap f r i x y q z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y q)
      (cubic_monic (f r) (f i) (f x) (f y) (f q)) (cubic_map f r i x y q) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y q : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x * y * q ^ 2

def inverseNumerator (r i x y q : R) : CurveAlgebra r i x y q :=
  -(x2 r i x y q ^ 2 + (x0 r i x y q + base r i x y q x) * base r i x y q y) *
    (base r i x y q ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y q * base r i x y q q)

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y q : R) :
    x2 r i x y q * inverseNumerator r i x y q = base r i x y q (norm r i x y q) := by
  have h0 := x0_sq r i x y q
  have h2 := x2_cubic r i x y q
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y q i) * base r i x y q y ^ 3 -
      base r i x y q i * base r i x y q x ^ 3 -
      x0 r i x y q * base r i x y q q) * h2 -
    base r i x y q q ^ 2 * h0

def x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (CurveAlgebra r i x y q)ˣ where
  val := x2 r i x y q
  inv := inverseNumerator r i x y q * base r i x y q (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y q : R) (u : Rˣ) (hu : (u : R) = norm r i x y q) :
    (x2Unit r i x y q u hu : CurveAlgebra r i x y q) = x2 r i x y q := rfl

variable [Nontrivial R]

theorem cubic_degree (r i x y q : R) : (cubic r i x y q).degree = 3 := by
  unfold cubic
  rw [add_assoc]
  have hl : (C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ q +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))).degree < 3 := by
    apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_le _) (by norm_num)
    · exact lt_of_le_of_lt degree_C_le (by norm_num)
  rw [degree_add_eq_left_of_degree_lt (by simpa using hl)]
  simp

theorem coefficient_small_monomial (r i x y q z : R) (j k : ℕ)
    (hj : j < 2) (hk : k < 3) :
    coefficient r i x y q (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      if j = 1 ∧ k = 2 then z else 0 := by
  have hc : AdjoinRoot.modByMonicHom (cubic_monic r i x y q)
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k) =
      C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k := by
    have heq : base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k =
        AdjoinRoot.mk (cubic r i x y q)
          (C (algebraMap R (Quadratic r x y) z * a r x y ^ j) * X ^ k) := by
      simp [base, x0, x2, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (cubic_monic r i x y q)).mpr
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by
      rw [cubic_degree]
      exact_mod_cast hk)
  have hq : AdjoinRoot.modByMonicHom (quadratic_monic r x y)
      (algebraMap R (Quadratic r x y) z * a r x y ^ j) = C z * X ^ j := by
    have heq : algebraMap R (Quadratic r x y) z * a r x y ^ j =
        AdjoinRoot.mk (quadratic r x y) (C z * X ^ j) := by
      simp [a, AdjoinRoot.algebraMap_eq]
    rw [heq, AdjoinRoot.modByMonicHom_mk]
    apply (modByMonic_eq_self_iff (quadratic_monic r x y)).mpr
    apply lt_of_le_of_lt (degree_C_mul_X_pow_le _ _)
    rw [quadratic, degree_X_pow_sub_C (by decide)]
    exact_mod_cast hj
  change ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
    (((AdjoinRoot.modByMonicHom (cubic_monic r i x y q))
      (base r i x y q z * x0 r i x y q ^ j * x2 r i x y q ^ k)).coeff 2)).coeff 1 = _
  rw [hc]
  simp only [coeff_C_mul_X_pow]
  by_cases hk2 : k = 2
  · subst k
    simp only [ite_true, hq, coeff_C_mul_X_pow]
    simp [eq_comm]
  · simp [hk2, eq_comm]

theorem coefficient_base_mul (r i x y q z : R) (v : CurveAlgebra r i x y q) :
    coefficient r i x y q (base r i x y q z * v) = z * coefficient r i x y q v := by
  unfold base
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply R
    (Quadratic r x y) (CurveAlgebra r i x y q)]
  simpa only [Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply] using
    (coefficient r i x y q).map_smul z v

end CycleQ2CechLinearCubic

#print axioms CycleQ2CechLinearCubic.x2_mul_inverseNumerator
#print axioms CycleQ2CechLinearCubic.coefficient_small_monomial
end
end
