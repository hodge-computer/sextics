import HodgeComputer.Constructions.QuadraticCovers.LaurentJets
import HodgeComputer.Constructions.EllipticCompanions.Residues
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Target-independent algebraic-cover residue utilities over any field:
1. Pure-ring 4×4 Schur complement determinant formula `det_J_fib_schur`.
2. Division-free quadratic remainder formulas `remDeg4_P1/P0`, `remDeg3_d1/d0`, and
   the two-root resultant-type identity `remDeg4_comb_roots`.
3. 5-point Lagrange interpolation `interp4`, polynomial-degree predicate `IsPolyDeg`,
   and scaled Laurent valuation bounds `ValLead.interp4_of` and `HasValGe.interp4_scaled`.
4. Simple-pole residue formula `simplePole_residue` and functorial base change
   `mapRatFunc` preserving regularity, finite residues, and the residue at infinity.

Extracted from the `symmetric-sextic-residual` construction (`benediamond`). -/

noncomputable section
namespace QuadraticCovers
open CrossedRationalResidue Polynomial
open scoped BigOperators Matrix LaurentSeries

/-- Pure-ring 4×4 Schur complement: if row 0 has `M 0 0 = M 0 1 = 0` and
`M * ![a', b', 1, v'] = ![0, 0, 0, E3_dot]`, then
`M.det = M 0 3 * (M 1 1 * M 2 0 - M 1 0 * M 2 1) * E3_dot`. -/
theorem det_J_fib_schur {R : Type*} [CommRing R] (M : Matrix (Fin 4) (Fin 4) R)
    (a' b' v' E3_dot : R)
    (h00 : M 0 0 = 0) (h01 : M 0 1 = 0)
    (h0 : M 0 2 + M 0 3 * v' = 0)
    (h1 : M 1 0 * a' + M 1 1 * b' + M 1 2 + M 1 3 * v' = 0)
    (h2 : M 2 0 * a' + M 2 1 * b' + M 2 2 + M 2 3 * v' = 0)
    (h3 : M 3 0 * a' + M 3 1 * b' + M 3 2 + M 3 3 * v' = E3_dot) :
    M.det = M 0 3 * (M 1 1 * M 2 0 - M 1 0 * M 2 1) * E3_dot := by
  let Rmat : Matrix (Fin 4) (Fin 4) R :=
    Matrix.of ![![1, 0, a', 0],
                ![0, 1, b', 0],
                ![0, 0, 1, 0],
                ![0, 0, v', 1]]
  have hRdet : Rmat.det = 1 := by
    rw [Matrix.det_succ_column_zero]
    simp only [Fin.sum_univ_four, Rmat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
      Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl,
      pow_zero, one_mul, Fin.isValue]
    have hsub : Rmat.submatrix (Fin.succAbove 0) Fin.succ =
        Matrix.of ![![1, b', 0], ![0, 1, 0], ![0, v', 1]] := by
      ext i j; fin_cases i <;> fin_cases j <;> rfl
    rw [hsub]
    simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
    ring
  let Mres : Matrix (Fin 4) (Fin 4) R :=
    Matrix.of ![![0, 0, 0, M 0 3],
                ![M 1 0, M 1 1, 0, M 1 3],
                ![M 2 0, M 2 1, 0, M 2 3],
                ![M 3 0, M 3 1, E3_dot, M 3 3]]
  have hMR : M * Rmat = Mres := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    fin_cases i <;> fin_cases j <;>
      (simp only [Rmat, Mres, Matrix.of_apply, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
         Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
         Matrix.head_cons, Matrix.tail_cons, Fin.isValue, mul_one, mul_zero, zero_mul,
         add_zero, zero_add, h00, h01])
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  have hdet : M.det = (M * Rmat).det := by rw [Matrix.det_mul, hRdet, mul_one]
  rw [hdet, hMR, Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four, Mres, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Fin.val_zero, Fin.val_one, Fin.val_two, show (3 : Fin 4).val = 3 from rfl,
    Fin.isValue]
  have hsub : Mres.submatrix Fin.succ (Fin.succAbove 3) =
      Matrix.of ![![M 1 0, M 1 1, 0], ![M 2 0, M 2 1, 0], ![M 3 0, M 3 1, E3_dot]] := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [hsub]
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.isValue]
  ring

/-- Division-free quadratic remainder of a degree-4 polynomial `p4 z^4 + ... + p0`
modulo `q2 z^2 + q1 z + q0`, scaled by `q2^3`. -/
def remDeg4_P1 {R : Type*} [CommRing R] (q2 q1 q0 p4 p3 p2 p1 : R) : R :=
  let r3 := q2 * p3 - q1 * p4
  let r2 := q2 * p2 - q0 * p4
  let s2 := q2 * r2 - q1 * r3
  let s1 := q2 ^ 2 * p1 - q0 * r3
  q2 * s1 - q1 * s2

def remDeg4_P0 {R : Type*} [CommRing R] (q2 q1 q0 p4 p3 p2 p0 : R) : R :=
  let r3 := q2 * p3 - q1 * p4
  let r2 := q2 * p2 - q0 * p4
  let s2 := q2 * r2 - q1 * r3
  q2 ^ 3 * p0 - q0 * s2

def remDeg3_d1 {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 : R) : R :=
  let t2 := q2 * e2 - q1 * e3
  let t1 := q2 * e1 - q0 * e3
  q2 * t1 - q1 * t2

def remDeg3_d0 {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e0 : R) : R :=
  let t2 := q2 * e2 - q1 * e3
  let t0 := q2 * e0
  q2 * t0 - q0 * t2

lemma remDeg4_eq {R : Type*} [CommRing R] (q2 q1 q0 p4 p3 p2 p1 p0 z : R) :
    q2 ^ 3 * (p4 * z ^ 4 + p3 * z ^ 3 + p2 * z ^ 2 + p1 * z + p0) =
      (q2 ^ 2 * p4 * z ^ 2 + q2 * (q2 * p3 - q1 * p4) * z +
        (q2 * (q2 * p2 - q0 * p4) - q1 * (q2 * p3 - q1 * p4))) *
        (q2 * z ^ 2 + q1 * z + q0) +
      (remDeg4_P1 q2 q1 q0 p4 p3 p2 p1 * z + remDeg4_P0 q2 q1 q0 p4 p3 p2 p0) := by
  simp only [remDeg4_P1, remDeg4_P0]; ring

lemma remDeg3_eq {R : Type*} [CommRing R] (q2 q1 q0 e3 e2 e1 e0 z : R) :
    q2 ^ 2 * (e3 * z ^ 3 + e2 * z ^ 2 + e1 * z + e0) =
      (q2 * e3 * z + (q2 * e2 - q1 * e3)) * (q2 * z ^ 2 + q1 * z + q0) +
      (remDeg3_d1 q2 q1 q0 e3 e2 e1 * z + remDeg3_d0 q2 q1 q0 e3 e2 e0) := by
  simp only [remDeg3_d1, remDeg3_d0]; ring

/-- Two-root evaluation identity for `P1 * d0 - P0 * d1`. -/
lemma remDeg4_comb_roots {R : Type*} [CommRing R]
    (q2 e3 e2 e1 e0 p4 p3 p2 p1 p0 z1 z2 : R) :
    let q1 := -q2 * (z1 + z2)
    let q0 := q2 * z1 * z2
    let d1 := remDeg3_d1 q2 q1 q0 e3 e2 e1
    let d0 := remDeg3_d0 q2 q1 q0 e3 e2 e0
    let P1 := remDeg4_P1 q2 q1 q0 p4 p3 p2 p1
    let P0 := remDeg4_P0 q2 q1 q0 p4 p3 p2 p0
    let P := fun z => p4 * z ^ 4 + p3 * z ^ 3 + p2 * z ^ 2 + p1 * z + p0
    let E3 := fun z => e3 * z ^ 3 + e2 * z ^ 2 + e1 * z + e0
    (P1 * d0 - P0 * d1) * (z1 - z2) = q2 ^ 5 * (P z1 * E3 z2 - P z2 * E3 z1) := by
  intro q1 q0 d1 d0 P1 P0 P E3
  have hq1 : q2 * z1 ^ 2 + q1 * z1 + q0 = 0 := by simp only [q1, q0]; ring
  have hq2 : q2 * z2 ^ 2 + q1 * z2 + q0 = 0 := by simp only [q1, q0]; ring
  have hP1 : q2 ^ 3 * P z1 = P1 * z1 + P0 := by
    have h := remDeg4_eq q2 q1 q0 p4 p3 p2 p1 p0 z1; rw [hq1, mul_zero, zero_add] at h; exact h
  have hP2 : q2 ^ 3 * P z2 = P1 * z2 + P0 := by
    have h := remDeg4_eq q2 q1 q0 p4 p3 p2 p1 p0 z2; rw [hq2, mul_zero, zero_add] at h; exact h
  have hE1 : q2 ^ 2 * E3 z1 = d1 * z1 + d0 := by
    have h := remDeg3_eq q2 q1 q0 e3 e2 e1 e0 z1; rw [hq1, mul_zero, zero_add] at h; exact h
  have hE2 : q2 ^ 2 * E3 z2 = d1 * z2 + d0 := by
    have h := remDeg3_eq q2 q1 q0 e3 e2 e1 e0 z2; rw [hq2, mul_zero, zero_add] at h; exact h
  linear_combination -(d1 * z2 + d0) * hP1 + (d1 * z1 + d0) * hP2 -
    q2 ^ 3 * P z1 * hE2 + q2 ^ 3 * P z2 * hE1

/-- 5-point Lagrange interpolation at `{0, 1, -1, 2, -2}` extracting `(p4, p3, p2, p1, p0)`. -/
def interp4 {F : Type*} [Field F] (f : F → F) : F × F × F × F × F :=
  let f0 := f 0; let f1 := f 1; let fm1 := f (-1); let f2 := f 2; let fm2 := f (-2)
  ( (-4 * (f1 + fm1) + (f2 + fm2) + 6 * f0) / 24,
    (-2 * (f1 - fm1) + (f2 - fm2)) / 12,
    (16 * (f1 + fm1) - (f2 + fm2) - 30 * f0) / 24,
    (8 * (f1 - fm1) - (f2 - fm2)) / 12,
    f0 )

lemma interp4_eq {F : Type*} [Field F] [CharZero F] {f : F → F} {c4 c3 c2 c1 c0 : F}
    (hf : ∀ z : F, f z = c4 * z ^ 4 + c3 * z ^ 3 + c2 * z ^ 2 + c1 * z + c0) :
    interp4 f = (c4, c3, c2, c1, c0) := by
  simp only [interp4, hf]
  refine Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring) (Prod.ext (by ring) (by ring))))

lemma map_interp4 {F E : Type*} [Field F] [Field E] [CharZero F] [CharZero E]
    (φ : F →+* E) (f : F → F) (g : E → E) (hfg : ∀ z : F, φ (f z) = g (φ z)) :
    let (p4, p3, p2, p1, p0) := interp4 f
    (φ p4, φ p3, φ p2, φ p1, φ p0) = interp4 g := by
  simp only [interp4]
  have h0 := hfg 0; have h1 := hfg 1; have hm1 := hfg (-1); have h2 := hfg 2; have hm2 := hfg (-2)
  simp only [map_zero, map_one, map_neg, map_ofNat] at h0 h1 hm1 h2 hm2
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ h0))) <;>
    simp only [map_div₀, map_add, map_sub, map_mul, map_neg, map_ofNat, h0, h1, hm1, h2, hm2]

/-- Predicate asserting `f : F → F` is represented by a polynomial of degree `≤ d`. -/
def IsPolyDeg {F : Type*} [Field F] (d : ℕ) (f : F → F) : Prop :=
  ∃ P : F[X], P.natDegree ≤ d ∧ ∀ z : F, f z = P.eval z

namespace IsPolyDeg
variable {F : Type*} [Field F]

lemma const (c : F) : IsPolyDeg 0 (fun _ => c) :=
  ⟨C c, by simp, fun _ => by simp⟩

lemma linear (a1 a0 : F) : IsPolyDeg 1 (fun z => a1 * z + a0) :=
  ⟨C a1 * X + C a0, by
    refine le_trans (natDegree_add_le _ _) (max_le ?_ (by simp))
    exact le_trans (natDegree_C_mul_le _ _) (by simp),
    fun z => by simp⟩

lemma mono {d1 d2 : ℕ} {f : F → F} (h : d1 ≤ d2) (hf : IsPolyDeg d1 f) : IsPolyDeg d2 f :=
  let ⟨P, hd, he⟩ := hf; ⟨P, hd.trans h, he⟩

lemma add {d : ℕ} {f g : F → F} (hf : IsPolyDeg d f) (hg : IsPolyDeg d g) :
    IsPolyDeg d (fun z => f z + g z) := by
  rcases hf with ⟨P, hP, heP⟩; rcases hg with ⟨Q, hQ, heQ⟩
  exact ⟨P + Q, (natDegree_add_le P Q).trans (max_le hP hQ), fun z => by simp [heP z, heQ z]⟩

lemma sub {d : ℕ} {f g : F → F} (hf : IsPolyDeg d f) (hg : IsPolyDeg d g) :
    IsPolyDeg d (fun z => f z - g z) := by
  rcases hf with ⟨P, hP, heP⟩; rcases hg with ⟨Q, hQ, heQ⟩
  exact ⟨P - Q, (natDegree_sub_le P Q).trans (max_le hP hQ), fun z => by simp [heP z, heQ z]⟩

lemma neg {d : ℕ} {f : F → F} (hf : IsPolyDeg d f) : IsPolyDeg d (fun z => -f z) := by
  rcases hf with ⟨P, hP, heP⟩
  exact ⟨-P, by simpa using hP, fun z => by simp [heP z]⟩

lemma mul {d1 d2 : ℕ} {f g : F → F} (hf : IsPolyDeg d1 f) (hg : IsPolyDeg d2 g) :
    IsPolyDeg (d1 + d2) (fun z => f z * g z) := by
  rcases hf with ⟨P, hP, heP⟩; rcases hg with ⟨Q, hQ, heQ⟩
  exact ⟨P * Q, natDegree_mul_le.trans (Nat.add_le_add hP hQ), fun z => by simp [heP z, heQ z]⟩

lemma smul_left {d : ℕ} (c : F) {f : F → F} (hf : IsPolyDeg d f) :
    IsPolyDeg d (fun z => c * f z) := by
  simpa using (const c).mul hf

lemma smul_right {d : ℕ} {f : F → F} (hf : IsPolyDeg d f) (c : F) :
    IsPolyDeg d (fun z => f z * c) := by
  simpa using hf.mul (const c)

lemma div_const {d : ℕ} {f : F → F} (hf : IsPolyDeg d f) (c : F) :
    IsPolyDeg d (fun z => f z / c) := by
  simpa only [div_eq_mul_inv] using hf.smul_right c⁻¹

lemma sq {d : ℕ} {f : F → F} (hf : IsPolyDeg d f) : IsPolyDeg (d + d) (fun z => f z ^ 2) := by
  simpa only [pow_two] using hf.mul hf

lemma congr {d : ℕ} {f g : F → F} (hf : IsPolyDeg d f) (h : ∀ z, f z = g z) : IsPolyDeg d g := by
  simpa only [funext h] using hf

lemma eq_deg4 [CharZero F] {f : F → F} (hf : IsPolyDeg 4 f) :
    let (p4, p3, p2, p1, p0) := interp4 f
    ∀ z : F, f z = p4 * z ^ 4 + p3 * z ^ 3 + p2 * z ^ 2 + p1 * z + p0 := by
  rcases hf with ⟨P, hP, heP⟩
  have h4 : ∀ z : F, f z = P.coeff 4 * z ^ 4 + P.coeff 3 * z ^ 3 + P.coeff 2 * z ^ 2 +
      P.coeff 1 * z + P.coeff 0 := by
    intro z
    rw [heP z, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hP)]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_one]
    ring
  rw [interp4_eq h4]
  exact h4

end IsPolyDeg

lemma ValLead.interp4_of {K : Type*} [Field K] [CharZero K] {k : ℤ}
    {g : LaurentSeries K → LaurentSeries K} {g0 : K → K}
    (hg : ∀ c : K, ValLead k (g (HahnSeries.C c)) (g0 c)) :
    let p := interp4 g
    let q := interp4 g0
    ValLead k p.1 q.1 ∧ ValLead k p.2.1 q.2.1 ∧ ValLead k p.2.2.1 q.2.2.1 ∧
      ValLead k p.2.2.2.1 q.2.2.2.1 ∧ ValLead k p.2.2.2.2 q.2.2.2.2 := by
  have h0 : ValLead k (g 0) (g0 0) := by simpa only [map_zero] using hg 0
  have h1 : ValLead k (g 1) (g0 1) := by simpa only [map_one] using hg 1
  have hm1 : ValLead k (g (-1)) (g0 (-1)) := by simpa only [map_neg, map_one] using hg (-1)
  have h2 : ValLead k (g 2) (g0 2) := by simpa only [map_ofNat] using hg 2
  have hm2 : ValLead k (g (-2)) (g0 (-2)) := by simpa only [map_neg, map_ofNat] using hg (-2)
  have h24 : (24 : K) ≠ 0 := by exact_mod_cast (by decide : (24 : ℕ) ≠ 0)
  have h12 : (12 : K) ≠ 0 := by exact_mod_cast (by decide : (12 : ℕ) ≠ 0)
  have hdiv24 {f : LaurentSeries K} {a : K} (hf : ValLead k f a) :
      ValLead k (f / 24) (a / 24) := by
    simpa only [sub_zero, Nat.cast_ofNat] using hf.div_of_ne (ValLead.of_nat 24) h24
  have hdiv12 {f : LaurentSeries K} {a : K} (hf : ValLead k f a) :
      ValLead k (f / 12) (a / 12) := by
    simpa only [sub_zero, Nat.cast_ofNat] using hf.div_of_ne (ValLead.of_nat 12) h12
  have hmulN (n : ℕ) {f : LaurentSeries K} {a : K} (hf : ValLead k f a) :
      ValLead k ((n : LaurentSeries K) * f) ((n : K) * a) := by
    simpa only [zero_add] using (ValLead.of_nat n).mul hf
  refine ⟨?_, ?_, ?_, ?_, h0⟩
  · have h4 : ValLead k (-4 * (g 1 + g (-1))) (-4 * (g0 1 + g0 (-1))) := by
      simpa only [Nat.cast_ofNat, neg_mul] using (hmulN 4 (h1.add hm1)).neg
    have h6 : ValLead k (6 * g 0) (6 * g0 0) := by
      simpa only [Nat.cast_ofNat] using hmulN 6 h0
    exact hdiv24 ((h4.add (h2.add hm2)).add h6)
  · have h2s : ValLead k (-2 * (g 1 - g (-1))) (-2 * (g0 1 - g0 (-1))) := by
      simpa only [Nat.cast_ofNat, neg_mul] using (hmulN 2 (h1.sub hm1)).neg
    exact hdiv12 (h2s.add (h2.sub hm2))
  · have h16 : ValLead k (16 * (g 1 + g (-1))) (16 * (g0 1 + g0 (-1))) := by
      simpa only [Nat.cast_ofNat] using hmulN 16 (h1.add hm1)
    have h30 : ValLead k (30 * g 0) (30 * g0 0) := by
      simpa only [Nat.cast_ofNat] using hmulN 30 h0
    exact hdiv24 ((h16.sub (h2.add hm2)).sub h30)
  · have h8 : ValLead k (8 * (g 1 - g (-1))) (8 * (g0 1 - g0 (-1))) := by
      simpa only [Nat.cast_ofNat] using hmulN 8 (h1.sub hm1)
    exact hdiv12 (h8.sub (h2.sub hm2))

/-- Scaled degree-4 interpolation valuation bound: if `g` has degree `≤ 4` and
`HasValGe k (g (single s c))` for all `c : K`, then `(interp4 g)` has valuations `≥ k - m * s`. -/
theorem HasValGe.interp4_scaled {K : Type*} [Field K] [CharZero K]
    {s k : ℤ} {g : LaurentSeries K → LaurentSeries K}
    (hdeg : IsPolyDeg 4 g) (hg : ∀ c : K, HasValGe k (g (HahnSeries.single s c))) :
    let p := interp4 g
    HasValGe (k - 4 * s) p.1 ∧ HasValGe (k - 3 * s) p.2.1 ∧
      HasValGe (k - 2 * s) p.2.2.1 ∧ HasValGe (k - s) p.2.2.2.1 ∧ HasValGe k p.2.2.2.2 := by
  have : CharZero (LaurentSeries K) := ⟨fun a b h => by
    have h0 := congrArg (fun x : LaurentSeries K => x.coeff 0) h
    rw [(ValLead.of_nat a).c0, (ValLead.of_nat b).c0] at h0
    exact Nat.cast_injective h0⟩
  set p := interp4 g
  let gsc : LaurentSeries K → LaurentSeries K := fun u => g (HahnSeries.single s 1 * u)
  have hgsc_eq : ∀ u : LaurentSeries K,
      gsc u = (HahnSeries.single (4 * s) 1 * p.1) * u ^ 4 +
              (HahnSeries.single (3 * s) 1 * p.2.1) * u ^ 3 +
              (HahnSeries.single (2 * s) 1 * p.2.2.1) * u ^ 2 +
              (HahnSeries.single s 1 * p.2.2.2.1) * u + p.2.2.2.2 := by
    intro u
    dsimp only [gsc]
    have h4 := hdeg.eq_deg4 (HahnSeries.single s 1 * u)
    change g (HahnSeries.single s 1 * u) = p.1 * (HahnSeries.single s 1 * u) ^ 4 +
      p.2.1 * (HahnSeries.single s 1 * u) ^ 3 + p.2.2.1 * (HahnSeries.single s 1 * u) ^ 2 +
      p.2.2.2.1 * (HahnSeries.single s 1 * u) + p.2.2.2.2 at h4
    rw [h4]
    have hsp (m : ℕ) : (HahnSeries.single s (1 : K)) ^ m = HahnSeries.single ((m : ℤ) * s) 1 := by
      rw [HahnSeries.single_pow, one_pow, nsmul_eq_mul]
    simp only [mul_pow, hsp, Nat.cast_ofNat]
    ring
  have hint_sc : interp4 gsc =
      (HahnSeries.single (4 * s) 1 * p.1, HahnSeries.single (3 * s) 1 * p.2.1,
       HahnSeries.single (2 * s) 1 * p.2.2.1, HahnSeries.single s 1 * p.2.2.2.1, p.2.2.2.2) :=
    interp4_eq hgsc_eq
  have hgsc_val : ∀ c : K, HasValGe k (gsc (HahnSeries.C c)) := by
    intro c
    have heq : HahnSeries.single s (1 : K) * HahnSeries.C c = HahnSeries.single s c := by
      rw [HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero, one_mul]
    simpa only [gsc, heq] using hg c
  have hval_all :
      HasValGe k (interp4 gsc).1 ∧ HasValGe k (interp4 gsc).2.1 ∧
      HasValGe k (interp4 gsc).2.2.1 ∧ HasValGe k (interp4 gsc).2.2.2.1 ∧
      HasValGe k (interp4 gsc).2.2.2.2 := by
    have hvl := ValLead.interp4_of (k := k - 1) (g := gsc) (g0 := fun _ => 0)
      (fun c => ValLead.of_hasValGe_succ (by simpa [sub_add_cancel] using hgsc_val c))
    have hq : interp4 (fun _ : K => (0 : K)) = (0, 0, 0, 0, 0) := by simp [interp4]
    rw [hq] at hvl
    exact ⟨by simpa [sub_add_cancel] using hvl.1.hasValGe_succ,
           by simpa [sub_add_cancel] using hvl.2.1.hasValGe_succ,
           by simpa [sub_add_cancel] using hvl.2.2.1.hasValGe_succ,
           by simpa [sub_add_cancel] using hvl.2.2.2.1.hasValGe_succ,
           by simpa [sub_add_cancel] using hvl.2.2.2.2.hasValGe_succ⟩
  rw [hint_sc] at hval_all
  have hunshift (m : ℤ) (x : LaurentSeries K) (hx : HasValGe k (HahnSeries.single m 1 * x)) :
      HasValGe (k - m) x := by
    have h := (HasValGe.single (-m) (1 : K)).mul hx
    have hmul : HahnSeries.single (-m) (1 : K) * (HahnSeries.single m 1 * x) = x := by
      rw [← mul_assoc, HahnSeries.single_mul_single, neg_add_cancel, mul_one]
      change 1 * x = x; rw [one_mul]
    rw [hmul] at h
    exact h.mono (by omega)
  exact ⟨hunshift (4 * s) p.1 hval_all.1,
         hunshift (3 * s) p.2.1 hval_all.2.1,
         hunshift (2 * s) p.2.2.1 hval_all.2.2.1,
         hunshift s p.2.2.2.1 hval_all.2.2.2.1,
         hval_all.2.2.2.2⟩

/-- Simple-pole residue formula for `P / Q` when `Q(a) = 0` and `Q'(a) ≠ 0`. -/
lemma simplePole_residue {K : Type*} [Field K] (P Q : K[X]) (a : K)
    (hQ0 : Q.eval a = 0) (hQd : Q.derivative.eval a ≠ 0) :
    CrossedRationalResidue.residue a
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q) =
    P.eval a / Q.derivative.eval a := by
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr hQ0
  have hR_eval : R.eval a = Q.derivative.eval a := by
    have hd := congrArg (fun f : K[X] => f.derivative.eval a) hR
    simp only [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero,
      one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at hd
    exact hd.symm
  have hRne : R.eval a ≠ 0 := hR_eval.symm ▸ hQd
  have hEq : algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) Q =
      (algebraMap K[X] (RatFunc K) P / algebraMap K[X] (RatFunc K) R) / uniformizer a := by
    rw [hR, map_mul, uniformizer]
    have hu := uniformizer_ne_zero a
    have hR0 : algebraMap K[X] (RatFunc K) R ≠ 0 :=
      polynomialMap_ne_zero (fun h => hRne (by simp [h]))
    field_simp [hu, hR0]
  rw [hEq, residue_div_uniformizer, valueAt_div_polynomials a P R hRne, hR_eval]

/-- Functorial extension of a field embedding `f : K →+* L` to `RatFunc K →+* RatFunc L`. -/
def mapRatFunc {K L : Type*} [Field K] [Field L] (f : K →+* L) : RatFunc K →+* RatFunc L :=
  IsFractionRing.lift (K := RatFunc K)
    (g := (algebraMap L[X] (RatFunc L)).comp (Polynomial.mapRingHom f))
    ((IsFractionRing.injective L[X] (RatFunc L)).comp (Polynomial.map_injective f f.injective))

lemma mapRatFunc_algebraMap {K L : Type*} [Field K] [Field L] (f : K →+* L) (P : K[X]) :
    mapRatFunc f (algebraMap K[X] (RatFunc K) P) = algebraMap L[X] (RatFunc L) (P.map f) :=
  IsFractionRing.lift_algebraMap _ P

lemma mapRatFunc_C {K L : Type*} [Field K] [Field L] (f : K →+* L) (c : K) :
    mapRatFunc f (RatFunc.C c) = RatFunc.C (f c) := by
  rw [← RatFunc.algebraMap_C, mapRatFunc_algebraMap, Polynomial.map_C, RatFunc.algebraMap_C]

lemma mapRatFunc_X {K L : Type*} [Field K] [Field L] (f : K →+* L) :
    mapRatFunc f (RatFunc.X : RatFunc K) = RatFunc.X := by
  rw [← RatFunc.algebraMap_X, mapRatFunc_algebraMap, Polynomial.map_X, RatFunc.algebraMap_X]

lemma mapRatFunc_uniformizer {K L : Type*} [Field K] [Field L] (f : K →+* L) (a : K) :
    mapRatFunc f (uniformizer a) = uniformizer (f a) := by
  simp only [uniformizer, mapRatFunc_algebraMap, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

lemma mapRatFunc_denom_dvd {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    (mapRatFunc f g).denom ∣ g.denom.map f := by
  set h := mapRatFunc f g
  have hQ0 : g.denom.map f ≠ 0 := by
    intro h0; exact g.denom_ne_zero (Polynomial.map_injective f f.injective (by simpa using h0))
  have heq : algebraMap L[X] (RatFunc L) h.num / algebraMap L[X] (RatFunc L) h.denom =
      algebraMap L[X] (RatFunc L) (g.num.map f) / algebraMap L[X] (RatFunc L) (g.denom.map f) := by
    rw [h.num_div_denom, ← mapRatFunc_algebraMap, ← mapRatFunc_algebraMap, ← map_div₀, g.num_div_denom]
  have hcross : h.num * g.denom.map f = g.num.map f * h.denom := by
    apply IsFractionRing.injective L[X] (RatFunc L)
    simp only [map_mul]
    have hd1 : algebraMap L[X] (RatFunc L) h.denom ≠ 0 := polynomialMap_ne_zero h.denom_ne_zero
    have hd2 : algebraMap L[X] (RatFunc L) (g.denom.map f) ≠ 0 := polynomialMap_ne_zero hQ0
    rw [div_eq_div_iff hd1 hd2] at heq
    exact heq
  have hdvd : h.denom ∣ h.num * g.denom.map f := ⟨g.num.map f, by rw [hcross, mul_comm]⟩
  exact h.isCoprime_num_denom.symm.dvd_of_dvd_mul_left hdvd

lemma RegularAt.mapRatFunc {K L : Type*} [Field K] [Field L] (f : K →+* L) {a : K} {g : RatFunc K}
    (hg : RegularAt a g) : RegularAt (f a) (QuadraticCovers.mapRatFunc f g) := by
  obtain ⟨P, Q, hQ, rfl⟩ := hg
  refine ⟨P.map f, Q.map f, ?_, ?_⟩
  · rw [Polynomial.eval_map_apply]; exact (map_ne_zero_iff f f.injective).mpr hQ
  · rw [map_div₀, mapRatFunc_algebraMap, mapRatFunc_algebraMap]

theorem residue_mapRatFunc {K L : Type*} [Field K] [Field L] (f : K →+* L) (a : K) (g : RatFunc K) :
    CrossedRationalResidue.residue (f a) (mapRatFunc f g) =
      f (CrossedRationalResidue.residue a g) := by
  obtain ⟨r, terms, hr, rfl⟩ := exists_regular_add_poleSum a g
  rw [map_add, map_add, map_add, hr.residue_eq_zero, (RegularAt.mapRatFunc f hr).residue_eq_zero,
    zero_add, zero_add]
  induction terms with
  | nil => simp [poleSum]
  | cons t ts ih =>
    rcases t with ⟨c, n⟩
    simp only [poleSum, map_add, map_mul, map_inv₀, map_pow, mapRatFunc_C, mapRatFunc_uniformizer]
    rw [residue_term, residue_term, ih]
    by_cases hn : n = 0 <;> simp [hn]

lemma mapRatFunc_reciprocal {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    mapRatFunc f (reciprocal g) = reciprocal (mapRatFunc f g) := by
  have hpoly (R : K[X]) :
      mapRatFunc f (reciprocal (algebraMap K[X] (RatFunc K) R)) =
        reciprocal (mapRatFunc f (algebraMap K[X] (RatFunc K) R)) := by
    induction R using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add, hp, hq]
    | monomial n c =>
      rw [← C_mul_X_pow_eq_monomial]
      simp only [map_mul, map_pow, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
        reciprocal_C, reciprocal_X, mapRatFunc_C, mapRatFunc_X, map_inv₀]
  induction g using RatFunc.induction_on with
  | f P Q _ =>
    simp only [map_div₀, hpoly]

theorem infinityCoefficient_mapRatFunc {K L : Type*} [Field K] [Field L] (f : K →+* L) (g : RatFunc K) :
    CrossedRationalResidue.infinityCoefficient (mapRatFunc f g) =
      f (CrossedRationalResidue.infinityCoefficient g) := by
  change residue 0 ((RatFunc.X ^ 2)⁻¹ * reciprocal (mapRatFunc f g)) =
    f (residue 0 ((RatFunc.X ^ 2)⁻¹ * reciprocal g))
  rw [← mapRatFunc_reciprocal, ← map_zero f, ← residue_mapRatFunc]
  congr 1
  simp only [map_mul, map_inv₀, map_pow, mapRatFunc_X]

end QuadraticCovers
#print axioms QuadraticCovers.residue_mapRatFunc
#print axioms QuadraticCovers.HasValGe.interp4_scaled
