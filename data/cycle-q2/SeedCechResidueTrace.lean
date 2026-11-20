import Proposal.SeedCechCurveCharts

/-! # Čech residues, boundary cancellation and trace on the seed curve -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/SeedCechFractions.lean -/
section
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoordinates (r : ℂ) (e : Bool) : Fin 4 → PowerChart r e :=
  ![x0 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointX e),
    x2 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e),
    base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e) (endpointY e)]

def powerEval (r : ℂ) (e : Bool) : Poly →+* PowerChart r e :=
  MvPolynomial.eval₂Hom
    ((base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e)).comp PowerSeries.C)
    (powerCoordinates r e)

def laurentEval (r : ℂ) (e : Bool) : Poly →+* LaurentChart r e :=
  (chartEmbedding r e).comp (powerEval r e)

@[simp] theorem powerCoordinates_zero (r : ℂ) (e : Bool) :
    powerCoordinates r e 0 = x0 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_one (r : ℂ) (e : Bool) :
    powerCoordinates r e 1 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointX e) := rfl
@[simp] theorem powerCoordinates_two (r : ℂ) (e : Bool) :
    powerCoordinates r e 2 = x2 (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) := rfl
@[simp] theorem powerCoordinates_three (r : ℂ) (e : Bool) :
    powerCoordinates r e 3 = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (endpointY e) := rfl

@[simp] theorem powerEval_X (r : ℂ) (e : Bool) (j : Fin 4) :
    powerEval r e (X j) = powerCoordinates r e j := by simp [powerEval]

@[simp] theorem powerEval_C (r : ℂ) (e : Bool) (c : ℂ) :
    powerEval r e (C c) = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (PowerSeries.C c) := by simp [powerEval]

theorem powerEval_curveF1 (r : ℂ) (e : Bool) : powerEval r e (curveF1 r) = 0 := by
  simp only [curveF1, relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one, powerCoordinates_three]
  rw [x0_sq, sub_eq_zero]
  simp [map_mul]

theorem powerEval_curveH (r : ℂ) (e : Bool) : powerEval r e curveH = 0 := by
  have h2 := x2_cubic (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e)
  simp only [map_sub, map_mul, map_pow, map_one] at h2
  simp only [curveH, h, b, map_sub, map_add, map_mul, map_pow,
    powerEval_X, powerEval_C, powerCoordinates_zero, powerCoordinates_one,
    powerCoordinates_two, powerCoordinates_three]
  linear_combination h2

theorem powerEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : powerEval r e p = 0 := by
  obtain ⟨u,v,hp⟩ := Ideal.mem_span_pair.mp hp
  rw [← hp, map_add, map_mul, map_mul, powerEval_curveF1, powerEval_curveH]
  ring

theorem laurentEval_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) : laurentEval r e p = 0 := by
  change chartEmbedding r e (powerEval r e p) = 0
  rw [powerEval_zero_of_curveIdeal r e hp, map_zero]


theorem uniformizer_ne_zero : seriesMap (PowerSeries.X : PS) ≠ 0 := by
  intro hh
  have hc := congrArg (fun f : LS => f.coeff 1) hh
  simpa [seriesMap, HahnSeries.ofPowerSeries_X] using hc

def uniformizerUnit : LSˣ := Units.mk0 _ uniformizer_ne_zero

def chartAUnit (r : ℂ) (e : Bool) : (LaurentChart r e)ˣ :=
  Units.map (base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))) uniformizerUnit

theorem laurentEval_curveA (r : ℂ) (e : Bool) :
    laurentEval r e curveA = (chartAUnit r e : LaurentChart r e) := by
  have hp : powerEval r e curveA = base (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) PowerSeries.X := by
    simp only [curveA, map_mul, powerEval_X, powerCoordinates_one, powerCoordinates_three]
    rw [← map_mul]
    congr 1
    cases e <;> simp [endpointX, endpointY]
  change chartEmbedding r e (powerEval r e curveA) = _
  rw [hp]
  exact curveMap_base seriesMap _ _ _ _ _

theorem laurentEval_curveB (r : ℂ) (e : Bool) :
    laurentEval r e curveB = (laurentX2Unit r e : LaurentChart r e) := by
  change chartEmbedding r e (powerEval r e (X 2)) =
    chartEmbedding r e (powerX2Unit r e : PowerChart r e)
  congr 1
  simp only [powerEval_X, powerCoordinates_two, powerX2Unit, coe_x2Unit]

def fraction (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : LaurentChart r e :=
  laurentEval r e p * ((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) ^ n *
    ((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) ^ m

def fractionResidue (r : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : ℂ :=
  endpointResidue r e (fraction r e p n m)

def cechResidue (r : ℂ) (p : Poly) (n m : ℕ) : ℂ :=
  fractionResidue r false p n m - fractionResidue r true p n m

theorem fraction_add (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p+q) n m = fraction r e p n m + fraction r e q n m := by
  simp [fraction, add_mul]

theorem fraction_sub (r : ℂ) (e : Bool) (p q : Poly) (n m : ℕ) :
    fraction r e (p-q) n m = fraction r e p n m - fraction r e q n m := by
  simp [fraction, sub_mul]

theorem cechResidue_add (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p+q) n m = cechResidue r p n m + cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_add, map_add]
  ring

theorem unit_pow_cancel {A : Type*} [CommRing A] (u : Aˣ) (n N : ℕ) (hn : n ≤ N) :
    (u : A) ^ (N-n) * ((u⁻¹ : Aˣ) : A) ^ N = ((u⁻¹ : Aˣ) : A) ^ n := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_sub_cancel_left, pow_add]
  calc
    _ = ((u : A) * ((u⁻¹ : Aˣ) : A)) ^ k * ((u⁻¹ : Aˣ) : A) ^ n := by
      rw [mul_pow]
      ring
    _ = _ := by simp

theorem fraction_change_denominator (r : ℂ) (e : Bool) (p : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M) :
    fraction r e (p * curveA ^ (N-n) * curveB ^ (M-m)) N M =
      fraction r e p n m := by
  unfold fraction
  simp only [map_mul, map_pow, laurentEval_curveA, laurentEval_curveB]
  calc
    _ = laurentEval r e p *
        (((chartAUnit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (N-n) *
          (((chartAUnit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ N) *
        (((laurentX2Unit r e : (LaurentChart r e)ˣ) : LaurentChart r e) ^ (M-m) *
          (((laurentX2Unit r e)⁻¹ : (LaurentChart r e)ˣ) : LaurentChart r e) ^ M) := by ring
    _ = _ := by rw [unit_pow_cancel _ n N hn, unit_pow_cancel _ m M hm]

theorem fraction_first_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveA^N) N M = fraction r e p 0 M := by
  simpa using fraction_change_denominator r e p 0 M N M (Nat.zero_le _) le_rfl

theorem fraction_second_open_term (r : ℂ) (e : Bool) (p : Poly) (N M : ℕ) :
    fraction r e (p * curveB^M) N M = fraction r e p N 0 := by
  simpa using fraction_change_denominator r e p N 0 N M le_rfl (Nat.zero_le _)

theorem fractionResidue_x2_open (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 0 m = 0 := by
  simpa [fractionResidue, fraction, laurentEval] using
    endpointResidue_x2_open r e (powerEval r e p) m

theorem cechResidue_x2_open (r : ℂ) (p : Poly) (m : ℕ) : cechResidue r p 0 m = 0 := by
  simp [cechResidue, fractionResidue_x2_open]

theorem fraction_zero_of_curveIdeal (r : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r) (n m : ℕ) : fraction r e p n m = 0 := by
  simp [fraction, laurentEval_zero_of_curveIdeal r e hp]

/-- Exact denominator-clearing definition of the degree-one Čech coboundaries
for the cover D₊(x₁x₃), D₊(x₂) of the projective sparse curve.  The two numerator
degrees enforce sections of its canonical bundle O(1). -/
def CechBoundary (r : ℂ) (p : Poly) (n m : ℕ) : Prop :=
  ∃ N M q s, n ≤ N ∧ m ≤ M ∧ q.IsHomogeneous (M + 1) ∧
    s.IsHomogeneous (2 * N + 1) ∧
    p * curveA ^ (N - n) * curveB ^ (M - m) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r

/-- Clearing arbitrary powers gives exactly the same two endpoint values as
the sum of the two single-open cochains. -/
theorem fraction_of_boundary_witness (r : ℂ) (e : Bool) (p q s : Poly)
    (n m N M : ℕ) (hn : n ≤ N) (hm : m ≤ M)
    (hmem : p * curveA^(N-n) * curveB^(M-m) -
      (q * curveA^N + s * curveB^M) ∈ curveIdeal r) :
    fraction r e p n m = fraction r e q 0 M + fraction r e s N 0 := by
  have hz := fraction_zero_of_curveIdeal r e hmem N M
  rw [fraction_sub, fraction_add, fraction_change_denominator r e p n m N M hn hm,
    fraction_first_open_term, fraction_second_open_term, sub_eq_zero] at hz
  exact hz

end CycleQ2SeedCech
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechJets.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open TrivSqZeroExt

abbrev Jet := TrivSqZeroExt ℂ ℂ

def firstJet : PS →+* Jet where
  toFun f := (PowerSeries.constantCoeff f, PowerSeries.coeff 1 f)
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_add' f g := by apply TrivSqZeroExt.ext <;> simp
  map_mul' f g := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [PowerSeries.coeff_one_mul, smul_eq_mul, op_smul_eq_smul]
      ring

@[simp] theorem firstJet_fst (f : PS) : (firstJet f).fst = PowerSeries.constantCoeff f := rfl
@[simp] theorem firstJet_snd (f : PS) : (firstJet f).snd = PowerSeries.coeff 1 f := rfl

theorem firstJet_X_sq : firstJet (PowerSeries.X : PS) ^ 2 = 0 := by
  apply TrivSqZeroExt.ext <;> simp [firstJet, pow_two, smul_eq_mul, op_smul_eq_smul]

theorem firstJet_I_sq : firstJet (PowerSeries.C Complex.I) ^ 2 = -1 := by
  rw [← map_pow, ← map_pow, Complex.I_sq, map_neg, map_one, map_neg, map_one]

/-- The finite second-order identity used to normalize the actual Čech
residue.  It is an identity in every commutative ring with the displayed four
relations; all coefficients are checked by `linear_combination`. -/
theorem inverse_fourth_jet_identity {A : Type*} [CommRing A]
    (a b t j r : A) (hb : b ^ 3 + (a+1)*t*b + a-j = 0)
    (ha : a ^ 2-r*t = 0) (ht : t^2=0) (hj : j^2+1=0) :
    b^4 * (-a*b^2 + 2*j*r*t*b^2 + 3*r*a*t*b^2 - 2*a*t) = a := by
  linear_combination
    (-3*a^2*b*r*t^2 + a^2*b*t - 3*a^2*r*t + a^2 +
      3*a*b^3*r*t - a*b^3 - 2*a*b*j*r*t^2 - 3*a*b*r*t^2 -
      a*b*t + a*j*r*t - a*j + 2*b^3*j*r*t - 2*b*j*r*t^2 +
      2*j^2*r*t) * hb +
    (3*a*b^2*r*t^3 - a*b^2*t^2 + 6*a*b*r*t^2 - 2*a*b*t +
      3*a*r*t - a + 2*b^2*j*r*t^3 + 6*b^2*r*t^3 -
      2*b*j*r*t^2 + 2*b*j*t + 6*b*r*t^2 - 4*j*r*t + 2*j) * ha +
    (4*a*b^2*j*r*t + 3*a*b^2*r^2*t^2 + 2*a*b^2*r*t + a*b^2 -
      4*a*b*j^2*r - 2*a*b*j*r + 6*a*b*r^2*t - 2*a*b*r +
      3*a*r^2 + 2*b^2*j*r^2*t^2 + 2*b^2*j*r*t + 6*b^2*r^2*t^2 -
      4*b*j^2*r - 2*b*j*r^2*t + 2*b*j*r + 6*b*r^2*t - 4*j*r^2) * ht +
    (-a*r*t - a + 2*j*r*t) * hj

abbrev JetChart (r : ℂ) (e : Bool) :=
  CurveAlgebra (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetEmbedding (r : ℂ) (e : Bool) : PowerChart r e →+* JetChart r e :=
  curveMap firstJet (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

def jetX2Unit (r : ℂ) (e : Bool) : (JetChart r e)ˣ :=
  Units.map (jetEmbedding r e) (powerX2Unit r e)

def jetBase (r : ℂ) (e : Bool) : Jet →+* JetChart r e :=
  base (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX0 (r : ℂ) (e : Bool) : JetChart r e :=
  x0 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetX2 (r : ℂ) (e : Bool) : JetChart r e :=
  x2 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

def jetCoefficient (r : ℂ) (e : Bool) : JetChart r e →ₗ[Jet] Jet :=
  coefficient (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e))

@[simp] theorem coe_jetX2Unit (r : ℂ) (e : Bool) :
    (jetX2Unit r e : JetChart r e) = jetX2 r e := by
  simp [jetX2Unit, jetEmbedding, powerX2Unit, jetX2]

theorem false_jet_relations (r : ℂ) :
    let A := jetX0 r false
    let B := jetX2 r false
    let T := jetBase r false (firstJet PowerSeries.X)
    let J := jetBase r false (firstJet (PowerSeries.C Complex.I))
    let R := jetBase r false (firstJet (PowerSeries.C r))
    (B^3+(A+1)*T*B+A-J=0) ∧ (A^2-R*T=0) ∧ T^2=0 ∧ J^2+1=0 := by
  dsimp only
  have ht : (jetBase r false (firstJet PowerSeries.X)) ^ 2 = 0 := by
    rw [← map_pow, firstJet_X_sq, map_zero]
  have ht3 : (jetBase r false (firstJet PowerSeries.X)) ^ 3 = 0 := by
    rw [pow_succ, ht, zero_mul]
  refine ⟨?_, ?_, ht, ?_⟩
  · have hh := x2_cubic (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX2 r false ^ 3 +
      (jetX0 r false + jetBase r false (firstJet (endpointX false))) *
        jetBase r false (firstJet (endpointY false)) * jetX2 r false +
      jetX0 r false * jetBase r false ((firstJet (endpointX false)) ^ 2) +
      jetBase r false ((1-firstJet (PowerSeries.C Complex.I)) *
        (firstJet (endpointY false)) ^ 3 - firstJet (PowerSeries.C Complex.I) *
        (firstJet (endpointX false)) ^ 3) = 0 at hh
    simpa only [endpointX, endpointY, map_one, map_sub, map_mul, map_pow,
      one_pow, mul_one, ht3, mul_zero, zero_sub, sub_eq_add_neg, map_add, map_neg, zero_add] using hh
  · have hh := x0_sq (firstJet (PowerSeries.C r))
      (firstJet (PowerSeries.C Complex.I)) (firstJet (endpointX false))
      (firstJet (endpointY false))
    change jetX0 r false ^ 2 = jetBase r false
      (firstJet (PowerSeries.C r) * firstJet (endpointX false) *
        firstJet (endpointY false)) at hh
    simpa only [endpointX, endpointY, map_one, mul_one, map_mul, sub_eq_zero] using hh
  · rw [← map_pow, firstJet_I_sq, map_neg, map_one]
    ring

theorem false_jet_inverse_fourth (r : ℂ) :
    jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 =
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X) := by
  obtain ⟨hb,ha,ht,hj⟩ := false_jet_relations r
  have hh := inverse_fourth_jet_identity _ _ _ _ _ hb ha ht hj
  let H : JetChart r false :=
    -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false (firstJet (PowerSeries.C Complex.I)) *
        jetBase r false (firstJet (PowerSeries.C r)) *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 +
      3 * jetBase r false (firstJet (PowerSeries.C r)) * jetX0 r false *
        jetBase r false (firstJet PowerSeries.X) * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false (firstJet PowerSeries.X)
  change jetX2 r false ^ 4 * H = jetX0 r false at hh
  change jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 = H
  rw [← hh]
  calc
    _ = (jetX2 r false ^ 4 * (((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) :
      JetChart r false) ^ 4) * H := by ring
    _ = H := by
      rw [← coe_jetX2Unit, ← mul_pow]
      rw [(jetX2Unit r false).mul_inv, one_pow, one_mul]

theorem false_jet_coefficient (r : ℂ) :
    jetCoefficient r false
      (jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
  rw [false_jet_inverse_fourth]
  let rr := firstJet (PowerSeries.C r)
  let ii := firstJet (PowerSeries.C Complex.I)
  let tt := firstJet (PowerSeries.X : PS)
  have heq :
      -jetX0 r false * jetX2 r false ^ 2 +
      2 * jetBase r false ii * jetBase r false rr * jetBase r false tt * jetX2 r false ^ 2 +
      3 * jetBase r false rr * jetX0 r false * jetBase r false tt * jetX2 r false ^ 2 -
      2 * jetX0 r false * jetBase r false tt =
      jetBase r false (-1 + 3*rr*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 2 +
      jetBase r false (2*ii*rr*tt) * jetX0 r false ^ 0 * jetX2 r false ^ 2 +
      jetBase r false (-2*tt) * jetX0 r false ^ 1 * jetX2 r false ^ 0 := by
    simp only [map_add, map_sub, map_mul, map_neg, map_ofNat, map_one, pow_zero, pow_one]
    ring
  rw [heq, map_add, map_add]
  unfold jetCoefficient jetBase jetX0 jetX2
  rw [coefficient_small_monomial _ _ _ _ _ 1 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 0 2 (by decide) (by decide),
    coefficient_small_monomial _ _ _ _ _ 1 0 (by decide) (by decide)]
  simp [rr, tt]

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.inverse_fourth_jet_identity
#print axioms CycleQ2SeedCech.false_jet_coefficient
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechCancellation.lean -/
section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def laurentCoefficient (r : ℂ) (e : Bool) : LaurentChart r e →ₗ[LS] LS :=
  coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentBase (r : ℂ) (e : Bool) : LS →+* LaurentChart r e :=
  base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentX0 (r : ℂ) (e : Bool) : LaurentChart r e :=
  x0 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

def laurentX2 (r : ℂ) (e : Bool) : LaurentChart r e :=
  x2 (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e))

theorem laurentEval_monomial (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) :
    laurentEval r e (monomial d z) =
      laurentBase r e (seriesMap (PowerSeries.C z)) * laurentX0 r e ^ d 0 *
        laurentBase r e (seriesMap (endpointX e)) ^ d 1 * laurentX2 r e ^ d 2 *
          laurentBase r e (seriesMap (endpointY e)) ^ d 3 := by
  rw [monomial_eq_C_mul_mon]
  simp [laurentEval, powerEval, mon, powerCoordinates, chartEmbedding,
    laurentBase, laurentX0, laurentX2, Matrix.cons_val_succ, Fin.reduceSucc, mul_assoc]

theorem fraction_monomial_first_open (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ) :
    fraction r e (monomial d z) n 0 =
      laurentBase r e (seriesMap (PowerSeries.C z) *
        seriesMap (endpointX e) ^ d 1 * seriesMap (endpointY e) ^ d 3 *
          (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)) *
        laurentX0 r e ^ d 0 * laurentX2 r e ^ d 2 := by
  simp only [fraction, pow_zero, mul_one, laurentEval_monomial]
  simp only [chartAUnit, Units.coe_map_inv, Units.coe_map, ← map_pow,
    laurentBase, map_mul, map_pow, MonoidHom.coe_coe]
  ring

theorem first_open_monomial_coefficient (r : ℂ) (e : Bool) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3) :
    laurentCoefficient r e (fraction r e (monomial d z) n 0) =
      if d 0 = 1 ∧ d 2 = 2 then
        seriesMap (PowerSeries.C z) * seriesMap (endpointX e) ^ d 1 *
          seriesMap (endpointY e) ^ d 3 * (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)
      else 0 := by
  rw [fraction_monomial_first_open]
  exact coefficient_small_monomial _ _ _ _ _ _ _ hd0 hd2

theorem scalar_endpoint_residue (z : ℂ) (b d n : ℕ) (e : Bool) :
    (seriesMap (PowerSeries.C z) * seriesMap (endpointX e) ^ b *
      seriesMap (endpointY e) ^ d * (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ n)).coeff (-1) =
        if (if e then (b : ℤ) else (d : ℤ)) - n = -1 then z else 0 := by
  cases e <;>
    simp [endpointX, endpointY, seriesMap, uniformizerUnit, HahnSeries.ofPowerSeries_C,
      HahnSeries.ofPowerSeries_X, HahnSeries.C, HahnSeries.inv_single, HahnSeries.single_pow,
      HahnSeries.single_mul_single, HahnSeries.coeff_single, sub_eq_add_neg, eq_comm]

theorem cechResidue_reduced_monomial (r : ℂ) (d : Exp) (z : ℂ) (n : ℕ)
    (hd0 : d 0 < 2) (hd2 : d 2 < 3)
    (hdegree : d 0 + d 1 + d 2 + d 3 = 2*n+1) :
    cechResidue r (monomial d z) n 0 = 0 := by
  change (laurentCoefficient r false (fraction r false (monomial d z) n 0)).coeff (-1) -
    (laurentCoefficient r true (fraction r true (monomial d z) n 0)).coeff (-1) = 0
  rw [first_open_monomial_coefficient _ _ _ _ _ hd0 hd2,
    first_open_monomial_coefficient _ _ _ _ _ hd0 hd2]
  by_cases he : d 0 = 1 ∧ d 2 = 2
  · rw [if_pos he, if_pos he, scalar_endpoint_residue, scalar_endpoint_residue]
    have hp : (d 3 : ℤ) - n = -1 ↔ (d 1 : ℤ) - n = -1 := by omega
    simp only [Bool.false_eq_true, if_false, if_true, hp, sub_self]
  · rw [if_neg he, if_neg he]
    simp

theorem cechResidue_sum (r : ℂ) {ι : Type*} (s : Finset ι) (p : ι → Poly) (n m : ℕ) :
    cechResidue r (∑ i ∈ s, p i) n m = ∑ i ∈ s, cechResidue r (p i) n m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [cechResidue, fractionResidue, fraction]
  | @insert i s hi ih => simp [Finset.sum_insert hi, cechResidue_add, ih]

/-- The residues at the two endpoints cancel on every canonical-bundle
section over D₊(x₁x₃), with no bound on the denominator power. -/
theorem cechResidue_first_open (r : ℂ) (p : Poly) (n : ℕ)
    (hp : p.IsHomogeneous (2*n+1)) : cechResidue r p n 0 = 0 := by
  obtain ⟨q,hq,hqh,hpq⟩ := exists_homogeneous_curve_normal r p (2*n+1) hp
  have heq (e : Bool) : fraction r e p n 0 = fraction r e q n 0 := by
    have hh := fraction_zero_of_curveIdeal r e hpq n 0
    rwa [fraction_sub, sub_eq_zero] at hh
  have hceq : cechResidue r p n 0 = cechResidue r q n 0 := by
    simp only [cechResidue, fractionResidue, heq]
  rw [hceq]
  conv_lhs => rw [q.as_sum]
  rw [cechResidue_sum]
  apply Finset.sum_eq_zero
  intro d hd
  apply cechResidue_reduced_monomial r d (q.coeff d) n (hq d hd).1 (hq d hd).2
  have hh : d.degree = 2*n+1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hqh (mem_support_iff.mp hd)
  rw [Finsupp.degree_eq_sum] at hh
  simpa [Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc, add_assoc] using hh

/-- The actual two-endpoint functional kills every Čech coboundary, including
ones requiring arbitrarily large denominator powers. -/
theorem cechResidue_zero_of_boundary (r : ℂ) (p : Poly) (n m : ℕ)
    (hboundary : CechBoundary r p n m) : cechResidue r p n m = 0 := by
  obtain ⟨N,M,q,s,hn,hm,hq,hs,hmem⟩ := hboundary
  have hfalse := fraction_of_boundary_witness r false p q s n m N M hn hm hmem
  have htrue := fraction_of_boundary_witness r true p q s n m N M hn hm hmem
  have heq : cechResidue r p n m = cechResidue r q 0 M + cechResidue r s N 0 := by
    simp only [cechResidue, fractionResidue, hfalse, htrue, map_add]
    ring
  rw [heq, cechResidue_x2_open, cechResidue_first_open r s N hs, add_zero]

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_zero_of_boundary
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechMembership.lean -/
section
/-! The finite published Artinian trace is now identified with an actual
Čech residue functional on the sparse seed curve.  Arbitrary denominator
powers are allowed in the definition of a coboundary. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace CycleQ2HomogeneousComponent

theorem relation_one_eq_curveA_sq (r : ℂ) : relation r 1 = curveA ^ 2 := by
  simp [relation, curveA, mul_pow]

theorem relation_two_eq_curveB_fourth (r : ℂ) : relation r 2 = curveB ^ 4 := by
  rfl

theorem curveA_sq_homogeneous : (curveA ^ 2).IsHomogeneous 4 := by
  simpa [curveA, mul_pow] using
    (isHomogeneous_X_pow (1 : Fin 4) 2).mul (isHomogeneous_X_pow (3 : Fin 4) 2)

theorem curveB_fourth_homogeneous : (curveB ^ 4).IsHomogeneous 4 :=
  isHomogeneous_X_pow (2 : Fin 4) 4

/-- Homogeneous projection turns arbitrary ideal-membership coefficients
into genuine canonical-bundle cochains on the two specified opens. -/
theorem boundary_of_mem_reducedIdeal (r : ℂ) {p : Poly}
    (hp : p.IsHomogeneous 9) (hmem : p ∈ reducedIdeal r) : CechBoundary r p 2 4 := by
  obtain ⟨u,hu⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
  have hu' : u 0 * curveF1 r + u 1 * curveA^2 + u 2 * curveB^4 + u 3 * curveH = p := by
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
      relation_one_eq_curveA_sq, relation_two_eq_curveB_fourth,
      Matrix.cons_val_succ, Fin.reduceSucc, curveF1, curveH,
      show relation r 3 = h from rfl, add_assoc] using hu
  have hh := congrArg (homogeneousComponent 9) hu'
  rw [map_add, map_add, map_add,
    component_mul_of_homogeneous _ _ (curveF1_homogeneous r) (by decide),
    component_mul_of_homogeneous _ _ curveA_sq_homogeneous (by decide),
    component_mul_of_homogeneous _ _ curveB_fourth_homogeneous (by decide),
    component_mul_of_homogeneous _ _ curveH_homogeneous (by decide),
    homogeneousComponent_of_mem hp, if_pos rfl] at hh
  refine ⟨2,4,homogeneousComponent 5 (u 1),homogeneousComponent 5 (u 2),
    le_rfl,le_rfl,homogeneousComponent_isHomogeneous 5 (u 1),
    homogeneousComponent_isHomogeneous 5 (u 2),?_⟩
  simp only [Nat.sub_self, pow_zero, mul_one]
  apply Ideal.mem_span_pair.mpr
  refine ⟨homogeneousComponent 7 (u 0),homogeneousComponent 6 (u 3),?_⟩
  norm_num at hh
  linear_combination hh


end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.boundary_of_mem_reducedIdeal
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechNormalization.lean -/
section
/-! The normalization of the actual two-endpoint Čech functional is obtained
from a checked identity in the first infinitesimal neighborhood of the two
endpoints.  No residue value is supplied as a hypothesis. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

def powerCoefficient (r : ℂ) (e : Bool) : PowerChart r e →ₗ[PS] PS :=
  coefficient (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)

theorem firstJet_powerCoefficient (r : ℂ) (e : Bool) (z : PowerChart r e) :
    firstJet (powerCoefficient r e z) = jetCoefficient r e (jetEmbedding r e z) := by
  symm
  exact coefficient_curveMap firstJet _ _ _ _ z

theorem uniformizer_inv_sq : (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) =
    HahnSeries.single (-2 : ℤ) 1 := by
  simp [uniformizerUnit, seriesMap, HahnSeries.ofPowerSeries_X,
    HahnSeries.inv_single, HahnSeries.single_pow]

/-- The double pole in x₁x₃ extracts the linear coefficient of an integral
power-series chart, for every power of the other cover equation. -/
theorem fractionResidue_double_pole (r : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r e p 2 m =
      PowerSeries.coeff 1 (powerCoefficient r e
        (powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m)) := by
  let z : PowerChart r e :=
    powerEval r e p * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ m
  have heq : fraction r e p 2 m =
      laurentBase r e (((uniformizerUnit⁻¹ : LSˣ) : LS) ^ 2) * chartEmbedding r e z := by
    simp only [fraction, laurentEval, RingHom.comp_apply, z, map_mul, map_pow,
      laurentBase, chartAUnit, laurentX2Unit, Units.coe_map_inv, Units.coe_map,
      MonoidHom.coe_coe]
    ring
  change (laurentCoefficient r e (fraction r e p 2 m)).coeff (-1) = _
  rw [heq]
  unfold laurentCoefficient laurentBase chartEmbedding
  rw [coefficient_base_mul, coefficient_curveMap, uniformizer_inv_sq,
    HahnSeries.coeff_single_mul]
  norm_num [seriesMap, powerCoefficient, PowerSeries.coeff_coe, z]

def soclePower (r : ℂ) (e : Bool) : PowerChart r e :=
  powerEval r e (mon 1 8 0 0) * ((powerX2Unit r e)⁻¹ : (PowerChart r e)ˣ) ^ 4

theorem jetEmbedding_soclePower (r : ℂ) (e : Bool) :
    jetEmbedding r e (soclePower r e) =
      jetX0 r e * (jetBase r e (firstJet (endpointX e)))^8 *
        ((jetX2Unit r e)⁻¹ : (JetChart r e)ˣ) ^ 4 := by
  simp only [soclePower, mon, map_mul, map_pow, powerEval_X,
    powerCoordinates_zero, powerCoordinates_one, powerCoordinates_two,
    powerCoordinates_three, pow_zero, pow_one, mul_one,
    jetEmbedding, curveMap_x0, curveMap_base, jetX0, jetBase,
    jetX2Unit, Units.coe_map_inv, MonoidHom.coe_coe]

theorem jetEmbedding_soclePower_false (r : ℂ) :
    jetEmbedding r false (soclePower r false) =
      jetX0 r false * ((jetX2Unit r false)⁻¹ : (JetChart r false)ˣ) ^ 4 := by
  rw [jetEmbedding_soclePower]
  simp only [endpointX, map_one, one_pow, mul_one]

theorem jetEmbedding_soclePower_true (r : ℂ) :
    jetEmbedding r true (soclePower r true) = 0 := by
  have ht : firstJet (PowerSeries.X : PS) ^ 8 = 0 := by
    rw [show 8 = 2 * 4 from rfl, pow_mul, firstJet_X_sq, zero_pow (by decide)]
  have ht' : (jetBase r true (firstJet PowerSeries.X)) ^ 8 = 0 := by
    rw [← map_pow, ht, map_zero]
  rw [jetEmbedding_soclePower]
  change jetX0 r true * (jetBase r true (firstJet PowerSeries.X))^8 * _ = 0
  rw [ht', mul_zero, zero_mul]

theorem soclePower_false_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) = 3*r := by
  have hh : firstJet (powerCoefficient r false (soclePower r false)) =
      -1 + 3 * firstJet (PowerSeries.C r) * firstJet PowerSeries.X := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_false, false_jet_coefficient]
  have hs := congrArg TrivSqZeroExt.snd hh
  norm_num [firstJet, smul_eq_mul, op_smul_eq_smul, TrivSqZeroExt.fst_natCast] at hs ⊢
  exact hs

theorem soclePower_true_coefficient (r : ℂ) :
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 0 := by
  have hh : firstJet (powerCoefficient r true (soclePower r true)) = 0 := by
    rw [firstJet_powerCoefficient, jetEmbedding_soclePower_true, map_zero]
  exact congrArg TrivSqZeroExt.snd hh

/-- The actual Laurent-series functional evaluates the published socle
representative to 3r at denominator (x₁x₃)²x₂⁴. -/
theorem cechResidue_socle (r : ℂ) :
    cechResidue r (mon 1 8 0 0) 2 4 = 3*r := by
  simp only [cechResidue, fractionResidue_double_pole]
  change PowerSeries.coeff 1 (powerCoefficient r false (soclePower r false)) -
    PowerSeries.coeff 1 (powerCoefficient r true (soclePower r true)) = 3*r
  rw [soclePower_false_coefficient, soclePower_true_coefficient, sub_zero]

theorem endpointResidue_scalar (r : ℂ) (e : Bool) (c : ℂ) (z : LaurentChart r e) :
    endpointResidue r e (laurentBase r e (seriesMap (PowerSeries.C c)) * z) =
      c * endpointResidue r e z := by
  change (laurentCoefficient r e
    (laurentBase r e (seriesMap (PowerSeries.C c)) * z)).coeff (-1) = _
  unfold laurentCoefficient laurentBase
  rw [coefficient_base_mul]
  change (seriesMap (PowerSeries.C c) * laurentCoefficient r e z).coeff (-1) = _
  rw [show seriesMap (PowerSeries.C c) = HahnSeries.single (0 : ℤ) c from
    HahnSeries.ofPowerSeries_C c, HahnSeries.coeff_single_zero_mul]
  rfl

theorem cechResidue_C_mul (r : ℂ) (c : ℂ) (p : Poly) (n m : ℕ) :
    cechResidue r (C c * p) n m = c * cechResidue r p n m := by
  have he (e : Bool) : fraction r e (C c * p) n m =
      laurentBase r e (seriesMap (PowerSeries.C c)) * fraction r e p n m := by
    simp [fraction, laurentEval, powerEval, chartEmbedding, laurentBase, mul_assoc]
  simp only [cechResidue, fractionResidue, he, endpointResidue_scalar]
  ring

theorem cechResidue_sub (r : ℂ) (p q : Poly) (n m : ℕ) :
    cechResidue r (p-q) n m = cechResidue r p n m - cechResidue r q n m := by
  simp only [cechResidue, fractionResidue, fraction_sub, map_sub]
  ring

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_socle
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechThetaCharts.lean -/
section
/-! Actual quotient charts for the family h+θx₀³, including the smooth
incidence seed θ=1.  The added term is reduced using x₀²=rx₁x₃, so the
cubic remains monic in x₂ without changing the curve ideal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS Jet firstJet endpointX endpointY seriesMap uniformizerUnit
  uniformizer_inv_sq unit_pow_cancel)
open MvPolynomial CycleQ2SeedTrace

def betaCoefficient (r θ : ℂ) (e : Bool) : PS :=
  endpointX e ^ 2 + PowerSeries.C θ * PowerSeries.C r * endpointX e * endpointY e

abbrev PowerChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

abbrev LaurentChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

abbrev JetChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def powerBase (r θ : ℂ) (e : Bool) : PS →+* PowerChart r θ e :=
  base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerX0 (r θ : ℂ) (e : Bool) : PowerChart r θ e :=
  x0 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerX2 (r θ : ℂ) (e : Bool) : PowerChart r θ e :=
  x2 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerCoefficient (r θ : ℂ) (e : Bool) : PowerChart r θ e →ₗ[PS] PS :=
  coefficient (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def laurentBase (r θ : ℂ) (e : Bool) : LS →+* LaurentChart r θ e :=
  base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

def laurentCoefficient (r θ : ℂ) (e : Bool) : LaurentChart r θ e →ₗ[LS] LS :=
  coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

def jetBase (r θ : ℂ) (e : Bool) : Jet →+* JetChart r θ e :=
  base (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetX0 (r θ : ℂ) (e : Bool) : JetChart r θ e :=
  x0 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetX2 (r θ : ℂ) (e : Bool) : JetChart r θ e :=
  x2 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetCoefficient (r θ : ℂ) (e : Bool) : JetChart r θ e →ₗ[Jet] Jet :=
  coefficient (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def chartEmbedding (r θ : ℂ) (e : Bool) : PowerChart r θ e →+* LaurentChart r θ e :=
  curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)

def jetEmbedding (r θ : ℂ) (e : Bool) : PowerChart r θ e →+* JetChart r θ e :=
  curveMap firstJet (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)

theorem firstJet_powerCoefficient (r θ : ℂ) (e : Bool) (z : PowerChart r θ e) :
    firstJet (powerCoefficient r θ e z) = jetCoefficient r θ e (jetEmbedding r θ e z) := by
  symm
  exact coefficient_curveMap firstJet _ _ _ _ _ z

theorem endpointNorm_isUnit (r θ : ℂ) (e : Bool) :
    IsUnit (norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (betaCoefficient r θ e)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [isUnit_iff_ne_zero]
  cases e <;>
    norm_num [CycleQ2CechLinearCubic.norm, betaCoefficient, endpointX, endpointY,
      Complex.ext_iff, Complex.I_sq]

def endpointNormUnit (r θ : ℂ) (e : Bool) : PSˣ := (endpointNorm_isUnit r θ e).unit

def powerX2Unit (r θ : ℂ) (e : Bool) : (PowerChart r θ e)ˣ :=
  x2Unit _ _ _ _ _ (endpointNormUnit r θ e) (endpointNorm_isUnit r θ e).unit_spec

@[simp] theorem coe_powerX2Unit (r θ : ℂ) (e : Bool) :
    (powerX2Unit r θ e : PowerChart r θ e) = powerX2 r θ e := rfl

def laurentX2Unit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (chartEmbedding r θ e) (powerX2Unit r θ e)

def jetX2Unit (r θ : ℂ) (e : Bool) : (JetChart r θ e)ˣ :=
  Units.map (jetEmbedding r θ e) (powerX2Unit r θ e)

@[simp] theorem coe_jetX2Unit (r θ : ℂ) (e : Bool) :
    (jetX2Unit r θ e : JetChart r θ e) = jetX2 r θ e := by
  simp [jetX2Unit, jetEmbedding, powerX2, jetX2]

def powerCoordinates (r θ : ℂ) (e : Bool) : Fin 4 → PowerChart r θ e :=
  ![powerX0 r θ e, powerBase r θ e (endpointX e), powerX2 r θ e,
    powerBase r θ e (endpointY e)]

def powerEval (r θ : ℂ) (e : Bool) : Poly →+* PowerChart r θ e :=
  MvPolynomial.eval₂Hom ((powerBase r θ e).comp PowerSeries.C) (powerCoordinates r θ e)

@[simp] theorem powerEval_C (r θ c : ℂ) (e : Bool) :
    powerEval r θ e (C c) = powerBase r θ e (PowerSeries.C c) := by simp [powerEval]

@[simp] theorem powerEval_X_zero (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 0) = powerX0 r θ e := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_one (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 1) = powerBase r θ e (endpointX e) := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_two (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 2) = powerX2 r θ e := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_three (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 3) = powerBase r θ e (endpointY e) := by simp [powerEval, powerCoordinates]


theorem powerEval_curveF1 (r θ : ℂ) (e : Bool) : powerEval r θ e (relation r 0) = 0 := by
  simp only [relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    powerEval_C, powerEval_X_zero, powerEval_X_one, powerEval_X_three]
  change x0 _ _ _ _ _ ^ 2 - _ = 0
  rw [x0_sq, sub_eq_zero]
  simp [powerBase, map_mul]

/-- The new chart is bound to the literal smooth-seed equation, not merely
to abstract first-order relations. -/
theorem powerEval_curveH (r θ : ℂ) (e : Bool) : powerEval r θ e (curveH θ) = 0 := by
  have h0 := x0_sq (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)
  have h2 := x2_cubic (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)
  change powerX0 r θ e ^ 2 = powerBase r θ e
    (PowerSeries.C r * endpointX e * endpointY e) at h0
  change powerX2 r θ e ^ 3 + (powerX0 r θ e + powerBase r θ e (endpointX e)) *
      powerBase r θ e (endpointY e) * powerX2 r θ e +
    powerX0 r θ e * powerBase r θ e (betaCoefficient r θ e) +
    powerBase r θ e ((1-PowerSeries.C Complex.I)*endpointY e^3-
      PowerSeries.C Complex.I*endpointX e^3) = 0 at h2
  simp only [betaCoefficient, map_add, map_sub, map_mul, map_pow, map_one] at h0 h2
  simp only [curveH, h, b, map_add, map_sub, map_mul, map_pow,
    powerEval_C, powerEval_X_zero, powerEval_X_one, powerEval_X_two, powerEval_X_three]
  linear_combination h2 + powerBase r θ e (PowerSeries.C θ) * powerX0 r θ e * h0

theorem powerEval_zero_of_curveIdeal (r θ : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r θ) : powerEval r θ e p = 0 := by
  obtain ⟨u,v,hp⟩ := Ideal.mem_span_pair.mp hp
  rw [← hp, map_add, map_mul, map_mul, powerEval_curveF1, powerEval_curveH]
  ring

def curveChart (r θ : ℂ) (e : Bool) : Poly ⧸ curveIdeal r θ →+* PowerChart r θ e :=
  Ideal.Quotient.lift _ (powerEval r θ e) (fun _ hp => powerEval_zero_of_curveIdeal r θ e hp)

def laurentEval (r θ : ℂ) (e : Bool) : Poly →+* LaurentChart r θ e :=
  (chartEmbedding r θ e).comp (powerEval r θ e)

def jetEval (r θ : ℂ) (e : Bool) : Poly →+* JetChart r θ e :=
  (jetEmbedding r θ e).comp (powerEval r θ e)

def chartAUnit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (laurentBase r θ e) uniformizerUnit

theorem laurentEval_curveA (r θ : ℂ) (e : Bool) :
    laurentEval r θ e (X 1 * X 3) = (chartAUnit r θ e : LaurentChart r θ e) := by
  have hp : powerEval r θ e (X 1 * X 3) = powerBase r θ e PowerSeries.X := by
    simp only [map_mul, powerEval_X_one, powerEval_X_three]
    rw [← map_mul]
    congr 1
    cases e <;> simp [endpointX, endpointY]
  change chartEmbedding r θ e (powerEval r θ e (X 1 * X 3)) = _
  rw [hp]
  exact curveMap_base seriesMap _ _ _ _ _ _

def fraction (r θ : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : LaurentChart r θ e :=
  laurentEval r θ e p * ((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^n *
    ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^m

def fractionResidue (r θ : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : ℂ :=
  (laurentCoefficient r θ e (fraction r θ e p n m)).coeff (-1)

def cechResidue (r θ : ℂ) (p : Poly) (n m : ℕ) : ℂ :=
  fractionResidue r θ false p n m - fractionResidue r θ true p n m

theorem fractionResidue_double_pole (r θ : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r θ e p 2 m =
      PowerSeries.coeff 1 (powerCoefficient r θ e
        (powerEval r θ e p * ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^m)) := by
  let z : PowerChart r θ e :=
    powerEval r θ e p * ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^m
  have heq : fraction r θ e p 2 m =
      laurentBase r θ e (((uniformizerUnit⁻¹ : LSˣ) : LS)^2) * chartEmbedding r θ e z := by
    simp only [fraction, laurentEval, RingHom.comp_apply, z, map_mul, map_pow,
      laurentBase, chartAUnit, laurentX2Unit, Units.coe_map_inv, MonoidHom.coe_coe]
    ring
  unfold fractionResidue
  rw [heq]
  unfold laurentCoefficient laurentBase chartEmbedding
  rw [coefficient_base_mul, coefficient_curveMap, uniformizer_inv_sq,
    HahnSeries.coeff_single_mul]
  norm_num [seriesMap, powerCoefficient, PowerSeries.coeff_coe, z]

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.powerEval_curveH
#print axioms CycleQ2SeedCechTheta.fractionResidue_double_pole
end
end

/- Component: continuation_3/cylinder_bridge/SeedCechTraceComparison.lean -/
section
/-! Identification of the published finite Artinian trace with the actual
all-poles Čech residue functional on the sparse seed curve. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

/-- Exact comparison with the previously checked finite trace. -/
theorem cechResidue_eq_trace (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : cechResidue r p 2 4 = (3*r) * traceLinear r p := by
  have hs : (mon 1 8 0 0).IsHomogeneous 9 := by simpa using mon_homogeneous 1 8 0 0
  have hm := homogeneous_degreeNine_mod_trace r hr hp
  have hb := boundary_of_mem_reducedIdeal r (hp.sub (hs.C_mul _)) hm
  have hz := cechResidue_zero_of_boundary r _ 2 4 hb
  rw [cechResidue_sub, cechResidue_C_mul, cechResidue_socle, sub_eq_zero] at hz
  simpa [mul_comm] using hz

/-- The actual degree-one Čech fraction is a coboundary exactly when the
published Artinian trace vanishes.  This includes coboundaries only visible
after increasing either denominator power. -/
theorem cechBoundary_iff_trace_zero (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : CechBoundary r p 2 4 ↔ traceLinear r p = 0 := by
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr
  constructor
  · intro hb
    have hz := cechResidue_zero_of_boundary r p 2 4 hb
    rw [cechResidue_eq_trace r hr hp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hr0)
  · intro ht
    have hm := homogeneous_degreeNine_mod_trace r hr hp
    simp only [ht, map_zero, zero_mul, sub_zero] at hm
    exact boundary_of_mem_reducedIdeal r hp hm

/-- In degree nine, allowing higher Čech denominator powers introduces no
additional relations beyond the actual four-generator Artinian ideal. -/
theorem cechBoundary_iff_mem_reducedIdeal (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : CechBoundary r p 2 4 ↔ p ∈ reducedIdeal r := by
  constructor
  · intro hb
    have ht := (cechBoundary_iff_trace_zero r hr hp).mp hb
    have hm := homogeneous_degreeNine_mod_trace r hr hp
    simpa only [ht, map_zero, zero_mul, sub_zero] using hm
  · exact boundary_of_mem_reducedIdeal r hp

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_eq_trace
#print axioms CycleQ2SeedCech.cechBoundary_iff_trace_zero
#print axioms CycleQ2SeedCech.cechBoundary_iff_mem_reducedIdeal
end
end
