import Proposal.GeometricFermatStrictGrowth
import Mathlib.Algebra.Module.LinearMap.Rat
import Proposal.GeometricUniversalJacobianFrames
import Proposal.IncidenceBasepointCharts
import Proposal.GeometricLocalizedDerivations
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Reduction of Fermat residues at split and inert primes

Parameter differentiation and coordinate pole removal give rising-factorial
coefficients in characteristic zero. The integral numerator after cancellation
has complementary support in the two prime residue classes. On the graded
Fermat monomials its nonzero entries recover the two orientations of the
strict-growth graph.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
namespace CycleQ2FermatPrimeCoefficient

section RationalPole
variable {K : Type*} [Field K] [CharZero K] (D : Derivation ℚ K K)

private theorem inverse_pole (F : K) (k : ℕ) :
    D (F⁻¹^(k+1)) = -(k+1:K)*D F*F⁻¹^(k+2) := by
  rw [D.leibniz_pow,D.leibniz_inv]
  simp [nsmul_eq_mul,smul_eq_mul,pow_add]
  ring

/-- Ordinary differentiation of a rational pole in a linear parameter
direction whose variation t and numerator A are constant. -/
theorem differentiate_pole (A F t : K) (hA : D A = 0) (hF : D F = t) (ht : D t = 0)
    (k n : ℕ) :
    D^[n] (A * F⁻¹^(k+1)) =
      (-1)^n * ((k+1).ascFactorial n : K) * A * t^n * F⁻¹^(k+n+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply',ih]
    have hc : D ((-1)^n * ((k+1).ascFactorial n : K) * A * t^n) = 0 := by
      simp [D.leibniz,hA,ht]
    rw [D.leibniz,hc,inverse_pole,hF]
    simp [smul_eq_mul,Nat.ascFactorial_succ,pow_succ,pow_add]
    ring

/-- One Fermat reduction step, written as an actual derivative. For n=0
the second term by itself is exact and has the forbidden exponent d-1. -/
theorem coordinate_pole_step (A x F : K) (e n k : ℕ) (hA : D A = 0) (hx : D x = 1)
    (hF : D F = (e+1 : K)*x^e) :
    D (A*x^n*F⁻¹^(k+1)) =
      (n:K)*A*x^(n-1)*F⁻¹^(k+1) - (k+1:K)*(e+1:K)*A*x^(n+e)*F⁻¹^(k+2) := by
  rw [D.leibniz,inverse_pole,D.leibniz,D.leibniz_pow,hA,hx,hF]
  simp [nsmul_eq_mul,smul_eq_mul,pow_add]
  ring

/-- Cancel the characteristic-zero denominators before reduction modulo a
prime dividing an intermediate factor. -/
theorem factorial_cancellation (k n l q : ℕ) (hk : 0 < k) (hl : 0 < l) (h : l + q = k+n) :
    (k.ascFactorial n : ℚ) / ((k+n-1).descFactorial q : ℚ) =
      ((l-1).factorial : ℚ) / ((k-1).factorial : ℚ) := by
  have ha := Nat.factorial_mul_ascFactorial' k n hk
  have hb := Nat.factorial_mul_ascFactorial' l q hl
  have hd : (k+n-1).descFactorial q = l.ascFactorial q := by
    rw [← h,Nat.add_descFactorial_eq_ascFactorial']
  rw [hd]
  have hlu : l.ascFactorial q ≠ 0 := by
    cases l with
    | zero => omega
    | succ l => exact Nat.ne_of_gt (Nat.ascFactorial_pos l q)
  field_simp
  exact_mod_cast (show k.ascFactorial n * (k-1).factorial = l.ascFactorial q * (l-1).factorial by
    rw [Nat.mul_comm,ha,Nat.mul_comm (l.ascFactorial q),hb,h])

end RationalPole

/-- Integer numerator factors accumulated while reducing a single exponent
modulo the Fermat derivative. The last residue exponent is b. -/
def rowFactor (p d q b : ℕ) : ZMod p :=
  if b + 1 = d then 0 else
    ∏ j ∈ Finset.range q, ((b + 1 + d*j : ℕ) : ZMod p)

private theorem strip {p d a m q b : ℕ} (hp : d < p) (ha : a + 1 < d)
    (hb : b < d) (he : a + p*m = d*q + b) :
    (b + 1 ≠ d ∧ ∀ j < q, ¬p ∣ b+1+d*j) ↔
    ∀ h ≤ m, ¬d ∣ a+1+p*h := by
  constructor
  · rintro ⟨hend,hstrip⟩ h hm ⟨t,ht⟩
    by_cases eq : h = m
    · subst h
      have hbd : d ∣ b+1 := by
        apply (Nat.dvd_add_iff_right (dvd_mul_right d q)).mpr
        exact ⟨t,by omega⟩
      exact hend (by have := Nat.le_of_dvd (by omega) hbd; omega)
    · have hmul := Nat.mul_le_mul_left p (show h+1 ≤ m by omega)
      rw [Nat.mul_succ] at hmul
      have htq : t ≤ q := by
        apply Nat.le_of_mul_le_mul_left _ (by omega : 0 < d)
        omega
      have htpos : 0 < t := by
        by_contra! hz
        simp [show t = 0 by omega] at ht
      apply hstrip (q-t) (by omega)
      refine ⟨m-h, ?_⟩
      rw [Nat.mul_sub,Nat.mul_sub]
      omega
  · intro nohit
    constructor
    · intro eq
      exact nohit m le_rfl ⟨q+1,by rw [Nat.mul_succ]; omega⟩
    · rintro j hj ⟨k,hk⟩
      have hmul := Nat.mul_le_mul_left d (show j+1 ≤ q by omega)
      rw [Nat.mul_succ] at hmul
      have hkpos : 0 < k := by
        by_contra! hz
        simp [show k = 0 by omega] at hk
      have hkm : k ≤ m := by
        by_contra! hm
        have hh := Nat.mul_le_mul_left p (show m+1 ≤ k by omega)
        rw [Nat.mul_succ] at hh
        omega
      apply nohit (m-k) (Nat.sub_le _ _)
      refine ⟨q-j,?_⟩
      rw [Nat.mul_sub,Nat.mul_sub]
      omega

theorem rowFactor_ne_zero_iff {p d a m q b : ℕ} [Fact p.Prime] (hp : d < p)
    (ha : a + 1 < d) (hb : b < d) (he : a + p*m = d*q + b) :
    rowFactor p d q b ≠ 0 ↔ ∀ h ≤ m, ¬d ∣ a+1+p*h := by
  rw [← strip hp ha hb he]
  by_cases hd : b+1 = d
  · simp [rowFactor,hd]
  · simp only [rowFactor,if_neg hd,Finset.prod_ne_zero_iff,Finset.mem_range,
      and_iff_right hd]
    apply forall_congr'
    intro j
    exact forall_congr' (fun _ => not_congr (ZMod.natCast_eq_zero_iff _ _))

/-- At a split prime, exponent addition must stay inside the Fermat basis. -/
theorem rowFactor_split {p d a m q b : ℕ} [Fact p.Prime] (hp : d < p)
    (ha : a + 1 < d) (hb : b < d) (he : a + p*m = d*q + b)
    (hpd : p ≡ 1 [MOD d]) :
    rowFactor p d q b ≠ 0 ↔ a+m+1 < d := by
  rw [rowFactor_ne_zero_iff hp ha hb he]
  have corr (h : ℕ) : d ∣ a+1+p*h ↔ d ∣ a+1+h := by
    simpa only [one_mul] using ((hpd.mul_right h).add_left (a+1)).dvd_iff (dvd_refl d)
  constructor
  · intro hh
    by_contra! hx
    apply hh (d-(a+1)) (by omega)
    exact (corr _).mpr (by rw [show a+1+(d-(a+1)) = d by omega])
  · intro hs h hm hh
    have := Nat.le_of_dvd (by omega) ((corr h).mp hh)
    omega

/-- At an inert prime, the tangent exponent must be subtractable. -/
theorem rowFactor_inert {p d a m q b : ℕ} [Fact p.Prime] (hp : d < p)
    (ha : a + 1 < d) (hb : b < d) (he : a + p*m = d*q + b)
    (hpd : d ∣ p+1) :
    rowFactor p d q b ≠ 0 ↔ m ≤ a := by
  rw [rowFactor_ne_zero_iff hp ha hb he]
  constructor
  · intro hh
    by_contra! hx
    apply hh (a+1) (by omega)
    simpa only [Nat.add_mul,one_mul,Nat.add_comm (a+1)] using dvd_mul_of_dvd_left hpd (a+1)
  · intro hs h hm hh
    have hx : a+1+p*h = (a+1-h)+(p+1)*h := by
      rw [Nat.add_mul,one_mul]
      omega
    rw [hx] at hh
    have hd := (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hpd h)).mpr hh
    have := Nat.le_of_dvd (by omega) hd
    omega

open CycleQ2FermatHiggs
open CycleQ2FermatVariationAlgebra (lowerExponent lowerExponent_properties)

def degree (k : Fin 5) := socle k + 2
private theorem deg_dvd (k : Fin 5) : degree k ∣ 6 := by fin_cases k <;> decide
private theorem deg_le (k : Fin 5) : degree k ≤ 6 :=
  Nat.le_of_dvd (by decide) (deg_dvd k)
private theorem deg_pos (k : Fin 5) : 0 < degree k := by simp [degree]

abbrev Tuple := Fin 5 → ℕ
def count (p : ℕ) (a m : Tuple) (k : Fin 5) := (a k + p*m k) / degree k
def terminal (p : ℕ) (a m : Tuple) (k : Fin 5) := (a k + p*m k) % degree k
private theorem division (p : ℕ) (a m : Tuple) (k : Fin 5) :
    a k + p*m k = degree k * count p a m k + terminal p a m k :=
  (Nat.div_add_mod _ _).symm
private theorem tail_lt (p : ℕ) (a m : Tuple) (k : Fin 5) : terminal p a m k < degree k :=
  Nat.mod_lt _ (deg_pos k)

/-- The five coordinate factors of the reduced residue, including division
by the Fermat degree at each step. Only its actual terminal exponent can
receive a coefficient. -/
noncomputable def reducedEntry (p : ℕ) [Fact p.Prime] (a m out : Tuple) : ZMod p :=
  if terminal p a m = out then
    ∏ k, rowFactor p (degree k) (count p a m k) (terminal p a m k) /
      (degree k : ZMod p)^(count p a m k)
  else 0

private theorem entry_iff {p : ℕ} [Fact p.Prime] (hp : 6 < p) (a m out : Tuple) :
    reducedEntry p a m out ≠ 0 ↔ terminal p a m = out ∧
      ∀ k, rowFactor p (degree k) (count p a m k) (terminal p a m k) ≠ 0 := by
  have hd (k : Fin 5) : (degree k : ZMod p) ≠ 0 := by
    intro h
    have hh := Nat.le_of_dvd (deg_pos k) ((ZMod.natCast_eq_zero_iff _ _).mp h)
    have := deg_le k
    omega
  by_cases e : terminal p a m = out
  · simp [reducedEntry,e,Finset.prod_ne_zero_iff,hd]
  · simp [reducedEntry,e]

theorem reducedEntry_split {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (a m out : Tuple) (ha : ∀ k, a k ≤ socle k) (ho : ∀ k, out k ≤ socle k) :
    reducedEntry p a m out ≠ 0 ↔ ∀ k, a k + m k = out k := by
  rw [entry_iff hp]
  have congru (k : Fin 5) : p ≡ 1 [MOD degree k] := hs.of_dvd (deg_dvd k)
  have hr (k : Fin 5) := rowFactor_split ((deg_le k).trans_lt hp)
    (show a k+1 < degree k by have := ha k; simp only [degree]; omega)
    (tail_lt p a m k) (division p a m k) (congru k)
  have term (k : Fin 5) (h : a k + m k + 1 < degree k) :
      terminal p a m k = a k + m k := by
    have he := ((congru k).mul_right (m k)).add_left (a k)
    change (a k + p*m k) % degree k = (a k + 1*m k) % degree k at he
    simpa only [terminal,one_mul,Nat.mod_eq_of_lt (show a k + m k < degree k by omega)] using he
  constructor
  · rintro ⟨h,hv⟩ k
    exact (term k ((hr k).mp (hv k))).symm.trans (congrFun h k)
  · intro e
    have h (k : Fin 5) : a k+m k+1 < degree k := by
      rw [e k]
      have := ho k
      simp only [degree]
      omega
    exact ⟨funext (fun k => (term k (h k)).trans (e k)), fun k => (hr k).mpr (h k)⟩

theorem reducedEntry_inert {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hi : 6 ∣ p+1)
    (a m out : Tuple) (ha : ∀ k, a k ≤ socle k) :
    reducedEntry p a m out ≠ 0 ↔ ∀ k, out k + m k = a k := by
  rw [entry_iff hp]
  have hr (k : Fin 5) := rowFactor_inert ((deg_le k).trans_lt hp)
    (show a k+1 < degree k by have := ha k; simp only [degree]; omega)
    (tail_lt p a m k) (division p a m k) ((deg_dvd k).trans hi)
  have term (k : Fin 5) (h : m k ≤ a k) : terminal p a m k = a k-m k := by
    have hsum : a k+p*m k = (a k-m k)+(p+1)*m k := by rw [Nat.add_mul,one_mul]; omega
    have ddiv := dvd_mul_of_dvd_left ((deg_dvd k).trans hi) (m k)
    have hlt : a k-m k < degree k := by have := ha k; simp only [degree]; omega
    unfold terminal
    rw [hsum,Nat.add_mod,Nat.mod_eq_zero_of_dvd ddiv,add_zero,Nat.mod_mod,Nat.mod_eq_of_lt hlt]
  constructor
  · rintro ⟨h,hv⟩ k
    have hle := (hr k).mp (hv k)
    rw [← congrFun h k,term k hle,Nat.sub_add_cancel hle]
  · intro e
    have h (k : Fin 5) : m k ≤ a k := by have := e k; omega
    refine ⟨funext (fun k => (term k (h k)).trans ?_), fun k => (hr k).mpr (h k)⟩
    exact Nat.sub_eq_of_eq_add (e k).symm

/-- In the actual upper/lower monomial bases, every split prime gives the
forward edges of the checked 35-matrix matching graph. -/
theorem forward_support {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (m : Fin 35) (i j : Fin 33) :
    reducedEntry p (basisMonomial i) (tangentMonomial m) (lowerExponent j) ≠ 0 ↔
      complement m i = some j := by
  rw [reducedEntry_split hp hs _ _ _ (basis_properties i).2.2 (lowerExponent_properties j).2.2,
    complement_spec]
  apply forall_congr'
  intro k
  have := (basis_properties j).2.2 k
  unfold lowerExponent
  omega

/-- Inert primes reverse exactly the same edges, in the same bases. -/
theorem reverse_support {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hi : p ≡ 5 [MOD 6])
    (m : Fin 35) (i j : Fin 33) :
    reducedEntry p (lowerExponent j) (tangentMonomial m) (basisMonomial i) ≠ 0 ↔
      complement m i = some j := by
  have hdiv : 6 ∣ p+1 := by change p%6 = 5%6 at hi; omega
  rw [reducedEntry_inert hp hdiv _ _ _ (lowerExponent_properties j).2.2,complement_spec]
  apply forall_congr'
  intro k
  have := (basis_properties j).2.2 k
  unfold lowerExponent
  omega

abbrev Sector := Sum (Fin 33) (Fin 33)
def source : Sector → Tuple
  | .inl i => basisMonomial i
  | .inr j => lowerExponent j
def pole : Sector → ℕ
  | .inl _ => 2
  | .inr _ => 3

private theorem weight_source (s : Sector) : weightedDegree (source s) + 6 = 6 * pole s := by
  rcases s with i|j
  · simp [source,pole,(basis_properties i).1]
  · simp [source,pole,(lowerExponent_properties j).1]
private theorem source_bound (s : Sector) : ∀ k, source s k ≤ socle k := by
  rcases s with i|j
  · exact (basis_properties i).2.2
  · exact (lowerExponent_properties j).2.2
private theorem wt_add (a b : Tuple) :
    weightedDegree (fun k => a k+b k) = weightedDegree a+weightedDegree b := by
  unfold weightedDegree
  ring
private theorem wt_smul (c : ℕ) (a : Tuple) :
    weightedDegree (fun k => c*a k) = c*weightedDegree a := by
  unfold weightedDegree
  ring
private theorem wt_steps (a : Tuple) : weightedDegree (fun k => degree k*a k) = 6*∑ k,a k := by
  change 6*a 0 + 6*a 1 + 6*a 2 + 6*a 3 + 2*(3*a 4) = _
  simp [Fin.sum_univ_succ]
  ring

/-- The ordinary pole index after all the coordinate reductions. -/
def reducedPole (p : ℕ) (s : Sector) (m : Fin 35) :=
  pole s+p - ∑ k, count p (source s) (tangentMonomial m) k

/-- Stripping a coordinate Fermat power lowers the weight by six and the pole by one. -/
theorem terminal_weight (n : ℕ) (s : Sector) (m : Fin 35) :
    weightedDegree (terminal n (source s) (tangentMonomial m)) + 6 = 6 * reducedPole n s m := by
  let a := source s
  let t := tangentMonomial m
  have he : (fun k => a k+n*t k) =
      (fun k => degree k * count n a t k + terminal n a t k) :=
    funext (division n a t)
  have e := congrArg weightedDegree he
  rw [wt_add,wt_smul,wt_add,wt_steps] at e
  have ht : weightedDegree t = 6 := (tangent_properties m).1
  have ha : weightedDegree a + 6 = 6 * pole s := weight_source s
  rw [ht] at e
  change weightedDegree (terminal n a t) + 6 = 6*(pole s+n-∑ k, count n a t k)
  omega

theorem reducedPole_eq {p : ℕ} (s u : Sector) (m : Fin 35)
    (h : terminal p (source s) (tangentMonomial m) = source u) :
    reducedPole p s m = pole u := by
  have e := terminal_weight p s m
  rw [h,weight_source] at e
  omega

/-- The order-three character survives all five coordinate reductions. -/
theorem terminal_character (n : ℕ) (s : Sector) (m : Fin 35) :
    character (terminal n (source s) (tangentMonomial m)) = 1 := by
  let a := source s
  let t := tangentMonomial m
  let w (v : Tuple) := 2*v 0 + 2*v 1 + v 2
  have h (k : Fin 5) : terminal n a t k ≡ a k + n*t k [MOD 3] :=
    (Nat.mod_modEq _ (degree k)).of_dvd (show 3 ∣ degree k by fin_cases k <;> decide)
  have ha : w a ≡ 1 [MOD 3] := by
    rcases s with i|j
    · exact (basis_properties i).2.1
    · exact (lowerExponent_properties j).2.1
  have ht : w t ≡ 0 [MOD 3] := (tangent_properties m).2.1
  have hm := (((h 0).mul_left 2).add ((h 1).mul_left 2)).add (h 2)
  have he : 2*(a 0+n*t 0)+2*(a 1+n*t 1)+(a 2+n*t 2) = w a + n*w t := by dsimp [w]; ring
  rw [he] at hm
  exact hm.trans (by simpa using ha.add (ht.mul_left n))

/-- Every terminal has pole at least two, including terms with a forbidden
exponent. Thus a forbidden terminal can be removed by an ordinary spatial derivative. -/
theorem two_le_reducedPole (n : ℕ) (s : Sector) (m : Fin 35) : 2 ≤ reducedPole n s m := by
  have hw := terminal_weight n s m
  have hc := terminal_character n s m
  unfold character at hc
  unfold weightedDegree at hw
  omega

private theorem source_injective : Function.Injective source := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (basis_injective h)
  · have hh := congrArg weightedDegree h
    simp [source,(basis_properties i).1,(lowerExponent_properties j).1] at hh
  · have hh := congrArg weightedDegree h
    simp [source,(lowerExponent_properties i).1,(basis_properties j).1] at hh
  · exact congrArg Sum.inr (CycleQ2FermatVariationAlgebra.lowerIndex_injective
      (Subtype.ext (congrArg CycleQ2FermatJacobian.exponent h)))

/-- Every bounded terminal is exactly one upper or lower Fermat residue monomial. -/
theorem unique_terminal_sector (n : ℕ) (s : Sector) (m : Fin 35)
    (hb : ∀ k, terminal n (source s) (tangentMonomial m) k ≤ socle k) :
    ∃! u : Sector, terminal n (source s) (tangentMonomial m) = source u ∧
      reducedPole n s m = pole u := by
  let b := terminal n (source s) (tangentMonomial m)
  have hw : weightedDegree b + 6 = 6 * reducedPole n s m := terminal_weight n s m
  have hc : character b = 1 := terminal_character n s m
  have bd (k : Fin 5) : b k ≤ socle k := hb k
  have hd : weightedDegree b = 6 ∨ weightedDegree b = 12 := by
    have b0 := bd 0
    have b1 := bd 1
    have b2 := bd 2
    have b3 := bd 3
    have b4 := bd 4
    change b 0 ≤ 4 at b0
    change b 1 ≤ 4 at b1
    change b 2 ≤ 4 at b2
    change b 3 ≤ 4 at b3
    change b 4 ≤ 1 at b4
    have hmax : weightedDegree b ≤ 18 := by unfold weightedDegree; omega
    have hneq : weightedDegree b ≠ 18 := by
      intro eq
      unfold weightedDegree at eq
      have e0 : b 0 = 4 := by omega
      have e1 : b 1 = 4 := by omega
      have e2 : b 2 = 4 := by omega
      simp [character,e0,e1,e2] at hc
    have hmin := two_le_reducedPole n s m
    omega
  obtain ⟨u,hu⟩ : ∃ u : Sector, b = source u := by
    let e := CycleQ2FermatJacobian.exponent b
    have eb : e ∈ CycleQ2FermatJacobian.bounded := hb
    rcases hd with hd|hd
    · obtain ⟨i,hi⟩ := CycleQ2FermatJacobian.basis_complete_bounded e eb hd hc
      exact ⟨.inl i, funext (fun k => (DFunLike.congr_fun hi k).symm)⟩
    · obtain ⟨j,hj⟩ := CycleQ2FermatVariationAlgebra.lower_complete_bounded e eb hd hc
      exact ⟨.inr j, funext (fun k => (DFunLike.congr_fun hj k).symm)⟩
  exact ⟨u,⟨hu,reducedPole_eq s u m hu⟩,fun v hv => source_injective (hv.1.symm.trans hu)⟩

/-- Exhaustive alternatives for a reduced term at every derivative order. -/
theorem terminal_classification (n : ℕ) (s : Sector) (m : Fin 35) :
    (∃ k, terminal n (source s) (tangentMonomial m) k = degree k - 1) ∨
      ∃! u : Sector, terminal n (source s) (tangentMonomial m) = source u ∧
        reducedPole n s m = pole u := by
  by_cases h : ∃ k, terminal n (source s) (tangentMonomial m) k = degree k - 1
  · exact Or.inl h
  · apply Or.inr
    apply unique_terminal_sector
    intro k
    have hn : terminal n (source s) (tangentMonomial m) k ≠ degree k - 1 := fun hk => h ⟨k,hk⟩
    have ht := tail_lt n (source s) (tangentMonomial m) k
    unfold degree at ht hn
    omega

/-- The coefficient of the specified output monomial in the Fermat
reduction formula, including the signed pole-factorial ratio. -/
noncomputable def primeEntry (p : ℕ) [Fact p.Prime] (s : Sector) (m : Fin 35) (u : Sector) : ZMod p :=
  (-1)^p * ((reducedPole p s m - 1).factorial : ZMod p) / ((pole s - 1).factorial : ZMod p) *
    reducedEntry p (source s) (tangentMonomial m) (source u)

theorem primeEntry_ne_zero_iff {p : ℕ} [Fact p.Prime] (hp : 6 < p) (s u : Sector) (m : Fin 35) :
    primeEntry p s m u ≠ 0 ↔ reducedEntry p (source s) (tangentMonomial m) (source u) ≠ 0 := by
  by_cases e : reducedEntry p (source s) (tangentMonomial m) (source u) = 0
  · simp [primeEntry,e]
  have hterminal : terminal p (source s) (tangentMonomial m) = source u := by
    by_contra! h
    exact e (by simp [reducedEntry,h])
  have h2 : (2:ZMod p) ≠ 0 := by
    intro h
    have hh := Nat.le_of_dvd (show 0 < 2 by decide) ((ZMod.natCast_eq_zero_iff 2 p).mp h)
    omega
  have hf (i : Sector) : ((pole i - 1).factorial : ZMod p) ≠ 0 := by
    cases i <;> simp [pole,h2]
  simp [primeEntry,reducedPole_eq s u m hterminal,hf,e]

private theorem plus_degree {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (s u : Sector) (m : Fin 35) (hn : primeEntry p s m u ≠ 0) : pole u = pole s + 1 := by
  have hrow := (primeEntry_ne_zero_iff hp s u m).mp hn
  have h := (reducedEntry_split hp hs _ _ _ (source_bound s) (source_bound u)).mp hrow
  have eq := congrArg weightedDegree (funext h)
  rw [wt_add,(tangent_properties m).1] at eq
  have := weight_source s
  have := weight_source u
  omega
private theorem minus_degree {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hi : p ≡ 5 [MOD 6])
    (s u : Sector) (m : Fin 35) (hn : primeEntry p s m u ≠ 0) : pole s = pole u + 1 := by
  have hdiv : 6 ∣ p+1 := by change p%6 = 5%6 at hi; omega
  have hrow := (primeEntry_ne_zero_iff hp s u m).mp hn
  have h := (reducedEntry_inert hp hdiv _ _ _ (source_bound s)).mp hrow
  have eq := congrArg weightedDegree (funext h)
  rw [wt_add,(tangent_properties m).1] at eq
  have := weight_source s
  have := weight_source u
  omega

/-- The full 66-coordinate split-prime matrix has only its forward
block, supported on the original complement table. -/
theorem split_support {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (s u : Sector) (m : Fin 35) :
    primeEntry p s m u ≠ 0 ↔
      match s,u with
      | .inl i,.inr j => complement m i = some j
      | _,_ => False := by
  rcases s with i|i <;> rcases u with j|j
  · refine ⟨fun hn => ?_,False.elim⟩
    have := plus_degree hp hs _ _ _ hn; simp [pole] at this
  · exact (primeEntry_ne_zero_iff hp _ _ m).trans (forward_support hp hs m i j)
  · refine ⟨fun hn => ?_,False.elim⟩
    have := plus_degree hp hs _ _ _ hn; simp [pole] at this
  · refine ⟨fun hn => ?_,False.elim⟩
    have := plus_degree hp hs _ _ _ hn; simp [pole] at this

/-- The full inert-prime matrix has precisely the reverse block. -/
theorem inert_support {p : ℕ} [Fact p.Prime] (hp : 6 < p) (hi : p ≡ 5 [MOD 6])
    (s u : Sector) (m : Fin 35) :
    primeEntry p s m u ≠ 0 ↔
      match s,u with
      | .inr j,.inl i => complement m i = some j
      | _,_ => False := by
  rcases s with i|i <;> rcases u with j|j
  · refine ⟨fun hn => ?_,False.elim⟩
    have := minus_degree hp hi _ _ _ hn; simp [pole] at this
  · refine ⟨fun hn => ?_,False.elim⟩
    have := minus_degree hp hi _ _ _ hn; simp [pole] at this
  · exact (primeEntry_ne_zero_iff hp _ _ m).trans (reverse_support hp hi m j i)
  · refine ⟨fun hn => ?_,False.elim⟩
    have := minus_degree hp hi _ _ _ hn; simp [pole] at this

open CycleQ2FermatStrictGrowth

section ScalarExtension
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]

/-- Split diagonal block, with lower indices in the order used by the
Fermat matching theorem. The coefficients may be extended to any field
of the same characteristic. -/
noncomputable def splitBlock (ι : ZMod p →+* K) (m : Fin 35) : Matrix (Fin 33) (Fin 33) K :=
  fun j i => ι (primeEntry p (.inl i) m (.inr j.rev))

/-- The inert block has the reversed source and target. -/
noncomputable def inertBlock (ι : ZMod p →+* K) (m : Fin 35) : Matrix (Fin 33) (Fin 33) K :=
  fun i j => ι (primeEntry p (.inr j.rev) m (.inl i))

theorem split_growth (ι : ZMod p →+* K) (hp : 6 < p) (hs : p ≡ 1 [MOD 6]) :
    RankGrowth K (splitBlock ι) := by
  apply weighted_forward_growth
  intro m i j
  change ι _ ≠ 0 ↔ _
  rw [map_ne_zero,exponentEdge_iff_complement]
  exact split_support hp hs (.inl i) (.inr j.rev) m

theorem inert_growth (ι : ZMod p →+* K) (hp : 6 < p) (hi : p ≡ 5 [MOD 6]) :
    RankGrowth K (inertBlock ι) := by
  apply weighted_reverse_growth
  intro m i j
  change ι _ ≠ 0 ↔ _
  rw [map_ne_zero,exponentEdge_iff_complement]
  exact inert_support hp hi (.inr j.rev) (.inl i) m
end ScalarExtension

section OppositePrimes
variable {K L : Type*} [Field K] [Field L] {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

/-- Stable reductions with the same rank profile in a split and an inert
characteristic must vanish together or equal the full ambient spaces. -/
theorem opposite_prime_dichotomy (ι : ZMod p →+* K) (κ : ZMod q →+* L)
    (hp : 6 < p) (hs : p ≡ 1 [MOD 6]) (hq : 6 < q) (hi : q ≡ 5 [MOD 6])
    (W : Submodule K ((Fin 33 → K) × (Fin 33 → K)))
    (W' : Submodule L ((Fin 33 → L) × (Fin 33 → L)))
    (hW : ∀ m x, x ∈ W → (0, (splitBlock ι m).mulVec x.1) ∈ W)
    (hW' : ∀ m x, x ∈ W' → ((inertBlock κ m).mulVec x.2, 0) ∈ W')
    (hprofile : rankProfile K W = rankProfile L W') :
    (W = ⊥ ∧ W' = ⊥) ∨ (W = ⊤ ∧ W' = ⊤) :=
  nonsplit_dichotomy K (split_growth ι hp hs) (inert_growth κ hq hi) W W' hW hW' hprofile
end OppositePrimes

end CycleQ2FermatPrimeCoefficient


noncomputable section
namespace CycleQ2FermatPrimePencil
open MvPolynomial
open CycleQ2FermatHiggs (basisMonomial tangentMonomial tangent_properties)
open CycleQ2FermatJacobian (Poly exponent fermat)
open CycleQ2FermatPrimeCoefficient (Tuple Sector source pole)
open CycleQ2FermatPrimeCoefficient (differentiate_pole coordinate_pole_step)
open HoldoutConstruction (timePolynomialDerivation extendRingDerivation)
open CycleQ2IncidenceNormalForm (fullInvariantPolynomial fullExponentOf fullInvariantPolynomial_of_homogeneous)

def mon (a : Tuple) : Poly := monomial (exponent a) 1
def pencil (m : Fin 35) : Polynomial Poly :=
  Polynomial.C fermat + Polynomial.X * Polynomial.C (mon (tangentMonomial m))

abbrev P := Polynomial Poly
abbrev L := FractionRing P
abbrev K := FractionRing Poly
abbrev lc := algebraMap P L
abbrev kc := algebraMap Poly K
abbrev constant (v : Poly) := lc (Polynomial.C v)

local instance canonicalIntL : Algebra ℤ L := Ring.toIntAlgebra L
local instance canonicalIntK : Algebra ℤ K := Ring.toIntAlgebra K

local instance ratModuleL : Module ℚ L := @Algebra.toModule ℚ L _ _ (DivisionRing.toRatAlgebra)
local instance ratModuleK : Module ℚ K := @Algebra.toModule ℚ K _ _ (DivisionRing.toRatAlgebra)

local instance smulRatK : SMul ℚ K := ratModuleK.toSMul

private def overRat {B : Type*} [Field B] [CharZero B] (D : Derivation ℤ B B) : Derivation ℚ B B :=
  Derivation.mk' D.toLinearMap.toAddMonoidHom.toRatLinearMap (fun a b => D.leibniz a b)

def time : Derivation ℚ L L :=
  overRat (extendRingDerivation (L:=L) (timePolynomialDerivation (E:=Poly)))

def spatial (i : Fin 5) : Derivation ℚ K K :=
  overRat (extendRingDerivation (L:=K) ((pderiv i : Derivation ℂ Poly Poly).restrictScalars ℤ))

private theorem time_apply (f : P) : time (lc f) = lc (Polynomial.derivative f) :=
  HoldoutConstruction.extendRingDerivation_apply (timePolynomialDerivation (E:=Poly)) f

@[simp] theorem dt_constant (v : Poly) : time (constant v) = 0 := by
  rw [constant,time_apply]
  simp
@[simp] theorem dt_pencil (m : Fin 35) : time (lc (pencil m)) = constant (mon (tangentMonomial m)) := by
  rw [time_apply]
  simp [pencil,constant]
@[simp] theorem partial_apply (i : Fin 5) (f : Poly) : spatial i (kc f) = kc (pderiv i f) :=
  HoldoutConstruction.extendRingDerivation_apply ((pderiv i : Derivation ℂ Poly Poly).restrictScalars ℤ) _

def rationalPole (s : Sector) (m : Fin 35) : L :=
  constant (mon (source s)) * (lc (pencil m))⁻¹^(pole s)

/-- The actual rational pole on every invariant one-parameter Fermat pencil
has the factorial coefficient and monomial numerator of the reduction formula. -/
theorem pencil_derivative (s : Sector) (m : Fin 35) (n : ℕ) :
    time^[n] (rationalPole s m) =
      (-1)^n * ((pole s).ascFactorial n : L) * constant (mon (source s)) *
        constant (mon (tangentMonomial m))^n * (lc (pencil m))⁻¹^(pole s+n) := by
  have h : pole s - 1 + 1 = pole s := by cases s <;> rfl
  simpa only [rationalPole, h, show pole s-1+n+1 = pole s+n by omega] using
    (differentiate_pole time (constant (mon (source s))) (lc (pencil m))
      (constant (mon (tangentMonomial m))) (dt_constant _) (dt_pencil _) (dt_constant _) (pole s-1) n)

/-- Every complex value of the pencil is a specialization of the original
coefficient family, with its own invariant coefficients. -/
theorem pencil_specializes (m : Fin 35) (s : ℂ) :
    let f := (pencil m).eval (C s)
    fullInvariantPolynomial 6 (fun e => coeff (fullExponentOf e.val) f) = f := by
  apply fullInvariantPolynomial_of_homogeneous
  simp only [pencil,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,
    Polynomial.eval_X,mon,C_mul_monomial,mul_one]
  apply CycleQ2GenericSexticGradient.fermat_homogeneous.add
  apply isWeightedHomogeneous_monomial
  exact (CycleQ2GeometricHiggsGradedIndices.weight_eq_iff _ 6 0).mpr
    ⟨(tangent_properties m).1,(tangent_properties m).2.1⟩

private theorem partial_fermat (i : Fin 5) :
    spatial i (kc fermat) = ((CycleQ2FermatJacobian.cutoff i : K)+1) *
      kc (X i)^CycleQ2FermatJacobian.cutoff i := by
  rw [partial_apply,CycleQ2FermatJacobian.derivative_eq,map_mul,
    CycleQ2FermatJacobian.generator,map_pow]
  congr 1
  have : C (CycleQ2FermatJacobian.derivativeScalar i) =
      (CycleQ2FermatJacobian.cutoff i : Poly) + 1 := by
    fin_cases i <;> norm_num [CycleQ2FermatJacobian.cutoff,CycleQ2FermatJacobian.derivativeScalar,
      CycleQ2FermatHiggs.socle,Fin.ext_iff,map_ofNat]
  simp [this]

/-- Actual rational divergence on the Fermat affine cone. The remaining
monomial a is independent of coordinate i. -/
theorem spatial_strip (i : Fin 5) (a : Tuple) (ha : a i = 0) (n k : ℕ) :
    spatial i (kc (mon a) * kc (X i)^n * (kc fermat)⁻¹^(k+1)) =
      (n:K)*kc (mon a)*kc (X i)^(n-1)*(kc fermat)⁻¹^(k+1) -
      (k+1:K)*(CycleQ2FermatJacobian.cutoff i+1:K)*kc (mon a)*
        kc (X i)^(n+CycleQ2FermatJacobian.cutoff i)*(kc fermat)⁻¹^(k+2) := by
  apply coordinate_pole_step
  · simp [mon,ha]
  · simp
  · exact partial_fermat i


/-- Rational densities modulo linear combinations of divergences whose
primitives have poles only on the actual Fermat hypersurface. -/
def divergences : Submodule ℚ K :=
  Submodule.span ℚ {z : K | ∃ (i : Fin 5) (f : Poly) (k : ℕ),
    z = spatial i (kc f * (kc fermat)⁻¹^k)}
abbrev Classes := K ⧸ divergences
abbrev toClass : K →ₗ[ℚ] Classes := divergences.mkQ

private theorem kill (i : Fin 5) (f : Poly) (n k : ℕ) :
    toClass (spatial i (kc f * kc (X i)^n * (kc fermat)⁻¹^k)) = 0 :=
  (Submodule.Quotient.mk_eq_zero divergences).mpr
    (Submodule.subset_span (show ∃ (j : Fin 5) (g : Poly) (l : ℕ),
      spatial i (kc f * kc (X i)^n * (kc fermat)⁻¹^k) = spatial j (kc g * (kc fermat)⁻¹^l) from
        ⟨i,f*X i^n,k,by rw [map_mul kc,map_pow kc]⟩))

def coordinateClass (i : Fin 5) (a : Tuple) (n k : ℕ) : Classes :=
  toClass (kc (mon a)*kc (X i)^n*(kc fermat)⁻¹^k)

private theorem class_step (i : Fin 5) (a : Tuple) (ha : a i = 0) (n k : ℕ) :
    coordinateClass i a (n+CycleQ2FermatJacobian.cutoff i) (k+2) =
      ((n:ℚ)/((k+1:ℚ)*(CycleQ2FermatJacobian.cutoff i+1:ℚ))) •
        coordinateClass i a (n-1) (k+1) := by
  let L₀ := kc (mon a)*kc (X i)^(n-1)*(kc fermat)⁻¹^(k+1)
  let H := kc (mon a)*kc (X i)^(n+CycleQ2FermatJacobian.cutoff i)*(kc fermat)⁻¹^(k+2)
  let c := (k+1:ℚ)*(CycleQ2FermatJacobian.cutoff i+1:ℚ)
  have sc : spatial i (kc (mon a) * kc (X i)^n * (kc fermat)⁻¹^(k+1)) =
      (n:ℚ) • L₀ - c • H := by
    rw [spatial_strip i a ha]
    have scalar (r : ℚ) (w : K) : r • w = (r:K)*w := @Algebra.smul_def ℚ K _ _ DivisionRing.toRatAlgebra r w
    rw [scalar,scalar]
    simp [L₀,H,c]
    ring
  have ht := congrArg toClass sc
  rw [kill,map_sub] at ht
  have hL : toClass ((n:ℚ) • L₀) = (n:ℚ) • toClass L₀ := toClass.map_smul _ _
  have hH : toClass (c • H) = c • toClass H := toClass.map_smul _ _
  rw [hL,hH] at ht
  have rel : c • toClass H = (n:ℚ) • toClass L₀ := (sub_eq_zero.mp ht.symm).symm
  have hc : c ≠ 0 := by dsimp [c]; positivity
  change toClass H = ((n:ℚ)/c) • toClass L₀
  calc
    _ = c⁻¹ • (c • toClass H) := by rw [← mul_smul,inv_mul_cancel₀ hc,one_smul]
    _ = _ := by rw [rel,← mul_smul,div_eq_mul_inv,mul_comm]

/-- All q removals of one Fermat power in the actual rational divergence
quotient, including the successive divisions by the previous pole indices. -/
theorem full_coordinate_strip (i : Fin 5) (a : Tuple) (ha : a i = 0) (b k q : ℕ) :
    let d := CycleQ2FermatPrimeCoefficient.degree i
    coordinateClass i a (b+d*q) (k+1+q) =
      ((∏ j ∈ Finset.range q, (b+1+d*j : ℚ)/d) /
        ((k+1).ascFactorial q : ℚ)) • coordinateClass i a b (k+1) := by
  dsimp only
  let d := CycleQ2FermatPrimeCoefficient.degree i
  have hd : d = CycleQ2FermatJacobian.cutoff i+1 := rfl
  induction q with
  | zero => simp
  | succ q ih =>
    have h := class_step i a ha (b+d*q+1) (k+q)
    have e : b+d*(q+1) = b+d*q+1+CycleQ2FermatJacobian.cutoff i := by rw [Nat.mul_succ]; omega
    change coordinateClass i a (b+d*(q+1)) (k+1+(q+1)) = _
    rw [e,show k+1+(q+1) = k+q+2 by omega,h,Nat.add_sub_cancel,
      show k+q+1 = k+1+q by omega,ih,← mul_smul,Finset.prod_range_succ,Nat.ascFactorial_succ]
    congr 1
    change _ = (∏ j ∈ Finset.range q, (b+1+d*j : ℚ)/d) * _ / _
    push_cast
    rw [show (CycleQ2FermatJacobian.cutoff i:ℚ)+1 = d by exact_mod_cast hd.symm]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring


def density (v : Tuple) (k : ℕ) : Classes := toClass (kc (mon v)*(kc fermat)⁻¹^k)

private theorem mon_update (v : Tuple) (i : Fin 5) (hv : v i = 0) (n : ℕ) :
    mon (Function.update v i n) = mon v * X i ^ n := by
  rw [mon,mon,X_pow_eq_monomial,monomial_mul,one_mul]
  apply congrArg (fun e : Fin 5 →₀ ℕ => monomial e (1:ℂ))
  ext j
  by_cases h : j = i
  · subst j; simp [hv]
  · simp [h]

private theorem coor_update (v : Tuple) (i : Fin 5) (hv : v i = 0) (n k : ℕ) :
    coordinateClass i v n k = density (Function.update v i n) k := by
  simp [density,coordinateClass,mon_update v i hv n]

def rowQ (i : Fin 5) (b q : ℕ) : ℚ :=
  ∏ j ∈ Finset.range q, (b+1+CycleQ2FermatPrimeCoefficient.degree i*j : ℚ) /
    (CycleQ2FermatPrimeCoefficient.degree i : ℚ)

/-- All five ordered Fermat reductions hold in the quotient by the genuine
rational coordinate divergences, with one common pole-factorial denominator. -/
theorem all_coordinate_strip (b q : Tuple) (k : ℕ) :
    let d := CycleQ2FermatPrimeCoefficient.degree
    density (fun i => b i+d i*q i) (k+1+∑ i,q i) =
      ((∏ i,rowQ i (b i) (q i)) / ((k+1).ascFactorial (∑ i,q i) : ℚ)) • density b (k+1) := by
  let d := CycleQ2FermatPrimeCoefficient.degree
  let v (T : Finset (Fin 5)) (i : Fin 5) := if i ∈ T then b i+d i*q i else b i
  suffices hAll : ∀ T : Finset (Fin 5),
      density (v T) (k+1+∑ i ∈ T,q i) =
        ((∏ i ∈ T,rowQ i (b i) (q i)) / ((k+1).ascFactorial (∑ i ∈ T,q i) : ℚ)) •
          density b (k+1) by
    simpa [v,d] using hAll Finset.univ
  intro T
  induction T using Finset.induction with
  | empty => simp [v]
  | @insert i T hi ih =>
    let a := Function.update (v T) i 0
    let N := ∑ j ∈ T, q j
    have hz : a i = 0 := Function.update_self _ _ _
    have he0 : Function.update a i (b i) = v T := by
      funext j
      by_cases hj : j=i
      · subst j; simp [v,hi]
      · simp [a,hj]
    have he1 : Function.update a i (b i+d i*q i) = v (insert i T) := by
      funext j
      by_cases hj : j=i
      · subst j; simp [v]
      · simp [a,v,hj]
    have h := full_coordinate_strip i a hz (b i) (k+N) (q i)
    change coordinateClass i a (b i+d i*q i) (k+N+1+q i) =
      (rowQ i (b i) (q i) / ((k+N+1).ascFactorial (q i):ℚ)) •
        coordinateClass i a (b i) (k+N+1) at h
    rw [coor_update a i hz,coor_update a i hz,he0,he1,show k+N+1=k+1+N by omega] at h
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    change density (v (insert i T)) (k+1+(q i+N)) = _
    rw [show k+1+(q i+N) = k+1+N+q i by omega,h,ih,← mul_smul]
    congr 1
    change _ = _ / ((k+1).ascFactorial (q i+N):ℚ)
    rw [Nat.add_comm (q i) N,← Nat.ascFactorial_mul_ascFactorial]
    push_cast
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring


private theorem mon_add (u v : Tuple) :
    mon (fun i => u i+v i) = mon u * mon v := by
  rw [mon,mon,mon,monomial_mul,one_mul,CycleQ2FermatJacobian.exponent_add]

private theorem mon_rising (u v : Tuple) (n : ℕ) :
    mon (fun i => u i+n*v i) = mon u * mon v^n := by
  induction n with
  | zero => simp
  | succ n h =>
    have e : (fun i => u i + (n+1)*v i) = (fun i => (u i+n*v i) + v i) := by
      funext i
      rw [Nat.succ_mul,Nat.add_assoc]
    rw [e,mon_add,h,pow_succ,mul_assoc]

private theorem fermat_ne_zero : fermat ≠ 0 := by
  intro h
  have e := congrArg (eval (fun _ : Fin 5 => (1:ℂ))) h
  norm_num [fermat] at e

def atZero : P →+* K := kc.comp (Polynomial.evalRingHom 0)
private theorem atZero_pencil (m : Fin 35) : atZero (pencil m) = kc fermat := by
  simp [atZero,pencil,Polynomial.coe_evalRingHom]
private theorem atZero_C (v : Poly) : atZero (Polynomial.C v) = kc v := by
  simp [atZero,Polynomial.coe_evalRingHom]

abbrev Regular (m : Fin 35) := Localization.Away (pencil m)
def sectionOfDerivative (s : Sector) (m : Fin 35) (n : ℕ) : Regular m :=
  (-1)^n * ((pole s).ascFactorial n : Regular m) *
    algebraMap P (Regular m) (Polynomial.C (mon (fun i => source s i+n*tangentMonomial m i))) *
    (IsLocalization.Away.invSelf (pencil m))^(pole s+n)

private theorem reg_value {B : Type*} [Field B] (g : P →+* B) (s : Sector) (m : Fin 35)
    (hg : IsUnit (g (pencil m))) (n : ℕ) :
    IsLocalization.Away.lift (S:=Regular m) (pencil m) hg (sectionOfDerivative s m n) =
      (-1)^n * ((pole s).ascFactorial n:B) *
        g (Polynomial.C (mon (fun i => source s i+n*tangentMonomial m i))) *
        (g (pencil m))⁻¹^(pole s+n) := by
  let φ : Regular m →+* B := IsLocalization.Away.lift (pencil m) hg
  have hinv : φ (IsLocalization.Away.invSelf (pencil m)) = (g (pencil m))⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have e := congrArg φ (IsLocalization.Away.mul_invSelf (S:=Regular m) (pencil m))
    rw [map_mul,map_one,IsLocalization.Away.lift_eq] at e
    simpa only [mul_comm] using e
  change φ _ = _
  simp only [sectionOfDerivative,map_mul,map_pow,map_neg,map_one,map_natCast,hinv]
  rw [IsLocalization.Away.lift_eq]

theorem generic_unit (m : Fin 35) : IsUnit (lc (pencil m)) := by
  have h : pencil m ≠ 0 := by
    intro h
    have := congrArg atZero h
    rw [atZero_pencil,map_zero] at this
    exact fermat_ne_zero ((IsFractionRing.injective Poly K) (by simpa using this))
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff lc (IsFractionRing.injective P L)).mpr h)

theorem special_unit (m : Fin 35) : IsUnit (atZero (pencil m)) := by
  rw [atZero_pencil]
  exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff kc (IsFractionRing.injective Poly K)).mpr fermat_ne_zero)

/-- The same regular section evaluates to the iterated parameter derivative
at the generic point and to its literal Fermat value at parameter zero. -/
theorem derivative_and_specialization (s : Sector) (m : Fin 35) (n : ℕ) :
    let z := sectionOfDerivative s m n
    IsLocalization.Away.lift (pencil m) (generic_unit m) z = time^[n] (rationalPole s m) ∧
    IsLocalization.Away.lift (pencil m) (special_unit m) z =
      (-1)^n * ((pole s).ascFactorial n:K) *
        kc (mon (fun i => source s i+n*tangentMonomial m i)) * (kc fermat)⁻¹^(pole s+n) := by
  constructor
  · rw [reg_value,pencil_derivative,mon_rising,Polynomial.C_mul,Polynomial.C_pow,map_mul,map_pow]
    simp only [constant]
    ring
  · rw [reg_value,atZero_C,atZero_pencil]


open CycleQ2FermatPrimeCoefficient (count terminal reducedPole degree reducedPole_eq)

/-- Scalar on the terminal monomial of the characteristic-zero Fermat
pole formula after cancelling the intermediate pole factorials. -/
def reducedScalar (s : Sector) (m : Fin 35) (n : ℕ) : ℚ :=
  let q := count n (source s) (tangentMonomial m)
  let b := terminal n (source s) (tangentMonomial m)
  (-1)^n * ((reducedPole n s m - 1).factorial : ℚ) / ((pole s-1).factorial : ℚ) *
    ∏ i,rowQ i (b i) (q i)

/-- The regular section of the true directional derivative at a terminal
standard monomial reduces to its recorded coefficient times that monomial.
All primitive denominators are powers of the Fermat equation. -/
theorem terminal_reduction_of_positive (s : Sector) (m : Fin 35) (n : ℕ)
    (hpos : 0 < reducedPole n s m) :
    toClass (IsLocalization.Away.lift (pencil m) (special_unit m) (sectionOfDerivative s m n)) =
      reducedScalar s m n • density (terminal n (source s) (tangentMonomial m)) (reducedPole n s m) := by
  let b := terminal n (source s) (tangentMonomial m)
  let q := count n (source s) (tangentMonomial m)
  let N := ∑ i,q i
  let l := reducedPole n s m
  have hs : 0 < pole s := by cases s <;> simp [pole]
  have hL : pole s+n-N = l := rfl
  have hu : 0 < l := hpos
  have hcount : l+N = pole s+n := by omega
  have v : (fun i => b i+degree i*q i) =
      (fun i => source s i+n*tangentMonomial m i) :=
    funext (fun i => Nat.mod_add_div _ _)
  have hlow := all_coordinate_strip b q (l-1)
  dsimp only at hlow
  rw [Nat.sub_add_cancel hu,hcount,v] at hlow
  let T := IsLocalization.Away.lift (pencil m) (special_unit m)
    (sectionOfDerivative s m n)
  let B := kc (mon (fun i => source s i+n*tangentMonomial m i)) * (kc fermat)⁻¹^(pole s+n)
  let c : ℚ := (-1)^n * ((pole s).ascFactorial n:ℚ)
  have hc : T = c • B := by
    rw [show T = _ from (derivative_and_specialization s m n).2]
    rw [show c • B = (c:K) * B from @Algebra.smul_def ℚ K _ _ DivisionRing.toRatAlgebra c B]
    simp [c,B]
    ring
  change toClass T = _
  rw [hc,toClass.map_smul]
  change c • density (fun i => source s i+n*tangentMonomial m i) (pole s+n) = _
  rw [hlow,← mul_smul]
  change _ • density b l = reducedScalar s m n • density b l
  congr 1
  have hfac := CycleQ2FermatPrimeCoefficient.factorial_cancellation (pole s) n l N hs hu hcount
  rw [← hcount,Nat.add_descFactorial_eq_ascFactorial'] at hfac
  unfold reducedScalar
  dsimp only
  change ((-1)^n * ((pole s).ascFactorial n:ℚ)) *
      ((∏ i,rowQ i (b i) (q i))/(l.ascFactorial N:ℚ)) =
    (-1)^n * ((l-1).factorial:ℚ) / ((pole s-1).factorial:ℚ) * ∏ i,rowQ i (b i) (q i)
  calc
    _ = (-1)^n * (((pole s).ascFactorial n:ℚ) / (l.ascFactorial N:ℚ)) *
        ∏ i,rowQ i (b i) (q i) := by ring
    _ = _ := by rw [hfac]; ring


/-- Integral numerator and denominator of the reduced scalar. All prime
factors of the denominator are 2 or 3. -/
def numerator (s : Sector) (m : Fin 35) (n : ℕ) : ℤ :=
  let q := count n (source s) (tangentMonomial m)
  let b := terminal n (source s) (tangentMonomial m)
  (-1)^n * ((reducedPole n s m-1).factorial:ℤ) *
    (∏ i, ∏ j ∈ Finset.range (q i), (b i + 1 + degree i*j) : ℕ)

def denominator (s : Sector) (m : Fin 35) (n : ℕ) : ℕ :=
  ((pole s-1).factorial) * ∏ i, degree i^(count n (source s) (tangentMonomial m) i)

theorem scalar_fraction (s : Sector) (m : Fin 35) (n : ℕ) :
    reducedScalar s m n = (numerator s m n : ℚ)/(denominator s m n:ℚ) := by
  simp [reducedScalar,numerator,denominator,rowQ,div_eq_mul_inv,
    mul_inv_rev,Finset.prod_mul_distrib]
  ring

theorem denominator_unit {p : ℕ} [Fact p.Prime] (hp : 6 < p) (s : Sector) (m : Fin 35) (n : ℕ) :
    (denominator s m n : ZMod p) ≠ 0 := by
  have hfac : ((pole s - 1).factorial : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hh := Nat.le_of_dvd (Nat.factorial_pos _) hdiv
    rcases s with i|j <;> simp [pole] at hh <;> omega
  have hdeg (i : Fin 5) : (degree i : ZMod p) ≠ 0 := by
    intro hz
    have hdiv := (ZMod.natCast_eq_zero_iff _ _).mp hz
    have hd : degree i ∣ 6 := by fin_cases i <;> decide
    have hl := Nat.le_of_dvd (show 0 < 6 by decide) hd
    have hh := Nat.le_of_dvd (show 0 < degree i by simp [degree]) hdiv
    omega
  simp [denominator,hfac,Finset.prod_ne_zero_iff,hdeg]

/-- The arithmetic matrix entry is the reduction, through the same two
integers, of the scalar of the rational Fermat differential. -/
theorem matrix_fraction {p : ℕ} [Fact p.Prime] (s u : Sector) (m : Fin 35) :
    CycleQ2FermatPrimeCoefficient.primeEntry p s m u =
      if terminal p (source s) (tangentMonomial m) = source u then
        (numerator s m p : ZMod p)/(denominator s m p : ZMod p) else 0 := by
  classical
  by_cases h : terminal p (source s) (tangentMonomial m) = source u
  · have hb (i : Fin 5) : source u i + 1 ≠ degree i := by
      have hbound : source u i ≤ CycleQ2FermatHiggs.socle i := by
        rcases u with a|b
        · exact (CycleQ2FermatHiggs.basis_properties a).2.2 i
        · exact (CycleQ2FermatVariationAlgebra.lowerExponent_properties b).2.2 i
      unfold degree
      omega
    simp [CycleQ2FermatPrimeCoefficient.primeEntry,CycleQ2FermatPrimeCoefficient.reducedEntry,
      CycleQ2FermatPrimeCoefficient.rowFactor,h,hb,numerator,denominator,div_eq_mul_inv,
      mul_inv_rev,Finset.prod_mul_distrib]
    ring
  · simp [CycleQ2FermatPrimeCoefficient.primeEntry,CycleQ2FermatPrimeCoefficient.reducedEntry,h]


private theorem forbidden_density (v : Tuple) (i : Fin 5) (hv : v i = degree i-1)
    (l : ℕ) (hl : 2 ≤ l) : density v l = 0 := by
  let a := Function.update v i 0
  have ha : a i = 0 := Function.update_self _ _ _
  have hc : degree i-1 = CycleQ2FermatJacobian.cutoff i := rfl
  have he : Function.update a i (CycleQ2FermatJacobian.cutoff i) = v := by
    funext j
    by_cases hj : j=i
    · subst j; simpa [hv] using hc.symm
    · simp [a,hj]
  have h := class_step i a ha 0 (l-2)
  rw [Nat.zero_add,coor_update a i ha,he,Nat.sub_add_cancel hl] at h
  simpa using h

/-- Integer numerator of the matrix entry in the specified target class. -/
def entryNumerator (n : ℕ) (s : Sector) (m : Fin 35) (u : Sector) : ℤ :=
  if terminal n (source s) (tangentMonomial m) = source u then numerator s m n else 0

theorem matrix_integer_fraction {p : ℕ} [Fact p.Prime] (s u : Sector) (m : Fin 35) :
    CycleQ2FermatPrimeCoefficient.primeEntry p s m u =
      (entryNumerator p s m u : ZMod p)/(denominator s m p : ZMod p) := by
  rw [matrix_fraction]
  by_cases h : terminal p (source s) (tangentMonomial m) = source u <;> simp [entryNumerator,h]

/-- The 66 rational matrix coefficients represent the specialized derivative
on the Fermat cone. The same integer numerator and denominator evaluate
to the arithmetic entry at every prime p>6 when n=p. -/
theorem derivative_matrix (s : Sector) (m : Fin 35) (n : ℕ) :
    toClass (IsLocalization.Away.lift (pencil m) (special_unit m) (sectionOfDerivative s m n)) =
      ∑ u : Sector, ((entryNumerator n s m u : ℚ)/(denominator s m n : ℚ)) •
        density (source u) (pole u) := by
  classical
  let b := terminal n (source s) (tangentMonomial m)
  let l := reducedPole n s m
  have hl : 2 ≤ l := CycleQ2FermatPrimeCoefficient.two_le_reducedPole n s m
  rw [terminal_reduction_of_positive s m n (by omega : 0 < l)]
  rcases CycleQ2FermatPrimeCoefficient.terminal_classification n s m with ⟨i,hi⟩|⟨u,hu,uni⟩
  · have hbad := forbidden_density b i hi l hl
    change reducedScalar s m n • density b l = _
    rw [hbad,smul_zero]
    symm
    apply Finset.sum_eq_zero
    intro u _
    have hb : b ≠ source u := by
      intro he
      have hbound : source u i ≤ CycleQ2FermatHiggs.socle i := by
        rcases u with a|j
        · exact (CycleQ2FermatHiggs.basis_properties a).2.2 i
        · exact (CycleQ2FermatVariationAlgebra.lowerExponent_properties j).2.2 i
      change b i = degree i-1 at hi
      rw [he] at hi
      unfold degree at hi
      omega
    simp [entryNumerator,show terminal n (source s) (tangentMonomial m) ≠ source u from hb]
  · rcases hu with ⟨he,hl'⟩
    rw [Finset.sum_eq_single u]
    · rw [he,hl',scalar_fraction]
      simp [entryNumerator,he]
    · intro v _ hv
      have hne : terminal n (source s) (tangentMonomial m) ≠ source v := by
        intro h
        exact hv (uni v ⟨h,reducedPole_eq s v m h⟩)
      simp [entryNumerator,hne]
    · simp

end CycleQ2FermatPrimePencil
end

#print axioms CycleQ2FermatPrimeCoefficient.split_support
#print axioms CycleQ2FermatPrimeCoefficient.inert_support
#print axioms CycleQ2FermatPrimeCoefficient.opposite_prime_dichotomy
#print axioms CycleQ2FermatPrimeCoefficient.terminal_classification
#print axioms CycleQ2FermatPrimePencil.pencil_specializes
#print axioms CycleQ2FermatPrimePencil.derivative_and_specialization
#print axioms CycleQ2FermatPrimePencil.denominator_unit
#print axioms CycleQ2FermatPrimePencil.matrix_integer_fraction
#print axioms CycleQ2FermatPrimePencil.derivative_matrix

noncomputable section
namespace CycleQ2FermatSymbolDetector
open CycleQ2PolynomialPoleSymbols (Poles Symbols relations symbol)

open CycleQ2FermatHiggs (socle basisMonomial basis_properties basis_injective weightedDegree)
open CycleQ2FermatJacobian (Exp exponent)
open CycleQ2FermatVariationAlgebra (lowerExponent lowerExponent_properties)
open CycleQ2FermatPrimeCoefficient (degree Sector source pole)
open MvPolynomial

variable (K : Type*) [Field K]

abbrev Polynomial := MvPolynomial (Fin 5) K

def fermatPolynomial : Polynomial K :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3

theorem fermatPolynomial_complex : fermatPolynomial ℂ = CycleQ2FermatJacobian.fermat := rfl

private theorem partial_fermat (i : Fin 5) :
    pderiv i (fermatPolynomial K) = C (degree i : K) * X i ^ (degree i - 1) := by
  fin_cases i <;> norm_num [fermatPolynomial,degree,socle,Pi.single_apply,Fin.ext_iff,map_ofNat] <;> first | rfl | exact Or.inl rfl

-- The contribution of one exponent to a chosen standard remainder.
private def coefficient (d b n : ℕ) : K :=
  if n % d = b then ∏ j ∈ Finset.range (n / d), (((b + 1 + d*j : ℕ) : K) / d) else 0

private theorem coefficient_step {d b : ℕ} (hd : 0 < d) (n : ℕ) :
    coefficient K d b (n+d) = coefficient K d b n * ((n+1 : ℕ) : K) / d := by
  unfold coefficient
  rw [Nat.add_mod_right, Nat.add_div_right _ hd]
  by_cases h : n % d = b
  · rw [if_pos h,if_pos h,Finset.prod_range_succ]
    have he : b+1+d*(n/d) = n+1 := by have := Nat.mod_add_div n d; omega
    rw [he,mul_div_assoc]
  · simp [h]

private theorem bounded (s : Sector) (i : Fin 5) : source s i < degree i - 1 := by
  rcases s with s|s
  · simpa [source,degree,Nat.lt_succ_iff] using (basis_properties s).2.2 i
  · simpa [source,degree,Nat.lt_succ_iff] using (lowerExponent_properties s).2.2 i

private def component (s : Sector) (a : Exp) (i : Fin 5) := coefficient K (degree i) (source s i) (a i)

private def weight (s : Sector) (a : Exp) : K := ∏ i, component K s a i

variable [NeZero (6 : K)]

private theorem degree_ne (i : Fin 5) : (degree i : K) ≠ 0 := by
  have h₆ := NeZero.ne (6 : K)
  have h₃ : (3 : K) ≠ 0 := by
    intro e
    apply h₆
    calc
      (6 : K) = 3 * 2 := by norm_num
      _ = 0 := by rw [e,zero_mul]
  rcases (show degree i = 6 ∨ degree i = 3 by fin_cases i <;> decide) with e|e
  · simpa only [e,Nat.cast_ofNat] using h₆
  · simpa only [e,Nat.cast_ofNat] using h₃

private theorem weight_axis (s : Sector) (i : Fin 5) (a : Exp) :
    (degree i : K) * weight K s (a + Finsupp.single i (degree i-1)) =
      (a i : K) * weight K s (a - Finsupp.single i 1) := by
  classical
  let R := ∏ k ∈ (Finset.univ : Finset (Fin 5)).erase i, component K s a k
  have same (v : Exp) (h : ∀ j, j ≠ i → v j = a j) :
      weight K s v = component K s v i * R := by
    rw [weight,← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    exact Finset.prod_congr rfl fun j hj => congrArg _ (h j (Finset.mem_erase.mp hj).1)
  rw [same _ (by intro j hj; simp [hj.symm]),same _ (by intro j hj; simp [hj.symm])]
  dsimp only [component]
  simp only [Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_eq_same]
  have hd : 0 < degree i := by simp [degree]
  have hdeg := degree_ne K i
  by_cases hz : a i = 0
  · have hrest : (degree i-1)%degree i = degree i-1 := Nat.mod_eq_of_lt (by omega)
    have hne : degree i-1 ≠ source s i := (bounded s i).ne'
    simp [hz,coefficient,hrest,hne]
  · have he : a i + (degree i - 1) = (a i - 1) + degree i := by omega
    rw [he,coefficient_step K hd,show a i-1+1 = a i by omega]
    field_simp

private def onPolynomial (s : Sector) : Polynomial K →ₗ[K] K :=
  (basisMonomials (Fin 5) K).constr K (weight K s)

omit [NeZero (6 : K)] in
private theorem monomial_value (s : Sector) (a : Exp) (c : K) :
    onPolynomial K s (monomial a c) = c * weight K s a := by
  have e : monomial a c = c • basisMonomials (Fin 5) K a := by
    rw [coe_basisMonomials,smul_monomial]; simp
  rw [e,map_smul]
  exact congrArg (c * ·) ((basisMonomials (Fin 5) K).constr_basis K (weight K s) a)

private theorem polynomial_divergence (s : Sector) (i : Fin 5) (G : Polynomial K) :
    onPolynomial K s (G * pderiv i (fermatPolynomial K)) = onPolynomial K s (pderiv i G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [partial_fermat,X_pow_eq_monomial,C_mul_monomial,
      monomial_mul,pderiv_monomial,monomial_value,monomial_value,mul_one]
    change c * (degree i : K) * weight K s (a + Finsupp.single i (degree i-1)) =
      c * (a i : K) * weight K s (a - Finsupp.single i 1)
    rw [mul_assoc,mul_assoc,weight_axis]
  | add P Q hP hQ => simp only [add_mul,map_add,hP,hQ]

/-- Fermat coefficient at one of the 66 invariant monomials. -/
def normalForm (s : Sector) : Symbols K (fermatPolynomial K) →ₗ[K] K :=
  let L : Poles K →ₗ[K] K := Finsupp.lsum K (fun _ => onPolynomial K s)
  (relations K (fermatPolynomial K)).liftQ L (Submodule.span_le.mpr (by
    rintro _ ⟨n,i,G,rfl⟩
    change L _ = 0
    simp only [L,map_sub,Finsupp.lsum_single,polynomial_divergence,sub_self]))

private theorem normalForm_symbol (s : Sector) (n : ℕ) (P : Polynomial K) :
    normalForm K s (symbol K (fermatPolynomial K) n P) = onPolynomial K s P := by
  change Finsupp.lsum K (fun _ : ℕ => onPolynomial K s) (Finsupp.single n P) = _
  exact Finsupp.lsum_single _ _ _ _

/-- The value on an arbitrary monomial, including every pole and every forbidden remainder. -/
theorem normalForm_monomial (s : Sector) (n : ℕ) (a : Exp) (c : K) :
    normalForm K s (symbol K (fermatPolynomial K) n (monomial a c)) =
      c * ∏ i, (if a i % degree i = source s i then
        ∏ j ∈ Finset.range (a i / degree i), (((source s i + 1 + degree i*j : ℕ) : K) / degree i)
        else 0) := (normalForm_symbol K s n _).trans (monomial_value K s a c)

private theorem injective : Function.Injective source := by
  rintro (i|i) (j|j) h
  · exact congrArg Sum.inl (basis_injective h)
  · have eq := congrArg weightedDegree h
    simp [source,(basis_properties i).1,(lowerExponent_properties j).1] at eq
  · have eq := congrArg weightedDegree h
    simp [source,(basis_properties j).1,(lowerExponent_properties i).1] at eq
  · apply congrArg Sum.inr
    apply basis_injective
    funext k
    have e := congrFun h k
    change socle k - basisMonomial i k = socle k - basisMonomial j k at e
    have := (basis_properties i).2.2 k
    have := (basis_properties j).2.2 k
    omega

def frame (s : Sector) : Symbols K (fermatPolynomial K) := symbol K (fermatPolynomial K) (pole s - 1) (monomial (exponent (source s)) 1)

theorem normalForm_frame (s t : Sector) : normalForm K s (frame K t) = if t = s then 1 else 0 := by
  classical
  rw [frame,normalForm_symbol,monomial_value,one_mul,weight]
  have entry (i : Fin 5) : component K s (exponent (source t)) i =
      if source t i = source s i then 1 else 0 := by
    have h := bounded t i
    have hlt : source t i < degree i := by omega
    simp [component,coefficient,Nat.mod_eq_of_lt hlt,Nat.div_eq_of_lt hlt]
  simp only [entry]
  split_ifs with h
  · subst t; simp
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp fun e => h (injective e)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- No polynomial divergence relation at any pole can kill a nonzero
linear combination of the 33 upper and 33 lower standard residue symbols. -/
theorem frame_linearIndependent : LinearIndependent K (frame K) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g h s
  have e := congrArg (normalForm K s) h
  simp only [map_sum,map_smul,normalForm_frame,map_zero,smul_eq_mul,mul_ite,mul_one,mul_zero] at e
  simpa only [Finset.sum_ite_eq', Finset.mem_univ,if_true] using e


/-- The unnormalized standard form at its ordinary pole order. -/
def ordinaryFrame (s : Sector) : Symbols K (fermatPolynomial K) :=
  ((pole s-1).factorial : K)⁻¹ • frame K s

theorem pole_factor_ne_zero (s : Sector) : ((pole s - 1).factorial : K) ≠ 0 := by
  have h₂ : (2 : K) ≠ 0 := by
    intro h
    apply NeZero.ne (6 : K)
    calc
      (6 : K) = 2 * 3 := by norm_num
      _ = 0 := by rw [h,zero_mul]
  cases s <;> simp [pole,h₂]

/-- Coordinates dual to the ordinary (unnormalized) standard forms. -/
def ordinaryCoordinate (s : Sector) : Symbols K (fermatPolynomial K) →ₗ[K] K :=
  ((pole s-1).factorial : K) • normalForm K s

theorem ordinaryCoordinate_frame (s t : Sector) :
    ordinaryCoordinate K s (ordinaryFrame K t) = if t = s then 1 else 0 := by
  have h₂ : (2 : K) ≠ 0 := by
    intro e
    apply NeZero.ne (6 : K)
    calc
      (6 : K) = 2 * 3 := by norm_num
      _ = 0 := by rw [e,zero_mul]
  have h (u : Sector) : ((pole u-1).factorial : K) ≠ 0 := by cases u <;> simp [pole,h₂]
  change ((pole s-1).factorial : K) * normalForm K s _ = _
  rw [ordinaryFrame,map_smul,smul_eq_mul,normalForm_frame]
  split_ifs with he
  · subst t; rw [mul_one,mul_inv_cancel₀ (h s)]
  · rw [mul_zero,mul_zero]

section PrimeCoordinates
open CycleQ2FermatHiggs (tangentMonomial)
open CycleQ2FermatPrimeCoefficient (Tuple terminal count rowFactor reducedEntry reducedPole_eq primeEntry)

variable (p : ℕ) [Fact p.Prime] [NeZero (6 : ZMod p)]

theorem normalForm_prime_monomial (s : Sector) (a m : Tuple) (n : ℕ) :
    normalForm (ZMod p) s (symbol (ZMod p) (fermatPolynomial (ZMod p)) n
      (monomial (exponent fun i => a i + p*m i) 1)) =
    reducedEntry p a m (source s) := by
  classical
  rw [normalForm_monomial,one_mul,reducedEntry]
  change (∏ i, if (a i+p*m i)%degree i = source s i then
    ∏ j ∈ Finset.range ((a i + p*m i)/degree i), (((source s i+1+degree i*j : ℕ) : ZMod p) / degree i)
    else 0) = _
  split_ifs with h
  · apply Finset.prod_congr rfl
    intro i _
    have he := congrFun h i
    change (a i+p*m i)%degree i = source s i at he
    have hg : source s i + 1 ≠ degree i := by have := bounded s i; omega
    rw [if_pos he]
    simp only [count,terminal,rowFactor,he,if_neg hg,Finset.prod_div_distrib,Finset.prod_const,
      Finset.card_range]
  · obtain ⟨i,hi⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

/-- The coefficient of the normalized p-fold monomial derivative in the
ordinary Fermat residue frame is exactly the signed arithmetic matrix entry. -/
theorem primeCoordinate (s u : Sector) (m : Fin 35) :
    ordinaryCoordinate (ZMod p) u (((-1 : ZMod p)^p / (pole s - 1).factorial) •
        symbol (ZMod p) (fermatPolynomial (ZMod p)) ((pole s - 1)+p)
          (monomial (exponent fun i => source s i + p*tangentMonomial m i) 1)) =
        primeEntry p s m u := by
  change ((pole u - 1).factorial : ZMod p) * normalForm (ZMod p) u _ = _
  rw [map_smul,smul_eq_mul,normalForm_prime_monomial,primeEntry]
  by_cases e : terminal p (source s) (tangentMonomial m) = source u
  · rw [reducedPole_eq s u m e]
    ring
  · simp only [reducedEntry,if_neg e,mul_zero]

/-- The explicit prime-entry formula is unchanged after extending the
prime field. This is the coefficient field used by arithmetic spreading. -/
theorem primeCoordinate_map {L : Type*} [Field L] [NeZero (6 : L)]
    (ι : ZMod p →+* L) (s u : Sector) (m : Fin 35) :
    ordinaryCoordinate L u (((-1 : L)^p / (pole s - 1).factorial) •
        symbol L (fermatPolynomial L) ((pole s - 1)+p)
          (monomial (exponent fun i => source s i + p*tangentMonomial m i) 1)) =
        ι (primeEntry p s m u) := by
  have h := congrArg ι (primeCoordinate p s u m)
  change ι (((pole u - 1).factorial : ZMod p) * normalForm (ZMod p) u _) = _ at h
  rw [map_smul,smul_eq_mul,normalForm_monomial,one_mul] at h
  change ((pole u - 1).factorial : L) * normalForm L u _ = _
  rw [map_smul,smul_eq_mul,normalForm_monomial,one_mul]
  simpa only [map_mul,map_div₀,map_pow,map_neg,map_one,map_natCast,
    map_prod,apply_ite,map_zero] using h

theorem normalized_primeCoordinate_map {L : Type*} [Field L] [NeZero (6 : L)]
    (ι : ZMod p →+* L) (s u : Sector) (m : Fin 35) :
    normalForm L u ((-1 : L)^p •
        symbol L (fermatPolynomial L) ((pole s - 1)+p)
          (monomial (exponent fun i => source s i + p*tangentMonomial m i) 1)) =
      (((pole s - 1).factorial : L) / ((pole u - 1).factorial : L)) *
        ι (primeEntry p s m u) := by
  have h := primeCoordinate_map p ι s u m
  change ((pole u - 1).factorial : L) * normalForm L u _ = _ at h
  rw [map_smul,smul_eq_mul] at h ⊢
  field_simp [pole_factor_ne_zero L s,pole_factor_ne_zero L u] at h ⊢
  linear_combination h

end PrimeCoordinates

end CycleQ2FermatSymbolDetector

#print axioms CycleQ2FermatSymbolDetector.normalForm_monomial
#print axioms CycleQ2FermatSymbolDetector.frame_linearIndependent
#print axioms CycleQ2FermatSymbolDetector.primeCoordinate
end

noncomputable section
namespace CycleQ2FermatSymbolDetector

open CycleQ2PolynomialPoleSymbols CycleQ2IncidenceNormalForm MvPolynomial
open CycleQ2FermatHiggs (tangentMonomial tangent_properties socle)
open CycleQ2FermatJacobian (exponent)
open CycleQ2FermatPrimeCoefficient (Sector source pole primeEntry)

variable (K : Type*) [Field K]

private theorem fermatFullHomogeneous :
    (fermatPolynomial K).IsWeightedHomogeneous fullGrading (6,0) := by
  have H (j : Fin 5) : (X j ^ CycleQ2GenericSexticGradient.purePower j :
      MvPolynomial (Fin 5) K).IsWeightedHomogeneous fullGrading (6,0) := by
    rw [X_pow_eq_monomial]
    apply isWeightedHomogeneous_monomial
    rw [Finsupp.weight_single]
    fin_cases j <;> decide
  exact ((((H 0).add (H 1)).add (H 2)).add (H 3)).add (H 4)

private theorem fermatLeading : (fermatPolynomial K).coeff (Finsupp.single 4 3) = 1 := by
  classical
  norm_num [fermatPolynomial,coeff_X_pow,Finsupp.single_eq_single_iff,Fin.ext_iff]

variable {R : Type*} [CommRing R] (t : R →+* K)

/-- Evaluate the universal monic family on the Fermat polynomial over the target field. -/
def fermatSpecialize :
    Symbols (TailRing R) (monicFamily R) →ₛₗ[monicEvaluation R t (fermatPolynomial K)]
        Symbols K (fermatPolynomial K) :=
  (Submodule.quotEquivOfEq _ _ (congrArg (relations K)
      (map_monicFamily R t _ (fermatFullHomogeneous K) (fermatLeading K)))).toLinearMap.comp
    (specialize (monicEvaluation R t (fermatPolynomial K)) (monicFamily R))

theorem fermatSpecialize_iterate (a : FullSexticTailIndex) (s : Fin 5 →₀ ℕ) (n r : ℕ) :
    fermatSpecialize K t ((connection (pderiv a) (monicFamily R))^[r]
        (symbol (TailRing R) (monicFamily R) n (monomial s 1))) =
      (-1 : K)^r • symbol K (fermatPolynomial K) (n+r)
        (monomial (r • fullExponentOf a.val.val + s) 1) := by
  simp only [fermatSpecialize, LinearMap.comp_apply]
  rw [specialize_monic_iterate, map_smul]
  rfl

/-- The tangent monomial labels in the Fermat frame select actual monic coefficient coordinates. -/
def tangentTail (m : Fin 35) : FullSexticTailIndex := by
  let e := exponent (tangentMonomial m)
  have H : Finsupp.weight fullGrading e = (6,0) :=
    (fullGrading_eq_iff _ 6).mpr
      ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩
  refine ⟨fullIndexOf e H, ?_⟩
  change tangentMonomial m 4 < 3
  have hb : tangentMonomial m 4 ≤ 1 := (tangent_properties m).2.2 4
  omega

@[simp] theorem tangentTail_exponent (m : Fin 35) :
    fullExponentOf (tangentTail m).val.val = exponent (tangentMonomial m) :=
  fullIndexOf_exponent (exponent (tangentMonomial m))
    ((fullGrading_eq_iff (exponent (tangentMonomial m)) 6).mpr
    ⟨(tangent_properties m).1, (tangent_properties m).2.1⟩)

private theorem iterate_constant (a : FullSexticTailIndex) (b : R)
    (x : Symbols (TailRing R) (monicFamily R)) (r : ℕ) :
    (connection (pderiv a) (monicFamily R))^[r] ((C b : TailRing R) • x) =
      (C b : TailRing R) • (connection (pderiv a) (monicFamily R))^[r] x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih,connection_smul,pderiv_C,
      zero_smul,add_zero]

/-- The p-fold coefficient derivative on the actual monic parameter space,
projected to the ordinary Fermat frame, is the arithmetic prime matrix. -/
theorem prime_monic_coordinate (p : ℕ) [Fact p.Prime] [NeZero (6 : ZMod p)]
    (s u : Sector) (m : Fin 35) :
    ordinaryCoordinate (ZMod p) u
        (fermatSpecialize (ZMod p) (RingHom.id (ZMod p))
        ((connection (pderiv (tangentTail m)) (monicFamily (ZMod p)))^[p]
          ((C (((pole s - 1).factorial : ZMod p)⁻¹) : TailRing (ZMod p)) •
            symbol (TailRing (ZMod p)) (monicFamily (ZMod p)) (pole s - 1)
              (monomial (exponent (source s)) 1)))) = primeEntry p s m u := by
  have h : p • fullExponentOf (tangentTail m).val.val + exponent (source s) =
      exponent (fun i => source s i + p * tangentMonomial m i) := by
    rw [tangentTail_exponent]
    ext i
    simp [Nat.add_comm]
  rw [iterate_constant,map_smulₛₗ,fermatSpecialize_iterate,h,smul_smul]
  simp only [monicEvaluation,eval₂Hom_C, RingHom.id_apply]
  rw [mul_comm,← div_eq_mul_inv]
  exact primeCoordinate p s u m

/-- The same actual monic coefficient derivative over an arbitrary field
receiving the prime field. No choice of a separate prime matrix is made. -/
theorem prime_monic_coordinate_map [NeZero (6 : K)]
    (p : ℕ) [Fact p.Prime] [NeZero (6 : ZMod p)] (ι : ZMod p →+* K)
    (s u : Sector) (m : Fin 35) :
    ordinaryCoordinate K u
        (fermatSpecialize K (RingHom.id K)
        ((connection (pderiv (tangentTail m)) (monicFamily K))^[p]
          ((C (((pole s - 1).factorial : K)⁻¹) : TailRing K) •
            symbol (TailRing K) (monicFamily K) (pole s - 1)
              (monomial (exponent (source s)) 1)))) = ι (primeEntry p s m u) := by
  have h : p • fullExponentOf (tangentTail m).val.val + exponent (source s) =
      exponent (fun i => source s i + p * tangentMonomial m i) := by
    rw [tangentTail_exponent]
    ext i
    simp [Nat.add_comm]
  rw [iterate_constant,map_smulₛₗ,fermatSpecialize_iterate,h,smul_smul]
  simp only [monicEvaluation,eval₂Hom_C, RingHom.id_apply]
  rw [mul_comm,← div_eq_mul_inv]
  exact primeCoordinate_map p ι s u m

/-- Coordinates in the normalized frame used by the regular connection.
The ordinary prime matrix is conjugated by the explicit pole factorials. -/
theorem normalized_prime_monic_coordinate_map [NeZero (6 : K)]
    (p : ℕ) [Fact p.Prime] [NeZero (6 : ZMod p)] (ι : ZMod p →+* K)
    (s u : Sector) (m : Fin 35) :
    normalForm K u
        (fermatSpecialize K (RingHom.id K)
        ((connection (pderiv (tangentTail m)) (monicFamily K))^[p]
          (symbol (TailRing K) (monicFamily K) (pole s - 1)
            (monomial (exponent (source s)) 1)))) =
      (((pole s - 1).factorial : K) / ((pole u - 1).factorial : K)) *
        ι (primeEntry p s m u) := by
  have h : p • fullExponentOf (tangentTail m).val.val + exponent (source s) =
      exponent (fun i => source s i + p * tangentMonomial m i) := by
    rw [tangentTail_exponent]
    ext i
    simp [Nat.add_comm]
  rw [fermatSpecialize_iterate,h]
  exact normalized_primeCoordinate_map p ι s u m

end CycleQ2FermatSymbolDetector

#print axioms CycleQ2FermatSymbolDetector.prime_monic_coordinate
#print axioms CycleQ2FermatSymbolDetector.primeCoordinate_map
#print axioms CycleQ2FermatSymbolDetector.prime_monic_coordinate_map
#print axioms CycleQ2FermatSymbolDetector.normalized_prime_monic_coordinate_map
end

/-!
# The universal residue frame at the Fermat coefficient point

The universal upper and lower labels have exactly the same exponents and
normalized poles as the detector frame. Transport along the equality of the
defining equations therefore identifies the actual specialized frame with the
66 independently detected symbols.
-/

noncomputable section
namespace CycleQ2FermatSymbolDetector

open CycleQ2PolynomialPoleSymbols (Symbols relations symbol)
open CycleQ2UniversalPoleFrame (equation basisSymbol Label)
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation universalF_seed)
open CycleQ2GeometricHiggsGradedIndices (exp_upperIndex exp_lowerIndex)
open CycleQ2FermatPrimeCoefficient (source pole)
open MvPolynomial

variable {K : Type} [Field K] (φ : CoeffRing →+* K)
    (hF : equation φ = fermatPolynomial K)

/-- Change only the presentation of the equation, using the induced equality
of the normalized polynomial-pole relation submodules. -/
def fermatEquationEquiv :
    Symbols K (equation φ) ≃ₗ[K] Symbols K (fermatPolynomial K) :=
  Submodule.quotEquivOfEq _ _ (congrArg (relations K) hF)

@[simp] theorem fermatEquationEquiv_symbol (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    fermatEquationEquiv φ hF (symbol K (equation φ) n P) =
      symbol K (fermatPolynomial K) n P := rfl

/-- Both lower frames use the complementary socle order without reindexing. -/
@[simp] theorem fermatEquationEquiv_basisSymbol (s : Label) :
    fermatEquationEquiv φ hF (basisSymbol φ s) = frame K s := by
  rcases s with i | i
  · simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole, exp_upperIndex,
      fermatEquationEquiv_symbol, frame, source, pole]
  · simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole, exp_lowerIndex,
      fermatEquationEquiv_symbol, frame, source, pole]

/-- The universal frame is linearly independent whenever its equation is
the Fermat equation, as witnessed by the explicit detector coordinates. -/
theorem basisSymbol_linearIndependent [NeZero (6 : K)] :
    LinearIndependent K (basisSymbol φ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have h := congrArg (fermatEquationEquiv φ hF) hc
  simp only [map_sum, map_smul, fermatEquationEquiv_basisSymbol, map_zero] at h
  exact (Fintype.linearIndependent_iff.mp (frame_linearIndependent K)) c h s

/-- The actual frame evaluated at the Fermat coefficient point is independent. -/
theorem seed_basisSymbol_linearIndependent :
    LinearIndependent ℂ (basisSymbol seedEvaluation) :=
  basisSymbol_linearIndependent seedEvaluation universalF_seed

/-- Coefficient specialization of the universal frame is independent whenever
the specialized equation is Fermat. This is the form needed by the regular
connection criterion, with the specialization map retained explicitly. -/
theorem specialized_basisSymbol_linearIndependent [NeZero (6 : K)]
    {R : Type} [CommRing R] (ψ : CoeffRing →+* R) (ρ : R →+* K)
    (h : MvPolynomial.map ρ (equation ψ) = fermatPolynomial K) :
    LinearIndependent K (fun i =>
      CycleQ2PolynomialPoleSymbols.specialize ρ (equation ψ) (basisSymbol ψ i)) := by
  classical
  let E := Submodule.quotEquivOfEq _ _ (congrArg (relations K) h)
  have hs (n : ℕ) (P : MvPolynomial (Fin 5) K) :
      E (symbol K (MvPolynomial.map ρ (equation ψ)) n P) =
        symbol K (fermatPolynomial K) n P := rfl
  have hf (s : Label) :
      E (CycleQ2PolynomialPoleSymbols.specialize ρ (equation ψ) (basisSymbol ψ s)) =
        frame K s := by
    rcases s with i | i
    · simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole,
        CycleQ2PolynomialPoleSymbols.specialize_symbol, map_monomial, map_one,
        exp_upperIndex, hs, frame, source, pole]
    · simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole,
        CycleQ2PolynomialPoleSymbols.specialize_symbol, map_monomial, map_one,
        exp_lowerIndex, hs, frame, source, pole]
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have ht := congrArg E hc
  simp only [map_sum, map_smul, hf, map_zero] at ht
  exact (Fintype.linearIndependent_iff.mp (frame_linearIndependent K)) c ht s

end CycleQ2FermatSymbolDetector
end

#print axioms CycleQ2FermatSymbolDetector.fermatEquationEquiv_basisSymbol
#print axioms CycleQ2FermatSymbolDetector.seed_basisSymbol_linearIndependent
#print axioms CycleQ2FermatSymbolDetector.specialized_basisSymbol_linearIndependent

/-!
# Independence on the actual coefficient open

Invert exactly the three universal Jacobian-frame determinants. Their Fermat
values are one, so the Fermat point remains on this open. Every coefficient
partial extends to the localization. Differential simplicity and the regular
connection matrices then promote the independent Fermat specialization to an
independent universal frame on the entire open.
-/

noncomputable section
namespace CycleQ2FermatCoefficientOpen

open MvPolynomial
open CycleQ2IncidenceNormalForm (FullInvariantIndex)
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation universalF_seed)
open CycleQ2HiggsJacobianFrames (frameDet seed_frameDet)
open CycleQ2UniversalPoleFrame (equation basisSymbol vectorRealize)
open CycleQ2GeometricLocalizedDerivations

def denominator : CoeffRing := frameDet 6 1 * frameDet 12 1 * frameDet 18 1

abbrev OpenCoefficients := Localization.Away denominator

def coefficientMap : CoeffRing →+* OpenCoefficients := algebraMap _ _

theorem seed_denominator : seedEvaluation denominator = 1 := by
  simp only [denominator, map_mul, seed_frameDet, one_mul]

theorem frame_units :
    IsUnit (coefficientMap (frameDet 6 1)) ∧
      IsUnit (coefficientMap (frameDet 12 1)) ∧
      IsUnit (coefficientMap (frameDet 18 1)) := by
  have h : IsUnit (coefficientMap denominator) :=
    IsLocalization.Away.algebraMap_isUnit denominator
  simp only [denominator, map_mul, IsUnit.mul_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The Fermat point extends across the chosen coefficient localization. -/
def fermatEvaluation : OpenCoefficients →+* ℂ :=
  IsLocalization.Away.lift denominator
    (show IsUnit (seedEvaluation denominator) by
      rw [seed_denominator]
      exact isUnit_one)

@[simp] theorem fermatEvaluation_coefficientMap (p : CoeffRing) :
    fermatEvaluation (coefficientMap p) = seedEvaluation p :=
  IsLocalization.Away.lift_eq denominator _ p

theorem fermatEvaluation_comp : fermatEvaluation.comp coefficientMap = seedEvaluation := by
  ext p
  exact fermatEvaluation_coefficientMap p

theorem equation_atFermat :
    MvPolynomial.map fermatEvaluation (equation coefficientMap) =
      CycleQ2FermatSymbolDetector.fermatPolynomial ℂ := by
  rw [equation, MvPolynomial.map_map, fermatEvaluation_comp]
  exact universalF_seed

/-- All 45 coefficient partials, extended to the actual localization. -/
def coefficientPartial (i : FullInvariantIndex 6) :
    Derivation ℤ OpenCoefficients OpenCoefficients :=
  (localizedDerivation (Submonoid.powers denominator) OpenCoefficients
    (pderiv i : Derivation ℂ CoeffRing CoeffRing)).restrictScalars ℤ

theorem coefficientPartial_coefficientMap (i : FullInvariantIndex 6) (p : CoeffRing) :
    coefficientPartial i (coefficientMap p) = coefficientMap (pderiv i p) :=
  localizedDerivation_algebraMap (Submonoid.powers denominator) OpenCoefficients (pderiv i) p

theorem differential_ideal_eq_top (I : Ideal OpenCoefficients) (hI : I ≠ ⊥)
    (stable : ∀ i x, x ∈ I → coefficientPartial i x ∈ I) : I = ⊤ := by
  classical
  exact CycleQ2DifferentialCoefficientIdeals.localization_eq_top
    (Submonoid.powers denominator) OpenCoefficients coefficientPartial
      coefficientPartial_coefficientMap I hI stable

/-- The 66 normalized residue symbols are independent on this explicit
coefficient open; regular connection matrices and Fermat detection supply
the proof without assuming generic frame independence. -/
theorem vectorRealize_injective : Function.Injective (vectorRealize coefficientMap) := by
  obtain ⟨h6, h12, h18⟩ := frame_units
  exact CycleQ2UniversalPoleFrame.vectorRealize_injective_of_specialized_independent
    coefficientMap h6 h12 h18 coefficientPartial differential_ideal_eq_top fermatEvaluation
    (CycleQ2FermatSymbolDetector.specialized_basisSymbol_linearIndependent
      coefficientMap fermatEvaluation equation_atFermat)

theorem basisSymbol_linearIndependent : LinearIndependent OpenCoefficients
    (basisSymbol coefficientMap) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have hz : vectorRealize coefficientMap c = 0 := hc
  have he : c = 0 := vectorRealize_injective
    (hz.trans (map_zero (vectorRealize coefficientMap)).symm)
  exact congrFun he s

/-- A generating matrix preserved by the coefficient connections cannot lose
an existing `r`-minor at every row and column choice after field specialization.
In particular this applies at the Fermat point of the same coefficient open. -/
theorem rank_specialize_ge {n s : Type*} [Fintype n] [Fintype s]
    (P : Matrix n s OpenCoefficients)
    (B : FullInvariantIndex 6 → Matrix n n OpenCoefficients)
    (C : FullInvariantIndex 6 → Matrix s s OpenCoefficients)
    (h : ∀ i, P.map (coefficientPartial i) = P * C i - B i * P) (r : ℕ)
    (hne : ∃ I : Fin r → n, ∃ J : Fin r → s, (P.submatrix I J).det ≠ 0)
    {L : Type*} [Field L] (ρ : OpenCoefficients →+* L) :
    r ≤ (P.map ρ).rank :=
  CycleQ2DifferentialMinorStability.rank_specialize_ge P r
    (CycleQ2DifferentialMinorStability.minorIdeal_eq_top coefficientPartial
      differential_ideal_eq_top P B C h r hne) ρ

end CycleQ2FermatCoefficientOpen
end

#print axioms CycleQ2FermatCoefficientOpen.differential_ideal_eq_top
#print axioms CycleQ2FermatCoefficientOpen.vectorRealize_injective
#print axioms CycleQ2FermatCoefficientOpen.basisSymbol_linearIndependent
#print axioms CycleQ2FermatCoefficientOpen.rank_specialize_ge

/-!
# Polynomial parameter charts and the monic coefficient open

The same argument applies after expressing the 45 raw coefficients in any
polynomial parameter ring. Only a Fermat-valued point of that parameter ring
is needed. In particular, fixing the leading coefficient to one leaves the
44 independent tail coordinates of the actual monic family.
-/

noncomputable section
namespace CycleQ2PolynomialCoefficientOpen

open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation universalF_seed)
open CycleQ2HiggsJacobianFrames (frameDet)
open CycleQ2UniversalPoleFrame (equation basisSymbol vectorRealize)
open CycleQ2GeometricLocalizedDerivations

abbrev Parameters (σ : Type) := MvPolynomial σ ℂ

variable {σ : Type} [Fintype σ] [DecidableEq σ]
    (ψ : CoeffRing →+* Parameters σ)

def denominator : Parameters σ := ψ CycleQ2FermatCoefficientOpen.denominator

abbrev OpenCoefficients := Localization.Away (denominator ψ)

def toOpen : Parameters σ →+* OpenCoefficients ψ := algebraMap _ _

def coefficientMap : CoeffRing →+* OpenCoefficients ψ := (toOpen ψ).comp ψ

theorem frame_units :
    IsUnit (coefficientMap ψ (frameDet 6 1)) ∧
      IsUnit (coefficientMap ψ (frameDet 12 1)) ∧
      IsUnit (coefficientMap ψ (frameDet 18 1)) := by
  have h : IsUnit (coefficientMap ψ CycleQ2FermatCoefficientOpen.denominator) :=
    IsLocalization.Away.algebraMap_isUnit (denominator ψ)
  simp only [CycleQ2FermatCoefficientOpen.denominator, map_mul, IsUnit.mul_iff] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

def coefficientPartial (i : σ) : Derivation ℤ (OpenCoefficients ψ) (OpenCoefficients ψ) :=
  (localizedDerivation (Submonoid.powers (denominator ψ)) (OpenCoefficients ψ)
    (pderiv i : Derivation ℂ (Parameters σ) (Parameters σ))).restrictScalars ℤ

theorem coefficientPartial_toOpen (i : σ) (p : Parameters σ) :
    coefficientPartial ψ i (toOpen ψ p) = toOpen ψ (pderiv i p) :=
  localizedDerivation_algebraMap (Submonoid.powers (denominator ψ))
    (OpenCoefficients ψ) (pderiv i) p

theorem differential_ideal_eq_top (I : Ideal (OpenCoefficients ψ)) (hI : I ≠ ⊥)
    (stable : ∀ i x, x ∈ I → coefficientPartial ψ i x ∈ I) : I = ⊤ :=
  CycleQ2DifferentialCoefficientIdeals.localization_eq_top
    (Submonoid.powers (denominator ψ)) (OpenCoefficients ψ) (coefficientPartial ψ)
      (coefficientPartial_toOpen ψ) I hI stable

variable (ρ₀ : Parameters σ →+* ℂ) (point : ρ₀.comp ψ = seedEvaluation)

theorem point_denominator : ρ₀ (denominator ψ) = 1 := by
  change (ρ₀.comp ψ) CycleQ2FermatCoefficientOpen.denominator = 1
  rw [point, CycleQ2FermatCoefficientOpen.seed_denominator]

def fermatEvaluation : OpenCoefficients ψ →+* ℂ :=
  IsLocalization.Away.lift (denominator ψ)
    (show IsUnit (ρ₀ (denominator ψ)) by
      rw [point_denominator ψ ρ₀ point]
      exact isUnit_one)

@[simp] theorem fermatEvaluation_toOpen (p : Parameters σ) :
    fermatEvaluation ψ ρ₀ point (toOpen ψ p) = ρ₀ p :=
  IsLocalization.Away.lift_eq (denominator ψ) _ p

theorem fermatEvaluation_comp :
    (fermatEvaluation ψ ρ₀ point).comp (coefficientMap ψ) = seedEvaluation := by
  ext p
  change fermatEvaluation ψ ρ₀ point (toOpen ψ (ψ p)) = seedEvaluation p
  rw [fermatEvaluation_toOpen]
  exact congrArg (fun f : CoeffRing →+* ℂ => f p) point

theorem equation_atFermat :
    MvPolynomial.map (fermatEvaluation ψ ρ₀ point) (equation (coefficientMap ψ)) =
      CycleQ2FermatSymbolDetector.fermatPolynomial ℂ := by
  rw [equation, MvPolynomial.map_map, fermatEvaluation_comp ψ ρ₀ point]
  exact universalF_seed

theorem vectorRealize_injective : Function.Injective (vectorRealize (coefficientMap ψ)) := by
  obtain ⟨h6, h12, h18⟩ := frame_units ψ
  exact CycleQ2UniversalPoleFrame.vectorRealize_injective_of_specialized_independent
    (coefficientMap ψ) h6 h12 h18 (coefficientPartial ψ) (differential_ideal_eq_top ψ)
    (fermatEvaluation ψ ρ₀ point)
    (CycleQ2FermatSymbolDetector.specialized_basisSymbol_linearIndependent
      (coefficientMap ψ) (fermatEvaluation ψ ρ₀ point) (equation_atFermat ψ ρ₀ point))

theorem basisSymbol_linearIndependent : LinearIndependent (OpenCoefficients ψ)
    (basisSymbol (coefficientMap ψ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc s
  have hz : vectorRealize (coefficientMap ψ) c = 0 := hc
  have he : c = 0 := vectorRealize_injective ψ ρ₀ point
    (hz.trans (map_zero (vectorRealize (coefficientMap ψ))).symm)
  exact congrFun he s

end CycleQ2PolynomialCoefficientOpen

namespace CycleQ2MonicFermatCoefficientOpen

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation fermatCoefficients)
open CycleQ2PolynomialPoleSymbols (TailRing monicFamily)

abbrev Parameters := TailRing ℂ

/-- The standard inclusion of the monic tail chart into all raw coefficients. -/
def rawCoordinate (e : FullInvariantIndex 6) : Parameters :=
  if h : (e.val 4).val < 3 then X ⟨e,h⟩ else 1

@[simp] theorem rawCoordinate_tail (e : FullSexticTailIndex) :
    rawCoordinate e.val = X e := by simp [rawCoordinate, e.property]

@[simp] theorem rawCoordinate_leading : rawCoordinate fullSexticLeadingIndex = 1 := by
  have h := (fullSextic_tail_iff_ne fullSexticLeadingIndex).not.mpr (not_not.mpr rfl)
  simp [rawCoordinate, h]

def rawToMonic : CoeffRing →+* Parameters := eval₂Hom C rawCoordinate

@[simp] theorem rawToMonic_C (c : ℂ) : rawToMonic (C c) = C c := by simp [rawToMonic]
@[simp] theorem rawToMonic_X (e : FullInvariantIndex 6) :
    rawToMonic (X e) = rawCoordinate e := by simp [rawToMonic]

theorem equation_rawToMonic : CycleQ2UniversalPoleFrame.equation rawToMonic = monicFamily ℂ := by
  rw [CycleQ2UniversalPoleFrame.equation, universalF, map_fullInvariantPolynomial]
  have h : rawToMonic ∘ (X : FullInvariantIndex 6 → CoeffRing) = rawCoordinate := by
    funext e
    exact rawToMonic_X e
  rw [h, fullInvariantPolynomial_sextic, rawCoordinate_leading]
  simp only [rawFullSextic, monicFamily, normalizedFullSextic, rawCoordinate_tail]

def fermatPoint : Parameters →+* ℂ := eval (fun e : FullSexticTailIndex => fermatCoefficients e.val)

private theorem seed_leading : seedEvaluation (X fullSexticLeadingIndex) = 1 := by
  rw [CycleQ2GenericSexticGradient.seedEvaluation, eval_X, fermatCoefficients,
    fullSexticLeadingIndex_exponent]
  change (CycleQ2FermatSymbolDetector.fermatPolynomial ℂ).coeff (Finsupp.single 4 3) = 1
  exact CycleQ2FermatSymbolDetector.fermatLeading ℂ

theorem fermat_factor : fermatPoint.comp rawToMonic = seedEvaluation := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fermatPoint, CycleQ2GenericSexticGradient.seedEvaluation]
  · intro e
    change fermatPoint (rawToMonic (X e)) = seedEvaluation (X e)
    rw [rawToMonic_X]
    by_cases h : (e.val 4).val < 3
    · rw [rawCoordinate_tail (⟨e,h⟩ : FullSexticTailIndex)]
      simp [fermatPoint, CycleQ2GenericSexticGradient.seedEvaluation]
    · have he : e = fullSexticLeadingIndex := by
        by_contra he
        exact h ((fullSextic_tail_iff_ne e).mpr he)
      subst e
      rw [rawCoordinate_leading, map_one]
      exact seed_leading.symm

abbrev OpenCoefficients := CycleQ2PolynomialCoefficientOpen.OpenCoefficients rawToMonic

abbrev coefficientMap : CoeffRing →+* OpenCoefficients :=
  CycleQ2PolynomialCoefficientOpen.coefficientMap rawToMonic

abbrev toOpen : Parameters →+* OpenCoefficients := CycleQ2PolynomialCoefficientOpen.toOpen rawToMonic

abbrev coefficientPartial := CycleQ2PolynomialCoefficientOpen.coefficientPartial rawToMonic

abbrev fermatEvaluation : OpenCoefficients →+* ℂ :=
  CycleQ2PolynomialCoefficientOpen.fermatEvaluation rawToMonic fermatPoint fermat_factor

theorem equation_monic : CycleQ2UniversalPoleFrame.equation coefficientMap =
    MvPolynomial.map toOpen (monicFamily ℂ) := by
  change MvPolynomial.map (toOpen.comp rawToMonic) universalF = _
  rw [← MvPolynomial.map_map]
  exact congrArg (MvPolynomial.map toOpen) equation_rawToMonic

theorem vectorRealize_injective :
    Function.Injective (CycleQ2UniversalPoleFrame.vectorRealize coefficientMap) :=
  CycleQ2PolynomialCoefficientOpen.vectorRealize_injective rawToMonic fermatPoint fermat_factor

theorem basisSymbol_linearIndependent : LinearIndependent OpenCoefficients
    (CycleQ2UniversalPoleFrame.basisSymbol coefficientMap) :=
  CycleQ2PolynomialCoefficientOpen.basisSymbol_linearIndependent rawToMonic fermatPoint fermat_factor

theorem rank_specialize_ge {n s : Type*} [Fintype n] [Fintype s]
    (P : Matrix n s OpenCoefficients)
    (B : FullSexticTailIndex → Matrix n n OpenCoefficients)
    (C : FullSexticTailIndex → Matrix s s OpenCoefficients)
    (h : ∀ i, P.map (coefficientPartial i) = P * C i - B i * P) (r : ℕ)
    (hne : ∃ I : Fin r → n, ∃ J : Fin r → s, (P.submatrix I J).det ≠ 0)
    {L : Type*} [Field L] (ρ : OpenCoefficients →+* L) : r ≤ (P.map ρ).rank :=
  CycleQ2DifferentialMinorStability.rank_specialize_ge P r
    (CycleQ2DifferentialMinorStability.minorIdeal_eq_top coefficientPartial
      (CycleQ2PolynomialCoefficientOpen.differential_ideal_eq_top rawToMonic) P B C h r hne) ρ

end CycleQ2MonicFermatCoefficientOpen
end

#print axioms CycleQ2PolynomialCoefficientOpen.vectorRealize_injective
#print axioms CycleQ2MonicFermatCoefficientOpen.equation_rawToMonic
#print axioms CycleQ2MonicFermatCoefficientOpen.vectorRealize_injective
#print axioms CycleQ2MonicFermatCoefficientOpen.rank_specialize_ge

/-!
# Clearing coefficient denominators in normalized pole symbols

Changing the coefficient ring by a localization localizes the entire pole
symbol module. This includes the relation submodule: a common denominator
for the numerator of a relation gives a relation over the original ring.
Consequently independence on the coefficient open persists over its field
of fractions without a flatness assumption on the residue realization.
-/

noncomputable section
namespace CycleQ2PoleSymbolLocalization

open MvPolynomial CycleQ2PolynomialPoleSymbols

variable {R : Type*} [CommRing R] (K : Type*) [CommRing K] [Algebra R K]

def polynomialMap : MvPolynomial (Fin 5) R →ₗ[R] MvPolynomial (Fin 5) K :=
  (AddMonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (Algebra.linearMap R K) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap

@[simp] theorem polynomialMap_apply (P : MvPolynomial (Fin 5) R) :
    polynomialMap K P = MvPolynomial.map (algebraMap R K) P := by
  ext m
  rw [MvPolynomial.coeff_map]
  rfl

def polesMap : Poles R →ₗ[R] Poles K :=
  Finsupp.mapRange.linearMap (polynomialMap K)

@[simp] theorem polesMap_single (n : ℕ) (P : MvPolynomial (Fin 5) R) :
    polesMap K (Finsupp.single n P) =
      Finsupp.single n (MvPolynomial.map (algebraMap R K) P) := by
  simp [polesMap, Finsupp.mapRange.linearMap, polynomialMap_apply]

private def relationVector (T : Type*) [CommRing T] (F : MvPolynomial (Fin 5) T)
    (n : ℕ) (i : Fin 5) (P : MvPolynomial (Fin 5) T) : Poles T :=
  Finsupp.single (n+1) (P * pderiv i F) - Finsupp.single n (pderiv i P)

private theorem relationVector_smul (T : Type*) [CommRing T]
    (F : MvPolynomial (Fin 5) T) (n : ℕ) (i : Fin 5)
    (a : T) (P : MvPolynomial (Fin 5) T) :
    relationVector T F n i (a • P) = a • relationVector T F n i P := by
  simp only [relationVector, smul_mul_assoc, map_smul, smul_sub, Finsupp.smul_single]

private theorem polesMap_relationVector (F : MvPolynomial (Fin 5) R)
    (n : ℕ) (i : Fin 5) (P : MvPolynomial (Fin 5) R) :
    polesMap K (relationVector R F n i P) =
      relationVector K (MvPolynomial.map (algebraMap R K) F) n i
        (MvPolynomial.map (algebraMap R K) P) := by
  simp only [relationVector, map_sub, polesMap_single, map_mul, ← pderiv_map]

variable (S : Submonoid R) [IsLocalization S K] (F : MvPolynomial (Fin 5) R)

instance polynomialMap_isLocalizedModule : IsLocalizedModule S (polynomialMap K (R := R)) := by
  unfold polynomialMap
  infer_instance

instance polesMap_isLocalizedModule : IsLocalizedModule S (polesMap K (R := R)) := by
  unfold polesMap
  infer_instance

/-- The defining normalized relations commute with coefficient localization.
Only one denominator is needed for each polynomial numerator. -/
theorem relations_localized :
    (relations R F).localized' K S (polesMap K) =
      relations K (MvPolynomial.map (algebraMap R K) F) := by
  simp only [relations, Submodule.localized'_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨n, i, P, rfl⟩, rfl⟩
    change polesMap K (relationVector R F n i P) ∈ _
    rw [polesMap_relationVector]
    exact Submodule.subset_span ⟨n, i, MvPolynomial.map (algebraMap R K) P, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, i, P, rfl⟩
    obtain ⟨⟨Q, s⟩, hs⟩ := IsLocalizedModule.surj S (polynomialMap K) P
    have hs' : (algebraMap R K (s : R)) • P = MvPolynomial.map (algebraMap R K) Q := by
      simpa only [algebraMap_smul, Submonoid.smul_def, polynomialMap_apply] using hs
    change relationVector K (MvPolynomial.map (algebraMap R K) F) n i P ∈ _
    apply (Submodule.smul_mem_iff_of_isUnit _ (IsLocalization.map_units K s)).mp
    rw [← relationVector_smul, hs', ← polesMap_relationVector]
    exact Submodule.subset_span ⟨relationVector R F n i Q, ⟨n, i, Q, rfl⟩, rfl⟩

def quotientEquiv :
    (Poles K ⧸ (relations R F).localized' K S (polesMap K)) ≃ₗ[K]
      Symbols K (MvPolynomial.map (algebraMap R K) F) :=
  Submodule.quotEquivOfEq _ _ (relations_localized K S F)

/-- The ordinary coefficient specialization, viewed as a linear localization
map for the scalar action of the original coefficient ring. -/
def localize : Symbols R F →ₗ[R] Symbols K (MvPolynomial.map (algebraMap R K) F) :=
  (quotientEquiv K S F).restrictScalars R ∘ₗ
    (relations R F).toLocalizedQuotient' K S (polesMap K)

instance localize_isLocalizedModule : IsLocalizedModule S (localize K S F) := by
  unfold localize
  infer_instance

@[simp] theorem localize_symbol (n : ℕ) (P : MvPolynomial (Fin 5) R) :
    localize K S F (symbol R F n P) =
      symbol K (MvPolynomial.map (algebraMap R K) F) n
        (MvPolynomial.map (algebraMap R K) P) := by
  change Submodule.Quotient.mk (polesMap K (Finsupp.single n P)) =
    Submodule.Quotient.mk (Finsupp.single n (MvPolynomial.map (algebraMap R K) P))
  rw [polesMap_single]

theorem localize_eq_specialize (x : Symbols R F) :
    localize K S F x = specialize (algebraMap R K) F x := by
  refine Submodule.Quotient.induction_on _ x ?_
  intro p
  induction p using Finsupp.induction_linear with
  | zero =>
    change localize K S F 0 = specialize (algebraMap R K) F 0
    simp
  | add p q hp hq =>
    change localize K S F (Submodule.Quotient.mk p + Submodule.Quotient.mk q) =
      specialize (algebraMap R K) F (Submodule.Quotient.mk p + Submodule.Quotient.mk q)
    rw [map_add, map_add, hp, hq]
  | single n P =>
    change localize K S F (symbol R F n P) =
      specialize (algebraMap R K) F (symbol R F n P)
    rw [localize_symbol, specialize_symbol]

/-- Every localized symbol has a common coefficient denominator. -/
theorem exists_denominator (x : Symbols K (MvPolynomial.map (algebraMap R K) F)) :
    ∃ (a : S) (y : Symbols R F),
      specialize (algebraMap R K) F y = (algebraMap R K (a : R)) • x := by
  obtain ⟨⟨y, a⟩, h⟩ := IsLocalizedModule.surj S (localize K S F) x
  exact ⟨a, y, by
    simpa only [localize_eq_specialize, Submonoid.smul_def, algebraMap_smul] using h.symm⟩

/-- A class becomes zero precisely when a coefficient denominator kills it. -/
theorem specialize_eq_zero_iff (x : Symbols R F) :
    specialize (algebraMap R K) F x = 0 ↔ ∃ a : S, (a : R) • x = 0 := by
  rw [← localize_eq_specialize K S F x]
  simpa only [Submonoid.smul_def] using IsLocalizedModule.eq_zero_iff S (localize K S F)

/-- Independence survives coefficient localization, including passage to
the generic coefficient field. -/
theorem linearIndependent {ι : Type*} {v : ι → Symbols R F}
    (hv : LinearIndependent R v) :
    LinearIndependent K (fun i => specialize (algebraMap R K) F (v i)) := by
  simpa only [Function.comp_apply, localize_eq_specialize] using
    (LinearIndependent.of_isLocalizedModule K S (localize K S F) hv)

end CycleQ2PoleSymbolLocalization
end

#print axioms CycleQ2PoleSymbolLocalization.relations_localized
#print axioms CycleQ2PoleSymbolLocalization.localize_isLocalizedModule
#print axioms CycleQ2PoleSymbolLocalization.linearIndependent

noncomputable section
namespace CycleQ2PoleSymbolLocalization

open MvPolynomial CycleQ2PolynomialPoleSymbols
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2UniversalPoleFrame (equation basisSymbol Label)

variable {R K : Type*} [CommRing R] [CommRing K]

theorem exists_nonzero_denominator [IsDomain R] [Algebra R K] [IsFractionRing R K]
    (F : MvPolynomial (Fin 5) R)
    (x : Symbols K (MvPolynomial.map (algebraMap R K) F)) :
    ∃ a : R, a ≠ 0 ∧ ∃ y : Symbols R F,
      specialize (algebraMap R K) F y = (algebraMap R K a) • x := by
  obtain ⟨a, y, h⟩ := exists_denominator K (nonZeroDivisors R) F x
  exact ⟨a, mem_nonZeroDivisors_iff_ne_zero.mp a.property, y, h⟩

/-- Identifies the equation obtained by two successive coefficient maps
with the equation obtained from their composite. -/
def equationMapEquiv (θ : R →+* K) (φ : CoeffRing →+* R) :
    Symbols K (MvPolynomial.map θ (equation φ)) ≃ₗ[K] Symbols K (equation (θ.comp φ)) :=
  Submodule.quotEquivOfEq _ _ (by simp only [equation, MvPolynomial.map_map])

@[simp] theorem equationMapEquiv_symbol (θ : R →+* K) (φ : CoeffRing →+* R)
    (n : ℕ) (P : MvPolynomial (Fin 5) K) :
    equationMapEquiv θ φ (symbol K (MvPolynomial.map θ (equation φ)) n P) =
      symbol K (equation (θ.comp φ)) n P := rfl

@[simp] theorem equationMapEquiv_specialize_basisSymbol
    (θ : R →+* K) (φ : CoeffRing →+* R) (i : Label) :
    equationMapEquiv θ φ (specialize θ (equation φ) (basisSymbol φ i)) =
      basisSymbol (θ.comp φ) i := by
  rcases i with i | i <;>
    simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole, specialize_symbol,
      map_monomial, map_one, equationMapEquiv_symbol]

/-- Independence can be checked after any injective coefficient map for
which the coefficient-changed frame is independent. -/
theorem basisSymbol_linearIndependent_of_map (θ : R →+* K) (φ : CoeffRing →+* R)
    (hθ : Function.Injective θ) (h : LinearIndependent K (basisSymbol (θ.comp φ))) :
    LinearIndependent R (basisSymbol φ) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hz : ∑ j, θ (c j) • specialize θ (equation φ) (basisSymbol φ j) = 0 := by
    simpa only [map_sum, map_smulₛₗ, map_zero] using
      congrArg (specialize θ (equation φ)) hc
  have he := congrArg (equationMapEquiv θ φ) hz
  simp only [map_sum, map_smul, equationMapEquiv_specialize_basisSymbol, map_zero] at he
  exact hθ (((Fintype.linearIndependent_iff.mp h) (fun j => θ (c j)) he i).trans
    (map_zero θ).symm)

/-- The literal universal basis, with its composite coefficient map,
remains independent after localization. -/
theorem basisSymbol_linearIndependent_localization (K : Type*) [CommRing K] [Algebra R K]
    (S : Submonoid R) [IsLocalization S K] (φ : CoeffRing →+* R)
    (h : LinearIndependent R (basisSymbol φ)) :
    LinearIndependent K (basisSymbol ((algebraMap R K).comp φ)) := by
  classical
  have hi := linearIndependent K S (equation φ) h
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro c hc i
  apply hi c ?_ i
  apply (equationMapEquiv (algebraMap R K) φ).injective
  simpa only [map_sum, map_smul, equationMapEquiv_specialize_basisSymbol, map_zero] using hc

end CycleQ2PoleSymbolLocalization

namespace CycleQ2PolynomialCoefficientOpen

open MvPolynomial CycleQ2GenericSexticGradient

variable {σ : Type} [Fintype σ] [DecidableEq σ]
    (ψ : CoeffRing →+* Parameters σ) (ρ₀ : Parameters σ →+* ℂ)
    (point : ρ₀.comp ψ = seedEvaluation)

theorem denominator_ne_zero : denominator ψ ≠ 0 := by
  intro h
  have he := point_denominator ψ ρ₀ point
  rw [h, map_zero] at he
  exact zero_ne_one he

theorem toOpen_injective : Function.Injective (toOpen ψ) :=
  IsLocalization.injective (OpenCoefficients ψ)
    (Submonoid.powers_le.mpr
      (mem_nonZeroDivisors_iff_ne_zero.mpr (denominator_ne_zero ψ ρ₀ point)))

/-- The frame is already independent over the polynomial parameter ring.
Any polynomial-coefficient relation would persist on its coefficient open. -/
theorem polynomial_basisSymbol_linearIndependent : LinearIndependent (Parameters σ)
    (CycleQ2UniversalPoleFrame.basisSymbol ψ) :=
  CycleQ2PoleSymbolLocalization.basisSymbol_linearIndependent_of_map (toOpen ψ) ψ
    (toOpen_injective ψ ρ₀ point) (basisSymbol_linearIndependent ψ ρ₀ point)

end CycleQ2PolynomialCoefficientOpen

namespace CycleQ2MonicFermatCoefficientOpen

open MvPolynomial CycleQ2GenericSexticGradient
open CycleQ2HiggsJacobianFrames (frameDet seed_frameDet)
open CycleQ2PolynomialPoleSymbols (monicFamily)

abbrev GenericCoefficients := FractionRing Parameters

def genericCoefficientMap : CoeffRing →+* GenericCoefficients :=
  (algebraMap Parameters GenericCoefficients).comp rawToMonic

theorem generic_equation_monic : CycleQ2UniversalPoleFrame.equation genericCoefficientMap =
    MvPolynomial.map (algebraMap Parameters GenericCoefficients) (monicFamily ℂ) := by
  change MvPolynomial.map ((algebraMap Parameters GenericCoefficients).comp rawToMonic) universalF = _
  rw [← MvPolynomial.map_map]
  exact congrArg (MvPolynomial.map (algebraMap Parameters GenericCoefficients)) equation_rawToMonic

theorem polynomial_basisSymbol_linearIndependent : LinearIndependent Parameters
    (CycleQ2UniversalPoleFrame.basisSymbol rawToMonic) :=
  CycleQ2PolynomialCoefficientOpen.polynomial_basisSymbol_linearIndependent
    rawToMonic fermatPoint fermat_factor

/-- Independence of the actual 66 normalized symbols over the fraction field
of the 44 monic coefficient parameters. -/
theorem generic_basisSymbol_linearIndependent : LinearIndependent GenericCoefficients
    (CycleQ2UniversalPoleFrame.basisSymbol genericCoefficientMap) :=
  CycleQ2PoleSymbolLocalization.basisSymbol_linearIndependent_localization GenericCoefficients
    (nonZeroDivisors Parameters) rawToMonic polynomial_basisSymbol_linearIndependent

theorem generic_vectorRealize_injective :
    Function.Injective (CycleQ2UniversalPoleFrame.vectorRealize genericCoefficientMap) := by
  classical
  intro v w h
  funext i
  apply sub_eq_zero.mp
  apply (Fintype.linearIndependent_iff.mp generic_basisSymbol_linearIndependent) (v-w) ?_ i
  change CycleQ2UniversalPoleFrame.vectorRealize genericCoefficientMap (v-w) = 0
  rw [map_sub, h, sub_self]

theorem generic_frame_units :
    IsUnit (genericCoefficientMap (frameDet 6 1)) ∧
      IsUnit (genericCoefficientMap (frameDet 12 1)) ∧
      IsUnit (genericCoefficientMap (frameDet 18 1)) := by
  have hu (n : ℕ) : IsUnit (genericCoefficientMap (frameDet n 1)) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    change algebraMap Parameters GenericCoefficients (rawToMonic (frameDet n 1)) = 0 at h
    have hz := IsFractionRing.injective Parameters GenericCoefficients
      (h.trans (map_zero (algebraMap Parameters GenericCoefficients)).symm)
    have hf := congrArg (fun f : CoeffRing →+* ℂ => f (frameDet n 1)) fermat_factor
    simp only [RingHom.comp_apply, seed_frameDet] at hf
    rw [hz, map_zero] at hf
    exact zero_ne_one hf
  exact ⟨hu 6, hu 12, hu 18⟩

end CycleQ2MonicFermatCoefficientOpen
end

#print axioms CycleQ2PoleSymbolLocalization.basisSymbol_linearIndependent_localization
#print axioms CycleQ2MonicFermatCoefficientOpen.polynomial_basisSymbol_linearIndependent
#print axioms CycleQ2MonicFermatCoefficientOpen.generic_basisSymbol_linearIndependent
#print axioms CycleQ2MonicFermatCoefficientOpen.generic_vectorRealize_injective
#print axioms CycleQ2MonicFermatCoefficientOpen.generic_frame_units

/-!
# Regular monic connections inside the generic coefficient field

The generic frame connection is the image of a connection on the explicit
Fermat-containing coefficient open. This follows from coefficient-map
naturality and the proved independence of the generic frame, so no extra
regularity hypothesis is imposed on a chosen generic connection matrix.
-/

noncomputable section
namespace CycleQ2MonicFermatCoefficientOpen

open MvPolynomial CycleQ2PolynomialPoleSymbols
open CycleQ2PolynomialCoefficientDerivation
open CycleQ2UniversalPoleFrame (Label equation basisSymbol vectorRealize)
open CycleQ2GeometricLocalizedDerivations
open CycleQ2IncidenceNormalForm (FullSexticTailIndex)

abbrev denominators : Submonoid Parameters :=
  Submonoid.powers (CycleQ2PolynomialCoefficientOpen.denominator rawToMonic)

theorem denominators_regular : denominators ≤ nonZeroDivisors Parameters :=
  Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr
    (CycleQ2PolynomialCoefficientOpen.denominator_ne_zero rawToMonic fermatPoint fermat_factor))

/-- The coefficient open embeds into the same fraction field as the monic
polynomial parameter ring. -/
def toGeneric : OpenCoefficients →ₐ[Parameters] GenericCoefficients :=
  Localization.mapToFractionRing GenericCoefficients denominators OpenCoefficients denominators_regular

@[simp] theorem toGeneric_toOpen (a : Parameters) :
    toGeneric (toOpen a) = algebraMap Parameters GenericCoefficients a :=
  toGeneric.commutes a

theorem toGeneric_injective : Function.Injective toGeneric := by
  change Function.Injective
    (IsLocalization.lift (S := OpenCoefficients)
      (Localization.map_isUnit_of_le GenericCoefficients denominators denominators_regular))
  apply (IsLocalization.lift_injective_iff _).mpr
  intro a b
  exact ⟨fun h => congrArg (algebraMap Parameters GenericCoefficients)
      (IsLocalization.injective OpenCoefficients denominators_regular h),
    fun h => congrArg (algebraMap Parameters OpenCoefficients)
      (IsFractionRing.injective Parameters GenericCoefficients h)⟩

@[simp] theorem toGeneric_coefficientMap (a : CycleQ2GenericSexticGradient.CoeffRing) :
    toGeneric (coefficientMap a) = genericCoefficientMap a :=
  toGeneric.commutes (rawToMonic a)

theorem toGeneric_comp : toGeneric.toRingHom.comp coefficientMap = genericCoefficientMap := by
  ext a
  exact toGeneric_coefficientMap a

def genericCoefficientPartial (e : FullSexticTailIndex) :
    Derivation ℤ GenericCoefficients GenericCoefficients :=
  HoldoutConstruction.extendRingDerivation (L := GenericCoefficients)
    (HoldoutConstruction.integerPartial (R := ℂ) e)

theorem genericCoefficientPartial_algebraMap (e : FullSexticTailIndex) (a : Parameters) :
    genericCoefficientPartial e (algebraMap Parameters GenericCoefficients a) =
      algebraMap Parameters GenericCoefficients (pderiv e a) :=
  HoldoutConstruction.extendRingDerivation_apply _ _

/-- The regular coefficient partial and the generic partial agree through
the actual embedding of the monic coefficient open. -/
theorem partial_toGeneric (e : FullSexticTailIndex) (a : OpenCoefficients) :
    genericCoefficientPartial e (toGeneric a) = toGeneric (coefficientPartial e a) := by
  apply derivation_commutes_of_algebraMap denominators
    (coefficientPartial e) (genericCoefficientPartial e) toGeneric.toRingHom
  intro p
  change genericCoefficientPartial e (toGeneric (toOpen p)) =
    toGeneric (coefficientPartial e (toOpen p))
  rw [toGeneric_toOpen, genericCoefficientPartial_algebraMap,
    CycleQ2PolynomialCoefficientOpen.coefficientPartial_toOpen, toGeneric_toOpen]

theorem equation_toGeneric :
    MvPolynomial.map toGeneric.toRingHom (equation coefficientMap) = equation genericCoefficientMap := by
  rw [equation, MvPolynomial.map_map, toGeneric_comp]

private def equationToGenericEquiv :
    Symbols GenericCoefficients (MvPolynomial.map toGeneric.toRingHom (equation coefficientMap)) ≃ₗ[GenericCoefficients]
      Symbols GenericCoefficients (equation genericCoefficientMap) :=
  Submodule.quotEquivOfEq _ _ (congrArg (relations GenericCoefficients) equation_toGeneric)

/-- Coefficient specialization into the literal generic frame presentation. -/
def toGenericSymbols : Symbols OpenCoefficients (equation coefficientMap) →ₛₗ[toGeneric.toRingHom]
    Symbols GenericCoefficients (equation genericCoefficientMap) :=
  equationToGenericEquiv.toLinearMap.comp
    (specialize toGeneric.toRingHom (equation coefficientMap))

@[simp] theorem toGenericSymbols_symbol (n : ℕ) (P : MvPolynomial (Fin 5) OpenCoefficients) :
    toGenericSymbols (symbol OpenCoefficients (equation coefficientMap) n P) =
      symbol GenericCoefficients (equation genericCoefficientMap) n
        (MvPolynomial.map toGeneric.toRingHom P) := by
  change equationToGenericEquiv
    (specialize toGeneric.toRingHom (equation coefficientMap)
      (symbol OpenCoefficients (equation coefficientMap) n P)) = _
  rw [specialize_symbol]
  rfl

@[simp] theorem toGenericSymbols_basisSymbol (i : Label) :
    toGenericSymbols (basisSymbol coefficientMap i) = basisSymbol genericCoefficientMap i := by
  rcases i with i | i <;>
    simp only [basisSymbol, CycleQ2UniversalPoleFrame.pole, toGenericSymbols_symbol,
      map_monomial, map_one]

@[simp] theorem toGenericSymbols_vectorRealize (v : Label → OpenCoefficients) :
    toGenericSymbols (vectorRealize coefficientMap v) =
      vectorRealize genericCoefficientMap (fun i => toGeneric (v i)) := by
  change toGenericSymbols (∑ i, v i • basisSymbol coefficientMap i) =
    ∑ i, toGeneric (v i) • basisSymbol genericCoefficientMap i
  simp only [map_sum, map_smulₛₗ, toGenericSymbols_basisSymbol]

private theorem coefficientDerivation_toGeneric (e : FullSexticTailIndex)
    (P : MvPolynomial (Fin 5) OpenCoefficients) :
    coefficientDerivation (genericCoefficientPartial e) (MvPolynomial.map toGeneric.toRingHom P) =
      MvPolynomial.map toGeneric.toRingHom (coefficientDerivation (coefficientPartial e) P) := by
  induction P using MvPolynomial.induction_on' with
  | monomial m c => simp only [map_monomial, coefficientDerivation_monomial, partial_toGeneric]
  | add P Q hP hQ => simp only [map_add, hP, hQ]

theorem toGenericSymbols_connection (e : FullSexticTailIndex)
    (x : Symbols OpenCoefficients (equation coefficientMap)) :
    toGenericSymbols (connection (coefficientPartial e) (equation coefficientMap) x) =
      connection (genericCoefficientPartial e) (equation genericCoefficientMap) (toGenericSymbols x) := by
  refine Submodule.Quotient.induction_on _ x (fun P => ?_)
  induction P using Finsupp.induction_linear with
  | zero => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | single n P =>
    change toGenericSymbols (connection (coefficientPartial e) (equation coefficientMap)
      (symbol OpenCoefficients (equation coefficientMap) n P)) =
      connection (genericCoefficientPartial e) (equation genericCoefficientMap)
        (toGenericSymbols (symbol OpenCoefficients (equation coefficientMap) n P))
    have hF : coefficientDerivation (genericCoefficientPartial e) (equation genericCoefficientMap) =
        MvPolynomial.map toGeneric.toRingHom
          (coefficientDerivation (coefficientPartial e) (equation coefficientMap)) := by
      rw [← equation_toGeneric, coefficientDerivation_toGeneric]
    simp only [connection_symbol, map_sub, toGenericSymbols_symbol, map_mul,
      coefficientDerivation_toGeneric, hF]

private theorem regularConnection_exists (e : FullSexticTailIndex) :
    ∃ B : Matrix Label Label OpenCoefficients, ∀ v : Label → OpenCoefficients,
      vectorRealize coefficientMap (fun i => coefficientPartial e (v i) + B.mulVec v i) =
        connection (coefficientPartial e) (equation coefficientMap) (vectorRealize coefficientMap v) := by
  obtain ⟨h6, h12, h18⟩ := CycleQ2PolynomialCoefficientOpen.frame_units rawToMonic
  exact CycleQ2UniversalPoleFrame.exists_vector_connection coefficientMap h6 h12 h18
    (coefficientPartial e)

def regularConnection (e : FullSexticTailIndex) : Matrix Label Label OpenCoefficients :=
  (regularConnection_exists e).choose

theorem regularConnection_spec (e : FullSexticTailIndex) (v : Label → OpenCoefficients) :
    vectorRealize coefficientMap
      (fun i => coefficientPartial e (v i) + (regularConnection e).mulVec v i) =
      connection (coefficientPartial e) (equation coefficientMap) (vectorRealize coefficientMap v) :=
  (regularConnection_exists e).choose_spec v

/-- Every generic connection matrix satisfying the actual symbol identity is
the image of the regular matrix on the monic coefficient open. -/
theorem generic_connection_eq_map (e : FullSexticTailIndex)
    (B : Matrix Label Label GenericCoefficients)
    (hB : ∀ v : Label → GenericCoefficients,
      vectorRealize genericCoefficientMap (fun i => genericCoefficientPartial e (v i) + B.mulVec v i) =
        connection (genericCoefficientPartial e) (equation genericCoefficientMap)
          (vectorRealize genericCoefficientMap v)) :
    B = (regularConnection e).map toGeneric := by
  classical
  have hmul (v : Label → OpenCoefficients) (i : Label) :
      B.mulVec (fun j => toGeneric (v j)) i = toGeneric ((regularConnection e).mulVec v i) := by
    have ho := congrArg toGenericSymbols (regularConnection_spec e v)
    rw [toGenericSymbols_vectorRealize, toGenericSymbols_connection,
      toGenericSymbols_vectorRealize] at ho
    have hv := generic_vectorRealize_injective ((hB (fun j => toGeneric (v j))).trans ho.symm)
    have hi := congrFun hv i
    rw [map_add, ← partial_toGeneric] at hi
    exact add_left_cancel hi
  ext i j
  have hw : (fun k => toGeneric (Pi.single j (1 : OpenCoefficients) k)) =
      Pi.single j (1 : GenericCoefficients) := by
    funext k
    by_cases h : k = j <;> simp [Pi.single_apply, h, eq_comm]
  have hi := hmul (Pi.single j 1) i
  rw [hw, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at hi
  exact hi

/-- The mapped regular matrix gives the generic connection on every vector,
including vectors whose coefficients have arbitrary generic denominators. -/
theorem mapped_regularConnection_spec (e : FullSexticTailIndex) (v : Label → GenericCoefficients) :
    vectorRealize genericCoefficientMap
      (fun i => genericCoefficientPartial e (v i) + ((regularConnection e).map toGeneric).mulVec v i) =
      connection (genericCoefficientPartial e) (equation genericCoefficientMap)
        (vectorRealize genericCoefficientMap v) := by
  obtain ⟨B, hB⟩ := CycleQ2UniversalPoleFrame.exists_vector_connection genericCoefficientMap
    generic_frame_units.1 generic_frame_units.2.1 generic_frame_units.2.2 (genericCoefficientPartial e)
  rw [← generic_connection_eq_map e B hB]
  exact hB v

end CycleQ2MonicFermatCoefficientOpen
end

#print axioms CycleQ2MonicFermatCoefficientOpen.toGeneric_injective
#print axioms CycleQ2MonicFermatCoefficientOpen.partial_toGeneric
#print axioms CycleQ2MonicFermatCoefficientOpen.generic_connection_eq_map
#print axioms CycleQ2MonicFermatCoefficientOpen.mapped_regularConnection_spec

/-!
# The regular lattice of an actual generic invariant subspace

Pullback through the coefficient-open embedding preserves the given generic
subspace. A common denominator for its finitely many coordinates proves that
the pullback spans the original subspace, rather than a replacement for it.
The connection matrices on finite generators are then consequences of
stability and Noetherianity.
-/

noncomputable section
namespace CycleQ2MonicFermatCoefficientOpen

open CycleQ2UniversalPoleFrame (Label)
open CycleQ2IncidenceNormalForm (FullSexticTailIndex)

/-- The coordinatewise embedding of the regular frame into the generic frame. -/
def toGenericVector : (Label → OpenCoefficients) →ₛₗ[toGeneric.toRingHom]
    (Label → GenericCoefficients) where
  toFun v i := toGeneric (v i)
  map_add' v w := by
    funext i
    exact map_add toGeneric (v i) (w i)
  map_smul' a v := by
    funext i
    exact map_mul toGeneric a (v i)

@[simp] theorem toGenericVector_apply (v : Label → OpenCoefficients) (i : Label) :
    toGenericVector v i = toGeneric (v i) := rfl

theorem toGenericVector_mulVec {s : Type*} [Fintype s]
    (P : Matrix Label s OpenCoefficients) (v : s → OpenCoefficients) :
    toGenericVector (P.mulVec v) = (P.map toGeneric).mulVec (fun j => toGeneric (v j)) := by
  classical
  funext i
  change toGeneric (∑ j, P i j * v j) = ∑ j, toGeneric (P i j) * toGeneric (v j)
  simp only [map_sum, map_mul]

theorem toGenericVector_connection (e : FullSexticTailIndex) (v : Label → OpenCoefficients) :
    toGenericVector (fun i => coefficientPartial e (v i) + (regularConnection e).mulVec v i) =
      fun i => genericCoefficientPartial e (toGenericVector v i) +
        ((regularConnection e).map toGeneric).mulVec (toGenericVector v) i := by
  classical
  funext i
  change toGeneric (coefficientPartial e (v i) + ∑ j, regularConnection e i j * v j) =
    genericCoefficientPartial e (toGeneric (v i)) +
      ∑ j, toGeneric (regularConnection e i j) * toGeneric (v j)
  simp only [map_add, map_sum, map_mul, partial_toGeneric]

/-- This is the inverse image of the specified generic subspace. -/
def regularLattice (W : Submodule GenericCoefficients (Label → GenericCoefficients)) :
    Submodule OpenCoefficients (Label → OpenCoefficients) :=
  W.comap toGenericVector

@[simp] theorem mem_regularLattice
    (W : Submodule GenericCoefficients (Label → GenericCoefficients))
    (v : Label → OpenCoefficients) : v ∈ regularLattice W ↔ toGenericVector v ∈ W := Iff.rfl

theorem regularLattice_stable
    (W : Submodule GenericCoefficients (Label → GenericCoefficients))
    (stable : ∀ e w, w ∈ W →
      (fun i => genericCoefficientPartial e (w i) +
        ((regularConnection e).map toGeneric).mulVec w i) ∈ W)
    (e : FullSexticTailIndex) (v : Label → OpenCoefficients) (hv : v ∈ regularLattice W) :
    (fun i => coefficientPartial e (v i) + (regularConnection e).mulVec v i) ∈ regularLattice W := by
  change toGenericVector (fun i => coefficientPartial e (v i) +
    (regularConnection e).mulVec v i) ∈ W
  rw [toGenericVector_connection]
  exact stable e _ hv

/-- Pullback from a field subspace is saturated in the regular frame. -/
theorem regularLattice_saturated
    (W : Submodule GenericCoefficients (Label → GenericCoefficients))
    {a : OpenCoefficients} (ha : a ≠ 0) {v : Label → OpenCoefficients}
    (hv : a • v ∈ regularLattice W) : v ∈ regularLattice W := by
  have hunit : IsUnit (toGeneric a) := isUnit_iff_ne_zero.mpr (by
    intro h
    exact ha (toGeneric_injective (h.trans (map_zero toGeneric).symm)))
  change toGenericVector (a • v) ∈ W at hv
  rw [map_smulₛₗ] at hv
  exact (Submodule.smul_mem_iff_of_isUnit W hunit).mp hv

/-- All 66 coordinate denominators can be cleared by one nonzero monic
parameter polynomial. Its numerator vector already lies on the coefficient open. -/
theorem exists_vector_denominator (w : Label → GenericCoefficients) :
    ∃ (a : nonZeroDivisors Parameters) (v : Label → OpenCoefficients),
      toGenericVector v = (algebraMap Parameters GenericCoefficients (a : Parameters)) • w := by
  classical
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors Parameters) w
  change ∀ i, ∃ b : Parameters, algebraMap Parameters GenericCoefficients b =
    (a : Parameters) • w i at ha
  choose b hb using ha
  refine ⟨a, fun i => toOpen (b i), ?_⟩
  funext i
  change toGeneric (toOpen (b i)) = algebraMap Parameters GenericCoefficients (a : Parameters) * w i
  rw [toGeneric_toOpen]
  simpa only [Algebra.smul_def] using hb i

/-- The regular pullback spans exactly the original generic subspace. -/
theorem regularLattice_spans
    (W : Submodule GenericCoefficients (Label → GenericCoefficients)) :
    Submodule.span GenericCoefficients
      (Set.range (fun v : regularLattice W => toGenericVector v.val)) = W := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    exact v.property
  · intro w hw
    obtain ⟨a, v, hv⟩ := exists_vector_denominator w
    have hvW : v ∈ regularLattice W := by
      change toGenericVector v ∈ W
      rw [hv]
      exact W.smul_mem _ hw
    apply (Submodule.smul_mem_iff_of_isUnit _
      (IsLocalization.map_units GenericCoefficients a)).mp
    rw [← hv]
    exact Submodule.subset_span ⟨⟨v, hvW⟩, rfl⟩

/-- Any finite regular generating matrix has generic column span equal to
the original subspace; no constant-rank hypothesis is assumed here. -/
theorem mapped_generator_range {s : Type*} [Fintype s]
    (W : Submodule GenericCoefficients (Label → GenericCoefficients))
    (P : Matrix Label s OpenCoefficients)
    (hP : LinearMap.range P.mulVecLin = regularLattice W) :
    LinearMap.range (P.map toGeneric).mulVecLin = W := by
  classical
  apply le_antisymm
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    have hcol : (fun i => P i j) ∈ regularLattice W := by
      rw [← hP, Matrix.range_mulVecLin]
      exact Submodule.subset_span ⟨j, rfl⟩
    exact hcol
  · intro w hw
    obtain ⟨a, v, hv⟩ := exists_vector_denominator w
    have hvW : v ∈ regularLattice W := by
      change toGenericVector v ∈ W
      rw [hv]
      exact W.smul_mem _ hw
    rw [← hP] at hvW
    obtain ⟨c, hc⟩ := hvW
    change P.mulVec c = v at hc
    have he := congrArg toGenericVector hc
    rw [toGenericVector_mulVec, hv] at he
    apply (Submodule.smul_mem_iff_of_isUnit _
      (IsLocalization.map_units GenericCoefficients a)).mp
    exact ⟨fun j => toGeneric (c j), he⟩

/-- A stable generic subspace supplies actual finite regular generators and
all their connection identities on this fixed Fermat-containing open. -/
theorem exists_regularLattice_generators
    (W : Submodule GenericCoefficients (Label → GenericCoefficients))
    (stable : ∀ e w, w ∈ W →
      (fun i => genericCoefficientPartial e (w i) +
        ((regularConnection e).map toGeneric).mulVec w i) ∈ W) :
    ∃ (s : ℕ) (P : Matrix Label (Fin s) OpenCoefficients)
      (C : FullSexticTailIndex → Matrix (Fin s) (Fin s) OpenCoefficients),
      LinearMap.range P.mulVecLin = regularLattice W ∧
      LinearMap.range (P.map toGeneric).mulVecLin = W ∧
      ∀ e, P.map (coefficientPartial e) = P * C e - regularConnection e * P := by
  obtain ⟨s, P, C, hP, hC⟩ :=
    CycleQ2DifferentialMinorStability.exists_noetherian_generator_connections
      coefficientPartial regularConnection (regularLattice W) (regularLattice_stable W stable)
  exact ⟨s, P, C, hP, mapped_generator_range W P hP, hC⟩

end CycleQ2MonicFermatCoefficientOpen
end

#print axioms CycleQ2MonicFermatCoefficientOpen.regularLattice_saturated
#print axioms CycleQ2MonicFermatCoefficientOpen.regularLattice_spans
#print axioms CycleQ2MonicFermatCoefficientOpen.exists_regularLattice_generators

noncomputable section
namespace CycleQ2MonicFermatCoefficientOpen

open MvPolynomial CycleQ2IncidenceNormalForm (FullSexticTailIndex fullExponentOf)

/-- An integral polynomial defining the same Fermat point over every
constant ring. Its coefficients determine the integral tail assignment. -/
def integralFermat : MvPolynomial (Fin 5) ℤ :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 3

def integerFermatTail (e : FullSexticTailIndex) : ℤ :=
  integralFermat.coeff (fullExponentOf e.val.val)

theorem integerFermatTail_cast (e : FullSexticTailIndex) :
    (integerFermatTail e : ℂ) = CycleQ2GenericSexticGradient.fermatCoefficients e.val := by
  change (Int.castRingHom ℂ) (integralFermat.coeff (fullExponentOf e.val.val)) =
    (CycleQ2FermatSymbolDetector.fermatPolynomial ℂ).coeff (fullExponentOf e.val.val)
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [integralFermat, CycleQ2FermatSymbolDetector.fermatPolynomial,
    map_add, map_pow, map_X]

theorem integerFermat_evaluation :
    eval (fun e : FullSexticTailIndex => (integerFermatTail e : ℂ)) = fermatPoint := by
  unfold fermatPoint
  congr 1
  funext e
  exact integerFermatTail_cast e

theorem integerFermat_denominator :
    (eval (fun e : FullSexticTailIndex => (integerFermatTail e : ℂ)))
      (CycleQ2PolynomialCoefficientOpen.denominator rawToMonic) = 1 := by
  rw [integerFermat_evaluation]
  exact CycleQ2PolynomialCoefficientOpen.point_denominator rawToMonic fermatPoint fermat_factor

theorem integerFermatTail_cast_field (K : Type*) [Field K] (e : FullSexticTailIndex) :
    (integerFermatTail e : K) =
      (CycleQ2FermatSymbolDetector.fermatPolynomial K).coeff (fullExponentOf e.val.val) := by
  change (Int.castRingHom K) (integralFermat.coeff (fullExponentOf e.val.val)) = _
  rw [← MvPolynomial.coeff_map]
  congr 1
  simp only [integralFermat,CycleQ2FermatSymbolDetector.fermatPolynomial,
    map_add,map_pow,map_X]

/-- The same integral Fermat assignment recovers the actual Fermat
polynomial after every change of constant characteristic. -/
theorem map_monicFamily_integerFermat (K : Type*) [Field K] :
    MvPolynomial.map (eval (fun e : FullSexticTailIndex => (integerFermatTail e : K)))
      (CycleQ2PolynomialPoleSymbols.monicFamily K) =
        CycleQ2FermatSymbolDetector.fermatPolynomial K := by
  have he : eval (fun e : FullSexticTailIndex => (integerFermatTail e : K)) =
      CycleQ2PolynomialPoleSymbols.monicEvaluation K (RingHom.id K)
        (CycleQ2FermatSymbolDetector.fermatPolynomial K) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [CycleQ2PolynomialPoleSymbols.monicEvaluation]
    · intro e
      simp only [eval_X,CycleQ2PolynomialPoleSymbols.monicEvaluation,eval₂Hom_X',
        integerFermatTail_cast_field]
  rw [he]
  exact CycleQ2PolynomialPoleSymbols.map_monicFamily K (RingHom.id K) _
    (CycleQ2FermatSymbolDetector.fermatFullHomogeneous K)
    (CycleQ2FermatSymbolDetector.fermatLeading K)

end CycleQ2MonicFermatCoefficientOpen
end

#print axioms CycleQ2MonicFermatCoefficientOpen.integerFermat_evaluation
#print axioms CycleQ2MonicFermatCoefficientOpen.integerFermat_denominator

/-!
# Prime matrices in the normalized regular frame

The regular connection was constructed on normalized pole symbols, whereas
the arithmetic prime entries use ordinary pole forms. Their change of frame
is the explicit diagonal matrix of pole factorials. These factors are units
in every characteristic above six, so the two actual prime blocks retain
the proved strict growth and the opposite-prime dichotomy.
-/

noncomputable section
namespace CycleQ2FermatNormalizedPrime

open CycleQ2FermatPrimeCoefficient (Sector pole primeEntry split_support inert_support)
open CycleQ2FermatSymbolDetector (pole_factor_ne_zero)
open CycleQ2FermatStrictGrowth

variable {K : Type*} [Field K] [NeZero (6 : K)] {p : ℕ} [Fact p.Prime]

def matrix (ι : ZMod p →+* K) (m : Fin 35) : Matrix Sector Sector K :=
  fun u s => (((pole s - 1).factorial : K) / ((pole u - 1).factorial : K)) *
    ι (primeEntry p s m u)

theorem entry_ne_zero_iff (ι : ZMod p →+* K) (m : Fin 35) (s u : Sector) :
    matrix ι m u s ≠ 0 ↔ primeEntry p s m u ≠ 0 := by
  simp only [matrix,mul_ne_zero_iff,div_ne_zero_iff,pole_factor_ne_zero,
    true_and,map_ne_zero]

def splitBlock (ι : ZMod p →+* K) (m : Fin 35) : Matrix (Fin 33) (Fin 33) K :=
  fun j i => matrix ι m (.inr j.rev) (.inl i)

def inertBlock (ι : ZMod p →+* K) (m : Fin 35) : Matrix (Fin 33) (Fin 33) K :=
  fun i j => matrix ι m (.inl i) (.inr j.rev)

/-- The upper and lower coordinates, with the existing reversed lower
ordering used by the strict-growth theorem. -/
def totalEquiv (K : Type*) [Field K] : (Sector → K) ≃ₗ[K] Total K where
  toFun v := (fun i => v (.inl i), fun j => v (.inr j.rev))
  invFun v := Sum.elim v.1 (fun j => v.2 j.rev)
  left_inv v := by
    funext s
    rcases s with i | i
    · rfl
    · simp only [Sum.elim_inr,Fin.rev_rev]
  right_inv v := by
    apply Prod.ext
    · rfl
    · funext j; simp only [Sum.elim_inr,Fin.rev_rev]
  map_add' v w := rfl
  map_smul' a v := rfl

theorem split_action (ι : ZMod p →+* K) (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (m : Fin 35) (v : Sector → K) :
    totalEquiv K ((matrix ι m).mulVec v) =
      (0,(splitBlock ι m).mulVec (totalEquiv K v).1) := by
  have hu (s : Sector) (i : Fin 33) : matrix ι m (.inl i) s = 0 := by
    by_contra hn
    have hz := (split_support hp hs s (.inl i) m).mp
      ((entry_ne_zero_iff ι m s (.inl i)).mp hn)
    cases s <;> exact hz
  have hl (i j : Fin 33) : matrix ι m (.inr j) (.inr i) = 0 := by
    by_contra hn
    exact (split_support hp hs (.inr i) (.inr j) m).mp
      ((entry_ne_zero_iff ι m (.inr i) (.inr j)).mp hn)
  apply Prod.ext
  · funext i
    change (∑ s, matrix ι m (.inl i) s * v s) = 0
    simp only [hu,zero_mul,Finset.sum_const_zero]
  · funext j
    change (∑ s, matrix ι m (.inr j.rev) s * v s) =
      ∑ i, matrix ι m (.inr j.rev) (.inl i) * v (.inl i)
    rw [Fintype.sum_sum_type]
    simp only [hl,zero_mul,Finset.sum_const_zero,add_zero]

theorem inert_action (ι : ZMod p →+* K) (hp : 6 < p) (hi : p ≡ 5 [MOD 6])
    (m : Fin 35) (v : Sector → K) :
    totalEquiv K ((matrix ι m).mulVec v) =
      ((inertBlock ι m).mulVec (totalEquiv K v).2,0) := by
  have hl (s : Sector) (j : Fin 33) : matrix ι m (.inr j) s = 0 := by
    by_contra hn
    have hz := (inert_support hp hi s (.inr j) m).mp
      ((entry_ne_zero_iff ι m s (.inr j)).mp hn)
    cases s <;> exact hz
  have hu (i j : Fin 33) : matrix ι m (.inl i) (.inl j) = 0 := by
    by_contra hn
    exact (inert_support hp hi (.inl j) (.inl i) m).mp
      ((entry_ne_zero_iff ι m (.inl j) (.inl i)).mp hn)
  apply Prod.ext
  · funext i
    change (∑ s, matrix ι m (.inl i) s * v s) =
      ∑ j, matrix ι m (.inl i) (.inr j.rev) * v (.inr j.rev)
    rw [Fintype.sum_sum_type]
    simp only [hu,zero_mul,Finset.sum_const_zero,zero_add]
    simpa only [Fin.revPerm_apply] using
      (Equiv.sum_comp Fin.revPerm
        (fun j : Fin 33 => matrix ι m (.inl i) (.inr j) * v (.inr j))).symm
  · funext j
    change (∑ s, matrix ι m (.inr j.rev) s * v s) = 0
    simp only [hl,zero_mul,Finset.sum_const_zero]

theorem split_stable (ι : ZMod p →+* K) (hp : 6 < p) (hs : p ≡ 1 [MOD 6])
    (W : Submodule K (Sector → K))
    (hW : ∀ m v, v ∈ W → (matrix ι m).mulVec v ∈ W)
    (m : Fin 35) (x : Total K) (hx : x ∈ W.map (totalEquiv K).toLinearMap) :
    (0,(splitBlock ι m).mulVec x.1) ∈ W.map (totalEquiv K).toLinearMap := by
  obtain ⟨v,hv,rfl⟩ := hx
  exact ⟨(matrix ι m).mulVec v,hW m v hv,split_action ι hp hs m v⟩

theorem inert_stable (ι : ZMod p →+* K) (hp : 6 < p) (hi : p ≡ 5 [MOD 6])
    (W : Submodule K (Sector → K))
    (hW : ∀ m v, v ∈ W → (matrix ι m).mulVec v ∈ W)
    (m : Fin 35) (x : Total K) (hx : x ∈ W.map (totalEquiv K).toLinearMap) :
    ((inertBlock ι m).mulVec x.2,0) ∈ W.map (totalEquiv K).toLinearMap := by
  obtain ⟨v,hv,rfl⟩ := hx
  exact ⟨(matrix ι m).mulVec v,hW m v hv,inert_action ι hp hi m v⟩

theorem split_growth (ι : ZMod p →+* K) (hp : 6 < p) (hs : p ≡ 1 [MOD 6]) :
    RankGrowth K (splitBlock ι) := by
  apply weighted_forward_growth
  intro m i j
  change matrix ι m (.inr j.rev) (.inl i) ≠ 0 ↔ _
  rw [entry_ne_zero_iff,exponentEdge_iff_complement]
  exact split_support hp hs (.inl i) (.inr j.rev) m

theorem inert_growth (ι : ZMod p →+* K) (hp : 6 < p) (hi : p ≡ 5 [MOD 6]) :
    RankGrowth K (inertBlock ι) := by
  apply weighted_reverse_growth
  intro m i j
  change matrix ι m (.inl i) (.inr j.rev) ≠ 0 ↔ _
  rw [entry_ne_zero_iff,exponentEdge_iff_complement]
  exact inert_support hp hi (.inr j.rev) (.inl i) m

/-- The same two-prime conclusion for the literal normalization used by
the regular residue frame and its actual connection matrices. -/
theorem opposite_prime_dichotomy {L : Type*} [Field L] [NeZero (6 : L)]
    {q : ℕ} [Fact q.Prime] (ι : ZMod p →+* K) (κ : ZMod q →+* L)
    (hp : 6 < p) (hs : p ≡ 1 [MOD 6]) (hq : 6 < q) (hi : q ≡ 5 [MOD 6])
    (W : Submodule K (Total K)) (W' : Submodule L (Total L))
    (hW : ∀ m x, x ∈ W → (0,(splitBlock ι m).mulVec x.1) ∈ W)
    (hW' : ∀ m x, x ∈ W' → ((inertBlock κ m).mulVec x.2,0) ∈ W')
    (hprofile : rankProfile K W = rankProfile L W') :
    (W = ⊥ ∧ W' = ⊥) ∨ (W = ⊤ ∧ W' = ⊤) :=
  nonsplit_dichotomy K (split_growth ι hp hs) (inert_growth κ hq hi)
    W W' hW hW' hprofile

end CycleQ2FermatNormalizedPrime
end

#print axioms CycleQ2FermatNormalizedPrime.split_growth
#print axioms CycleQ2FermatNormalizedPrime.inert_growth
#print axioms CycleQ2FermatNormalizedPrime.opposite_prime_dichotomy
