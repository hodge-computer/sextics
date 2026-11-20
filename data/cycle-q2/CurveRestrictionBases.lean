import Proposal.SegreTangentRelations

/-! # Restriction to the seed curves in graded quotient bases -/

set_option Elab.async false

/- Component: continuation_3/CurveRestrictionNormalForm.lean -/
section
/-! Integral normal forms for both actual curve restrictions.  The right curve
uses a scaled linear change of coordinates, so every formula is integral. -/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm
open scoped MonomialOrder

variable {R : Type*} [CommRing R]

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

abbrev CurvePoly (R : Type*) [CommRing R] := MvPolynomial (Fin 4) R
abbrev CurveExponent := Fin 4 →₀ ℕ

def exponent (v : Fin 4 → ℕ) : CurveExponent := Finsupp.equivFunOnFinite.symm v
@[simp] theorem exponent_apply (v : Fin 4 → ℕ) (i : Fin 4) : exponent v i = v i := rfl

def mon (a b c d : ℕ) : CurvePoly R := X 0 ^ a * X 1 ^ b * X 2 ^ c * X 3 ^ d

theorem mon_eq_monomial (a b c d : ℕ) :
    (mon a b c d : CurvePoly R) = monomial (exponent ![a,b,c,d]) 1 := by
  simp only [mon, X_pow_eq_monomial, monomial_mul, one_mul]
  apply congrArg (fun e : CurveExponent => monomial e (1 : R))
  ext i
  fin_cases i <;> simp [exponent, Finsupp.single_apply, Fin.ext_iff]

theorem monomial_eq_C_mul_mon (a b c d : ℕ) (r : R) :
    monomial (exponent ![a,b,c,d]) r = C r * mon a b c d := by
  rw [mon_eq_monomial, C_mul_monomial, mul_one]

theorem mon_homogeneous (a b c d : ℕ) :
    (mon a b c d : CurvePoly R).IsHomogeneous (a+b+c+d) := by
  rw [mon_eq_monomial]
  apply isHomogeneous_monomial
  norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ, add_assoc,
    Matrix.cons_val_succ, Fin.reduceSucc]

inductive Side | left | right deriving DecidableEq, Fintype

def xBound : Side → ℕ | .left => 2 | .right => 3
def zBound : Side → ℕ | .left => 3 | .right => 2

def curveWeight : Side → CurveExponent →+ ℕ
  | .left =>
    { toFun := fun d => 3*d 0+d 1+3*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }
  | .right =>
    { toFun := fun d => 3*d 0+d 1+4*d 2+d 3
      map_zero' := by simp
      map_add' := by intro a b; simp only [Finsupp.add_apply]; omega }

def curveOrder (s : Side) : MonomialOrder (Fin 4) :=
  weightedOrder MonomialOrder.lex (curveWeight s)

def quadric (s : Side) (r : R) : CurvePoly R :=
  match s with
  | .left => X 0 ^ 2 - C r * X 1 * X 3
  | .right => X 2 ^ 2 + X 0 ^ 2

def cubic (s : Side) (r ι : R) : CurvePoly R :=
  match s with
  | .left => X 2 ^ 3 + X 0*X 2*X 3 + X 1*X 2*X 3 + X 0*X 1^2 +
      C r*X 0*X 1*X 3 + C (1-ι)*X 3^3 - C ι*X 1^3
  | .right => X 0 ^ 3 - X 0^2*X 3 - X 0*X 1*X 3 + X 2*X 1*X 3 -
      X 0*X 1^2 - X 2*X 1^2 - C (2*(1-ι))*X 3^3 + C (2*ι)*X 1^3

def quadricLead : Side → CurveExponent
  | .left => Finsupp.single 0 2
  | .right => Finsupp.single 2 2

def cubicLead : Side → CurveExponent
  | .left => Finsupp.single 2 3
  | .right => Finsupp.single 0 3

def leftTailExponent (j : Fin 6) : CurveExponent :=
  ![exponent ![1,0,1,1], exponent ![0,1,1,1], exponent ![1,2,0,0],
    exponent ![1,1,0,1], exponent ![0,0,0,3], exponent ![0,3,0,0]] j

def leftTailCoefficient (r ι : R) (j : Fin 6) : R := ![1,1,1,r,1-ι,-ι] j

def rightTailExponent (j : Fin 7) : CurveExponent :=
  ![exponent ![2,0,0,1], exponent ![1,1,0,1], exponent ![0,1,1,1],
    exponent ![1,2,0,0], exponent ![0,2,1,0], exponent ![0,0,0,3],
    exponent ![0,3,0,0]] j

def rightTailCoefficient (ι : R) (j : Fin 7) : R :=
  ![-1,-1,1,-1,-1,-(2*(1-ι)),2*ι] j

theorem left_quadric_shape (r : R) :
    quadric .left r = monomial (quadricLead .left) 1 +
      ∑ _j : Fin 1, monomial (exponent ![0,1,0,1]) (-r) := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon] <;> ring

theorem right_quadric_shape (r : R) :
    quadric .right r = monomial (quadricLead .right) 1 +
      ∑ _j : Fin 1, monomial (exponent ![2,0,0,0]) 1 := by
  simp only [Fin.sum_univ_one, quadricLead]
  rw [← X_pow_eq_monomial, monomial_eq_C_mul_mon]
  simp [quadric, mon]

theorem left_cubic_shape (r ι : R) :
    cubic .left r ι = monomial (cubicLead .left) 1 +
      ∑ j : Fin 6, monomial (leftTailExponent j) (leftTailCoefficient r ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, leftTailExponent, leftTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem right_cubic_shape (r ι : R) :
    cubic .right r ι = monomial (cubicLead .right) 1 +
      ∑ j : Fin 7, monomial (rightTailExponent j) (rightTailCoefficient ι j) := by
  simp only [cubicLead, ← X_pow_eq_monomial]
  simp only [Fin.sum_univ_succ, rightTailExponent, rightTailCoefficient,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceSucc,
    Matrix.head_cons, Matrix.tail_cons, monomial_eq_C_mul_mon]
  norm_num [cubic, mon, Matrix.cons_val_succ, Fin.reduceSucc]
  ring

theorem quadric_leading [Nontrivial R] (s : Side) (r : R) :
    (curveOrder s).degree (quadric s r) = quadricLead s ∧
      (curveOrder s).Monic (quadric s r) := by
  cases s
  · rw [left_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_quadric_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, quadricLead, Finsupp.single_apply, Fin.ext_iff]

theorem cubic_leading [Nontrivial R] (s : Side) (r ι : R) :
    (curveOrder s).degree (cubic s r ι) = cubicLead s ∧
      (curveOrder s).Monic (cubic s r ι) := by
  cases s
  · rw [left_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, leftTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]
  · rw [right_cubic_shape]
    apply degree_monic_add_sum
    · apply weightedOrder_lt_of_weight_lt
      norm_num [curveWeight, cubicLead, Finsupp.single_apply, Fin.ext_iff]
    · intro j
      apply weightedOrder_lt_of_weight_lt
      fin_cases j <;> norm_num [curveWeight, rightTailExponent, cubicLead,
        Matrix.cons_val_succ, Fin.reduceSucc, Finsupp.single_apply, Fin.ext_iff]

theorem leading_coprime [Nontrivial R] (s : Side) (r ι : R) :
    ∀ j, (curveOrder s).degree (quadric s r) j = 0 ∨
      (curveOrder s).degree (cubic s r ι) j = 0 := by
  rw [(quadric_leading s r).1, (cubic_leading s r ι).1]
  intro j
  cases s <;> fin_cases j <;> simp [quadricLead, cubicLead]

def Standard (s : Side) (p : CurvePoly R) : Prop :=
  ∀ e ∈ p.support, e 0 < xBound s ∧ e 2 < zBound s

theorem standard_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s p ↔ Reduced (curveOrder s) (quadric s r) (cubic s r ι) p := by
  simp only [Standard, Reduced, (quadric_leading s r).1, (cubic_leading s r ι).1]
  apply forall_congr'
  intro e
  apply forall_congr'
  intro he
  cases s <;> simp only [quadricLead, cubicLead, Finsupp.single_le_iff, xBound, zBound]
  · omega
  · omega

theorem quadric_homogeneous (s : Side) (r : R) :
    (quadric s r).IsHomogeneous 2 := by
  cases s
  · rw [left_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_quadric_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [quadricLead])
    · apply (homogeneousSubmodule (Fin 4) R 2).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      norm_num [Finsupp.degree_eq_sum, Fin.sum_univ_succ,
        Matrix.cons_val_succ, Fin.reduceSucc]

theorem cubic_homogeneous (s : Side) (r ι : R) :
    (cubic s r ι).IsHomogeneous 3 := by
  cases s
  · rw [left_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [leftTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]
  · rw [right_cubic_shape]
    apply IsHomogeneous.add
    · exact isHomogeneous_monomial _ (by simp [cubicLead])
    · apply (homogeneousSubmodule (Fin 4) R 3).sum_mem
      intro j hj
      apply isHomogeneous_monomial
      fin_cases j <;> norm_num [rightTailExponent, Finsupp.degree_eq_sum,
        Fin.sum_univ_succ, Matrix.cons_val_succ, Fin.reduceSucc]

def curveIdeal (s : Side) (r ι : R) : Ideal (CurvePoly R) :=
  equationsIdeal (quadric s r) (cubic s r ι)

abbrev CurveRing (s : Side) (r ι : R) := CurvePoly R ⧸ curveIdeal s r ι

theorem existsUnique_normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    ∃! q, Standard s q ∧ ∃ a b, p = a * quadric s r + b * cubic s r ι + q := by
  simpa only [standard_iff s r ι] using
    existsUnique_reduced_representative (curveOrder s) (quadric s r) (cubic s r ι) p
      (quadric_leading s r).2 (cubic_leading s r ι).2 (leading_coprime s r ι)

def normal [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) : CurvePoly R :=
  (existsUnique_normal s r ι p).choose

theorem normal_spec [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    Standard s (normal s r ι p) ∧
      ∃ a b, p = a * quadric s r + b * cubic s r ι + normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.1

theorem normal_unique [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R)
    (hq : Standard s q) (hrep : ∃ a b, p = a * quadric s r + b * cubic s r ι + q) :
    q = normal s r ι p :=
  (existsUnique_normal s r ι p).choose_spec.2 q ⟨hq, hrep⟩

theorem normal_homogeneous [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} {d : ℕ} (hp : p.IsHomogeneous d) :
    (normal s r ι p).IsHomogeneous d := by
  obtain ⟨hr, a, b, heq⟩ := normal_spec s r ι p
  exact reduced_isHomogeneous (curveOrder s) (quadric_leading s r).2
    (cubic_leading s r ι).2 (leading_coprime s r ι)
    (quadric_homogeneous s r) (cubic_homogeneous s r ι) hp
    ((standard_iff s r ι _).mp hr) heq

theorem normal_eq_self [Nontrivial R] (s : Side) (r ι : R)
    {p : CurvePoly R} (hp : Standard s p) : normal s r ι p = p := by
  exact (normal_unique s r ι p p hp ⟨0,0,by simp⟩).symm

@[simp] theorem map_quadric {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r : R) :
    MvPolynomial.map φ (quadric s r) = quadric s (φ r) := by
  cases s <;> simp [quadric]

@[simp] theorem map_cubic {S : Type*} [CommRing S] (φ : R →+* S) (s : Side) (r ι : R) :
    MvPolynomial.map φ (cubic s r ι) = cubic s (φ r) (φ ι) := by
  cases s <;> simp [cubic, map_ofNat]

theorem standard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {s : Side} {p : CurvePoly R} (hp : Standard s p) :
    Standard s (MvPolynomial.map φ p) := by
  intro e he
  exact hp e (MvPolynomial.support_map_subset φ p he)

theorem normal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : CurvePoly R) :
    MvPolynomial.map φ (normal s r ι p) =
      normal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  obtain ⟨hr,a,b,hp⟩ := normal_spec s r ι p
  apply normal_unique
  · exact standard_map φ hr
  · refine ⟨MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
    simpa only [map_add, map_mul, map_quadric, map_cubic] using congrArg (MvPolynomial.map φ) hp

/-- The left restriction eliminates w.  The right restriction is the integral
scaled coordinate change (x₀,x₁,x₂,x₃,w)=(u+v,2y₁,u-v,2y₃,4ry₁y₃). -/
def restrictionValues (s : Side) (r : R) : Fin 5 → CurvePoly R :=
  match s with
  | .left => ![X 0, X 1, X 2, X 3, -(X 2^2)]
  | .right => ![X 0+X 2, 2*X 1, X 0-X 2, 2*X 3, C (4*r)*X 1*X 3]

def substitution (s : Side) (r : R) : MvPolynomial (Fin 5) R →ₐ[R] CurvePoly R :=
  aeval (restrictionValues s r)

@[simp] theorem substitution_X (s : Side) (r : R) (i : Fin 5) :
    substitution s r (X i) = restrictionValues s r i := by
  simp [substitution]

@[simp] theorem substitution_C (s : Side) (r c : R) :
    substitution s r (C c) = C c := by
  simp [substitution]

theorem left_h_identity (r ι : R) :
    substitution .left r (CycleQ2IncidenceEquations.smoothH ι) =
      cubic .left r ι + X 0 * quadric .left r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_h_identity (r ι : R) :
    substitution .right r (CycleQ2IncidenceEquations.smoothH ι) =
      -4 * cubic .right r ι + (6*X 0-2*X 3) * quadric .right r := by
  simp only [CycleQ2IncidenceEquations.smoothH, CycleQ2IncidenceEquations.smoothB,
    CycleQ2IncidenceEquations.smoothA, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, cubic, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem left_G_identity (r : R) :
    substitution .left r (CycleQ2IncidenceEquations.seedG r) =
      quadric .left r * (X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem right_G_identity (r : R) :
    substitution .right r (CycleQ2IncidenceEquations.seedG r) =
      2 * quadric .right r * (X 0^4+14*X 0^2*X 2^2+X 2^4) := by
  simp only [CycleQ2IncidenceEquations.seedG, CycleQ2SegreSeed.seedG, CycleQ2SegreSeed.linkageG, map_sub, map_add, map_mul, map_pow,
    substitution_X, substitution_C]
  norm_num [restrictionValues, quadric, Matrix.cons_val_succ, Fin.reduceSucc, map_ofNat]
  ring

theorem substitution_h_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothH ι) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0, 1, by ring⟩
  · rw [right_h_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨6*X 0-2*X 3, -4, by ring⟩

theorem substitution_G_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.seedG r) ∈ curveIdeal s r ι := by
  cases s
  · rw [left_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨X 0^4+C r*X 0^2*X 1*X 3+C (r^2)*X 1^2*X 3^2, 0, by ring⟩
  · rw [right_G_identity]
    apply Ideal.mem_span_pair.mpr
    exact ⟨2*(X 0^4+14*X 0^2*X 2^2+X 2^4), 0, by ring⟩

theorem substitution_F_mem (s : Side) (r ι : R) :
    substitution s r (CycleQ2IncidenceEquations.smoothF r ι) ∈ curveIdeal s r ι := by
  rw [CycleQ2IncidenceEquations.smoothF, map_add, map_mul]
  exact Ideal.add_mem _ (substitution_G_mem s r ι)
    (Ideal.mul_mem_right _ _ (substitution_h_mem s r ι))

theorem standard_add {s : Side} {p q : CurvePoly R}
    (hp : Standard s p) (hq : Standard s q) : Standard s (p+q) := by
  intro e he
  rcases Finset.mem_union.mp (support_add he) with h | h
  · exact hp e h
  · exact hq e h

theorem standard_C_mul {s : Side} {p : CurvePoly R} (hp : Standard s p) (c : R) :
    Standard s (C c*p) := by
  intro e he
  apply hp e
  apply mem_support_iff.mpr
  intro hz
  exact (mem_support_iff.mp he) (by rw [coeff_C_mul, hz, mul_zero])

theorem normal_add [Nontrivial R] (s : Side) (r ι : R) (p q : CurvePoly R) :
    normal s r ι (p+q) = normal s r ι p + normal s r ι q := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  obtain ⟨hq,c,d,hcd⟩ := normal_spec s r ι q
  symm
  apply normal_unique
  · exact standard_add hp hq
  · refine ⟨a+c,b+d,?_⟩
    linear_combination hab+hcd

theorem normal_C_mul [Nontrivial R] (s : Side) (r ι c : R) (p : CurvePoly R) :
    normal s r ι (C c*p) = C c*normal s r ι p := by
  obtain ⟨hp,a,b,hab⟩ := normal_spec s r ι p
  symm
  apply normal_unique
  · exact standard_C_mul hp c
  · refine ⟨C c*a,C c*b,?_⟩
    linear_combination C c*hab

def normalLinear [Nontrivial R] (s : Side) (r ι : R) : CurvePoly R →ₗ[R] CurvePoly R where
  toFun := normal s r ι
  map_add' := normal_add s r ι
  map_smul' := fun c p => by
    simpa only [smul_eq_C_mul, RingHom.id_apply] using normal_C_mul s r ι c p

theorem normal_sub_mem [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    p-normal s r ι p ∈ curveIdeal s r ι := by
  obtain ⟨_,a,b,hp⟩ := normal_spec s r ι p
  apply Ideal.mem_span_pair.mpr
  exact ⟨a,b,by linear_combination -hp⟩

theorem normal_eq_zero_iff [Nontrivial R] (s : Side) (r ι : R) (p : CurvePoly R) :
    normal s r ι p = 0 ↔ p ∈ curveIdeal s r ι := by
  constructor
  · intro hp
    simpa only [hp, sub_zero] using normal_sub_mem s r ι p
  · intro hp
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    symm
    exact normal_unique s r ι p 0 (by simp [Standard])
      ⟨a,b,by simpa only [add_zero] using hab.symm⟩

@[simp] theorem map_restrictionValues {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (j : Fin 5) :
    MvPolynomial.map φ (restrictionValues s r j) = restrictionValues s (φ r) j := by
  cases s <;> fin_cases j <;>
    norm_num [restrictionValues, map_ofNat, Matrix.cons_val_succ, Fin.reduceSucc]

theorem substitution_map {S : Type*} [CommRing S]
    (φ : R →+* S) (s : Side) (r : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (substitution s r p) =
      substitution s (φ r) (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, hp, map_X, substitution_X, map_restrictionValues]

/-- A linear map representing the genuine restriction, with the canonical
curve representative chosen by the proved normal-form theorem. -/
def restrictionNormal [Nontrivial R] (s : Side) (r ι : R) :
    MvPolynomial (Fin 5) R →ₗ[R] CurvePoly R :=
  (normalLinear s r ι).comp (substitution s r).toLinearMap

@[simp] theorem restrictionNormal_apply [Nontrivial R]
    (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    restrictionNormal s r ι p = normal s r ι (substitution s r p) := rfl

theorem restrictionNormal_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (restrictionNormal s r ι p) =
      restrictionNormal s (φ r) (φ ι) (MvPolynomial.map φ p) := by
  simp only [restrictionNormal_apply, normal_map, substitution_map]

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.quadric_leading
#print axioms CycleQ2CurveRestriction.cubic_leading
#print axioms CycleQ2CurveRestriction.normal_homogeneous
#print axioms CycleQ2CurveRestriction.substitution_F_mem
#print axioms CycleQ2CurveRestriction.restrictionNormal_map
end
end

/- Component: continuation_3/CurveRestrictionIndices.lean -/
section
/-! Exhaustive finite monomial indices for the two curve restrictions. -/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceGradedBasis

abbrev TargetRawIndex (s : Side) (d : ℕ) :=
  Fin (xBound s) × Fin (zBound s) × Fin (d+1)

def TargetAllowed (s : Side) (d : ℕ) (q : TargetRawIndex s d) : Prop :=
  q.1.val + q.2.1.val + q.2.2.val ≤ d

instance (s : Side) (d : ℕ) (q : TargetRawIndex s d) : Decidable (TargetAllowed s d q) :=
  inferInstanceAs (Decidable (_ ≤ _))

abbrev TargetIndex (s : Side) (d : ℕ) := {q : TargetRawIndex s d // TargetAllowed s d q}

def targetCoordinates {s : Side} {d : ℕ} (q : TargetIndex s d) : Fin 4 → ℕ :=
  ![q.val.1.val, q.val.2.2.val, q.val.2.1.val,
    d-(q.val.1.val+q.val.2.1.val+q.val.2.2.val)]

abbrev TargetExponents (s : Side) (d : ℕ) :=
  {e : Fin 4 → ℕ // e 0 < xBound s ∧ e 2 < zBound s ∧ e 0+e 1+e 2+e 3=d}

def targetExponentEquiv (s : Side) (d : ℕ) : TargetIndex s d ≃ TargetExponents s d where
  toFun q := ⟨targetCoordinates q, by
    have h := q.property
    change q.val.1.val<xBound s ∧ q.val.2.1.val<zBound s ∧
      q.val.1.val+q.val.2.2.val+q.val.2.1.val+
        (d-(q.val.1.val+q.val.2.1.val+q.val.2.2.val))=d
    exact ⟨q.val.1.isLt,q.val.2.1.isLt,by dsimp [TargetAllowed] at h; omega⟩⟩
  invFun e := ⟨(⟨e.val 0,e.property.1⟩,⟨e.val 2,e.property.2.1⟩,
    ⟨e.val 1,by have := e.property.2.2; omega⟩), by
      have := e.property.2.2
      change e.val 0+e.val 2+e.val 1≤d
      omega⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d-(e.val 0+e.val 2+e.val 1)=e.val 3
      have := e.property.2.2
      omega

def targetExponent {s : Side} {d : ℕ} (q : TargetIndex s d) : CurveExponent :=
  exponent (targetCoordinates q)

@[simp] theorem targetExponent_apply {s : Side} {d : ℕ} (q : TargetIndex s d) (i : Fin 4) :
    targetExponent q i = targetCoordinates q i := rfl

theorem targetExponent_injective {s : Side} {d : ℕ} :
    Function.Injective (targetExponent (s:=s) (d:=d)) := by
  intro q q' h
  apply (targetExponentEquiv s d).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : CurveExponent => e i) h

theorem left_target_count : Fintype.card (TargetIndex .left 10) = 57 := by decide

theorem right_target_count : Fintype.card (TargetIndex .right 8) = 45 := by decide

abbrev SourceRawIndex (d : ℕ) := (Fin 3 × Fin 3) × (Fin (d+1) × Fin (d+1))

def SourceAllowed (d ch : ℕ) (q : SourceRawIndex d) : Prop :=
  q.1.1.val+q.2.1.val+q.2.2.val+2*q.1.2.val≤d ∧
    (2*q.1.1.val+2*q.2.1.val+q.2.2.val)%3=ch

instance (d ch : ℕ) (q : SourceRawIndex d) : Decidable (SourceAllowed d ch q) :=
  inferInstanceAs (Decidable (_ ∧ _))

abbrev SourceIndex (d ch : ℕ) := {q : SourceRawIndex d // SourceAllowed d ch q}

def sourceCoordinates {d ch : ℕ} (q : SourceIndex d ch) : Fin 5 → ℕ :=
  ![q.val.1.1.val,q.val.2.1.val,q.val.2.2.val,
    d-(q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+2*q.val.1.2.val),q.val.1.2.val]

abbrev SourceExponents (d ch : ℕ) :=
  {e : Fin 5 → ℕ // e 0<3 ∧ e 4<3 ∧
    e 0+e 1+e 2+e 3+2*e 4=d ∧ (2*e 0+2*e 1+e 2)%3=ch}

def sourceExponentEquiv (d ch : ℕ) : SourceIndex d ch ≃ SourceExponents d ch where
  toFun q := ⟨sourceCoordinates q, by
    have hw := q.property.1
    have hc := q.property.2
    change q.val.1.1.val<3 ∧ q.val.1.2.val<3 ∧
      q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+
        (d-(q.val.1.1.val+q.val.2.1.val+q.val.2.2.val+2*q.val.1.2.val))+
        2*q.val.1.2.val=d ∧ (2*q.val.1.1.val+2*q.val.2.1.val+q.val.2.2.val)%3=ch
    exact ⟨q.val.1.1.isLt,q.val.1.2.isLt,by omega,hc⟩⟩
  invFun e := ⟨((⟨e.val 0,e.property.1⟩,⟨e.val 4,e.property.2.1⟩),
    (⟨e.val 1,by have := e.property.2.2.1; omega⟩,
     ⟨e.val 2,by have := e.property.2.2.1; omega⟩)), by
    constructor
    · have := e.property.2.2.1
      change e.val 0+e.val 1+e.val 2+2*e.val 4≤d
      omega
    · exact e.property.2.2.2⟩
  left_inv q := by apply Subtype.ext; rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d-(e.val 0+e.val 1+e.val 2+2*e.val 4)=e.val 3
      have := e.property.2.2.1
      omega
    · rfl

def sourceExponent {d ch : ℕ} (q : SourceIndex d ch) : FullExponent :=
  Finsupp.equivFunOnFinite.symm (sourceCoordinates q)

@[simp] theorem sourceExponent_apply {d ch : ℕ} (q : SourceIndex d ch) (i : Fin 5) :
    sourceExponent q i = sourceCoordinates q i := rfl

theorem sourceExponent_injective {d ch : ℕ} :
    Function.Injective (sourceExponent (d:=d) (ch:=ch)) := by
  intro q q' h
  apply (sourceExponentEquiv d ch).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : FullExponent => e i) h

theorem left_source_count : Fintype.card (SourceIndex 10 0) = 113 := by decide

theorem right_source_count : Fintype.card (SourceIndex 8 1) = 68 := by decide

theorem targetExponent_degree {s : Side} {d : ℕ} (q : TargetIndex s d) :
    (targetExponent q).degree=d := by
  have h := ((targetExponentEquiv s d) q).property.2.2
  change targetCoordinates q 0+targetCoordinates q 1+targetCoordinates q 2+targetCoordinates q 3=d at h
  simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using h

theorem sourceExponent_grade {d ch : ℕ} (q : SourceIndex d ch) :
    Finsupp.weight fullGrading (sourceExponent q)=(d,(ch : ZMod 3)) := by
  have h := ((sourceExponentEquiv d ch) q).property
  rw [fullGrading_weight]
  apply Prod.ext
  · exact h.2.2.1
  · change ((2*sourceCoordinates q 0+2*sourceCoordinates q 1+sourceCoordinates q 2 : ℕ) : ZMod 3)=_
    have hc : (2*sourceCoordinates q 0+2*sourceCoordinates q 1+sourceCoordinates q 2)%3=ch := h.2.2.2
    simpa using congrArg (fun n : ℕ => (n : ZMod 3)) hc

theorem sourceMonomial_standard {R : Type*} [CommRing R] {d ch : ℕ}
    (q : SourceIndex d ch) (c : R) : FullStandard (monomial (sourceExponent q) c) := by
  intro e he
  obtain rfl := Finset.mem_singleton.mp (support_monomial_subset he)
  have h := ((sourceExponentEquiv d ch) q).property
  exact ⟨h.1,h.2.1⟩

theorem sourceMonomial_homogeneous {R : Type*} [CommRing R] {d ch : ℕ}
    (q : SourceIndex d ch) (c : R) :
    (monomial (sourceExponent q) c).IsWeightedHomogeneous fullGrading (d,(ch : ZMod 3)) :=
  isWeightedHomogeneous_monomial _ _ _ (sourceExponent_grade q)

section CurveBasis
variable {R : Type*} [CommRing R] [Nontrivial R]

theorem curve_reduced_exponent_iff (s : Side) (r ι : R) (e : CurveExponent) :
    e ∈ reducedExponents (curveOrder s) (quadric s r) (cubic s r ι) ↔
      e 0<xBound s ∧ e 2<zBound s := by
  change (¬ (curveOrder s).degree (quadric s r)≤e) ∧
    (¬ (curveOrder s).degree (cubic s r ι)≤e) ↔ _
  rw [(quadric_leading s r).1,(cubic_leading s r ι).1]
  cases s <;> simp only [quadricLead,cubicLead,Finsupp.single_le_iff,xBound,zBound] <;> omega

def curveGradedExponentEquiv (s : Side) (r ι : R) (d : ℕ) :
    gradedExponents (1 : Fin 4 → ℕ) (curveOrder s) (quadric s r) (cubic s r ι) d ≃
      TargetExponents s d where
  toFun e := ⟨e.val, by
    have hb := (curve_reduced_exponent_iff s r ι e.val).mp e.property.1
    refine ⟨hb.1,hb.2,?_⟩
    have hd := e.property.2
    simp only [Pi.one_def] at hd
    rw [← Finsupp.degree_eq_weight_one] at hd
    simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using hd⟩
  invFun e := ⟨exponent e.val, by
    constructor
    · apply (curve_reduced_exponent_iff s r ι _).mpr
      exact ⟨e.property.1,e.property.2.1⟩
    · simp only [Pi.one_def]
      rw [← Finsupp.degree_eq_weight_one]
      simpa [Finsupp.degree_eq_sum,Fin.sum_univ_succ,add_assoc] using e.property.2.2⟩
  left_inv e := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by apply Subtype.ext; rfl

abbrev CurvePiece (s : Side) (r ι : R) (d : ℕ) :=
  quotientPiece (1 : Fin 4 → ℕ) (quadric s r) (cubic s r ι) d

def curvePieceBasis (s : Side) (r ι : R) (d : ℕ) :
    Module.Basis (TargetIndex s d) R (CurvePiece s r ι d) :=
  (CycleQ2IncidenceGradedBasis.basis (1 : Fin 4 → ℕ) (curveOrder s)
    (quadric s r) (cubic s r ι) d (quadric_leading s r).2
    (cubic_leading s r ι).2 (leading_coprime s r ι)
    (quadric_homogeneous s r) (cubic_homogeneous s r ι)).reindex
      ((curveGradedExponentEquiv s r ι d).trans (targetExponentEquiv s d).symm)

theorem curvePieceBasis_apply (s : Side) (r ι : R) (d : ℕ) (q : TargetIndex s d) :
    (curvePieceBasis s r ι d q).val =
      Ideal.Quotient.mk (curveIdeal s r ι) (monomial (targetExponent q) 1) := by
  rw [curvePieceBasis,Module.Basis.reindex_apply,CycleQ2IncidenceGradedBasis.basis_apply]
  rfl

theorem left_curvePiece_rank (r ι : R) : Module.finrank R (CurvePiece .left r ι 10) = 57 := by
  rw [Module.finrank_eq_card_basis (curvePieceBasis .left r ι 10),left_target_count]

theorem right_curvePiece_rank (r ι : R) : Module.finrank R (CurvePiece .right r ι 8) = 45 := by
  rw [Module.finrank_eq_card_basis (curvePieceBasis .right r ι 8),right_target_count]

end CurveBasis
end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_source_count
#print axioms CycleQ2CurveRestriction.right_source_count
#print axioms CycleQ2CurveRestriction.left_curvePiece_rank
#print axioms CycleQ2CurveRestriction.right_curvePiece_rank
end
end

/- Component: continuation_3/CurveRestrictionSourceBasis.lean -/
section
/-! Bases of the actual source pieces for both curve restrictions, including
character one. The source ring is the existing smooth seed quotient. -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceGradedBasis
  CycleQ2IncidenceEquations CycleQ2SegreTangentLocal

variable {R : Type*} [CommRing R]

theorem seed_h_normalized (ι : R) :
    smoothH ι=normalizedFullCubic (fun e => seedCubicCoefficients ι e.val) := by
  rw [←seedCubicCoefficients_polynomial,fullInvariantPolynomial_cubic]
  change monomial (Finsupp.single 0 3) (seedCubicCoefficients ι fullCubicLeadingIndex)+_= _
  simp only [seedCubicCoefficients,fullCubicLeadingIndex_exponent,smoothH_leading_coefficient]
  rfl

theorem seed_F_normalized (r ι : R) :
    smoothF r ι=normalizedFullSextic (fun e => seedSexticCoefficients r ι e.val) := by
  rw [←seedSexticCoefficients_polynomial,fullInvariantPolynomial_sextic]
  change monomial (Finsupp.single 4 3) (seedSexticCoefficients r ι fullSexticLeadingIndex)+_= _
  simp only [seedSexticCoefficients,fullSexticLeadingIndex_exponent,smoothF_leading_coefficient]
  rfl

theorem seed_h_leading [Nontrivial R] (ι : R) :
    fullAuxiliaryOrder.degree (smoothH ι)=Finsupp.single 0 3 ∧
      fullAuxiliaryOrder.Monic (smoothH ι) := by
  rw [seed_h_normalized]
  exact normalizedFullCubic_leading_data _

theorem seed_F_leading [Nontrivial R] (r ι : R) :
    fullAuxiliaryOrder.degree (smoothF r ι)=Finsupp.single 4 3 ∧
      fullAuxiliaryOrder.Monic (smoothF r ι) := by
  rw [seed_F_normalized]
  exact normalizedFullSextic_leading_data _

theorem seed_leading_coprime [Nontrivial R] (r ι : R) :
    ∀ j, fullAuxiliaryOrder.degree (smoothH ι) j=0 ∨
      fullAuxiliaryOrder.degree (smoothF r ι) j=0 := by
  rw [(seed_h_leading ι).1,(seed_F_leading r ι).1]
  intro j
  fin_cases j <;> simp

theorem seed_reduced_exponent_iff [Nontrivial R] (r ι : R) (e : FullExponent) :
    e ∈ reducedExponents fullAuxiliaryOrder (smoothH ι) (smoothF r ι) ↔
      e 0<3 ∧ e 4<3 := by
  change (¬ fullAuxiliaryOrder.degree (smoothH ι)≤e) ∧
    (¬ fullAuxiliaryOrder.degree (smoothF r ι)≤e) ↔ _
  rw [(seed_h_leading ι).1,(seed_F_leading r ι).1,
    Finsupp.single_le_iff,Finsupp.single_le_iff]
  omega

def seedGradedExponentEquiv [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3) :
    gradedExponents fullGrading fullAuxiliaryOrder (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3)) ≃
      SourceExponents d ch where
  toFun e := ⟨e.val,by
    have hb := (seed_reduced_exponent_iff r ι e.val).mp e.property.1
    have hg := e.property.2
    rw [fullGrading_weight] at hg
    have hd := congrArg Prod.fst hg
    have hc := congrArg Prod.snd hg
    refine ⟨hb.1,hb.2,hd,?_⟩
    change ((2*e.val 0+2*e.val 1+e.val 2:ℕ):ZMod 3)=(ch:ZMod 3) at hc
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp hc
    simpa only [Nat.mod_eq_of_lt hch] using hm⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm e.val,by
    constructor
    · apply (seed_reduced_exponent_iff r ι _).mpr
      exact ⟨e.property.1,e.property.2.1⟩
    · rw [fullGrading_weight]
      apply Prod.ext
      · exact e.property.2.2.1
      · have hc := congrArg (fun n : ℕ => (n:ZMod 3)) e.property.2.2.2
        simpa using hc⟩
  left_inv e := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by apply Subtype.ext; rfl

abbrev SeedPiece (r ι : R) (d ch : ℕ) :=
  quotientPiece fullGrading (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3))

def seedPieceBasis [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3) :
    Module.Basis (SourceIndex d ch) R (SeedPiece r ι d ch) :=
  (CycleQ2IncidenceGradedBasis.basis fullGrading fullAuxiliaryOrder
    (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3)) (seed_h_leading ι).2
    (seed_F_leading r ι).2 (seed_leading_coprime r ι)
    (smoothH_homogeneous ι) (smoothF_homogeneous r ι)).reindex
      ((seedGradedExponentEquiv r ι d ch hch).trans (sourceExponentEquiv d ch).symm)

theorem seedPieceBasis_apply [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3)
    (q : SourceIndex d ch) :
    (seedPieceBasis r ι d ch hch q).val=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
        (monomial (sourceExponent q) 1) := by
  rw [seedPieceBasis,Module.Basis.reindex_apply,CycleQ2IncidenceGradedBasis.basis_apply]
  rfl

theorem left_seedPiece_rank [Nontrivial R] (r ι : R) :
    Module.finrank R (SeedPiece r ι 10 0)=113 := by
  rw [Module.finrank_eq_card_basis (seedPieceBasis r ι 10 0 (by decide)),left_source_count]

theorem right_seedPiece_rank [Nontrivial R] (r ι : R) :
    Module.finrank R (SeedPiece r ι 8 1)=68 := by
  rw [Module.finrank_eq_card_basis (seedPieceBasis r ι 8 1 (by decide)),right_source_count]

/-- The actual quotient algebra restriction. Both seed generators map into the
explicit curve ideal, as proved by the integral substitution identities. -/
def seedRestriction (s : Side) (r ι : R) : SeedRing r ι →ₐ[R] CurveRing s r ι :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (curveIdeal s r ι)).comp (substitution s r)) (by
    intro p hp
    change Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    rw [←hab,map_add,map_mul,map_mul]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (substitution_h_mem s r ι))
      (Ideal.mul_mem_left _ _ (substitution_F_mem s r ι)))

@[simp] theorem seedRestriction_mk (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    seedRestriction s r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p) := rfl

def ordinaryWeight : Fin 5 → ℕ := ![1,1,1,1,2]

theorem restrictionValues_homogeneous (s : Side) (r : R) (j : Fin 5) :
    (restrictionValues s r j).IsHomogeneous (ordinaryWeight j) := by
  cases s <;> fin_cases j
  · exact isHomogeneous_X R 0
  · exact isHomogeneous_X R 1
  · exact isHomogeneous_X R 2
  · exact isHomogeneous_X R 3
  · exact (isHomogeneous_X_pow (R:=R) (2 : Fin 4) 2).neg
  · exact (isHomogeneous_X R 0).add (isHomogeneous_X R 2)
  · change (2*X 1 : CurvePoly R).IsHomogeneous 1
    simpa only [map_ofNat] using (isHomogeneous_X R (1 : Fin 4)).C_mul (2 : R)
  · exact (isHomogeneous_X R 0).sub (isHomogeneous_X R 2)
  · change (2*X 3 : CurvePoly R).IsHomogeneous 1
    simpa only [map_ofNat] using (isHomogeneous_X R (3 : Fin 4)).C_mul (2 : R)
  · change (C (4*r)*X 1*X 3 : CurvePoly R).IsHomogeneous 2
    simpa only [mul_assoc] using
      ((isHomogeneous_X R (1 : Fin 4)).mul (isHomogeneous_X R (3 : Fin 4))).C_mul (4*r)

theorem substitution_monomial_homogeneous (s : Side) (r : R) (e : FullExponent) (c : R) :
    (substitution s r (monomial e c)).IsHomogeneous (fullDegree e) := by
  classical
  have he : monomial e c=C c*∏ i : Fin 5, X i^e i := by
    rw [monomial_eq,Finsupp.prod_fintype]
    intro i
    simp
  rw [he,map_mul,map_prod,substitution_C]
  apply IsHomogeneous.C_mul
  simp only [map_pow,substitution_X]
  have hd : (∑ i : Fin 5, ordinaryWeight i*e i)=fullDegree e := by
    norm_num [ordinaryWeight,fullDegree,Fin.sum_univ_succ,Matrix.cons_val_succ,Fin.reduceSucc]
    change e 0+(e 1+(e 2+(e 3+2*e 4)))=e 0+e 1+e 2+e 3+2*e 4
    omega
  rw [←hd]
  exact IsHomogeneous.prod _ _ _ (fun i _ => (restrictionValues_homogeneous s r i).pow (e i))

theorem substitution_homogeneous (s : Side) (r : R) {p : MvPolynomial (Fin 5) R}
    {d : ℕ} {ch : ZMod 3} (hp : p.IsWeightedHomogeneous fullGrading (d,ch)) :
    (substitution s r p).IsHomogeneous d := by
  classical
  rw [p.as_sum,map_sum]
  apply (homogeneousSubmodule (Fin 4) R d).sum_mem
  intro e he
  have hg := hp (mem_support_iff.mp he)
  rw [fullGrading_weight] at hg
  have hd := congrArg Prod.fst hg
  change fullDegree e=d at hd
  change (substitution s r (monomial e (p.coeff e))).IsHomogeneous d
  simpa only [hd] using substitution_monomial_homogeneous s r e (p.coeff e)

/-- Restriction on the actual homogeneous quotient pieces. -/
def seedRestrictionPiece (s : Side) (r ι : R) (d ch : ℕ) :
    SeedPiece r ι d ch →ₗ[R] CurvePiece s r ι d :=
  (((seedRestriction s r ι).toLinearMap.comp (SeedPiece r ι d ch).subtype).codRestrict
    (CurvePiece s r ι d) (by
      intro q
      obtain ⟨p,hp,hpq⟩ := Submodule.mem_map.mp q.property
      apply Submodule.mem_map.mpr
      refine ⟨substitution s r p,substitution_homogeneous s r hp,?_⟩
      change Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p)=seedRestriction s r ι q.val
      rw [←hpq]
      rfl))

theorem seedRestrictionPiece_apply (s : Side) (r ι : R) (d ch : ℕ)
    (q : SeedPiece r ι d ch) :
    (seedRestrictionPiece s r ι d ch q).val=seedRestriction s r ι q.val := rfl

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_seedPiece_rank
#print axioms CycleQ2CurveRestriction.right_seedPiece_rank
#print axioms CycleQ2CurveRestriction.seedRestriction

#print axioms CycleQ2CurveRestriction.substitution_homogeneous
#print axioms CycleQ2CurveRestriction.seedRestrictionPiece
end
end

/- Component: continuation_3/CurveQuotientFiniteFree.lean -/
section
/-!
# The actual two curve quotients are finite free over two base coordinates

Both quotients retain their original checked equations. Their six basis
vectors are x0^a*x2^b, with the respective bounds(2,3) and(3,2).
-/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveQuotientFiniteFree

open MvPolynomial CycleQ2CurveRestriction CycleQ2IncidenceNormalForm
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

abbrev Base := MvPolynomial (Fin 2) R
abbrev Nested := MvPolynomial (Fin 2) (Base R)
abbrev ShiftIndex (s : Side) := Fin (xBound s) × Fin (zBound s)

def splitIndex : Fin 4 ≃ Fin 2 ⊕ Fin 2 where
  toFun := ![Sum.inl 0,Sum.inr 0,Sum.inl 1,Sum.inr 1]
  invFun := Sum.elim ![0,2] ![1,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by cases i with
    | inl i => fin_cases i <;> rfl
    | inr i => fin_cases i <;> rfl

def remainingIndex (i : Fin 2) : Fin 4 := ![1,3] i

def regroup : CurvePoly R ≃ₐ[R] Nested R :=
  (renameEquiv R splitIndex).trans (sumAlgEquiv R (Fin 2) (Fin 2))

@[simp] theorem regroup_C (c : R) : regroup R (C c)=C (C c) := by simp [regroup]
@[simp] theorem regroup_X_zero : regroup R (X 0)=X 0 := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_one : regroup R (X 1)=C (X 0) := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_two : regroup R (X 2)=X 1 := by simp [regroup,splitIndex]
@[simp] theorem regroup_X_three : regroup R (X 3)=C (X 1) := by simp [regroup,splitIndex]

def remainingInclusion : Base R →ₐ[R] CurvePoly R := rename remainingIndex

theorem regroup_remaining (p : Base R) : regroup R (remainingInclusion R p)=C p := by
  have h : (regroup R).toAlgHom.comp (remainingInclusion R)=
      IsScalarTower.toAlgHom R (Base R) (Nested R) := by
    ext i
    fin_cases i <;> simp [remainingInclusion,remainingIndex]
  exact congrArg (fun f : Base R →ₐ[R] Nested R => f p) h

instance remainingAlgebra : Algebra (Base R) (CurvePoly R) :=
  (remainingInclusion R).toRingHom.toAlgebra

def regroupOverBase : CurvePoly R ≃ₐ[Base R] Nested R where
  toRingEquiv := (regroup R).toRingEquiv
  commutes' p := regroup_remaining R p

def nestedWeight : (Fin 2 →₀ ℕ) →+ ℕ where
  toFun e := 3*e 0+4*e 1
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def nestedOrder : MonomialOrder (Fin 2) := weightedOrder MonomialOrder.lex nestedWeight

def qLead : Side → (Fin 2 →₀ ℕ)
  | .left => Finsupp.single 0 2
  | .right => Finsupp.single 1 2

def hLead : Side → (Fin 2 →₀ ℕ)
  | .left => Finsupp.single 1 3
  | .right => Finsupp.single 0 3

def qTail : Side → (Fin 2 →₀ ℕ)
  | .left => 0
  | .right => Finsupp.single 0 2

def qCoefficient (s : Side) (r : R) : Base R :=
  match s with
  | .left => -(C r*X 0*X 1)
  | .right => 1

def hTail (s : Side) : Fin 4 → (Fin 2 →₀ ℕ) :=
  match s with
  | .left => ![Finsupp.single 0 1+Finsupp.single 1 1,Finsupp.single 1 1,Finsupp.single 0 1,0]
  | .right => ![Finsupp.single 0 2,Finsupp.single 0 1,Finsupp.single 1 1,0]

def hCoefficient (s : Side) (r ι : R) : Fin 4 → Base R :=
  match s with
  | .left => ![X 1,X 0*X 1,X 0^2+C r*X 0*X 1,C (1-ι)*X 1^3-C ι*X 0^3]
  | .right => ![-X 1,-X 0*X 1-X 0^2,X 0*X 1-X 0^2,-C (2*(1-ι))*X 1^3+C (2*ι)*X 0^3]

def nestedQ (s : Side) (r : R) : Nested R :=
  monomial (qLead s) 1 + ∑ _j : Fin 1, monomial (qTail s) (qCoefficient R s r)

def nestedH (s : Side) (r ι : R) : Nested R :=
  monomial (hLead s) 1 + ∑ j : Fin 4, monomial (hTail s j) (hCoefficient R s r ι j)

theorem regroup_quadric (s : Side) (r : R) : regroup R (quadric s r)=nestedQ R s r := by
  cases s <;> simp [quadric,nestedQ,qLead,qTail,qCoefficient,← X_pow_eq_monomial] <;> ring

theorem regroup_cubic (s : Side) (r ι : R) : regroup R (cubic s r ι)=nestedH R s r ι := by
  cases s <;>
    simp [cubic,nestedH,hLead,hTail,hCoefficient,Fin.sum_univ_succ,
      Matrix.cons_val_succ,Fin.reduceSucc,MvPolynomial.monomial_single_add,
      ← X_pow_eq_monomial,← C_mul_X_pow_eq_monomial] <;> ring

theorem nestedQ_leading [Nontrivial R] (s : Side) (r : R) :
    nestedOrder.degree (nestedQ R s r)=qLead s ∧ nestedOrder.Monic (nestedQ R s r) := by
  unfold nestedQ
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,qLead,Finsupp.single_apply,Fin.ext_iff]
  · intro j
    apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,qLead,qTail,Finsupp.single_apply,Fin.ext_iff]

theorem nestedH_leading [Nontrivial R] (s : Side) (r ι : R) :
    nestedOrder.degree (nestedH R s r ι)=hLead s ∧ nestedOrder.Monic (nestedH R s r ι) := by
  unfold nestedH
  apply degree_monic_add_sum
  · apply weightedOrder_lt_of_weight_lt
    cases s <;> norm_num [nestedWeight,hLead,Finsupp.single_apply,Fin.ext_iff]
  · intro j
    apply weightedOrder_lt_of_weight_lt
    cases s <;> fin_cases j <;>
      norm_num [nestedWeight,hLead,hTail,Finsupp.single_apply,Fin.ext_iff]

theorem nested_coprime [Nontrivial R] (s : Side) (r ι : R) :
    ∀ j, nestedOrder.degree (nestedQ R s r) j=0 ∨ nestedOrder.degree (nestedH R s r ι) j=0 := by
  intro j
  rw [(nestedQ_leading R s r).1,(nestedH_leading R s r ι).1]
  cases s <;> fin_cases j <;> simp [qLead,hLead]

def nestedIdeal (s : Side) (r ι : R) : Ideal (Nested R) :=
  equationsIdeal (nestedQ R s r) (nestedH R s r ι)

theorem nestedIdeal_map (s : Side) (r ι : R) : nestedIdeal R s r ι=
    (curveIdeal s r ι).map (regroupOverBase R).toRingHom := by
  simp only [nestedIdeal,curveIdeal,equationsIdeal,Ideal.map_span,Set.image_insert_eq,
    Set.image_singleton]
  change Ideal.span {nestedQ R s r,nestedH R s r ι}=
    Ideal.span {regroup R (quadric s r),regroup R (cubic s r ι)}
  rw [regroup_quadric,regroup_cubic]

instance curveModule (s : Side) (r ι : R) : Module (Base R) (CurveRing s r ι) :=
  (inferInstance : Algebra (Base R) (CurveRing s r ι)).toModule

def quotientRegroup (s : Side) (r ι : R) :
    CurveRing s r ι ≃ₐ[Base R] (Nested R ⧸ nestedIdeal R s r ι) :=
  Ideal.quotientEquivAlg _ _ (regroupOverBase R) (nestedIdeal_map R s r ι)

theorem reduced_iff [Nontrivial R] (s : Side) (r ι : R) (e : Fin 2 →₀ ℕ) :
    e∈reducedExponents nestedOrder (nestedQ R s r) (nestedH R s r ι) ↔
      e 0<xBound s ∧ e 1<zBound s := by
  change (¬nestedOrder.degree (nestedQ R s r)≤e) ∧
    (¬nestedOrder.degree (nestedH R s r ι)≤e) ↔ _
  rw [(nestedQ_leading R s r).1,(nestedH_leading R s r ι).1]
  cases s <;> simp [qLead,hLead,xBound,zBound,Finsupp.single_le_iff,and_comm]

def nestedExponentEquiv [Nontrivial R] (s : Side) (r ι : R) :
    reducedExponents nestedOrder (nestedQ R s r) (nestedH R s r ι) ≃ ShiftIndex s where
  toFun e := (⟨e.val 0,((reduced_iff R s r ι e.val).mp e.property).1⟩,
    ⟨e.val 1,((reduced_iff R s r ι e.val).mp e.property).2⟩)
  invFun ab := ⟨Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val,
    (reduced_iff R s r ι _).mpr (by simpa using And.intro ab.1.isLt ab.2.isLt)⟩
  left_inv e := by apply Subtype.ext; ext j; fin_cases j <;> simp
  right_inv ab := by apply Prod.ext <;> apply Fin.ext <;> simp

def nestedBasis [Nontrivial R] (s : Side) (r ι : R) :
    Module.Basis (ShiftIndex s) (Base R) (Nested R ⧸ nestedIdeal R s r ι) :=
  (quotientBasis nestedOrder (nestedQ R s r) (nestedH R s r ι)
    (nestedQ_leading R s r).2 (nestedH_leading R s r ι).2 (nested_coprime R s r ι)).reindex
      (nestedExponentEquiv R s r ι)

theorem nestedBasis_apply [Nontrivial R] (s : Side) (r ι : R) (ab : ShiftIndex s) :
    nestedBasis R s r ι ab=Ideal.Quotient.mk (nestedIdeal R s r ι)
      (X 0^ab.1.val*X 1^ab.2.val) := by
  unfold nestedBasis
  erw [Module.Basis.reindex_apply,quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ab.1.val+Finsupp.single 1 ab.2.val) 1=_
  rw [MvPolynomial.monomial_single_add,← X_pow_eq_monomial]

def curveBasis [Nontrivial R] (s : Side) (r ι : R) :
    Module.Basis (ShiftIndex s) (Base R) (CurveRing s r ι) :=
  (nestedBasis R s r ι).map (quotientRegroup R s r ι).symm.toLinearEquiv

theorem curveBasis_apply [Nontrivial R] (s : Side) (r ι : R) (ab : ShiftIndex s) :
    curveBasis R s r ι ab=Ideal.Quotient.mk (curveIdeal s r ι)
      ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val) := by
  apply (quotientRegroup R s r ι).injective
  simp only [curveBasis,Module.Basis.map_apply,AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply,nestedBasis_apply]
  change Ideal.Quotient.mk _ (X 0^ab.1.val*X 1^ab.2.val)=
    Ideal.Quotient.mk _ (regroup R ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val))
  simp

theorem curveQuotient_free [Nontrivial R] (s : Side) (r ι : R) : Module.Free (Base R) (CurveRing s r ι) :=
  Module.Free.of_basis (curveBasis R s r ι)

theorem curveQuotient_finite [Nontrivial R] (s : Side) (r ι : R) : Module.Finite (Base R) (CurveRing s r ι) :=
  Module.Finite.of_basis (curveBasis R s r ι)

theorem curveQuotient_rank_six [Nontrivial R] (s : Side) (r ι : R) :
    Module.finrank (Base R) (CurveRing s r ι)=6 := by
  rw [Module.finrank_eq_card_basis (curveBasis R s r ι)]
  cases s <;> decide

theorem basis_degree_bound (s : Side) (ab : ShiftIndex s) : ab.1.val+ab.2.val≤3 := by
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  cases s <;> simp only [xBound,zBound] at ha hb <;> omega

theorem basisMonomial_homogeneous (s : Side) (ab : ShiftIndex s) :
    ((X 0:CurvePoly R)^ab.1.val*X 2^ab.2.val).IsWeightedHomogeneous
      (fun _ => 1:Fin 4→ℕ) (ab.1.val+ab.2.val) := by
  convert ((isWeightedHomogeneous_X R (fun _ : Fin 4 => 1) 0).pow ab.1.val).mul
    ((isWeightedHomogeneous_X R (fun _ : Fin 4 => 1) 2).pow ab.2.val) using 1 <;> simp

end CycleQ2CurveQuotientFiniteFree

#print axioms CycleQ2CurveQuotientFiniteFree.curveQuotient_rank_six
#print axioms CycleQ2CurveQuotientFiniteFree.curveBasis_apply
end
end
