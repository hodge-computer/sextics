import Proposal.GeometricCechPoleReduction

/-!
# Surjectivity of the actual homogeneous simple-pole presentation

Arbitrary degree-one overlap sections are reduced by their two pole orders.
Above degree nine, the actual numerator lies in the four-generator ideal.
Homogeneous coefficient extraction lowers one pole order in each summand;
sections with only one denominator are actual chart boundaries.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GeometricCechPoleReduction

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricKoszulTrace

theorem high_degree_curve_relation (r : ℂ) (hr : r ^ 3 = 2)
    {n : ℕ} (hn : 9 < n) (p : Poly) (hp : p.IsHomogeneous n) :
    ∃ c d : Poly, c.IsHomogeneous (n - 4) ∧ d.IsHomogeneous (n - 4) ∧
      curveMap r 0 p = curveMap r 0 c * curveG1 r 0 + curveMap r 0 d * curveG2 r 0 := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  let v : Fin 4 → Poly := ![relation r 0, curveH 0, firstQuartic r, secondQuartic]
  let deg : Fin 4 → ℕ := ![2, 3, 4, 4]
  have hv : ∀ i, (v i).IsHomogeneous (deg i) := by
    intro i
    fin_cases i
    · exact relation_zero_homogeneous r
    · exact sparse_curveH_homogeneous 0
    · exact firstQuartic_homogeneous r
    · exact secondQuartic_homogeneous
  have hmem : p ∈ Ideal.span (Set.range v) := by
    have hmem := homogeneous_mem_reducedIdeal_of_degree_gt_nine r hr hn hp
    rw [← fourGeneratorIdeal_zero_eq_reducedIdeal r hr0] at hmem
    simpa only [fourGeneratorIdeal, v, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union] using hmem
  obtain ⟨q, hq, _, heq⟩ :=
    CycleQ2GeometricGradedWitness.exists_homogeneous_coefficients deg v hv n p hp hmem
  refine ⟨q 2, q 3, hq 2, hq 3, ?_⟩
  rw [← heq]
  simp only [map_add, map_mul, Fin.sum_univ_succ, v, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero, curveMap_f1, curveMap_h,
    mul_zero, zero_add, curveMap_firstQuartic, curveMap_secondQuartic]
  rfl

/-- An actual overlap fraction with independent pole orders at the two
quartics. The balanced denominator only presents the same localization. -/
def mixedFraction (r : ℂ) (n m : ℕ) (a : CurveRing r 0) : Overlap r 0 :=
  awayFraction r 0 (curveG1 r 0 * curveG2 r 0) (n + m)
    (a * curveG1 r 0 ^ m * curveG2 r 0 ^ n)

theorem mixedFraction_add (r : ℂ) (n m : ℕ) (a b : CurveRing r 0) :
    mixedFraction r n m (a + b) = mixedFraction r n m a + mixedFraction r n m b := by
  simp only [mixedFraction, awayFraction, add_mul, Localization.add_mk_self]

theorem mixedFraction_mul_first (r : ℂ) (n m : ℕ) (a : CurveRing r 0) :
    mixedFraction r (n + 1) m (a * curveG1 r 0) = mixedFraction r n m a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 r 0 * curveG2 r 0) ^ (n + 1 + m) *
      (a * curveG1 r 0 ^ m * curveG2 r 0 ^ n) =
    (curveG1 r 0 * curveG2 r 0) ^ (n + m) *
      (a * curveG1 r 0 * curveG1 r 0 ^ m * curveG2 r 0 ^ (n + 1))
  rw [show n + 1 + m = (n + m) + 1 by omega, pow_succ, pow_succ]
  ring

theorem mixedFraction_mul_second (r : ℂ) (n m : ℕ) (a : CurveRing r 0) :
    mixedFraction r n (m + 1) (a * curveG2 r 0) = mixedFraction r n m a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 r 0 * curveG2 r 0) ^ (n + (m + 1)) *
      (a * curveG1 r 0 ^ m * curveG2 r 0 ^ n) =
    (curveG1 r 0 * curveG2 r 0) ^ (n + m) *
      (a * curveG2 r 0 * curveG1 r 0 ^ (m + 1) * curveG2 r 0 ^ n)
  rw [show n + (m + 1) = (n + m) + 1 by omega, pow_succ, pow_succ]
  ring

theorem mixedFraction_balanced (r : ℂ) (n : ℕ) (a : CurveRing r 0) :
    mixedFraction r n n a = awayFraction r 0 (curveG1 r 0 * curveG2 r 0) n a := by
  simp only [mixedFraction, awayFraction, Localization.mk_eq_mk']
  apply IsLocalization.mk'_eq_of_eq
  change (curveG1 r 0 * curveG2 r 0) ^ (n + n) * a =
    (curveG1 r 0 * curveG2 r 0) ^ n *
      (a * curveG1 r 0 ^ n * curveG2 r 0 ^ n)
  rw [pow_add, mul_pow]
  ring

def mixedRepresentative (r : ℂ) (n m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m))) : OverlapDegreeOne r 0 :=
  ⟨mixedFraction r n m (curveMap r 0 p), by
    apply awayFraction_mem_degreeOne r 0 _ 8 (curveG12_mem_grade r 0) (n + m)
    have hgrade := SetLike.mul_mem_graded
      (SetLike.mul_mem_graded (curveMap_mem_grade r 0 hp)
        (SetLike.pow_mem_graded m (curveG1_mem_grade r 0)))
      (SetLike.pow_mem_graded n (curveG2_mem_grade r 0))
    have hdegree : 1 + 4 * (n + m) + m * 4 + n * 4 = 1 + (n + m) * 8 := by omega
    simpa only [nsmul_eq_mul, Nat.cast_id, hdegree] using hgrade⟩

def mixedCechClass (r : ℂ) (n m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m))) : DegreeOneCech r 0 :=
  QuotientAddGroup.mk (mixedRepresentative r n m p hp)

theorem mixedCechClass_add (r : ℂ) (n m : ℕ) (p q : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + m)))
    (hq : q.IsHomogeneous (1 + 4 * (n + m))) :
    mixedCechClass r n m (p + q) (hp.add hq) =
      mixedCechClass r n m p hp + mixedCechClass r n m q hq := by
  have hrep : mixedRepresentative r n m (p + q) (hp.add hq) =
      mixedRepresentative r n m p hp + mixedRepresentative r n m q hq := by
    apply Subtype.ext
    exact (congrArg (mixedFraction r n m) (map_add (curveMap r 0) p q)).trans
      (mixedFraction_add r n m _ _)
  change (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _ =
    (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _ +
      (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _
  rw [hrep, map_add]

def firstPoleSection (r : ℂ) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * n)) : FirstDegreeOne r 0 :=
  ⟨awayFraction r 0 (curveG1 r 0) n (curveMap r 0 p),
    awayFraction_mem_degreeOne r 0 _ 4 (curveG1_mem_grade r 0) n _
      (by simpa only [Nat.mul_comm] using curveMap_mem_grade r 0 hp)⟩

def secondPoleSection (r : ℂ) (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * m)) : SecondDegreeOne r 0 :=
  ⟨awayFraction r 0 (curveG2 r 0) m (curveMap r 0 p),
    awayFraction_mem_degreeOne r 0 _ 4 (curveG2_mem_grade r 0) m _
      (by simpa only [Nat.mul_comm] using curveMap_mem_grade r 0 hp)⟩

theorem mixedRepresentative_first (r : ℂ) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + 0))) :
    mixedRepresentative r n 0 p hp =
      firstDegreeOneRestriction r 0 (firstPoleSection r n p (by simpa using hp)) := by
  apply Subtype.ext
  change mixedFraction r n 0 (curveMap r 0 p) =
    awayRestriction r 0 (curveG1 r 0) (curveG2 r 0) (curveG1 r 0 * curveG2 r 0) rfl
      (awayFraction r 0 (curveG1 r 0) n (curveMap r 0 p))
  rw [awayRestriction_fraction]
  simp only [mixedFraction, Nat.add_zero, pow_zero, mul_one]

theorem mixedRepresentative_second (r : ℂ) (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (0 + m))) :
    mixedRepresentative r 0 m p hp =
      secondDegreeOneRestriction r 0 (secondPoleSection r m p (by simpa using hp)) := by
  apply Subtype.ext
  change mixedFraction r 0 m (curveMap r 0 p) =
    awayRestriction r 0 (curveG2 r 0) (curveG1 r 0) (curveG1 r 0 * curveG2 r 0)
      (mul_comm _ _) (awayFraction r 0 (curveG2 r 0) m (curveMap r 0 p))
  rw [awayRestriction_fraction]
  simp only [mixedFraction, Nat.zero_add, pow_zero, mul_one]

theorem mixedCechClass_first_zero (r : ℂ) (n : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (n + 0))) : mixedCechClass r n 0 p hp = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(firstPoleSection r n p (by simpa using hp), 0), ?_⟩
  rw [mixedRepresentative_first]
  simp [degreeOneCoboundary]

theorem mixedCechClass_second_zero (r : ℂ) (m : ℕ) (p : Poly)
    (hp : p.IsHomogeneous (1 + 4 * (0 + m))) : mixedCechClass r 0 m p hp = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  refine ⟨(0, -(secondPoleSection r m p (by simpa using hp))), ?_⟩
  rw [mixedRepresentative_second]
  simp [degreeOneCoboundary]

theorem mixedCechClass_one_one (r : ℂ) (p : Poly) (hp : p.IsHomogeneous 9) :
    mixedCechClass r 1 1 p hp = degreeNineCechClass r 0 p hp := by
  apply congrArg QuotientAddGroup.mk
  apply Subtype.ext
  exact mixedFraction_balanced r 1 (curveMap r 0 p)

theorem degreeNineCechClass_zero (r : ℂ) :
    degreeNineCechClass r 0 0 (isHomogeneous_zero (Fin 4) ℂ 9) = 0 := by
  have hz : degreeNineRepresentative r 0 0 (isHomogeneous_zero (Fin 4) ℂ 9) = 0 := by
    apply Subtype.ext
    change awayFraction r 0 (curveG1 r 0 * curveG2 r 0) 1 (curveMap r 0 0) = 0
    rw [map_zero]
    exact Localization.mk_zero _
  change (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _ = 0
  rw [hz, map_zero]

theorem degreeNineCechClass_add (r : ℂ) (p q : Poly)
    (hp : p.IsHomogeneous 9) (hq : q.IsHomogeneous 9) :
    degreeNineCechClass r 0 (p + q) (hp.add hq) =
      degreeNineCechClass r 0 p hp + degreeNineCechClass r 0 q hq := by
  rw [← mixedCechClass_one_one, ← mixedCechClass_one_one, ← mixedCechClass_one_one]
  exact mixedCechClass_add r 1 1 p q hp hq

theorem mixedCechClass_relation (r : ℂ) (n m : ℕ) (p c d : Poly)
    (hp : p.IsHomogeneous (1 + 4 * ((n + 1) + (m + 1))))
    (hc : c.IsHomogeneous (1 + 4 * (n + (m + 1))))
    (hd : d.IsHomogeneous (1 + 4 * ((n + 1) + m)))
    (hrelation : curveMap r 0 p =
      curveMap r 0 c * curveG1 r 0 + curveMap r 0 d * curveG2 r 0) :
    mixedCechClass r (n + 1) (m + 1) p hp =
      mixedCechClass r n (m + 1) c hc + mixedCechClass r (n + 1) m d hd := by
  have hrep : mixedRepresentative r (n + 1) (m + 1) p hp =
      mixedRepresentative r n (m + 1) c hc + mixedRepresentative r (n + 1) m d hd := by
    apply Subtype.ext
    change mixedFraction r (n + 1) (m + 1) (curveMap r 0 p) =
      mixedFraction r n (m + 1) (curveMap r 0 c) +
        mixedFraction r (n + 1) m (curveMap r 0 d)
    rw [hrelation, mixedFraction_add, mixedFraction_mul_first, mixedFraction_mul_second]
  change (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _ =
    (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _ +
      (QuotientAddGroup.mk' (degreeOneBoundaries r 0)) _
  rw [hrep, map_add]

/-- Every pair of homogeneous pole orders reduces to an actual
degree-nine numerator with simple poles at both quartics. -/
theorem mixedCechClass_exists_degreeNine (r : ℂ) (hr : r ^ 3 = 2)
    (n m : ℕ) (p : Poly) (hp : p.IsHomogeneous (1 + 4 * (n + m))) :
    ∃ (q : Poly) (hq : q.IsHomogeneous 9),
      mixedCechClass r n m p hp = degreeNineCechClass r 0 q hq := by
  have aux : ∀ s n m, n + m = s →
      ∀ (p : Poly) (hp : p.IsHomogeneous (1 + 4 * (n + m))),
        ∃ (q : Poly) (hq : q.IsHomogeneous 9),
          mixedCechClass r n m p hp = degreeNineCechClass r 0 q hq := by
    intro s
    induction s using Nat.strong_induction_on with
    | h s ih =>
        intro n m hsum p hp
        cases n with
        | zero =>
            refine ⟨0, isHomogeneous_zero (Fin 4) ℂ 9, ?_⟩
            rw [mixedCechClass_second_zero, degreeNineCechClass_zero]
        | succ n =>
            cases m with
            | zero =>
                refine ⟨0, isHomogeneous_zero (Fin 4) ℂ 9, ?_⟩
                rw [mixedCechClass_first_zero, degreeNineCechClass_zero]
            | succ m =>
                by_cases hbase : n = 0 ∧ m = 0
                · obtain ⟨rfl, rfl⟩ := hbase
                  exact ⟨p, hp, mixedCechClass_one_one r p hp⟩
                · have hhigh : 9 < 1 + 4 * ((n + 1) + (m + 1)) := by omega
                  obtain ⟨c, d, hc, hd, hrelation⟩ :=
                    high_degree_curve_relation r hr hhigh p hp
                  have hc' : c.IsHomogeneous (1 + 4 * (n + (m + 1))) := by
                    convert hc using 1; omega
                  have hd' : d.IsHomogeneous (1 + 4 * ((n + 1) + m)) := by
                    convert hd using 1; omega
                  obtain ⟨qc, hqc, heqc⟩ :=
                    ih (n + (m + 1)) (by omega) n (m + 1) rfl c hc'
                  obtain ⟨qd, hqd, heqd⟩ :=
                    ih ((n + 1) + m) (by omega) (n + 1) m rfl d hd'
                  refine ⟨qc + qd, hqc.add hqd, ?_⟩
                  rw [mixedCechClass_relation r n m p c d hp hc' hd' hrelation,
                    heqc, heqd, degreeNineCechClass_add]
  exact aux (n + m) n m rfl p hp

/-- The degree-nine simple-pole construction is surjective onto the
entire actual degree-one Cech quotient, including arbitrary pole orders.
No geometric Serre-duality or comparison assumption is supplied. -/
theorem degreeNineCechClass_surjective (r : ℂ) (hr : r ^ 3 = 2)
    (z : DegreeOneCech r 0) :
    ∃ (p : Poly) (hp : p.IsHomogeneous 9), degreeNineCechClass r 0 p hp = z := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
  obtain ⟨n, a, ha, hax⟩ := x.property
  obtain ⟨p, hp, hpa⟩ := ha
  change p.IsHomogeneous (1 + n * 8) at hp
  change curveMap r 0 p = a at hpa
  have hp' : p.IsHomogeneous (1 + 4 * (n + n)) := by
    convert hp using 1 <;> omega
  have hx : mixedRepresentative r n n p hp' = x := by
    apply Subtype.ext
    change mixedFraction r n n (curveMap r 0 p) = (x : Overlap r 0)
    rw [mixedFraction_balanced, hpa]
    exact hax
  obtain ⟨q, hq, heq⟩ := mixedCechClass_exists_degreeNine r hr n n p hp'
  refine ⟨q, hq, ?_⟩
  rw [← heq]
  change QuotientAddGroup.mk (mixedRepresentative r n n p hp') = QuotientAddGroup.mk x
  exact congrArg QuotientAddGroup.mk hx

/-- A complex multiple of the fixed normalization numerator, retaining
the actual degree-one Cech quotient rather than introducing a new space. -/
def normalizedCechClass (r c : ℂ) : DegreeOneCech r 0 :=
  degreeNineCechClass r 0 (C c * mon 1 8 0 0) ((mon_homogeneous 1 8 0 0).C_mul c)

theorem degreeNineCechClass_eq_normalized (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCechClass r 0 p hp = normalizedCechClass r (traceLinear r p) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  have hmem := homogeneous_degreeNine_mod_trace r hr hp
  have heq := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
  rw [map_sub, sub_eq_zero] at heq
  exact degreeNineCechClass_eq_of_reducedQuotient_eq r hr0 p _ hp
    ((mon_homogeneous 1 8 0 0).C_mul (traceLinear r p)) heq

/-- Every actual homogeneous Cech class, with no bound on its initial
pole orders, is represented by a complex multiple of `x0*x1^8/(g1*g2)`.
Uniqueness of this scalar requires the independent nonvanishing result. -/
theorem normalizedCechClass_surjective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Surjective (normalizedCechClass r) := by
  intro z
  obtain ⟨p, hp, hpz⟩ := degreeNineCechClass_surjective r hr z
  exact ⟨traceLinear r p, (degreeNineCechClass_eq_normalized r hr p hp).symm.trans hpz⟩

end CycleQ2GeometricCechPoleReduction

end
