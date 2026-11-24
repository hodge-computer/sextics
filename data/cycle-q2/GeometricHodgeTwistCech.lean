import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Tactic

/-!
# Four-open Laurent Čech calculation of the weighted cubic twists

In the monic cubic normal form each coefficient of `1,w,w²` is a Laurent
polynomial in the four weight-one variables. On an intersection its poles
can occur only in the inverted coordinates. The degree is shifted by twice
the exponent of `w`. We compute exactness in degrees one and two of this
algebraic Čech complex for every integral twist.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeTwistCech

abbrev Vertex := Fin 4
abbrev Exp := Vertex → ℤ
abbrev NormalForm (A : Type*) [Zero A] := Fin 3 → (Exp →₀ A)

/-- Membership of one Laurent monomial on a standard intersection. -/
def Allowed (t : ℤ) (S : Finset Vertex) (j : Fin 3) (e : Exp) : Prop :=
  (∑ i, e i) + 2 * (j.val : ℤ) = t ∧ ∀ i, e i < 0 → i ∈ S

variable {A : Type*} [AddCommGroup A]

/-- The full group of Laurent normal forms of this twist and pole set. -/
def sections (A : Type*) [AddCommGroup A] (t : ℤ) (S : Finset Vertex) :
    AddSubgroup (NormalForm A) where
  carrier := {p | ∀ j e, ¬ Allowed t S j e → p j e = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' := by
    intro p q hp hq j e he
    exact (add_zero (0 : A)) ▸ congrArg₂ (· + ·) (hp j e he) (hq j e he)
  neg_mem' := by
    intro p hp j e he
    change -(p j e) = 0
    rw [hp j e he, neg_zero]

/-- The chart restriction keeps all Laurent coefficients. -/
def restrict {t : ℤ} {S T : Finset Vertex} (h : S ⊆ T) (u : sections A t S) : sections A t T :=
  ⟨u.val, fun j e he => u.property j e fun hS => he ⟨hS.1, fun i hi => h (hS.2 i hi)⟩⟩

abbrev C0 (A : Type*) [AddCommGroup A] (t : ℤ) := (i : Vertex) → sections A t {i}
abbrev C1 (A : Type*) [AddCommGroup A] (t : ℤ) := (i j : Vertex) → sections A t {i,j}
abbrev C2 (A : Type*) [AddCommGroup A] (t : ℤ) := (i j k : Vertex) → sections A t {i,j,k}
abbrev C3 (A : Type*) [AddCommGroup A] (t : ℤ) := (i j k l : Vertex) → sections A t {i,j,k,l}

variable {t : ℤ}

def d0 (c : C0 A t) : C1 A t := fun i j =>
  restrict (by grind) (c j) - restrict (by grind) (c i)

def d1 (c : C1 A t) : C2 A t := fun i j k =>
  restrict (by grind) (c j k) - restrict (by grind) (c i k) + restrict (by grind) (c i j)

def d2 (c : C2 A t) : C3 A t := fun i j k l =>
  restrict (by grind) (c j k l) - restrict (by grind) (c i k l) +
    restrict (by grind) (c i j l) - restrict (by grind) (c i j k)

theorem d1_d0 (c : C0 A t) : d1 (d0 c) = 0 := by
  funext i j k
  apply Subtype.ext
  change ((c k).val - (c j).val) - ((c k).val - (c i).val) + ((c j).val - (c i).val) = 0
  abel

theorem d2_d1 (c : C1 A t) : d2 (d1 c) = 0 := by
  funext i j k l
  apply Subtype.ext
  change ((c k l).val - (c j l).val + (c j k).val) - ((c k l).val - (c i l).val + (c i k).val) +
    ((c j l).val - (c i l).val + (c i j).val) - ((c j k).val - (c i k).val + (c i j).val) = 0
  abel

/-- A nonnegative coordinate can be adjoined to or removed from an allowed pole set. -/
private def vertex (e : Exp) : Vertex :=
  if h : ∃ i, 0 ≤ e i then Classical.choose h else 0

private theorem vertex_nonneg {e : Exp} {S : Finset Vertex} (hs : S.card < 4)
    (h : ∀ i, e i < 0 → i ∈ S) : 0 ≤ e (vertex e) := by
  have he : ∃ i, 0 ≤ e i := by
    by_contra! hn
    have hall : Finset.univ ⊆ S := fun i _ => h i (hn i)
    have := Finset.card_le_card hall
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  simpa only [vertex, dif_pos he] using Classical.choose_spec he

private def split (v : Vertex → NormalForm A) : NormalForm A := fun j =>
  ∑ i, (v i j).filter (fun e => vertex e = i)

private theorem split_coeff (v : Vertex → NormalForm A) (j : Fin 3) (e : Exp) :
    split v j e = v (vertex e) j e := by
  classical
  simp [split, Finsupp.finsetSum_apply, Finsupp.filter_apply]

/-- One formula gives finite Laurent polynomials on the smaller intersections. -/
private def contractSection {S : Finset Vertex} (hS : S.card ≤ 2)
    (v : (i : Vertex) → sections A t (insert i S)) : sections A t S := by
  refine ⟨split (fun i => (v i).val), ?_⟩
  intro j e hn
  rw [split_coeff]
  apply (v (vertex e)).property j e
  intro he
  apply hn
  refine ⟨he.1, fun i hi => ?_⟩
  rcases Finset.mem_insert.mp (he.2 i hi) with h | h
  · have hc : (insert (vertex e) S).card < 4 := by
      have := Finset.card_insert_le (vertex e) S
      omega
    exact False.elim ((not_lt_of_ge (vertex_nonneg hc he.2)) (h ▸ hi))
  · exact h

def h1 (c : C1 A t) : C0 A t := fun i => contractSection (by simp) (fun a => c a i)

def h2 (c : C2 A t) : C1 A t := fun i j =>
  contractSection (by have := Finset.card_insert_le i ({j} : Finset Vertex); simpa using this) (fun a => c a i j)

/-- Every degree-one cocycle has a finite Laurent primitive on the four single charts. -/
theorem exact_one (c : C1 A t) (hc : d1 c = 0) : d0 (h1 c) = c := by
  funext i j
  apply Subtype.ext
  funext slot
  ext e
  have h := congrArg (fun z : C2 A t => (z (vertex e) i j).val slot e) hc
  change (c i j).val slot e - (c (vertex e) j).val slot e + (c (vertex e) i).val slot e = 0 at h
  change split _ slot e - split _ slot e = (c i j).val slot e
  rw [split_coeff, split_coeff]
  abel_nf at h ⊢
  grind

/-- Every degree-two cocycle has a finite Laurent primitive on the pair intersections. -/
theorem exact_two (c : C2 A t) (hc : d2 c = 0) : d1 (h2 c) = c := by
  funext i j k
  apply Subtype.ext
  funext slot
  ext e
  have h := congrArg (fun z : C3 A t => (z (vertex e) i j k).val slot e) hc
  change (c i j k).val slot e - (c (vertex e) j k).val slot e +
    (c (vertex e) i k).val slot e - (c (vertex e) i j).val slot e = 0 at h
  change split _ slot e - split _ slot e + split _ slot e = (c i j k).val slot e
  rw [split_coeff, split_coeff, split_coeff]
  abel_nf at h ⊢
  grind

/-! ## The top Laurent coefficient

The increasing four-open complex has a single top intersection. Its four
faces are indexed by the omitted coordinate. The following quotient uses
the actual alternating restriction map, with signs `+,-,+,-`.
-/

abbrev Top (A : Type*) [AddCommGroup A] (t : ℤ) := sections A t Finset.univ
abbrev TopFaces (A : Type*) [AddCommGroup A] (t : ℤ) :=
  (i : Vertex) → sections A t (Finset.univ.erase i)

/-- Alternating restriction from the four increasing triple intersections. -/
def topBoundary : TopFaces A t →+ Top A t where
  toFun c := restrict (Finset.subset_univ _) (c 0) -
    restrict (Finset.subset_univ _) (c 1) +
    restrict (Finset.subset_univ _) (c 2) -
    restrict (Finset.subset_univ _) (c 3)
  map_zero' := by
    apply Subtype.ext
    change (0 : NormalForm A) - 0 + 0 - 0 = 0
    abel
  map_add' c d := by
    apply Subtype.ext
    change (c 0).val + (d 0).val - ((c 1).val + (d 1).val) +
        ((c 2).val + (d 2).val) - ((c 3).val + (d 3).val) =
      ((c 0).val - (c 1).val + (c 2).val - (c 3).val) +
        ((d 0).val - (d 1).val + (d 2).val - (d 3).val)
    abel

def AllNegative (e : Exp) : Prop := ∀ i, e i < 0

/-- The part which cannot extend across any one coordinate hyperplane. -/
def negativePart (p : Top A t) : Top A t := by
  classical
  refine ⟨fun j => (p.val j).filter AllNegative, ?_⟩
  intro j e he
  simp only [Finsupp.filter_apply]
  split_ifs
  · exact p.property j e he
  · rfl

private theorem vertex_nonneg_of_not_allNegative {e : Exp}
    (h : ¬ AllNegative e) : 0 ≤ e (vertex e) := by
  have he : ∃ i, 0 ≤ e i := by
    simpa only [AllNegative, not_forall, not_lt] using h
  simpa only [vertex, dif_pos he] using Classical.choose_spec he

/-- Assign every extendible monomial to one face on which it is regular. -/
private def complementaryFace (p : Top A t) (i : Vertex) :
    sections A t (Finset.univ.erase i) := by
  classical
  refine ⟨fun j => (p.val j).filter (fun e => vertex e = i ∧ ¬ AllNegative e), ?_⟩
  intro j e he
  simp only [Finsupp.filter_apply]
  split_ifs with h
  · apply p.property j e
    intro ha
    apply he
    refine ⟨ha.1, fun k hk => ?_⟩
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ k⟩
    intro hki
    have hv := vertex_nonneg_of_not_allNegative h.2
    rw [h.1, ← hki] at hv
    exact (not_lt_of_ge hv) hk
  · rfl

private def topPrimitive (p : Top A t) : TopFaces A t := fun i =>
  if i = 1 ∨ i = 3 then -complementaryFace p i else complementaryFace p i

/-- Removing the strictly negative terms has an explicit finite Čech primitive. -/
theorem topBoundary_topPrimitive (p : Top A t) :
    topBoundary (topPrimitive p) = p - negativePart p := by
  classical
  apply Subtype.ext
  funext j
  apply Finsupp.ext
  intro e
  by_cases he : AllNegative e
  · simp [topBoundary, topPrimitive, restrict, complementaryFace, negativePart,
      Finsupp.filter_apply, he]
  · obtain ⟨i, hv⟩ : ∃ i : Vertex, vertex e = i := ⟨vertex e, rfl⟩
    fin_cases i <;>
      simp [topBoundary, topPrimitive, restrict, complementaryFace, negativePart,
        Finsupp.filter_apply, he, hv]

private theorem negative_face_coefficient (i : Vertex)
    (p : sections A t (Finset.univ.erase i)) (j : Fin 3) (e : Exp)
    (he : AllNegative e) : p.val j e = 0 := by
  apply p.property j e
  intro h
  exact Finset.not_mem_erase i Finset.univ (h.2 i (he i))

/-- Every top boundary has zero coefficient at every strictly negative monomial. -/
theorem negativePart_topBoundary (c : TopFaces A t) :
    negativePart (topBoundary c) = 0 := by
  classical
  apply Subtype.ext
  funext j
  apply Finsupp.ext
  intro e
  by_cases he : AllNegative e
  · simp only [negativePart, Finsupp.filter_apply, if_pos he]
    change (c 0).val j e - (c 1).val j e + (c 2).val j e - (c 3).val j e = 0
    rw [negative_face_coefficient 0 (c 0) j e he,
      negative_face_coefficient 1 (c 1) j e he,
      negative_face_coefficient 2 (c 2) j e he,
      negative_face_coefficient 3 (c 3) j e he]
    abel
  · simp [negativePart, Finsupp.filter_apply, he]

theorem top_mem_boundary_iff (p : Top A t) :
    p ∈ (topBoundary : TopFaces A t →+ Top A t).range ↔ negativePart p = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    exact negativePart_topBoundary c
  · intro hp
    refine ⟨topPrimitive p, ?_⟩
    rw [topBoundary_topPrimitive, hp, sub_zero]

def negativeExponent : Exp := fun _ => -1

/-- The degree-one partial fraction has no pole at the omitted coordinate. -/
def partialExponent (i : Vertex) : Exp := fun k => if k = i then 0 else -1

theorem partialExponent_allowed (i : Vertex) :
    Allowed 1 (Finset.univ.erase i) 2 (partialExponent i) := by
  refine ⟨?_, ?_⟩
  · fin_cases i <;> decide
  · intro k hk
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ k⟩
    intro h
    subst k
    simp [partialExponent] at hk

def partialGenerator (i : Vertex) (a : A) : sections A 1 (Finset.univ.erase i) := by
  classical
  refine ⟨fun j => if j = 2 then Finsupp.single (partialExponent i) a else 0, ?_⟩
  intro j e he
  by_cases hj : j = 2
  · subst j
    by_cases hx : e = partialExponent i
    · subst e
      exact False.elim (he (partialExponent_allowed i))
    · simp [hx, eq_comm]
  · simp [hj]

/-- In weight zero there is exactly one all-negative normal-form monomial. -/
theorem negative_weight_zero (j : Fin 3) (e : Exp) (he : AllNegative e)
    (hw : (∑ i, e i) + 2 * (j.val : ℤ) = 0) :
    j = 2 ∧ e = negativeExponent := by
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hj := j.isLt
  have hs : e 0 + e 1 + e 2 + e 3 + 2 * (j.val : ℤ) = 0 := by
    simpa only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Fin.sum_univ_zero, add_zero, add_assoc] using hw
  have hj2 : j.val = 2 := by omega
  refine ⟨Fin.ext hj2, ?_⟩
  funext i
  fin_cases i <;> change e _ = -1 <;> omega

/-- Positive twists have no all-negative Laurent monomials. -/
theorem not_negative_of_positive {t : ℤ} (ht : 0 < t) (j : Fin 3) (e : Exp)
    (hw : (∑ i, e i) + 2 * (j.val : ℤ) = t) : ¬ AllNegative e := by
  intro he
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have h3 := he 3
  have hj := j.isLt
  have hs : e 0 + e 1 + e 2 + e 3 + 2 * (j.val : ℤ) = t := by
    simpa only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ,
      Fin.sum_univ_zero, add_zero, add_assoc] using hw
  omega

/-- The top coefficient is that of `w²/(x₀x₁x₂x₃)`. -/
def topCoefficient : Top A 0 →+ A where
  toFun p := p.val 2 negativeExponent
  map_zero' := rfl
  map_add' _ _ := rfl

theorem negativePart_eq_zero_iff (p : Top A 0) :
    negativePart p = 0 ↔ topCoefficient p = 0 := by
  classical
  constructor
  · intro hp
    have h := congrArg (fun z : Top A 0 => z.val 2 negativeExponent) hp
    simpa [negativePart, Finsupp.filter_apply, AllNegative, negativeExponent,
      topCoefficient] using h
  · intro hp
    apply Subtype.ext
    funext j
    apply Finsupp.ext
    intro e
    by_cases he : AllNegative e
    · simp only [negativePart, Finsupp.filter_apply, if_pos he]
      by_cases hw : Allowed 0 Finset.univ j e
      · obtain ⟨rfl, rfl⟩ := negative_weight_zero j e he hw.1
        exact hp
      · exact p.property j e hw
    · simp [negativePart, Finsupp.filter_apply, he]

theorem top_mem_boundary_iff_coefficient_zero (p : Top A 0) :
    p ∈ (topBoundary : TopFaces A 0 →+ Top A 0).range ↔ topCoefficient p = 0 :=
  (top_mem_boundary_iff p).trans (negativePart_eq_zero_iff p)

/-- The usual increasing Čech top quotient on the four standard charts. -/
abbrev TopQuotient (A : Type*) [AddCommGroup A] (t : ℤ) :=
  Top A t ⧸ (topBoundary : TopFaces A t →+ Top A t).range

/-- The coefficient descends through the actual alternating boundary range. -/
def topTrace : TopQuotient A 0 →+ A :=
  QuotientAddGroup.lift _ topCoefficient (fun p hp =>
    (top_mem_boundary_iff_coefficient_zero p).mp hp)

@[simp] theorem topTrace_mk (p : Top A 0) :
    topTrace (QuotientAddGroup.mk p) = topCoefficient p := rfl

theorem topTrace_injective : Function.Injective (topTrace : TopQuotient A 0 →+ A) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (by
    ext p
    exact top_mem_boundary_iff_coefficient_zero p)

/-- The distinguished normal-form monomial with an arbitrary coefficient. -/
def topGenerator (a : A) : Top A 0 := by
  classical
  refine ⟨fun j => if j = 2 then Finsupp.single negativeExponent a else 0, ?_⟩
  intro j e he
  by_cases hj : j = 2
  · subst j
    by_cases h : e = negativeExponent
    · subst e
      exact False.elim (he ⟨by decide, fun _ _ => Finset.mem_univ _⟩)
    · simp [h, eq_comm]
  · simp [hj]

@[simp] theorem topCoefficient_topGenerator (a : A) :
    topCoefficient (topGenerator a) = a := by
  classical
  simp [topCoefficient, topGenerator]

theorem topTrace_surjective : Function.Surjective (topTrace : TopQuotient A 0 →+ A) := by
  intro a
  exact ⟨QuotientAddGroup.mk (topGenerator a), topCoefficient_topGenerator a⟩

/-- The top Čech quotient of the actual Laurent model is its coefficient group. -/
def topTraceEquiv : TopQuotient A 0 ≃+ A :=
  AddEquiv.ofBijective topTrace ⟨topTrace_injective, topTrace_surjective⟩

theorem topBoundary_surjective_of_positive {t : ℤ} (ht : 0 < t) :
    Function.Surjective (topBoundary : TopFaces A t →+ Top A t) := by
  intro p
  apply (top_mem_boundary_iff p).mpr
  classical
  apply Subtype.ext
  funext j
  apply Finsupp.ext
  intro e
  by_cases he : AllNegative e
  · simp only [negativePart, Finsupp.filter_apply, if_pos he]
    apply p.property j e
    intro h
    exact not_negative_of_positive ht j e h.1 he
  · simp [negativePart, Finsupp.filter_apply, he]

section Scalars

variable {R : Type*} [CommRing R] {S : Finset Vertex}

/-- Scalar multiplication keeps precisely the same allowed homogeneous exponents. -/
def scalarSection (a : R) (p : sections R t S) : sections R t S :=
  ⟨a • p.val, fun j e he => by
    change a * p.val j e = 0
    rw [p.property j e he, mul_zero]⟩

@[simp] theorem scalarSection_coefficient (a : R) (p : sections R t S)
    (j : Fin 3) (e : Exp) : (scalarSection a p).val j e = a * p.val j e := rfl

@[simp] theorem topCoefficient_scalarSection (a : R) (p : Top R 0) :
    topCoefficient (scalarSection a p) = a * topCoefficient p := rfl

end Scalars

end CycleQ2HodgeTwistCech
end

#print axioms CycleQ2HodgeTwistCech.exact_one
#print axioms CycleQ2HodgeTwistCech.exact_two
#print axioms CycleQ2HodgeTwistCech.topTraceEquiv
#print axioms CycleQ2HodgeTwistCech.topBoundary_surjective_of_positive
