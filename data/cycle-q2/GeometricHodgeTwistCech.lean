import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
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

end CycleQ2HodgeTwistCech
end

#print axioms CycleQ2HodgeTwistCech.exact_one
#print axioms CycleQ2HodgeTwistCech.exact_two
