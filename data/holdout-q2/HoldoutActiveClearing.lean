import Proposal.HoldoutSubstitution

noncomputable section
namespace HoldoutQ2.Clearing
open MvPolynomial
variable {k : ℂ}

abbrev Regular (k : ℂ) := RegularSpecialization.Coefficients (goodParameters k)
abbrev ActivePoly (k : ℂ) := MvPolynomial (Fin 4) (Regular k)

def activeImage (k : ℂ) (v : Fin 4 → BasePoly) : ActivePoly k →+* FunctionField :=
  eval₂Hom (regularParameterMap k) (fun j => baseMap (v j))

/-- All finitely many homogeneous active polynomials admit simultaneous polynomial
representatives after one homogeneous clearing of their regular coefficients.
The degrees may vary with the family index, so the same factor clears a
degree-27 determinant and four degree-30 pole-two numerators. -/
theorem exists_active_homogeneous_representatives {ι : Type*} [Fintype ι]
    (P : ι → ActivePoly k) (h : ι → ℕ) (hP : ∀ i, (P i).IsHomogeneous (h i))
    (v : Fin 4 → BasePoly) (hv : ∀ j, (v j).IsHomogeneous 2) :
    ∃ (n : ℕ) (D : BasePoly) (N : ι → BasePoly),
      D.IsHomogeneous (2*n) ∧ goodBase k D ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*(n+h i))) ∧
      (∀ i, baseMap (N i) = baseMap D * activeImage k v (P i)) := by
  classical
  let I := Σ i : ι, ↥(P i).support
  let z : I → Regular k := fun k => (P k.1).coeff k.2.val
  obtain ⟨n, D, U, hD, hDgood, hU, hrep⟩ := exists_regular_homogeneous_representatives z
  let term (s : Fin 4 →₀ ℕ) : BasePoly := ∏ j ∈ s.support, v j ^ s j
  let N : ι → BasePoly := fun i => ∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val
  refine ⟨n,D,N,hD,hDgood,?_,?_⟩
  · intro i
    apply IsHomogeneous.sum
    intro s hs
    have ht : (term s.val).IsHomogeneous (2*h i) := by
      have ht' := IsHomogeneous.prod s.val.support (fun j => v j ^ s.val j)
        (fun j => 2 * s.val j) (fun j _ => (hv j).pow (s.val j))
      have hd := (hP i).degree_eq_sum_deg_support s.property
      simpa only [term, ← Finset.mul_sum, ← hd] using ht'
    have hh := (hU ⟨i,s⟩).mul ht
    convert hh using 1 <;> omega
  · intro i
    change baseMap (∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val) = _
    simp only [map_sum, map_mul, hrep, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp only [activeImage, coe_eval₂Hom, eval₂_eq, term, map_prod, map_pow, z]
    exact Finset.sum_coe_sort (P i).support
      (fun s => regularParameterMap k ((P i).coeff s) * ∏ j ∈ s.support, baseMap (v j) ^ s j)

def activeFibre (k : ℂ) (v : Fin 4 → BasePoly) : ActivePoly k →+* BasePoly :=
  eval₂Hom (C.comp (RegularSpecialization.specialize (goodParameters k))) (fun j => ratioBase k (v j))

/-- Simultaneous active clearing with its exact coefficient-specialized fibre. -/
theorem exists_active_representatives_with_fibre {ι : Type*} [Fintype ι]
    (P : ι → ActivePoly k) (h : ι → ℕ) (hP : ∀ i, (P i).IsHomogeneous (h i))
    (v : Fin 4 → BasePoly) (hv : ∀ j, (v j).IsHomogeneous 2) :
    ∃ (n : ℕ) (q : Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodParameters k q ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*(n+h i))) ∧
      (∀ i, baseMap (N i) = baseMap D * activeImage k v (P i)) ∧
      (∀ i, ratioBase k (N i) = C (goodParameters k q) * xa^n * activeFibre k v (P i)) := by
  classical
  let I := Σ i : ι, ↥(P i).support
  let z : I → Regular k := fun k => (P k.1).coeff k.2.val
  obtain ⟨n,q,D,U,hD,hq,hU,hfibre,hrep⟩ := exists_regular_representatives_with_fibre z
  let term (s : Fin 4 →₀ ℕ) : BasePoly := ∏ j ∈ s.support, v j ^ s j
  let N : ι → BasePoly := fun i => ∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val
  refine ⟨n,q,D,N,hD,hq,?_,?_,?_⟩
  · intro i
    apply IsHomogeneous.sum
    intro s hs
    have ht : (term s.val).IsHomogeneous (2*h i) := by
      have ht' := IsHomogeneous.prod s.val.support (fun j => v j ^ s.val j)
        (fun j => 2 * s.val j) (fun j _ => (hv j).pow (s.val j))
      have hd := (hP i).degree_eq_sum_deg_support s.property
      simpa only [term, ← Finset.mul_sum, ← hd] using ht'
    have hh := (hU ⟨i,s⟩).mul ht
    convert hh using 1 <;> omega
  · intro i
    change baseMap (∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val) = _
    simp only [map_sum, map_mul, hrep, mul_assoc]
    rw [← Finset.mul_sum]
    congr 1
    simp only [activeImage, coe_eval₂Hom, eval₂_eq, term, map_prod, map_pow, z]
    exact Finset.sum_coe_sort (P i).support
      (fun s => regularParameterMap k ((P i).coeff s) * ∏ j ∈ s.support, baseMap (v j) ^ s j)
  · intro i
    change ratioBase k (∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val) = _
    simp only [map_sum, map_mul]
    calc
      _ = ∑ s : ↥(P i).support, (C (goodParameters k q) * xa^n) *
          (C (RegularSpecialization.specialize (goodParameters k) (z ⟨i,s⟩)) * ratioBase k (term s.val)) := by
        apply Finset.sum_congr rfl
        intro s hs
        rw [hfibre]
        simp only [map_mul]
        ring
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        simp only [activeFibre, coe_eval₂Hom, eval₂_eq, RingHom.comp_apply,
          term, map_prod, map_pow, z]
        exact Finset.sum_coe_sort (P i).support
          (fun s => C (RegularSpecialization.specialize (goodParameters k) ((P i).coeff s)) *
            ∏ j ∈ s.support, ratioBase k (v j) ^ s j)


/-- The denominator/numerator packaging used by the pole-two cubic field.
The common coefficient factor `u` does not change the relative degree 3. -/
theorem exists_q2_representatives_with_fibre
    (D : ActivePoly k) (N : Fin 4 → ActivePoly k) (d : ℕ)
    (hD : D.IsHomogeneous d) (hN : ∀ i, (N i).IsHomogeneous (d+3))
    (v : Fin 4 → BasePoly) (hv : ∀ j, (v j).IsHomogeneous 2) :
    ∃ (n : ℕ) (q : Parameters) (u Q : BasePoly) (P : Fin 4 → BasePoly),
      HomogeneousDatum q n u ∧ goodParameters k q ≠ 0 ∧
      Q.IsHomogeneous (2*(n+d)) ∧
      (∀ i, (P i).IsHomogeneous (2*(n+d+3))) ∧
      baseMap Q = baseMap u * activeImage k v D ∧
      (∀ i, baseMap (P i) = baseMap u * activeImage k v (N i)) ∧
      ratioBase k Q = C (goodParameters k q) * xa^n * activeFibre k v D ∧
      (∀ i, ratioBase k (P i) =
        C (goodParameters k q) * xa^n * activeFibre k v (N i)) := by
  let family : Option (Fin 4) → ActivePoly k := fun i => i.elim D N
  let degree : Option (Fin 4) → ℕ := fun i => i.elim d (fun _ => d+3)
  have hfamily : ∀ i, (family i).IsHomogeneous (degree i) := by
    intro i
    cases i with
    | none => exact hD
    | some j => exact hN j
  obtain ⟨n,q,u,P,hu,hq,hPh,hrep,hfiber⟩ :=
    exists_active_representatives_with_fibre family degree hfamily v hv
  refine ⟨n,q,u,P none,fun i => P (some i),hu,hq,hPh none,?_,
    hrep none,fun i => hrep (some i),hfiber none,fun i => hfiber (some i)⟩
  intro i
  simpa only [degree, Option.elim_some, Nat.add_assoc] using hPh (some i)

end HoldoutQ2.Clearing

#print axioms HoldoutQ2.Clearing.exists_active_homogeneous_representatives
#print axioms HoldoutQ2.Clearing.exists_active_representatives_with_fibre

#print axioms HoldoutQ2.Clearing.exists_q2_representatives_with_fibre
