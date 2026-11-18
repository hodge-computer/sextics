import Proposal.HomogeneousSubstitution
import Proposal.HomogeneousFibre

noncomputable section
namespace QuadricContactClearing
open MvPolynomial

abbrev Regular := RegularSpecialization.Coefficients goodParameters
abbrev ActivePoly := MvPolynomial (Fin 4) Regular

def activeImage (v : Fin 4 → BasePoly) : ActivePoly →+* FunctionField :=
  eval₂Hom regularParameterMap (fun j => baseMap (v j))

/-- All finitely many homogeneous active polynomials admit simultaneous polynomial
representatives after one homogeneous clearing of their regular coefficients.
This applies to a degree-27 determinant and its four degree-27 numerators. -/
theorem exists_active_homogeneous_representatives {ι : Type*} [Fintype ι]
    (P : ι → ActivePoly) (h : ℕ) (hP : ∀ i, (P i).IsHomogeneous h)
    (v : Fin 4 → BasePoly) (hv : ∀ j, (v j).IsHomogeneous 2) :
    ∃ (n : ℕ) (D : BasePoly) (N : ι → BasePoly),
      D.IsHomogeneous (2*n) ∧ goodBase D ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*(n+h))) ∧
      (∀ i, baseMap (N i) = baseMap D * activeImage v (P i)) := by
  classical
  let I := Σ i : ι, ↥(P i).support
  let z : I → Regular := fun k => (P k.1).coeff k.2.val
  obtain ⟨n, D, U, hD, hDgood, hU, hrep⟩ := exists_regular_homogeneous_representatives z
  let term (s : Fin 4 →₀ ℕ) : BasePoly := ∏ j ∈ s.support, v j ^ s j
  let N : ι → BasePoly := fun i => ∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val
  refine ⟨n,D,N,hD,hDgood,?_,?_⟩
  · intro i
    apply IsHomogeneous.sum
    intro s hs
    have ht : (term s.val).IsHomogeneous (2*h) := by
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
      (fun s => regularParameterMap ((P i).coeff s) * ∏ j ∈ s.support, baseMap (v j) ^ s j)

def activeFibre (v : Fin 4 → BasePoly) : ActivePoly →+* BasePoly :=
  eval₂Hom (C.comp (RegularSpecialization.specialize goodParameters)) (fun j => ratioBase (v j))

/-- Simultaneous active clearing with its exact coefficient-specialized fibre. -/
theorem exists_active_representatives_with_fibre {ι : Type*} [Fintype ι]
    (P : ι → ActivePoly) (h : ℕ) (hP : ∀ i, (P i).IsHomogeneous h)
    (v : Fin 4 → BasePoly) (hv : ∀ j, (v j).IsHomogeneous 2) :
    ∃ (n : ℕ) (q : Parameters) (D : BasePoly) (N : ι → BasePoly),
      HomogeneousDatum q n D ∧ goodParameters q ≠ 0 ∧
      (∀ i, (N i).IsHomogeneous (2*(n+h))) ∧
      (∀ i, baseMap (N i) = baseMap D * activeImage v (P i)) ∧
      (∀ i, ratioBase (N i) = C (goodParameters q) * ac^n * activeFibre v (P i)) := by
  classical
  let I := Σ i : ι, ↥(P i).support
  let z : I → Regular := fun k => (P k.1).coeff k.2.val
  obtain ⟨n,q,D,U,hD,hq,hU,hfibre,hrep⟩ := exists_regular_representatives_with_fibre z
  let term (s : Fin 4 →₀ ℕ) : BasePoly := ∏ j ∈ s.support, v j ^ s j
  let N : ι → BasePoly := fun i => ∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val
  refine ⟨n,q,D,N,hD,hq,?_,?_,?_⟩
  · intro i
    apply IsHomogeneous.sum
    intro s hs
    have ht : (term s.val).IsHomogeneous (2*h) := by
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
      (fun s => regularParameterMap ((P i).coeff s) * ∏ j ∈ s.support, baseMap (v j) ^ s j)
  · intro i
    change ratioBase (∑ s : ↥(P i).support, U ⟨i,s⟩ * term s.val) = _
    simp only [map_sum, map_mul]
    calc
      _ = ∑ s : ↥(P i).support, (C (goodParameters q) * ac^n) *
          (C (RegularSpecialization.specialize goodParameters (z ⟨i,s⟩)) * ratioBase (term s.val)) := by
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
          (fun s => C (RegularSpecialization.specialize goodParameters ((P i).coeff s)) *
            ∏ j ∈ s.support, ratioBase (v j) ^ s j)

end QuadricContactClearing

#print axioms QuadricContactClearing.exists_active_homogeneous_representatives
#print axioms QuadricContactClearing.exists_active_representatives_with_fibre
