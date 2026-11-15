import Proposal.PhysicalJacobianGeometry
import Mathlib.RingTheory.Derivation.Basic

/-! Generic derivative calculation before specializing the coefficient field.
This keeps the physical quadratic extension opaque during the rational
Jacobian calculation and retains an arbitrary last coordinate u. -/
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
namespace MixedPolarJacobianCalculus
open MixedPolarJacobianGeometry
variable {K : Type*} [Field K]
local instance : Algebra ℤ K := Ring.toIntAlgebra _

def coordinates (p : Fin 6 → K) (u : K) : Fin 5 → K :=
  ![p 2^2*(p 3/p 0)^6,(p 4/p 1)/(p 3/p 0),
    (p 5/p 2)/(p 3/p 0),p 2^2,p 2^4*u]

theorem jacobian_formula (D : Fin 5 → Derivation ℤ K K)
    (p f : Fin 6 → K) (u : K)
    (h0 : p 0≠0) (h1 : p 1≠0) (h2 : p 2≠0) (h3 : p 3≠0) (hf : f 0≠0)
    (hD : ∀ i j,D i (p j)=(if j=i.succ then 1 else 0)-
      f i.succ/f 0*(if j=0 then 1 else 0)) :
    (fun j i => D i (coordinates p u j))=rawMatrix p f (fun i=>D i u) u := by
  have hn (i : Fin 5) (n : ℕ) [n.AtLeastTwo] : D i (ofNat(n):K)=0 :=
    (D i).map_natCast n
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [coordinates,rawMatrix,
      Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,Matrix.cons_val_one,Matrix.cons_val,
      Derivation.leibniz_div,Derivation.leibniz_pow,Derivation.leibniz,
      smul_eq_mul,nsmul_eq_mul,hn,hD] <;>
    norm_num [Fin.ext_iff,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Matrix.head_cons,Matrix.tail_cons,Derivation.leibniz,Derivation.leibniz_pow,
      Derivation.leibniz_div,Derivation.leibniz_inv,
      smul_eq_mul,nsmul_eq_mul,hD] <;> try field_simp <;> ring
  all_goals first | rfl | simp
end MixedPolarJacobianCalculus
#print axioms MixedPolarJacobianCalculus.jacobian_formula
