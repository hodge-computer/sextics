import Proposal.PhysicalJacobianGeometry

/-! The determinant-to-volume identity is calculated over an abstract field,
so normalization of the concrete algebraic extension does not enlarge this
rational identity. The last row remains arbitrary. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace MixedPolarJacobianVolumeIdentity
open scoped BigOperators
open MixedPolarJacobianGeometry
variable {K : Type*} [Field K] [CharZero K]

def weight (p : Fin 6 → K) : K := p 3^3/(4*p 0^5*p 1^2*p 2^2)
def paired (p f : Fin 6 → K) : K := p 0*f 0+p 3*f 3
def secondPaired (p f : Fin 6 → K) : K := p 1*f 1+p 4*f 4
def volumeVector (p f : Fin 6 → K) : Fin 5 → K :=
  ![weight p*paired p f*p 1,0,-weight p*secondPaired p f*p 3,
    weight p*paired p f*p 4,0]

theorem determinant_volume (p f : Fin 6 → K) (z : Fin 5 → K) (u : K)
    (h0 : p 0≠0) (h1 : p 1≠0) (h2 : p 2≠0) (h3 : p 3≠0) (hf : f 0≠0) :
    f 0*(rawMatrix p f z u).det=
      -48*(p 2^2)^4*(∑ i,volumeVector p f i*z i) := by
  rw [raw_determinant p f z u h0 h1 h2 h3 hf]
  simp only [volumeVector,weight,paired,secondPaired,
    Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.reduceSucc,
    Finset.univ_eq_empty,Finset.sum_empty,zero_mul,add_zero,zero_add]
  field_simp
  ring

/-- The rational volume vector commutes with every field embedding. -/
theorem volumeVector_map {F : Type*} [Field F] (φ : F →+* K)
    (p f : Fin 6 → F) :
    volumeVector (fun i=>φ (p i)) (fun i=>φ (f i))=
      fun i=>φ (volumeVector p f i) := by
  funext i
  fin_cases i <;>
    norm_num [volumeVector,weight,paired,secondPaired,map_div₀,map_mul,map_pow,map_add,
      map_ofNat,map_zero,map_neg]

end MixedPolarJacobianVolumeIdentity
#print axioms MixedPolarJacobianVolumeIdentity.determinant_volume
