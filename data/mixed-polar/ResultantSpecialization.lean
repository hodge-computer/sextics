import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! A specialization test valid for every chosen root of a quadratic.
This is used for the mixed-polar shear: at the good physical specialization
both roots coalesce at zero, and each covariant has a nonzero value there.
The proof uses a fixed-size resultant and does not evaluate rational functions
at poles. Prepared with OpenAI Codex assistance. -/
noncomputable section
namespace MixedPolarResultant
open Polynomial
variable {R K C : Type*} [CommRing R] [Field K] [Field C]

theorem eval_ne_zero_of_double_root_specialization
    (toField : R →+* K) (toPoint : R →+* C)
    (kernel : ∀ r, toField r=0 → toPoint r=0)
    (q P : Polynomial R) (k : K) (u : C)
    (hq : q.natDegree≤2)
    (hroot : q.eval₂ toField k=0)
    (hspecial : q.map toPoint=Polynomial.C u*Polynomial.X^2)
    (hu : u≠0) (hP : P.eval₂ toPoint 0≠0) :
    P.eval₂ toField k≠0 := by
  intro hz
  let n := P.natDegree
  have hqField : (q.map toField).natDegree≤2 :=
    (natDegree_map_le).trans hq
  have hPField : (P.map toField).natDegree≤n := natDegree_map_le
  obtain ⟨s,t,hs,ht,hbezout⟩ := exists_mul_add_mul_eq_C_resultant
    (q.map toField) (P.map toField) hqField hPField (Or.inl (by decide : 2≠0))
  have hzero : toField (q.resultant P 2 n)=0 := by
    have h := congrArg (Polynomial.eval k) hbezout
    simp only [eval_add,eval_mul,eval_C,eval_map,hroot,hz,zero_mul,zero_add] at h
    rw [resultant_map_map] at h
    exact h.symm
  have hpointZero := kernel (q.resultant P 2 n) hzero
  have hPPoint : (P.map toPoint).natDegree≤n := natDegree_map_le
  have hpoint : toPoint (q.resultant P 2 n)=u^n*(P.eval₂ toPoint 0)^2 := by
    rw [← resultant_map_map,hspecial,resultant_C_mul_left]
    rw [resultant_X_pow_left _ 2 n hPPoint]
    rw [coeff_zero_eq_eval_zero,eval_map]
  rw [hpoint] at hpointZero
  exact (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hP)) hpointZero

end MixedPolarResultant
#print axioms MixedPolarResultant.eval_ne_zero_of_double_root_specialization
