import HodgeComputer.Constructions.FiniteAlgebra.AdjoinRootSpecialization
import HodgeComputer.Constructions.FiniteAlgebra.FiniteAlgebraInverse

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

namespace AdjoinRootSpecialization

open Polynomial Module
variable {R K : Type*} [CommRing R] [Field K]

/-- Units in a finite free monic quotient can be lifted from the good fiber.
No irreducibility of the degree-27 polynomial is required. -/
theorem isUnit_of_specialize_isUnit (f : R →+* K)
    (p : Polynomial (RegularSpecialization.Coefficients f)) (hp : p.Monic)
    (x : AdjoinRoot p)
    (hx : IsUnit (specialize (RegularSpecialization.specialize f) p x)) : IsUnit x := by
  let e := RegularSpecialization.specialize f
  have hd : (p.map e).natDegree = p.natDegree := hp.natDegree_map e
  let b := basis p hp rfl
  let bs := basis (p.map e) (hp.map e) hd
  apply FiniteAlgebraInverse.isUnit_of_leftMulMatrix b x
  rw [RegularSpecialization.isUnit_det_iff]
  change ((Algebra.leftMulMatrix (basis p hp rfl) x).map e).det ≠ 0
  rw [map_leftMulMatrix e p hp rfl hd]
  exact (Matrix.isUnit_iff_isUnit_det _).mp (hx.map (Algebra.leftMulMatrix bs).toMonoidHom) |>.ne_zero

/-- Version with the specialized polynomial named explicitly. -/
theorem isUnit_of_map_isUnit (f : R →+* K)
    (p : Polynomial (RegularSpecialization.Coefficients f)) (hp : p.Monic)
    (q : Polynomial K) (hq : q = p.map (RegularSpecialization.specialize f))
    (hdiv : q ∣ p.map (RegularSpecialization.specialize f)) (x : AdjoinRoot p)
    (hx : IsUnit (AdjoinRoot.map (RegularSpecialization.specialize f) p q hdiv x)) :
    IsUnit x := by
  subst q
  exact isUnit_of_specialize_isUnit f p hp x hx

/-- A concrete Bezout identity directly gives the specialized algebra unit. -/
theorem isUnit_mk_of_bezout {S : Type*} [CommRing S] (p g h q : S[X])
    (hbez : g*h-p*q=1) : IsUnit (AdjoinRoot.mk p g) := by
  apply isUnit_iff_exists_inv.mpr
  refine ⟨AdjoinRoot.mk p h, ?_⟩
  have he := congrArg (AdjoinRoot.mk p) hbez
  simpa only [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero, map_one] using he

end AdjoinRootSpecialization

