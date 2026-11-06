import HodgeComputer.Constructions.PolarCubic.Differential
import Mathlib.Tactic.LinearCombination

/-! Passage from the polynomial differential identity to the rational
covering map. All normal-chart and denominator assumptions are explicit.
The normalization is explained in solution.md. The cyclic construction is
due to hodgepodgeconjecture; the transitive adaptation was prepared for fqlx
with OpenAI Codex assistance. This reverse-edge specialization was prepared
for benediamond with OpenAI Codex assistance. -/
noncomputable section
namespace PolarCubicMap
variable {R K : Type*} [CommRing R] [Field K] [CharZero K]

/-- The polynomial identity supplies the invariant differential with its
exact scalar factor, after evaluation on the source cubic. -/
theorem differential_from_identity
    (ρ : R →+* K) (P Q : R → R) (D : Derivation ℤ K K)
    (u h q j : R) (hu : ρ u=0) (hg : ρ (P u)≠0)
    (hh : ρ h≠0) (hj : ρ j≠0)
    (Dh : D (ρ h)=ρ (Q h)-ρ (Q u)/ρ (P u)*ρ (P h))
    (Dq : D (ρ q)=ρ (Q q)-ρ (Q u)/ρ (P u)*ρ (P q))
    (identity : h*(P u*Q q-Q u*P q)-2*q*(P u*Q h-Q u*P h)+3*j=
      u*(P h*Q q-Q h*P q)) :
    D (ρ q/(ρ h)^2)/(2*(-ρ j/(2*(ρ h)^3)))=3/ρ (P u) := by
  have hi := congrArg ρ identity
  simp only [map_add,map_sub,map_mul,map_ofNat,hu,zero_mul] at hi
  rw [Derivation.leibniz_div,Derivation.leibniz_pow,Dh,Dq]
  simp only [smul_eq_mul,nsmul_eq_mul]
  norm_num
  field_simp
  linear_combination -hi

open PolarCovariants MvPolynomial
/-- This specializes the abstract differential lemma to the checked integral
covariants of every six-coefficient cubic, without assuming an injective
evaluation map or differentiating the specialized coefficient. -/
theorem differential
    (a b c d e f : R) (ρ : Affine R →+* K) (D : Derivation ℤ K K)
    (hu : ρ (Upoly a b c d e f)=0)
    (hg : ρ (pderiv 0 (Upoly a b c d e f))≠0)
    (hh : ρ (Hpoly a b c d e f)≠0) (hj : ρ (Jpoly a b c d e f)≠0)
    (compatible : ∀ p : Affine R, D (ρ p)=ρ (pderiv 1 p)-
      ρ (pderiv 1 (Upoly a b c d e f))/ρ (pderiv 0 (Upoly a b c d e f))*ρ (pderiv 0 p)) :
    D (ρ (Thetapoly a b c d e f)/(ρ (Hpoly a b c d e f))^2)/
      (2*(-ρ (Jpoly a b c d e f)/(2*(ρ (Hpoly a b c d e f))^3)))=
        3/ρ (pderiv 0 (Upoly a b c d e f)) :=
  differential_from_identity ρ (pderiv 0) (pderiv 1) D
    (Upoly a b c d e f) (Hpoly a b c d e f) (Thetapoly a b c d e f)
    (Jpoly a b c d e f) hu hg hh hj (compatible _) (compatible _)
    (relative_identity a b c d e f)

end PolarCubicMap
#print axioms PolarCubicMap.differential
