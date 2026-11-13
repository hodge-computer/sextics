import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Algebra.Module.LinearMap.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-! Reusable finite-algebra and contact calculus extracted from `HeadOfNaps`’
accepted quadric-contact-broken (#122) and holdout-q2 (#124) proofs.
See this directory’s README for hypotheses, entry points, and attribution. -/

noncomputable section
namespace QuadricContactFraction
variable {P F : Type*} [CommRing P] [IsDomain P] [Field F]
  [Algebra ℚ P] [Algebra P F] [IsFractionRing P F]
  [Algebra ℚ F] [IsScalarTower ℚ P F]

private def num (x : F) : P := Classical.choose (IsFractionRing.div_surjective P x)
private def den (x : F) : P := Classical.choose (Classical.choose_spec (IsFractionRing.div_surjective P x))
omit [IsDomain P] [Algebra ℚ P] [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem den_mem (x : F) : den (P := P) x ∈ nonZeroDivisors P :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).1
omit [IsDomain P] [Algebra ℚ P] [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem repr_eq (x : F) :
    algebraMap P F (num x) / algebraMap P F (den x) = x :=
  (Classical.choose_spec (Classical.choose_spec (IsFractionRing.div_surjective P x))).2
omit [Algebra ℚ P] [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem den_ne (x : F) : algebraMap P F (den x) ≠ 0 :=
  IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (den_mem x)
omit [Algebra ℚ P] [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem map_ne {x : P} (hx : x ≠ 0) : algebraMap P F x ≠ 0 := by
  exact fun h => hx ((IsFractionRing.injective P F) (by simpa using h))

private def quotientD (D : Derivation ℚ P P) (x : F) : F :=
  (algebraMap P F (D (num x)) * algebraMap P F (den x) -
    algebraMap P F (num x) * algebraMap P F (D (den x))) /
    algebraMap P F (den x) ^ 2

omit [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem quotientD_div (D : Derivation ℚ P P) (a b : P) (hb : b ≠ 0) :
    quotientD D (algebraMap P F a / algebraMap P F b) =
      (algebraMap P F (D a) * algebraMap P F b -
        algebraMap P F a * algebraMap P F (D b)) / algebraMap P F b ^ 2 := by
  let x := algebraMap P F a / algebraMap P F b
  have hd := den_ne (P := P) x
  have hb' := map_ne (F := F) hb
  have hcross : num x * b = a * den x := by
    apply IsFractionRing.injective P F
    simpa only [map_mul] using (div_eq_div_iff hd hb').mp (repr_eq (P := P) x)
  have hdcross := congrArg (fun p : P => algebraMap P F (D p)) hcross
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul] at hdcross
  have hcross' := congrArg (algebraMap P F) hcross
  simp only [map_mul] at hcross'
  change (algebraMap P F (D (num x)) * algebraMap P F (den x) -
    algebraMap P F (num x) * algebraMap P F (D (den x))) /
    algebraMap P F (den x)^2 = _
  field_simp
  linear_combination
    algebraMap P F (den x) * algebraMap P F b * hdcross -
    (algebraMap P F b * algebraMap P F (D (den x)) +
      algebraMap P F (den x) * algebraMap P F (D b)) * hcross'

omit [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem quotientD_map (D : Derivation ℚ P P) (a : P) :
    quotientD D (algebraMap P F a) = algebraMap P F (D a) := by
  have h := quotientD_div (F := F) D a 1 one_ne_zero
  simpa using h

omit [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem quotientD_add (D : Derivation ℚ P P) (x y : F) :
    quotientD D (x+y) = quotientD D x + quotientD D y := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c,d,hd,rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b + algebraMap P F c / algebraMap P F d =
      algebraMap P F (a*d+c*b) / algebraMap P F (b*d) := by
    simp only [map_add, map_mul]
    field_simp
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_add, map_mul, Derivation.leibniz, smul_eq_mul]
  field_simp
  ring

omit [Algebra ℚ F] [IsScalarTower ℚ P F] in
private theorem quotientD_mul (D : Derivation ℚ P P) (x y : F) :
    quotientD D (x*y) = x * quotientD D y + y * quotientD D x := by
  obtain ⟨a,b,hb,rfl⟩ := IsFractionRing.div_surjective P x
  obtain ⟨c,d,hd,rfl⟩ := IsFractionRing.div_surjective P y
  have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
  have hd0 : d ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hd
  have hb' := map_ne (F := F) hb0
  have hd' := map_ne (F := F) hd0
  have he : algebraMap P F a / algebraMap P F b * (algebraMap P F c / algebraMap P F d) =
      algebraMap P F (a*c) / algebraMap P F (b*d) := by
    simp only [map_mul, mul_div_mul_comm]
  rw [he, quotientD_div D _ _ (mul_ne_zero hb0 hd0), quotientD_div D _ _ hb0,
    quotientD_div D _ _ hd0]
  simp only [map_mul, Derivation.leibniz, map_add, smul_eq_mul]
  field_simp
  ring

/-- A derivation on a rational algebra extends to its fraction field. Its action
is proved from the quotient rule; no derivative of a chosen representative is assumed. -/
def extend (D : Derivation ℚ P P) : Derivation ℚ F F :=
  Derivation.mk'
    ({ toFun := quotientD D
       map_zero' := by simpa using quotientD_map (F := F) D 0
       map_add' := quotientD_add D } : F →+ F).toRatLinearMap
    (by intro x y; exact quotientD_mul D x y)

@[simp] theorem extend_map (D : Derivation ℚ P P) (a : P) :
    extend (F := F) D (algebraMap P F a) = algebraMap P F (D a) :=
  quotientD_map D a

 theorem extend_div (D : Derivation ℚ P P) (a b : P) (hb : b ≠ 0) :
    extend (F := F) D (algebraMap P F a / algebraMap P F b) =
      (algebraMap P F (D a) * algebraMap P F b -
        algebraMap P F a * algebraMap P F (D b)) / algebraMap P F b ^ 2 :=
  quotientD_div D a b hb

end QuadricContactFraction
#print axioms QuadricContactFraction.extend_map
#print axioms QuadricContactFraction.extend_div

