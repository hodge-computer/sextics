import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import Mathlib.Tactic.LinearCombination

/-! First variation of a map to a Weierstrass cubic.

The curve identity and relative differential identity give the exact
moving-map correction. The jet version works at a fixed parameter value;
it does not assume a parameter derivation on a specialized function field.
Applications supply the curve, tangent, and first-variation identities.

Extracted from hodgepodgeconjecture's cycle-three construction,
prepared with OpenAI Codex assistance. The residue framework builds on
fqlx and the Hodge Computer collaborators. Original declaration namespaces
are retained; do not import the accepted copy alongside this module. -/

noncomputable section
namespace CycleMovingMap

variable {K : Type*} [Field K] [CharZero K]

/-- A version using only the first parameter derivatives at a fixed parameter
value. It therefore applies after specializing the auxiliary coefficient to
one: no parameter derivation on the specialized function field is assumed. -/
theorem moving_weierstrass_jet
    (D : Derivation ℤ K K) (ξ η a b g m ξdot ηdot adot bdot gdot : K)
    (hg : g ≠ 0) (hη : η ≠ 0)
    (curve : η^2 = ξ^3+a*ξ+b) (Da : D a = 0) (Db : D b = 0)
    (differential : D ξ / (2*η) = m/g)
    (curve_jet : 2*η*ηdot = (3*ξ^2+a)*ξdot+adot*ξ+bdot)
    (differential_jet :
      g^2*(2*η*D ξdot-2*D ξ*ηdot) = -4*η^2*m*gdot) :
    m*gdot/g^2 + D (ξdot/(2*η)) = m*(adot*ξ+bdot)/(2*η^2*g) := by
  have hD := congrArg D curve
  simp only [Derivation.leibniz_pow, Derivation.leibniz, map_add,
    smul_eq_mul, nsmul_eq_mul, Da, Db] at hD
  norm_num at hD
  have hD2 : D (2:K) = 0 := D.map_natCast 2
  rw [Derivation.leibniz_div, Derivation.leibniz]
  simp only [hD2, smul_eq_mul]
  field_simp at differential ⊢
  apply (mul_left_cancel₀ hη)
  linear_combination
    (g^2*D ξ)*curve_jet-(g^2*ξdot)*hD+
    η*differential_jet+(g*(adot*ξ+bdot))*differential

/-- The pole-two source on the original normal chart, expressed as the
Jacobian source and the exact moving-map correction. In the cycle-three
application `m=3` and `gdot/g` is the original cubic residue source. -/
theorem residue_source_from_jet
    (D : Derivation ℤ K K) (ξ η a b g m ξdot ηdot adot bdot gdot : K)
    (hg : g ≠ 0) (hη : η ≠ 0) (hm : m ≠ 0)
    (curve : η^2 = ξ^3+a*ξ+b) (Da : D a = 0) (Db : D b = 0)
    (differential : D ξ / (2*η) = m/g)
    (curve_jet : 2*η*ηdot = (3*ξ^2+a)*ξdot+adot*ξ+bdot)
    (differential_jet :
      g^2*(2*η*D ξdot-2*D ξ*ηdot) = -4*η^2*m*gdot) :
    gdot/g=(adot*ξ+bdot)/(2*η^2)-(g/m)*D (ξdot/(2*η)) := by
  have h := moving_weierstrass_jet D ξ η a b g m ξdot ηdot adot bdot gdot
    hg hη curve Da Db differential curve_jet differential_jet
  field_simp at h ⊢
  linear_combination h

/-- The exact differential correction for a map that varies with a parameter.
`D` differentiates along the cubic, and `E` differentiates the parameter while
keeping the source tangent coordinate fixed. The constant `m` is the factor in
the pullback of the invariant differential. -/
theorem moving_weierstrass_source
    (D E : Derivation ℤ K K) (ξ η a b g m : K)
    (hg : g ≠ 0) (hη : η ≠ 0)
    (curve : η^2 = ξ^3+a*ξ+b)
    (Da : D a = 0) (Db : D b = 0) (Em : E m = 0)
    (mixed : E (D ξ) = D (E ξ))
    (differential : D ξ / (2*η) = m/g) :
    m * E g / g^2 + D (E ξ / (2*η)) =
      m * (E a * ξ + E b) / (2*η^2*g) := by
  have hD := congrArg D curve
  have hE := congrArg E curve
  simp only [Derivation.leibniz_pow, Derivation.leibniz, map_add,
    smul_eq_mul, nsmul_eq_mul, Da, Db] at hD hE
  norm_num at hD hE
  have hD2 : D (2:K) = 0 := D.map_natCast 2
  have hE2 : E (2:K) = 0 := E.map_natCast 2
  have hdiff := congrArg E differential
  simp only [Derivation.leibniz_div, Derivation.leibniz,
    hE2, smul_eq_mul, Em, mixed] at hdiff
  rw [Derivation.leibniz_div, Derivation.leibniz]
  simp only [hD2, smul_eq_mul]
  field_simp at differential hdiff ⊢
  apply (mul_left_cancel₀ hη)
  linear_combination
    (g^2 * D ξ) * hE - (g^2 * E ξ) * hD +
    η * hdiff + (g*(E a*ξ+E b)) * differential

end CycleMovingMap

#print axioms CycleMovingMap.moving_weierstrass_jet
#print axioms CycleMovingMap.residue_source_from_jet
#print axioms CycleMovingMap.moving_weierstrass_source
