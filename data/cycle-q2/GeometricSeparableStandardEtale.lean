import Mathlib.RingTheory.Etale.StandardEtale

/-!
# Explicit finite separable polynomial as standard etale algebra

This is the algebraic etaleness step of the cycle-q2 generic multisection
spreading argument. Given a monic separable polynomial over any commutative
ring, its Bezout identity produces an actual StandardEtalePair with g = 1.
The resulting algebra is etale without assuming its etaleness or passing
through unverified scheme geometry.

It also supplies a map from that algebra to any actual algebra containing
a root, and records that this map evaluates the chosen generator to that
root. This does not prove that the original field-valued parameter map
extends over an open pencil or that the closed cycle projector specializes.
The protected theorem remains unchanged.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

open Polynomial

namespace CycleQ2SeparableStandardEtale

variable {R : Type*} [CommRing R]

/-- The actual standard-etale pair for a monic separable polynomial;
g = 1, so no unspecified localization polynomial is inserted. -/
def pair (f : R[X]) (hm : f.Monic) (hs : f.Separable) : StandardEtalePair R where
  f := f
  monic_f := hm
  g := 1
  cond := by
    obtain ⟨a, b, hab⟩ := hs
    refine ⟨b, a, 0, ?_⟩
    simpa only [pow_zero, mul_comm, add_comm] using hab

/-- Etaleness is derived from the standard-etale construction. -/
theorem pair_isEtale (f : R[X]) (hm : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (pair f hm hs).Ring := inferInstance

variable {S : Type*} [CommRing S] [Algebra R S]

/-- The original root of f determines an algebra hom from the concrete
standard-etale presentation to its containing algebra. -/
def liftRoot (f : R[X]) (hm : f.Monic) (hs : f.Separable)
    (x : S) (hx : aeval x f = 0) :
    (pair f hm hs).Ring →ₐ[R] S :=
  (pair f hm hs).lift x ⟨hx, by simp [pair]⟩

/-- The standard-etale generator really maps to the specified root. -/
@[simp] theorem liftRoot_X (f : R[X]) (hm : f.Monic) (hs : f.Separable)
    (x : S) (hx : aeval x f = 0) :
    liftRoot f hm hs x hx (pair f hm hs).X = x := by
  exact (pair f hm hs).lift_X x ⟨hx, by simp [pair]⟩

end CycleQ2SeparableStandardEtale

end

#print axioms CycleQ2SeparableStandardEtale.pair_isEtale
#print axioms CycleQ2SeparableStandardEtale.liftRoot_X
