import Proposal.SeedCechThetaData

/-!
# Regularity of the seed linkage

The linkage element restricts to a unit on the seed fiber and acts injectively.
-/

set_option Elab.async false

/- Component: continuation_3/SeedLinkageRegular.lean -/
section
/-!
# Regularity of the actual linkage denominator on the seed surface

Specializing the remaining base coordinates to (0,0,1) gives x0^3=ι-1
and w^3=-x0^6. If ι≠1, both x0 and w are units in that fiber, so the
linkage denominator x0^2*w+r*x1*x3*x2^2 is a unit there. Finite freeness
over the three-coordinate polynomial ring proves it is a nonzerodivisor
in the original seed quotient. No irreducibility of the seed is assumed.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLinkageRegular

open MvPolynomial CycleQ2SegreTangentLocal CycleQ2SeedQuotientFiniteFree
  CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations CycleQ2IncidenceFirstOrder
open scoped TensorProduct

variable {K : Type*} [Field K]

def basePoint : Base K →+* K := eval (fun j : Fin 3 => if j=2 then 1 else 0)

local instance basePointAlgebra : Algebra (Base K) K := (basePoint (K := K)).toAlgebra

abbrev Fiber (r ι : K) := K ⊗[Base K] SeedRing r ι

local instance fiberCommRing (r ι : K) : CommRing (Fiber r ι) :=
  Algebra.TensorProduct.instCommRing

local instance fiberAlgebra (r ι : K) : Algebra K (Fiber r ι) :=
  Algebra.TensorProduct.leftAlgebra

def toFiber (r ι : K) : SeedRing r ι →+* Fiber r ι :=
  (Algebra.TensorProduct.includeRight : SeedRing r ι →ₐ[Base K] Fiber r ι).toRingHom

def ambientToFiber (r ι : K) : Poly K →+* Fiber r ι :=
  (toFiber r ι).comp (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)))

def z (r ι : K) (j : Fin 5) : Fiber r ι := ambientToFiber r ι (X j)
theorem ambient_X (r ι : K) (j : Fin 5) : ambientToFiber r ι (X j) = z r ι j := rfl

def coefficientMap (r ι : K) : K →+* Fiber r ι := (ambientToFiber r ι).comp C

theorem remainingCoordinate (r ι : K) (j : Fin 3) :
    ambientToFiber r ι (X (remainingIndex j)) =
      algebraMap K (Fiber r ι) ((basePoint (K := K)) (X j)) := by
  have he : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
      (X (remainingIndex j)) = algebraMap (Base K) (SeedRing r ι) (X j) := by
    change Ideal.Quotient.mk _ (X (remainingIndex j)) =
      Ideal.Quotient.mk _ (remainingInclusion K (X j))
    simp [remainingInclusion]
  change toFiber r ι (Ideal.Quotient.mk _ (X (remainingIndex j))) = _
  rw [he]
  change Algebra.TensorProduct.includeRight (algebraMap (Base K) (SeedRing r ι) (X j)) = _
  rw [AlgHom.commutes]
  rfl

theorem z_one (r ι : K) : z r ι 1 = 0 := by
  have h := remainingCoordinate r ι 0
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem z_two (r ι : K) : z r ι 2 = 0 := by
  have h := remainingCoordinate r ι 1
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem z_three (r ι : K) : z r ι 3 = 1 := by
  have h := remainingCoordinate r ι 2
  simpa [remainingIndex, basePoint, z, ← Algebra.TensorProduct.one_def] using h

theorem ambient_h (r ι : K) : ambientToFiber r ι (smoothH ι) = 0 := by
  have h : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (smoothH ι) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [equationsIdeal]))
  change toFiber r ι (Ideal.Quotient.mk _ (smoothH ι)) = 0
  rw [h, map_zero]

theorem ambient_g (r ι : K) : ambientToFiber r ι (seedG r) = 0 := by
  have h : Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) (seedG r) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply (smoothSeed_mem_iff_linkage r ι).mpr
    exact ⟨0,1,by simp⟩
  change toFiber r ι (Ideal.Quotient.mk _ (seedG r)) = 0
  rw [h, map_zero]

theorem x0_cubed (r ι : K) : z r ι 0^3 = coefficientMap r ι (ι-1) := by
  have hh := ambient_h r ι
  change z r ι 0^3 = ambientToFiber r ι (C (ι-1))
  simp only [smoothH, smoothB, smoothA, map_sub, map_add, map_mul, map_pow,
    ambient_X, z_one, z_two, z_three, zero_pow (by decide : 3≠0),
    zero_pow (by decide : 2≠0), one_pow, zero_mul, mul_zero, add_zero, zero_add,
    mul_one] at hh
  rw [map_sub, map_sub, map_one, map_one]
  linear_combination hh

theorem w_cubed (r ι : K) : z r ι 4^3 = -(z r ι 0^6) := by
  have hg := ambient_g r ι
  simp only [seedG, CycleQ2SegreSeed.seedG_expanded, map_sub, map_add, map_mul,
    map_pow, ambient_X, z_one, z_two, z_three, zero_pow (by decide : 3≠0),
    zero_pow (by decide : 6≠0), one_pow, zero_mul, mul_zero, sub_zero,
    add_zero, zero_add] at hg
  linear_combination hg

theorem x0_unit (r ι : K) (hι : ι≠1) : IsUnit (z r ι 0) := by
  apply (isUnit_pow_iff (by decide : 3≠0)).mp
  rw [x0_cubed]
  exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hι)).map (coefficientMap r ι)

theorem w_unit (r ι : K) (hι : ι≠1) : IsUnit (z r ι 4) := by
  apply (isUnit_pow_iff (by decide : 3≠0)).mp
  rw [w_cubed]
  exact (IsUnit.neg_iff _).mpr ((x0_unit r ι hι).pow 6)

def linkagePolynomial (r : K) : Poly K :=
  CycleQ2SegreSeed.seedP (C r) (X 0) (X 1) (X 2) (X 3) (X 4)

def linkageElement (r ι : K) : SeedRing r ι :=
  Ideal.Quotient.mk _ (linkagePolynomial r)

theorem linkage_fiber (r ι : K) :
    toFiber r ι (linkageElement r ι) = z r ι 0^2*z r ι 4 := by
  change ambientToFiber r ι (linkagePolynomial r) = _
  simp only [linkagePolynomial, CycleQ2SegreSeed.seedP, CycleQ2SegreSeed.linkageP,
    map_add, map_mul, map_pow, ambient_X, z_one, z_two, z_three, zero_mul, mul_zero,
    add_zero]

theorem linkage_unit_fiber (r ι : K) (hι : ι≠1) :
    IsUnit (toFiber r ι (linkageElement r ι)) := by
  rw [linkage_fiber]
  exact ((x0_unit r ι hι).pow 2).mul (w_unit r ι hι)

/-- The actual linkage element is a nonzerodivisor over every field at
every r and every ι≠1, including both the complex and modular seeds. -/
theorem linkage_mul_injective (r ι : K) (hι : ι≠1) :
    Function.Injective (fun x : SeedRing r ι => linkageElement r ι*x) := by
  letI : Module.Free (Base K) (SeedRing r ι) := seedQuotient_free K r ι
  letI : Module.Finite (Base K) (SeedRing r ι) := seedQuotient_finite K r ι
  exact CycleQ2UnitFiberRegular.injective_mul_of_unit_fiber (A := K)
    (linkageElement r ι) (linkage_unit_fiber r ι hι)

end CycleQ2SeedLinkageRegular

#print axioms CycleQ2SeedLinkageRegular.linkage_unit_fiber
#print axioms CycleQ2SeedLinkageRegular.linkage_mul_injective
end
end
