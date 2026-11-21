import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Proposal.GeometricNormalConnecting
import Proposal.GeometricSeedSurfaceSparse1
import Proposal.GeometricSeedSurfaceSparse2
import Proposal.GeometricSeedSurfaceSparse3
import Proposal.GeometricSeedCubicGradient
import Proposal.GeometricSeedCoordinateCover

/-! Source-preserving extraction of the actual seed Jacobian certificates. -/

set_option Elab.async false

/- Component: continuation_20261112/SeedSurfaceBranchSparse.lean -/
section
namespace CycleQ2SeedSurfaceBranchSparse
open CycleQ2SeedSurfaceSparsePolynomial
open scoped BigOperators

def denominator (j : Fin 3) : GaussianInt := ![denominator1,denominator2,denominator3] j
def multipliers (j : Fin 3) : Fin 8 → Sparse := ![multipliers1,multipliers2,multipliers3] j

theorem identity {R : Type*} [CommRing R] (j : Fin 3) (φ : GaussianInt →+* R)
    (x : Fin 5 → R) :
    φ (denominator j) * x j.succ.castSucc^17 =
      ∑ k, eval φ x (multipliers j k) * eval φ x (generators k) := by
  fin_cases j
  · exact identity1 φ x
  · exact identity2 φ x
  · exact identity3 φ x

end CycleQ2SeedSurfaceBranchSparse

#print axioms CycleQ2SeedSurfaceBranchSparse.identity
end



/- Component: continuation_20261112/SeedSurfaceBranchGradient.lean -/
section
/-! # The actual r=57 branch Jacobian cover

The exact Gaussian-integer identities are bound to the literal sextic
q=x0^6+x2^6-57^3*x1^3*x3^3 and cubic h=smoothH I.  They put the
seventeenth powers of x1,x2,x3 in the equation-and-Jacobian ideal.
The consequence concerns every prime on these three coordinate opens.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedSurfaceBranchGradient

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
open scoped BigOperators

def branchEquation : Poly ℂ :=
  X 0^6 + X 2^6 - C ((57 : ℂ)^3)*X 1^3*X 3^3

def minor (j k : Fin 4) : Poly ℂ :=
  pderiv j.castSucc branchEquation * pderiv k.castSucc (smoothH Complex.I) -
    pderiv k.castSucc branchEquation * pderiv j.castSucc (smoothH Complex.I)

def minorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def generators : Fin 8 → Poly ℂ :=
  ![branchEquation, smoothH Complex.I, minor 0 1, minor 0 2, minor 0 3,
    minor 1 2, minor 1 3, minor 2 3]

def coefficientMap : GaussianInt →+* Poly ℂ :=
  (C : ℂ →+* Poly ℂ).comp GaussianInt.toComplex

def sparsePolynomial (p : CycleQ2SeedSurfaceSparsePolynomial.Sparse) : Poly ℂ :=
  CycleQ2SeedSurfaceSparsePolynomial.eval coefficientMap (fun j => X j) p

def witnesses (j : Fin 3) (k : Fin 8) : Poly ℂ :=
  sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.multipliers j k)

theorem generators_binding (j : Fin 8) :
    sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.generators j) = generators j := by
  have hc : (C (57 : ℂ) : Poly ℂ) = 57 := map_ofNat _ _
  have hn (k : Fin 5) : pderiv k (57 : Poly ℂ) = 0 := by
    rw [←hc]
    exact pderiv_C
  fin_cases j <;>
    simp [sparsePolynomial, coefficientMap, CycleQ2SeedSurfaceSparsePolynomial.eval,
      CycleQ2SeedSurfaceSparsePolynomial.termValue, CycleQ2SeedSurfaceSparsePolynomial.monomial,
      CycleQ2SeedSurfaceBranchSparse.generators, GaussianInt.toComplex,
      Zsqrtd.lift_apply_apply, generators, minor, branchEquation,
      smoothH, smoothB, smoothA, Derivation.leibniz, map_pow, map_ofNat, hn] <;> ring

theorem denominator_ne_zero (j : Fin 3) :
    (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) ≠ 0 := by
  intro h
  have hz : CycleQ2SeedSurfaceBranchSparse.denominator j = 0 :=
    GaussianInt.toComplex_injective (h.trans (map_zero GaussianInt.toComplex).symm)
  have hre := congrArg Zsqrtd.re hz
  fin_cases j <;>
    norm_num [CycleQ2SeedSurfaceBranchSparse.denominator,
      CycleQ2SeedSurfaceBranchSparse.denominator1,
      CycleQ2SeedSurfaceBranchSparse.denominator2,
      CycleQ2SeedSurfaceBranchSparse.denominator3] at hre

theorem coordinate_power_identity (j : Fin 3) :
    C (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) * X j.succ.castSucc^17 =
      ∑ k, witnesses j k * generators k := by
  calc
    C (CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ) * X j.succ.castSucc^17 =
        ∑ k, witnesses j k *
          sparsePolynomial (CycleQ2SeedSurfaceBranchSparse.generators k) :=
      CycleQ2SeedSurfaceBranchSparse.identity j coefficientMap (fun k => X k)
    _ = _ := by simp only [generators_binding]

def jacobianIdeal : Ideal (Poly ℂ) := Ideal.span (Set.range generators)

theorem coordinate_power_mem_jacobian (j : Fin 3) :
    (X j.succ.castSucc : Poly ℂ)^17 ∈ jacobianIdeal := by
  have hsum : C ((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ)) *
      X j.succ.castSucc^17 ∈ jacobianIdeal := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left jacobianIdeal
    (C (((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ))⁻¹)) hsum
  have hc : C (((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ))⁻¹) *
      C ((CycleQ2SeedSurfaceBranchSparse.denominator j : ℂ)) = (1 : Poly ℂ) := by
    rw [←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- The branch Jacobian minors cover the three coordinate opens that
cover every relevant prime of the actual seed surface. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hq : branchEquation ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 3, X j.succ.castSucc ∉ P) :
    ∃ j : Fin 6, minor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  by_contra! hzero
  have hgen (j : Fin 8) : generators j ∈ P := by
    fin_cases j
    · exact hq
    · exact hh
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3
    · exact hzero 4
    · exact hzero 5
  have hle : jacobianIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hgen j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (coordinate_power_mem_jacobian j)))

theorem field_minor_cover {K : Type*} [Field K] (φ : Poly ℂ →+* K)
    (hq : φ branchEquation = 0) (hh : φ (smoothH Complex.I) = 0)
    (hx : ∃ j : Fin 3, φ (X j.succ.castSucc) ≠ 0) :
    ∃ j : Fin 6, φ (minor (minorPairs j).1 (minorPairs j).2) ≠ 0 := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  exact prime_minor_cover (RingHom.ker φ) hq hh hx

end CycleQ2SeedSurfaceBranchGradient

#print axioms CycleQ2SeedSurfaceBranchGradient.coordinate_power_mem_jacobian
#print axioms CycleQ2SeedSurfaceBranchGradient.prime_minor_cover
end
end



/- Component: continuation_20261112/SeedSurfaceGradient.lean -/
section
/-! # A relevant-prime Jacobian cover for the actual seed surface

For G=w^3+q and F=G+h*k, the two-row Jacobian minors of (F,h) agree
with those of (G,h) modulo h.  Away from w=0, the cubic gradient cover
and partial_w G=3*w^2 give a minor.  On w=0, the exact branch cover
gives a minor.  The conclusion is bound to actualSeedEquation57 1 and
thetaH1 and holds at every relevant prime over the complex coefficients.
-/

noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 30000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedSurfaceGradient

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2NormalConnecting
open scoped BigOperators

def gMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (seedG (57 : ℂ)) * pderiv k (smoothH Complex.I) -
    pderiv k (seedG (57 : ℂ)) * pderiv j (smoothH Complex.I)

def surfaceMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (smoothF (57 : ℂ) Complex.I) * pderiv k (smoothH Complex.I) -
    pderiv k (smoothF (57 : ℂ) Complex.I) * pderiv j (smoothH Complex.I)

def correctionMinor (j k : Fin 5) : Poly ℂ :=
  pderiv j (smoothK Complex.I) * pderiv k (smoothH Complex.I) -
    pderiv k (smoothK Complex.I) * pderiv j (smoothH Complex.I)

theorem seedG_eq_branch :
    seedG (57 : ℂ) = CycleQ2SeedSurfaceBranchGradient.branchEquation + X 4^3 := by
  rw [seedG, CycleQ2SegreSeed.seedG_expanded]
  simp only [CycleQ2SeedSurfaceBranchGradient.branchEquation, map_pow]
  ring

theorem surfaceMinor_eq (j k : Fin 5) :
    surfaceMinor j k = gMinor j k + smoothH Complex.I * correctionMinor j k := by
  unfold surfaceMinor gMinor correctionMinor
  simp only [smoothF, map_add, Derivation.leibniz, smul_eq_mul]
  ring

theorem surfaceMinor_not_mem (P : Ideal (Poly ℂ))
    (hh : smoothH Complex.I ∈ P) {j k : Fin 5}
    (hg : gMinor j k ∉ P) : surfaceMinor j k ∉ P := by
  intro hs
  have hc : smoothH Complex.I * correctionMinor j k ∈ P :=
    Ideal.mul_mem_right _ _ hh
  have h := P.sub_mem hs hc
  rw [surfaceMinor_eq, add_sub_cancel_right] at h
  exact hg h

theorem gMinor_base (j k : Fin 4) :
    gMinor j.castSucc k.castSucc = CycleQ2SeedSurfaceBranchGradient.minor j k := by
  have hd (a : Fin 4) : pderiv a.castSucc (seedG (57 : ℂ)) =
      pderiv a.castSucc CycleQ2SeedSurfaceBranchGradient.branchEquation := by
    rw [seedG_eq_branch, map_add]
    have hz : pderiv a.castSucc (X (4 : Fin 5)^3 : Poly ℂ) = 0 := by
      fin_cases a <;> simp
    rw [hz, add_zero]
  unfold gMinor CycleQ2SeedSurfaceBranchGradient.minor
  rw [hd, hd]

theorem gMinor_w (j : Fin 4) :
    gMinor 4 j.castSucc = (3 : Poly ℂ)*X 4^2*
      pderiv j.castSucc (smoothH Complex.I) := by
  have hg : pderiv (4 : Fin 5) (seedG (57 : ℂ)) = (3 : Poly ℂ)*X 4^2 := by
    rw [seedG_eq_branch]
    simp [CycleQ2SeedSurfaceBranchGradient.branchEquation] <;> ring
  have hh : pderiv (4 : Fin 5) (smoothH Complex.I : Poly ℂ) = 0 := by
    simp [smoothH, smoothB, smoothA]
  simp only [gMinor, hg, hh, mul_zero, sub_zero]

theorem cubic_prime_gradient_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hx : ∃ j : Fin 4, X j.castSucc ∉ P) :
    ∃ j : Fin 4, pderiv j.castSucc (smoothH Complex.I : Poly ℂ) ∉ P := by
  by_contra! hzero
  have hle : Ideal.span (Set.range (fun k : Fin 4 =>
      pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hzero j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem 5
    (hle (CycleQ2SeedCubicGradient.coordinate_power_mem_gradient_ideal j)))

/-- All relevant primes of the actual incidence seed surface admit a
nonvanishing two-column Jacobian minor. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hF : smoothF (57 : ℂ) Complex.I ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, surfaceMinor j k ∉ P := by
  have hbase : ∃ j : Fin 3, X j.succ.castSucc ∉ P := by
    rcases CycleQ2SeedCoordinateCover.seedPrime_coordinate_cover (57 : ℂ)
      Complex.I P hh hF hx with h1 | h2 | h3
    · exact ⟨0,h1⟩
    · exact ⟨1,h2⟩
    · exact ⟨2,h3⟩
  by_cases hw : (X (4 : Fin 5) : Poly ℂ) ∈ P
  · have hprod : smoothH Complex.I * smoothK Complex.I ∈ P :=
      Ideal.mul_mem_right _ _ hh
    have hG : seedG (57 : ℂ) ∈ P := by
      simpa only [smoothF, add_sub_cancel_right] using P.sub_mem hF hprod
    have hw3 : (X (4 : Fin 5) : Poly ℂ)^3 ∈ P :=
      Ideal.pow_mem_of_mem P hw 3 (by decide)
    have hq : CycleQ2SeedSurfaceBranchGradient.branchEquation ∈ P := by
      rw [seedG_eq_branch] at hG
      simpa only [add_sub_cancel_right] using P.sub_mem hG hw3
    obtain ⟨a,ha⟩ := CycleQ2SeedSurfaceBranchGradient.prime_minor_cover P hq hh hbase
    refine ⟨(CycleQ2SeedSurfaceBranchGradient.minorPairs a).1.castSucc,
      (CycleQ2SeedSurfaceBranchGradient.minorPairs a).2.castSucc,?_⟩
    apply surfaceMinor_not_mem P hh
    simpa only [gMinor_base] using ha
  · have hbase4 : ∃ j : Fin 4, X j.castSucc ∉ P := by
      obtain ⟨j,hj⟩ := hbase
      exact ⟨j.succ,hj⟩
    obtain ⟨j,hj⟩ := cubic_prime_gradient_cover P hbase4
    have h3 : (3 : Poly ℂ) ∉ P := by
      apply Ideal.notMem_of_isUnit P
      simpa only [map_ofNat] using
        (isUnit_iff_ne_zero.mpr (by norm_num : (3 : ℂ) ≠ 0)).map
          (C : ℂ →+* Poly ℂ)
    have hw2 : (X (4 : Fin 5) : Poly ℂ)^2 ∉ P := by
      intro h
      exact hw ((inferInstance : P.IsPrime).mem_of_pow_mem 2 h)
    refine ⟨4,j.castSucc,surfaceMinor_not_mem P hh ?_⟩
    rw [gMinor_w]
    exact (inferInstance : P.IsPrime).mul_notMem
      ((inferInstance : P.IsPrime).mul_notMem h3 hw2) hj

def actualNormalMinor (j k : Fin 5) : Poly ℂ :=
  Matrix.det (fun a b : Fin 2 =>
    pderiv (![j,k] b) (![actualSeedEquation 57 1,thetaH 1] a))

theorem actualNormalMinor_eq (j k : Fin 5) :
    actualNormalMinor j k = surfaceMinor j k := by
  simp only [actualNormalMinor, Matrix.det_fin_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, actualSeedEquation_eq_smoothF, ←smoothH_eq_thetaH]
  rfl

/-- The cover is bound to the literal ordered target tuple (F,h) used
in the global conormal construction. -/
theorem actual_prime_normal_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hF : actualSeedEquation 57 1 ∈ P) (hh : thetaH 1 ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j k : Fin 5, actualNormalMinor j k ∉ P := by
  rw [actualSeedEquation_eq_smoothF] at hF
  rw [←smoothH_eq_thetaH] at hh
  obtain ⟨j,k,hjk⟩ := prime_minor_cover P hF hh hx
  exact ⟨j,k,by simpa only [actualNormalMinor_eq] using hjk⟩

theorem actual_field_normal_cover {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (hF : φ (actualSeedEquation 57 1) = 0)
    (hh : φ (thetaH 1) = 0) (hx : ∃ j : Fin 5, φ (X j) ≠ 0) :
    ∃ j k : Fin 5, IsUnit (φ (actualNormalMinor j k)) := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨j,k,hjk⟩ := actual_prime_normal_cover (RingHom.ker φ) hF hh hx
  exact ⟨j,k,isUnit_iff_ne_zero.mpr hjk⟩

end CycleQ2SeedSurfaceGradient

#print axioms CycleQ2SeedSurfaceGradient.prime_minor_cover
#print axioms CycleQ2SeedSurfaceGradient.actual_prime_normal_cover
#print axioms CycleQ2SeedSurfaceGradient.actual_field_normal_cover
end
end


/- End of source-preserving extraction. -/
