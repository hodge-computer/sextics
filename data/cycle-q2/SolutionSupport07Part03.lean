import Proposal.GeometricNormalizedCartierClass
import Proposal.GeometricIncidenceCechTrace
import Proposal.GeometricCurveCover
import Proposal.SolutionSupport07Part02
import Proposal.GeometricSeedConormalBases
import Proposal.GeometricNormalConnecting

/-! Components extracted from SolutionSupport07.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_20261112/LocalizationBoundaryClearing.lean -/
section
/-! Denominator clearing for two genuine localization restriction maps.
No domain or injectivity hypothesis on any localization map is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace CycleQ2LocalizationBoundary

section TwoOpens
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- An arbitrary boundary on two principal opens has a polynomial
denominator-clearing witness. The extra common-product factor coming
from equality in the overlap localization is retained explicitly. -/
theorem clear_two_open_boundary (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away y T]
    [IsLocalization.Away (x*y) U]
    (f : S →+* U) (g : T →+* U)
    (hf : ∀ a, f (algebraMap R S a) = algebraMap R U a)
    (hg : ∀ a, g (algebraMap R T a) = algebraMap R U a)
    (a : S) (b : T) (p : R) (n m : ℕ)
    (h : (f a + g b) * algebraMap R U x ^ n * algebraMap R U y ^ m =
      algebraMap R U p) :
    ∃ (N M : ℕ) (q s : R), n ≤ N ∧ m ≤ M ∧
      p*x^(N-n)*y^(M-m) = q*x^N+s*y^M := by
  obtain ⟨na, a0, ha⟩ := IsLocalization.Away.surj x a
  obtain ⟨nb, b0, hb⟩ := IsLocalization.Away.surj y b
  have ha' : f a * algebraMap R U x ^ na = algebraMap R U a0 := by
    simpa only [map_mul, map_pow, hf] using congrArg f ha
  have hb' : g b * algebraMap R U y ^ nb = algebraMap R U b0 := by
    simpa only [map_mul, map_pow, hg] using congrArg g hb
  have heq : algebraMap R U (p*x^na*y^nb) =
      algebraMap R U (a0*x^n*y^(m+nb)+b0*x^(n+na)*y^m) := by
    simp only [map_mul, map_add, map_pow, pow_add]
    rw [← h, ← ha', ← hb']
    ring
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (x*y) heq
  refine ⟨n+na+k, m+nb+k, b0*y^(m+k), a0*x^(n+k), by omega, by omega, ?_⟩
  have hn : n+na+k-n=na+k := by omega
  have hm : m+nb+k-m=nb+k := by omega
  rw [hn,hm]
  simp only [mul_pow,pow_add] at hk ⊢
  linear_combination hk

end TwoOpens

section UnitPowers
variable {R : Type*} [CommRing R]

/-- Removing unit factors from the two denominator generators does not
change whether a numerator has an unrestricted boundary witness. -/
theorem unscale_boundary (a b p q s : R) (u v : Rˣ) (d e N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (h : p*((u:R)*a^d)^(N-1)*((v:R)*b^e)^(M-1) =
      q*((u:R)*a^d)^N+s*((v:R)*b^e)^M) :
    ∃ q' s' : R, p*a^(d*(N-1))*b^(e*(M-1)) =
      q'*a^(d*N)+s'*b^(e*M) := by
  refine ⟨q*(u:R)*((v⁻¹:Rˣ):R)^(M-1),
    s*(v:R)*((u⁻¹:Rˣ):R)^(N-1), ?_⟩
  have hu : (u:R)^(N-1)*((u⁻¹:Rˣ):R)^(N-1)=1 := by
    rw [← mul_pow, u.mul_inv, one_pow]
  have hv : (v:R)^(M-1)*((v⁻¹:Rˣ):R)^(M-1)=1 := by
    rw [← mul_pow, v.mul_inv, one_pow]
  have hNe : N=(N-1)+1 := by omega
  have hMe : M=(M-1)+1 := by omega
  have huN : (u:R)^N = (u:R)^(N-1)*(u:R) := by
    conv_lhs => rw [hNe,pow_succ]
  have hvM : (v:R)^M = (v:R)^(M-1)*(v:R) := by
    conv_lhs => rw [hMe,pow_succ]
  simp only [mul_pow, ← pow_mul] at h
  rw [huN,hvM] at h
  linear_combination ((u⁻¹:Rˣ):R)^(N-1)*((v⁻¹:Rˣ):R)^(M-1)*h -
    p*a^(d*(N-1))*b^(e*(M-1))*((v:R)^(M-1)*((v⁻¹:Rˣ):R)^(M-1))*hu -
    p*a^(d*(N-1))*b^(e*(M-1))*hv +
    q*a^(d*N)*(u:R)*((v⁻¹:Rˣ):R)^(M-1)*hu +
    s*b^(e*M)*(v:R)*((u⁻¹:Rˣ):R)^(N-1)*hv

end UnitPowers
end CycleQ2LocalizationBoundary

#print axioms CycleQ2LocalizationBoundary.clear_two_open_boundary
#print axioms CycleQ2LocalizationBoundary.unscale_boundary
end
end


/- Component: continuation_20261112/HomogeneousPrimeCoverOpen.lean -/
section
/-! A relevant-prime cover at the actual seed persists on an actual
polynomial open, via radical membership and finite homogeneous coefficient
maps. This does not invoke geometric smoothness as an assumed conclusion.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2HomogeneousPrimeCoverOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousIdealOpen
open scoped BigOperators

section HighDegree
variable {K : Type*} [CommRing K]

theorem coordinate_powers_of_prime_cover (I : Ideal (Poly K))
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime], I ≤ P →
      ∀ j : Fin 5, X j ∈ P) :
    ∃ n : Fin 5 → ℕ, ∀ j, (X j : Poly K)^n j ∈ I := by
  classical
  have hj (j : Fin 5) : (X j : Poly K) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    letI : P.IsPrime := hP.2
    exact hcover P hP.1 j
  choose n hn using hj
  exact ⟨n,hn⟩

theorem high_degree_monomial_mem (I : Ideal (Poly K)) (n : Fin 5 → ℕ)
    (hn : ∀ j, (X j : Poly K)^n j ∈ I) (T : ℕ)
    (hT : (∑ j, n j) < T) (e : FullInvariantIndex (6*T)) :
    (monomial (fullExponentOf e.val) 1 : Poly K) ∈ I := by
  classical
  have hdvd : ∃ j : Fin 5, n j ≤ fullExponentOf e.val j := by
    by_contra h
    push_neg at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have hd := e.property.1
    simp only [fullExponentOf_apply] at h0 h1 h2 h3 h4
    simp only [fullDegree] at hd
    simp [Fin.sum_univ_succ] at hT
    omega
  obtain ⟨j,hj⟩ := hdvd
  have he : Finsupp.single j (n j) ≤ fullExponentOf e.val :=
    Finsupp.single_le_iff.mpr hj
  have hm : (monomial (fullExponentOf e.val) 1 : Poly K) =
      X j^n j * monomial (fullExponentOf e.val-Finsupp.single j (n j)) 1 := by
    rw [X_pow_eq_monomial,monomial_mul,one_mul,add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (hn j)

theorem high_degree_homogeneous_mem (I : Ideal (Poly K)) (n : Fin 5 → ℕ)
    (hn : ∀ j, (X j : Poly K)^n j ∈ I) (T : ℕ)
    (hT : (∑ j, n j) < T) (p : Poly K) (hp : HG p (6*T,0)) : p ∈ I := by
  rw [← fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial,mul_one] using
    Ideal.mul_mem_left I (C (p.coeff (fullExponentOf e.val)))
      (high_degree_monomial_mem I n hn T hT e)

theorem coordinate_power_homogeneous (T : ℕ) (j : Fin 5) :
    HG ((X j : Poly K)^(if j=4 then 3*T else 6*T)) (6*T,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  have h6 : (6 : ZMod 3)=0 := by decide
  fin_cases j <;> simp [fullGrading, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,h6]
  <;> ring

end HighDegree

section CoefficientOpen
variable {R K : Type*} [CommRing R] [CommRing K]
  {ι : Type*} [Fintype ι]

/-- A seed cover by a finite homogeneous ideal gives a polynomial open
where the same ideal contains powers of every projective coordinate. -/
theorem exists_prime_cover_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0))
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime],
      generatorIdeal (fun j => map f (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        ∀ (P : Ideal (Poly S)) [P.IsPrime],
          generatorIdeal (fun j => map φ (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P := by
  classical
  obtain ⟨n,hn⟩ := coordinate_powers_of_prime_cover
    (generatorIdeal (fun j => map f (g j))) hcover
  let T := (∑ j, n j) + (∑ j, degree j) + 1
  have hT : (∑ j, n j) < T := by dsimp [T]; omega
  have hle (j : ι) : degree j ≤ 6*T := by
    have hj : degree j ≤ ∑ i : ι, degree i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (degree i)) (Finset.mem_univ j)
    dsimp [T]
    omega
  have hseed (p : Poly K) (hp : HG p (6*T,0)) :
      p ∈ generatorIdeal (fun j => map f (g j)) :=
    high_degree_homogeneous_mem _ n hn T hT p hp
  obtain ⟨s,hs,hspec⟩ := exists_homogeneous_open f c hfc g degree hgen (6*T) hle hseed
  refine ⟨s,hs,?_⟩
  intro S _ φ hφ P _ hP j
  have hj := hspec S φ hφ _ (coordinate_power_homogeneous (K := S) T j)
  exact (inferInstance : P.IsPrime).mem_of_pow_mem _ (hP hj)

/-- Pointedness forces every open containing the seed to remain a unit
over the generic field, so the actual projective prime cover persists. -/
theorem prime_cover_of_pointed {L : Type*} [Field L]
    (f : R →+* K) (c : K →+* R) (hfc : ∀ x, f (c x)=x)
    (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) [Nontrivial K]
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime],
      generatorIdeal (fun j => map f (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P)
    (φ : R →+* L) (hpointed : ∀ a, φ a=0 → f a=0)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hP : generatorIdeal (fun j => map φ (g j)) ≤ P) :
    ∀ j : Fin 5, X j ∈ P := by
  obtain ⟨s,hs,hopen⟩ := exists_prime_cover_open f c hfc g degree hgen hcover
  have hu : IsUnit (φ s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact one_ne_zero (hs.symm.trans (hpointed s hz))
  exact hopen L φ hu P hP

end CoefficientOpen
end CycleQ2HomogeneousPrimeCoverOpen

#print axioms CycleQ2HomogeneousPrimeCoverOpen.exists_prime_cover_open
#print axioms CycleQ2HomogeneousPrimeCoverOpen.prime_cover_of_pointed
end
end


/- Component: continuation_20261112/SeedGenuineNormalConnecting.lean -/
section
/-!
# Genuine normal lifts and their overlap coefficient

The map throughout this file is the dual of the actual natural cotangent
map for J=(F,h) contained in I=(f1,f2,h). A basis of the source conormal
module is required to consist of the actual equation classes. Such bases
are already constructed on the seed Jacobian charts and at every relevant
prime. The statements are also ready for a global equation-class basis.

The second denominator chart receives its genuine target conormal basis.
Both local splitting formulas are realized as actual normal homomorphisms,
their difference is in the kernel of the natural map, and its canonical
kernel coordinate is the existing overlapCoefficient. The final identities
describe changes of lifts; graded sheaf gluing is a separate construction.
-/

noncomputable section
open scoped TensorProduct BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2GenuineNormalConnecting

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap
  CycleQ2NormalConnecting CycleQ2SeedTrace

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

section SecondChart

def secondSurfaceDuals (d : Fin 3 → Derivation ℂ P S) (u : Sˣ) (k : S) :
    Fin 2 → Derivation ℂ P S :=
  ![(↑(u⁻¹) : S) • d 1, d 2 - (k * (↑(u⁻¹) : S)) • d 1]

theorem secondSurfaceDuals_equations (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S originalG2) (i j : Fin 2) :
    secondSurfaceDuals d u (algebraMap P S (thetaK θ)) i
      (surfaceEquations r θ j) = if i = j then 1 else 0 := by
  have hF1 := sourceDual_F r θ hI d hd 1
  have hF2 := sourceDual_F r θ hI d hd 2
  change d 1 (actualSeedEquation r θ) = algebraMap P S originalG2 at hF1
  change d 2 (actualSeedEquation r θ) = algebraMap P S (thetaK θ) at hF2
  have hh1 : d 1 (thetaH θ) = 0 := by simpa [curveEquations] using hd 1 2
  have hh2 : d 2 (thetaH θ) = 1 := by simpa [curveEquations] using hd 2 2
  rw [← hu] at hF1
  fin_cases i <;> fin_cases j <;>
    simp [secondSurfaceDuals, surfaceEquations, Derivation.smul_apply,
      Derivation.sub_apply, hF1, hF2, hh1, hh2, smul_eq_mul, mul_assoc]

/-- The actual target conormal basis on a source Jacobian chart where g2
is a unit. It complements surfaceConormalBasisOnFirstOpen. -/
def surfaceConormalBasisOnSecondOpen (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S originalG2) :
    Module.Basis (Fin 2) S (SurfaceConormal (S := S) r θ) :=
  conormalBasis (surfaceIdeal r θ)
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (surfaceEquations r θ) rfl
    (secondSurfaceDuals d u (algebraMap P S (thetaK θ)))
    (secondSurfaceDuals_equations r θ hI d hd u hu)

end SecondChart


end CycleQ2GenuineNormalConnecting

#print axioms CycleQ2GenuineNormalConnecting.surfaceConormalBasisOnSecondOpen
#print axioms CycleQ2GenuineNormalConnecting.genuineLifts_same_image
#print axioms CycleQ2GenuineNormalConnecting.genuineLift_difference_coefficient
#print axioms CycleQ2GenuineNormalConnecting.changed_lifts_coefficient
end
end


/- Component: continuation_20261112/SeedBoundaryProjection.lean -/
section
/-!
# Homogeneous extraction from arbitrary seed Cech boundary coefficients

For the actual theta-family curve ideal, an arbitrary polynomial boundary
witness for a homogeneous degree-one fraction can be projected to the
correct homogeneous numerator degrees. Thus unbounded and initially
inhomogeneous numerator coefficients introduce no additional boundaries
for the checked derivative fraction. Localization denominator clearing is
a separate input to this purely polynomial step.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedBoundaryProjection

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
  CycleQ2HomogeneousComponent
open CycleQ2SeedCech (curveA curveB)

theorem curveA_homogeneous : curveA.IsHomogeneous 2 := by
  simpa [curveA] using (isHomogeneous_X ℂ (1 : Fin 4)).mul (isHomogeneous_X ℂ (3 : Fin 4))

theorem curveB_homogeneous : curveB.IsHomogeneous 1 := by
  exact isHomogeneous_X ℂ (2 : Fin 4)

/-- Homogeneous projection of arbitrary denominator-clearing coefficients.
The bound on N,M permits every higher pole order needed by localization. -/
theorem boundary_of_unrestricted_witness (r θ : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) (N M : ℕ) (q s : Poly)
    (hn : 2 ≤ N) (hm : 4 ≤ M)
    (hmem : p * curveA ^ (N - 2) * curveB ^ (M - 4) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r θ) :
    CechBoundary r θ p 2 4 := by
  let D := 2 * N + M + 1
  have hD2 : 2 ≤ D := by dsimp [D]; omega
  have hD3 : 3 ≤ D := by dsimp [D]; omega
  have hAN : (curveA ^ N).IsHomogeneous (2 * N) := curveA_homogeneous.pow N
  have hBM : (curveB ^ M).IsHomogeneous M := by simpa using curveB_homogeneous.pow M
  have hp' : (p * curveA ^ (N - 2) * curveB ^ (M - 4)).IsHomogeneous D := by
    convert (hp.mul (curveA_homogeneous.pow (N - 2))).mul
      (curveB_homogeneous.pow (M - 4)) using 1 <;> dsimp [D] <;> omega
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hmem
  have hh := congrArg (homogeneousComponent D) huv
  have hF : (relation r 0).IsHomogeneous 2 := CycleQ2SeedCech.curveF1_homogeneous r
  rw [map_add, component_mul_of_homogeneous _ _ hF hD2,
    component_mul_of_homogeneous _ _ (curveH_homogeneous θ) hD3,
    map_sub, map_add, homogeneousComponent_eq_self hp',
    component_mul_of_homogeneous _ _ hAN (by dsimp [D]; omega),
    component_mul_of_homogeneous _ _ hBM (by dsimp [D]; omega)] at hh
  have hDA : D - 2 * N = M + 1 := by dsimp [D]; omega
  have hDB : D - M = 2 * N + 1 := by dsimp [D]; omega
  rw [hDA, hDB] at hh
  refine ⟨N, M, homogeneousComponent (M + 1) q,
    homogeneousComponent (2 * N + 1) s, hn, hm,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_isHomogeneous _ _, ?_⟩
  apply Ideal.mem_span_pair.mpr
  exact ⟨homogeneousComponent (D - 2) u, homogeneousComponent (D - 3) v, hh⟩


/-- The actual nonzero trace excludes arbitrary polynomial boundary
coefficients once denominators have been cleared. -/
theorem no_unrestricted_boundary (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0)
    (N M : ℕ) (q s : Poly) (hn : 2 ≤ N) (hm : 4 ≤ M) :
    derivativeNumerator (cubicDeformation v) * curveA ^ (N - 2) * curveB ^ (M - 4) -
      (q * curveA ^ N + s * curveB ^ M) ∉ curveIdeal r θ := by
  intro hmem
  exact nonboundary_of_derivativeTrace_ne_zero r θ hr v hv
    (boundary_of_unrestricted_witness r θ _ (derivativeNumerator_homogeneous v)
      N M q s hn hm hmem)

end CycleQ2SeedBoundaryProjection

#print axioms CycleQ2SeedBoundaryProjection.boundary_of_unrestricted_witness
#print axioms CycleQ2SeedBoundaryProjection.no_unrestricted_boundary
end
end


/- Component: continuation_20261112/SeedTwoOpenCover.lean -/
section
/-!
# The two denominator opens cover the actual projective seed curve

On a prime of the curve, simultaneous vanishing of g1 and g2 forces
x1*x3 and x2 to vanish. The quadratic then forces x0 to vanish, and the
literal cubic with coefficients -i and 1-i forces both remaining
coordinates to vanish. Thus D(g1),D(g2) contain every relevant prime.
The statement applies to the weighted five-variable presentation as well.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false



#print axioms CycleQ2SeedTwoOpenCover.relevant_prime_cover
#print axioms CycleQ2SeedTwoOpenCover.weighted_relevant_prime_cover
end
end


/- Component: continuation_20261112/UniversalSurfaceFiniteFree.lean -/
section
/-!
# The normalized universal incidence surface is finite free over three coordinates

The two equations are the actual full invariant cubic and sextic, with their
distinguished coefficients normalized to one.  No seed specialization, smoothness,
or cohomological flatness is assumed.  The nine basis vectors are the original
classes of x0^a*w^b.  This supplies the missing relative input for the explicit
three-coordinate Cech calculation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurface

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree
open scoped MonomialOrder

variable (R : Type*) [CommRing R]



























end CycleQ2UniversalSurface

#print axioms CycleQ2UniversalSurface.surfaceBasis_apply
#print axioms CycleQ2UniversalSurface.surfaceQuotient_rank_nine
end
end


/- Component: continuation_20261112/CharacterTopCech.lean -/
section
/-!
# Top Cech coordinates in all three characters

The degree remains zero.  The character is retained as an explicit parameter,
so the ambient-test character-one piece is computed rather than identified
with the previously checked character-zero piece.  Their respective ranks
are eight and seven.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CharacterTopCech

open CycleQ2SeedCechThreeOpen
open CycleQ2SeedCechTopCohomology (SmallExponents topExponent topExponent_negative
  topExponent_injective)
open scoped BigOperators

section Indices
variable (χ : ZMod 3)

abbrev TopIndex :=
  {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = (0,χ)}

theorem topIndex_count : Fintype.card (TopIndex χ) = if χ=0 then 7 else 8 := by
  fin_cases χ <;> decide

def topCoordinate (q : TopIndex χ) : ShiftIndex × LaurentExponent :=
  (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective (topCoordinate χ) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent => q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent => q.2) hab)

/-- The finite exponent bound uses degree zero and is uniform in the character. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = (0,χ)) :
    ∃ q : TopIndex χ, topCoordinate χ q = (ab,e) := by
  have hd := congrArg Prod.fst hg
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i = 0 at hd
  rw [Fin.sum_univ_three] at hd
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have bounds (i : Fin 3) : (-e i - 1).toNat < 4 := by
    fin_cases i
    · change (-e 0 - 1).toNat < 4; omega
    · change (-e 1 - 1).toNat < 4; omega
    · change (-e 2 - 1).toNat < 4; omega
  let v : SmallExponents :=
    (⟨(-e 0 - 1).toNat, bounds 0⟩,
     ⟨(-e 1 - 1).toNat, bounds 1⟩,
     ⟨(-e 2 - 1).toNat, bounds 2⟩)
  have hv : topExponent v = e := by
    ext i
    fin_cases i
    · change -(((-e 0 - 1).toNat : ℤ) + 1) = e 0; omega
    · change -(((-e 1 - 1).toNat : ℤ) + 1) = e 1; omega
    · change -(((-e 2 - 1).toNat : ℤ) + 1) = e 2; omega
  refine ⟨⟨(ab,v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

end Indices

variable (R : Type*) [CommRing R] (χ : ZMod 3)



def topProjection : gradedFamilies R χ →ₗ[R] ((TopIndex χ) →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R χ) (q : (TopIndex χ)) :
    topProjection R χ p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : (TopIndex χ)) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : (TopIndex χ)) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R χ q ab).coeff e = if topCoordinate χ q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : (TopIndex χ)) : gradedFamilies R χ := ⟨basisFamily R χ q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : (TopIndex χ)) :
    topProjection R χ (basisSection R χ q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R χ q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate χ q = topCoordinate χ j then 1 else 0) = _
  simp only [(topCoordinate_injective χ).eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R χ) := by
  intro p
  refine ⟨∑ q : (TopIndex χ), p q • basisSection R χ q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R χ) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R χ) :=
  poleSubmodule R χ {0, 1} ⊔ poleSubmodule R χ {0, 2} ⊔ poleSubmodule R χ {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R χ) :
    topProjection R χ p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = (0,χ)
    · obtain ⟨q, hq⟩ := exists_topIndex χ ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : (TopIndex χ) →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R χ s ≤ LinearMap.ker (topProjection R χ) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R χ ≤ LinearMap.ker (topProjection R χ) :=
  sup_le (sup_le (poleSubmodule_le_ker R χ {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R χ {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R χ {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) : gradedFamilies R χ :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R χ P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R χ) :
    filterSection R χ P p ∈ poleSubmodule R χ s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R χ = LinearMap.ker (topProjection R χ) := by
  apply le_antisymm (topBoundary_le_ker R χ)
  intro p hp
  have hz := (topProjection_zero_iff R χ p).mp hp
  let p01 := filterSection R χ (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R χ (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R χ (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R χ {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R χ {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R χ {1, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · exact he.2.2
    · simp at hi
    · simp at hi
  have heq : p = p01 + p02 + p12 := by
    apply Subtype.ext
    funext ab
    apply AddMonoidAlgebra.ext
    ext e
    change (p.val ab).coeff e =
      ((p01.val ab + p02.val ab + p12.val ab).coeff e)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      p01, p02, p12, filterSection_coeff]
    by_cases h2 : 0 ≤ e 2
    · simp [h2, not_lt.mpr h2]
    · by_cases h1 : 0 ≤ e 1
      · simp [lt_of_not_ge h2, h1, not_lt.mpr h1]
      · by_cases h0 : 0 ≤ e 0
        · simp [h2, h1, lt_of_not_ge h2, lt_of_not_ge h1, h0]
        · have hn : ∀ i, e i < 0 := by
            intro i
            fin_cases i
            · exact lt_of_not_ge h0
            · exact lt_of_not_ge h1
            · exact lt_of_not_ge h2
          simp [lt_of_not_ge h2, lt_of_not_ge h1, h0, hz ab e hn]
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact (show poleSubmodule R χ {0, 1} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R χ {0, 2} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R χ {1, 2} ≤ topBoundary R χ from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R χ ⧸ topBoundary R χ

def topCechEquiv : TopCechQuotient R χ ≃ₗ[R] ((TopIndex χ) →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R χ)).trans
    ((topProjection R χ).quotKerEquivOfSurjective (topProjection_surjective R χ))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R χ) :
    topCechEquiv R χ (Submodule.Quotient.mk p) = topProjection R χ p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis (TopIndex χ) R (TopCechQuotient R χ) :=
  Finsupp.basisSingleOne.map (topCechEquiv R χ).symm

@[simp] theorem topCechBasis_apply (q : (TopIndex χ)) :
    topCechBasis R χ q = Submodule.Quotient.mk (basisSection R χ q) := by
  apply (topCechEquiv R χ).injective
  simp [topCechBasis]

theorem topCech_rank [Nontrivial R] : Module.finrank R (TopCechQuotient R χ) = if χ=0 then 7 else 8 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R χ), topIndex_count χ]

end CycleQ2CharacterTopCech

#print axioms CycleQ2CharacterTopCech.topIndex_count
#print axioms CycleQ2CharacterTopCech.topCechBasis_apply
#print axioms CycleQ2CharacterTopCech.topCech_rank
end
end


/- Component: continuation_20261112/SeedSurfaceBranchSparseBase.lean -/
section
/-! A kernel-checkable sparse polynomial identity checker over Gaussian integers.

All executable definitions use natural-number tuples, lists, and structural
recursion. The checker is sound for arbitrary term lists; sortedness only
improves its ability to combine equal monomials and is never a proof premise.
No external arithmetic result or evaluator axiom is used.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SeedSurfaceSparsePolynomial

abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Term := Exponent × GaussianInt
abbrev Sparse := List Term

def exponentAdd (a b : Exponent) : Exponent :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2.1+b.2.2.2.1,
    a.2.2.2.2+b.2.2.2.2)

def code (e : Exponent) : ℕ :=
  e.1 + 32*(e.2.1 + 32*(e.2.2.1 + 32*(e.2.2.2.1 + 32*e.2.2.2.2)))

def termProduct (a b : Term) : Term :=
  (exponentAdd a.1 b.1, a.2*b.2)

/-- Fuel exhaustion preserves every term. Equality of exponent tuples is
checked before combining; the numeric sorting key need not be injective. -/
def addFuel : ℕ → Sparse → Sparse → Sparse
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a::p, b::q =>
      if a.1 = b.1 then (a.1, a.2+b.2) :: addFuel n p q
      else if code a.1 ≤ code b.1 then a :: addFuel n p (b::q)
      else b :: addFuel n (a::p) q

def add (p q : Sparse) : Sparse := addFuel (p.length+q.length+1) p q

def mul (p q : Sparse) : Sparse :=
  p.foldr (fun a acc => add (q.map (termProduct a)) acc) []

def neg (p : Sparse) : Sparse := p.map (fun a => (a.1, -a.2))
def checkZero (p : Sparse) : Bool := p.all (fun a => decide (a.2 = 0))

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def monomial (x : Fin 5 → R) (e : Exponent) : R :=
  x 0 ^ e.1 * x 1 ^ e.2.1 * x 2 ^ e.2.2.1 *
    x 3 ^ e.2.2.2.1 * x 4 ^ e.2.2.2.2

def termValue (φ : GaussianInt →+* R) (x : Fin 5 → R) (a : Term) : R := φ a.2 * monomial x a.1
def eval (φ : GaussianInt →+* R) (x : Fin 5 → R) (p : Sparse) : R := (p.map (termValue φ x)).sum

@[simp] theorem eval_nil (x : Fin 5 → R) : eval φ x [] = 0 := rfl
@[simp] theorem eval_cons (x : Fin 5 → R) (a : Term) (p : Sparse) :
    eval φ x (a::p) = termValue φ x a + eval φ x p := rfl

theorem eval_append (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (p ++ q) = eval φ x p + eval φ x q := by simp [eval]

theorem eval_addFuel (x : Fin 5 → R) (n : ℕ) (p q : Sparse) :
    eval φ x (addFuel n p q) = eval φ x p + eval φ x q := by
  induction n generalizing p q with
  | zero => exact eval_append φ x p q
  | succ n ih =>
    cases p with
    | nil => simp [addFuel]
    | cons a p =>
      cases q with
      | nil => simp [addFuel]
      | cons b q =>
        by_cases he : a.1 = b.1
        · simp only [addFuel, if_pos he, eval_cons, ih, termValue,
            map_add]
          rw [he]
          ring
        · simp only [addFuel, if_neg he]
          split <;> simp only [eval_cons, ih] <;> ring

@[simp] theorem eval_add (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (add p q) = eval φ x p + eval φ x q := eval_addFuel φ x _ p q

theorem monomial_exponentAdd (x : Fin 5 → R) (a b : Exponent) :
    monomial x (exponentAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, exponentAdd, pow_add]
  ring

theorem termValue_product (x : Fin 5 → R) (a b : Term) :
    termValue φ x (termProduct a b) = termValue φ x a * termValue φ x b := by
  simp only [termValue, termProduct, map_mul,
    monomial_exponentAdd]
  ring

theorem eval_mul (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (mul p q) = eval φ x p * eval φ x q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    change eval φ x (add (q.map (termProduct a)) (mul p q)) = _
    rw [eval_add, ih, eval_cons]
    have h : eval φ x (q.map (termProduct a)) = termValue φ x a * eval φ x q := by
      simp only [eval, List.map_map, Function.comp_def, termValue_product,
        List.sum_map_mul_left]
    rw [h]
    ring

theorem termValue_neg (x : Fin 5 → R) (a : Term) :
    termValue φ x (a.1, -a.2) = -termValue φ x a := by
  simp only [termValue, map_neg, neg_mul]

theorem eval_neg (x : Fin 5 → R) (p : Sparse) :
    eval φ x (neg p) = -eval φ x p := by
  simp only [neg, eval, List.map_map, Function.comp_def, termValue_neg]
  simpa only [List.map_map, Function.comp_def] using (List.sum_neg (p.map (termValue φ x))).symm

theorem eval_zero_of_all (x : Fin 5 → R) (p : Sparse)
    (h : p.all (fun a => decide (a.2 = 0)) = true) : eval φ x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eval_cons, ih h.2, add_zero]
    unfold termValue
    rw [h.1, map_zero, zero_mul]

/-- A literal zero check yields the polynomial identity under every Gaussian-integer ring homomorphism. Concrete checks use ordinary kernel reduction. -/
theorem eval_eq_zero_of_check (x : Fin 5 → R) (p : Sparse)
    (h : checkZero p = true) : eval φ x p = 0 := eval_zero_of_all φ x p h

end Soundness
end CycleQ2SeedSurfaceSparsePolynomial

#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_eq_zero_of_check
#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_mul

/-! The literal r=57 branch certificate in exact Gaussian sparse form.
All coefficient pairs come unchanged from the stored characteristic-zero
certificate. Small generators are the first argument of sparse multiplication.
-/

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option Elab.async false
namespace CycleQ2SeedSurfaceBranchSparse
open CycleQ2SeedSurfaceSparsePolynomial
open scoped BigOperators

def generators : Fin 8 → Sparse :=
  ![[((6,0,0,0,0),⟨1,0⟩),
    ((0,0,6,0,0),⟨1,0⟩),
    ((0,3,0,3,0),⟨-185193,0⟩)],
    [((3,0,0,0,0),⟨1,0⟩),
    ((1,2,0,0,0),⟨1,0⟩),
    ((0,3,0,0,0),⟨0,-1⟩),
    ((0,0,3,0,0),⟨1,0⟩),
    ((1,0,1,1,0),⟨1,0⟩),
    ((0,1,1,1,0),⟨1,0⟩),
    ((0,0,0,3,0),⟨1,-1⟩)],
    [((6,1,0,0,0),⟨12,0⟩),
    ((5,2,0,0,0),⟨0,-18⟩),
    ((5,0,1,1,0),⟨6,0⟩),
    ((2,2,0,3,0),⟨1666737,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩),
    ((0,2,1,4,0),⟨555579,0⟩)],
    [((5,0,2,0,0),⟨18,0⟩),
    ((2,0,5,0,0),⟨-18,0⟩),
    ((0,2,5,0,0),⟨-6,0⟩),
    ((6,0,0,1,0),⟨6,0⟩),
    ((5,1,0,1,0),⟨6,0⟩),
    ((0,0,6,1,0),⟨-6,0⟩)],
    [((6,0,1,0,0),⟨6,0⟩),
    ((5,1,1,0,0),⟨6,0⟩),
    ((5,0,0,2,0),⟨18,-18⟩),
    ((2,3,0,2,0),⟨1666737,0⟩),
    ((0,5,0,2,0),⟨555579,0⟩),
    ((0,3,1,3,0),⟨555579,0⟩)],
    [((1,1,5,0,0),⟨-12,0⟩),
    ((0,2,5,0,0),⟨0,18⟩),
    ((0,0,6,1,0),⟨-6,0⟩),
    ((0,2,2,3,0),⟨-1666737,0⟩),
    ((1,2,0,4,0),⟨-555579,0⟩),
    ((0,3,0,4,0),⟨-555579,0⟩)],
    [((1,4,0,2,0),⟨1111158,0⟩),
    ((0,5,0,2,0),⟨0,-1666737⟩),
    ((1,2,1,3,0),⟨-555579,0⟩),
    ((0,2,0,5,0),⟨-1666737,1666737⟩)],
    [((1,0,6,0,0),⟨6,0⟩),
    ((0,1,6,0,0),⟨6,0⟩),
    ((0,3,2,2,0),⟨1666737,0⟩),
    ((0,0,5,2,0),⟨18,-18⟩),
    ((1,3,0,3,0),⟨555579,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩)]]

def combine (g n : Fin 8 → Sparse) : Sparse :=
  add (mul (g 0) (n 0)) (add (mul (g 1) (n 1))
    (add (mul (g 2) (n 2)) (add (mul (g 3) (n 3))
    (add (mul (g 4) (n 4)) (add (mul (g 5) (n 5))
    (add (mul (g 6) (n 6)) (mul (g 7) (n 7))))))))

theorem eval_combine {R : Type*} [CommRing R] (φ : GaussianInt →+* R)
    (x : Fin 5 → R) (g n : Fin 8 → Sparse) :
    eval φ x (combine g n) = ∑ k, eval φ x (g k) * eval φ x (n k) := by
  simp only [combine,eval_add,eval_mul,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Fin.reduceSucc]

end CycleQ2SeedSurfaceBranchSparse
end


/- Component: continuation_20261112/MonicRegularConormal.lean -/
section
/-! Conormal bases for two or three monic equations with disjoint leading
monomials. All polynomial and cotangent modules are the actual modules.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators TensorProduct MonomialOrder
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false



#print axioms CycleQ2MonicRegular.pair_relation_coefficients
#print axioms CycleQ2MonicRegular.triple_relation_coefficients
end
end


/- Component: continuation_20261112/SeedLocalizationBoundary.lean -/
section
/-! Actual seed localization boundaries give unrestricted polynomial
boundary witnesses. In particular no fixed pole-order bound is imposed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizationBoundary
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
  CycleQ2NormalConnecting CycleQ2LocalizationBoundary
open CycleQ2SeedCech (curveA curveB)

theorem paired_denominator_identity (r θ : ℂ) (p : Poly) :
    pairedNormalOverlap r θ p *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ) *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ) =
      algebraMap (CurveRing r θ) (Overlap r θ) (-curveMap r θ (derivativeNumerator p)) := by
  have hp : overlapAmbient r θ derivativeA *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (derivativeNumerator p)) := by
    change algebraMap (CurveRing r θ) (Overlap r θ)
        (curveMap r θ (substitute derivativeA)) * _ = _
    rw [← map_mul, ← map_mul, substitute_derivativeA]
  rw [← coe_firstOverlapUnit, ← coe_secondOverlapUnit]
  simp only [pairedNormalOverlap,normalOverlapCoefficient,overlapCoefficient,
    map_zero,mul_zero,zero_sub,map_neg]
  calc
    _ = -(overlapAmbient r θ derivativeA *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)) *
        (((firstOverlapUnit r θ)⁻¹ : (Overlap r θ)ˣ) : Overlap r θ) *
        (firstOverlapUnit r θ : Overlap r θ) *
        (((secondOverlapUnit r θ)⁻¹ : (Overlap r θ)ˣ) : Overlap r θ) *
        (secondOverlapUnit r θ : Overlap r θ) := by ring
    _ = _ := by
      rw [mul_assoc _ _ (firstOverlapUnit r θ : Overlap r θ),
        (firstOverlapUnit r θ).inv_mul,mul_one,
        mul_assoc _ _ (secondOverlapUnit r θ : Overlap r θ),
        (secondOverlapUnit r θ).inv_mul,mul_one,hp]

/-- Actual first- and second-open sections, of arbitrary pole order and
without any homogeneity restriction, clear to the polynomial boundary
relation used by the residue obstruction. -/
theorem paired_boundary_witness (r θ : ℂ) (hr : r ≠ 0) (p : Poly)
    (a : FirstOpen r θ) (b : SecondOpen r θ)
    (h : pairedNormalOverlap r θ p = firstRestriction r θ a + secondRestriction r θ b) :
    ∃ (N M : ℕ) (q s : Poly), 2 ≤ N ∧ 4 ≤ M ∧
      derivativeNumerator p * curveA^(N-2)*curveB^(M-4) -
        (q*curveA^N+s*curveB^M) ∈ curveIdeal r θ := by
  have hnum := paired_denominator_identity r θ p
  rw [h] at hnum
  have hnum' : (firstRestriction r θ a + secondRestriction r θ b) *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ)^1 *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ)^1 =
      algebraMap (CurveRing r θ) (Overlap r θ) (-curveMap r θ (derivativeNumerator p)) := by
    simpa only [pow_one] using hnum
  obtain ⟨N,M,q,s,hN,hM,hclear⟩ := clear_two_open_boundary
    (curveG1 r θ) (curveG2 r θ) (firstRestriction r θ) (secondRestriction r θ)
    (fun z => IsLocalization.Away.awayToAwayRight_eq _ _ z)
    (fun z => IsLocalization.Away.awayToAwayLeft_eq _ _ z) a b
    (-curveMap r θ (derivativeNumerator p)) 1 1 hnum'
  let u : (CurveRing r θ)ˣ := Units.map ((curveMap r θ).comp C).toMonoidHom
    (Units.mk0 (3*r^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)))
  let v : (CurveRing r θ)ˣ := Units.map ((curveMap r θ).comp C).toMonoidHom
    (Units.mk0 3 (by norm_num))
  have hg1 : curveG1 r θ = (u:CurveRing r θ)*(curveMap r θ curveA)^2 := by
    rw [curveG1,ambientCurveMap_g1,map_mul,map_pow]
    rfl
  have hg2 : curveG2 r θ = (v:CurveRing r θ)*(curveMap r θ curveB)^4 := by
    rw [curveG2,ambientCurveMap_g2,map_mul,map_pow]
    rfl
  rw [hg1,hg2] at hclear
  obtain ⟨q',s',heq⟩ := unscale_boundary (curveMap r θ curveA) (curveMap r θ curveB)
    (-curveMap r θ (derivativeNumerator p)) q s u v 2 4 N M hN hM hclear
  obtain ⟨qP,hqP⟩ := Ideal.Quotient.mk_surjective (-q')
  obtain ⟨sP,hsP⟩ := Ideal.Quotient.mk_surjective (-s')
  refine ⟨2*N,4*M,qP,sP,by omega,by omega,?_⟩
  have hNe : 2*N-2=2*(N-1) := by omega
  have hMe : 4*M-4=4*(M-1) := by omega
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change curveMap r θ (_ - _) = 0
  simp only [map_sub,map_add,map_mul,map_pow,hNe,hMe]
  change curveMap r θ (derivativeNumerator p) * (curveMap r θ curveA)^(2*(N-1)) *
      (curveMap r θ curveB)^(4*(M-1)) -
      (Ideal.Quotient.mk (curveIdeal r θ) qP * (curveMap r θ curveA)^(2*N) +
       Ideal.Quotient.mk (curveIdeal r θ) sP * (curveMap r θ curveB)^(4*M)) = 0
  rw [hqP,hsP]
  linear_combination -heq

end CycleQ2SeedLocalizationBoundary

#print axioms CycleQ2SeedLocalizationBoundary.paired_denominator_identity
#print axioms CycleQ2SeedLocalizationBoundary.paired_boundary_witness
end
end


/- Component: continuation_20261112/SurfaceJacobianGrading.lean -/
section
/-! Homogeneous Jacobian-minor generators of the actual surface family,
with exact coefficient-map and literal seed bindings. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceSurfaceGradientOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousPrimeCoverOpen
open CycleQ2IncidenceBasepointOpen (Coeff familyF familyH seedEvaluation)

def minor {R : Type*} [CommRing R] (F h : Poly R) (j k : Fin 5) : Poly R :=
  pderiv j F * pderiv k h - pderiv k F * pderiv j h

abbrev Index := Fin 2 ⊕ (Fin 5 × Fin 5)

def generators : Index → Poly Coeff
  | Sum.inl j => ![familyF,familyH] j
  | Sum.inr (j,k) => minor familyF familyH j k ^ 3

def degree : Index → ℕ
  | Sum.inl j => ![6,3] j
  | Sum.inr (j,k) => 3*(9-(fullGrading j).1-(fullGrading k).1)

theorem pderiv_homogeneous {R : Type*} [CommRing R] {p : Poly R}
    (d : ℕ) (hd : 2 ≤ d) (hp : HG p (d,0)) (j : Fin 5) :
    HG (pderiv j p) (d-(fullGrading j).1,-(fullGrading j).2) := by
  apply hp.pderiv
  apply Prod.ext
  · have hj : (fullGrading j).1 ≤ 2 := by fin_cases j <;> decide
    simp only [Prod.fst_add]
    omega
  · simp

theorem minor_homogeneous {R : Type*} [CommRing R] {F h : Poly R}
    (hF : HG F (6,0)) (hh : HG h (3,0)) (j k : Fin 5) :
    HG (minor F h j k)
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
  have h1 := (pderiv_homogeneous 6 (by decide) hF j).mul
    (pderiv_homogeneous 3 (by decide) hh k)
  have h2 := (pderiv_homogeneous 6 (by decide) hF k).mul
    (pderiv_homogeneous 3 (by decide) hh j)
  have hj : (fullGrading j).1 ≤ 2 := by fin_cases j <;> decide
  have hk : (fullGrading k).1 ≤ 2 := by fin_cases k <;> decide
  have hgrade1 : (6-(fullGrading j).1,-(fullGrading j).2) +
      (3-(fullGrading k).1,-(fullGrading k).2) =
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
    apply Prod.ext
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add,sub_eq_add_neg]
  have hgrade2 : (6-(fullGrading k).1,-(fullGrading k).2) +
      (3-(fullGrading j).1,-(fullGrading j).2) =
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
    apply Prod.ext
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add,sub_eq_add_neg]; abel
  rw [hgrade1] at h1
  rw [hgrade2] at h2
  exact h1.sub h2

theorem generators_homogeneous (i : Index) : HG (generators i) (degree i,0) := by
  cases i with
  | inl j =>
    fin_cases j
    · exact fullInvariantPolynomial_homogeneous 6 _
    · exact fullInvariantPolynomial_homogeneous 3 _
  | inr jk =>
    rcases jk with ⟨j,k⟩
    have hh := (minor_homogeneous (R := Coeff) (F := familyF) (h := familyH)
      (fullInvariantPolynomial_homogeneous 6 _)
      (fullInvariantPolynomial_homogeneous 3 _) j k).pow 3
    change HG (minor familyF familyH j k ^ 3)
      (3*(9-(fullGrading j).1-(fullGrading k).1),0)
    convert hh using 1
    apply Prod.ext
    · simp [nsmul_eq_mul]
    · have h3 : (3 : ZMod 3) = 0 := by decide
      simp [nsmul_eq_mul,h3]

theorem minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F h : Poly R) (j k : Fin 5) :
    map φ (minor F h j k) = minor (map φ F) (map φ h) j k := by
  simp only [minor,map_sub,map_mul,←pderiv_map]

theorem familyF_seed : map seedEvaluation familyF =
    CycleQ2IncidenceEquations.smoothF (57:ℂ) Complex.I := by
  have h := congrFun CycleQ2IncidenceBasepointOpen.seed_universalGenerators (10:Fin 11)
  simpa [CycleQ2IncidenceBasepointOpen.universalGenerators,
    CycleQ2IncidenceBasepointOpen.generators,CycleQ2IncidenceBasepointOpen.seedFamilyGenerators,
    familyF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using h

theorem familyH_seed : map seedEvaluation familyH =
    CycleQ2IncidenceEquations.smoothH Complex.I := by
  have h := congrFun CycleQ2IncidenceBasepointOpen.seed_universalGenerators (9:Fin 11)
  simpa [CycleQ2IncidenceBasepointOpen.universalGenerators,
    CycleQ2IncidenceBasepointOpen.generators,CycleQ2IncidenceBasepointOpen.seedFamilyGenerators,
    familyH,Matrix.cons_val_succ',Matrix.cons_val_zero'] using h

end CycleQ2IncidenceSurfaceGradientOpen

#print axioms CycleQ2IncidenceSurfaceGradientOpen.generators_homogeneous
#print axioms CycleQ2IncidenceSurfaceGradientOpen.familyF_seed
#print axioms CycleQ2IncidenceSurfaceGradientOpen.familyH_seed
end
end


