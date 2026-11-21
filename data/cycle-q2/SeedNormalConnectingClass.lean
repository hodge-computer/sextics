import Proposal.GeometricSeedSurfaceGradient
import Proposal.IncidenceKodairaSpencerMap

/-!
# The nonzero normal connecting class on the seed
-/

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

/- Component: continuation_20261112/SeedNormalRestriction.lean -/
section
/-!
# Restriction and exactness for the genuine seed normal map

Restriction of normal homomorphisms is scalar extension of Hom, defined
through the tensor-Hom adjunction. It commutes with the dual of the actual
natural cotangent map. On either denominator chart, the actual kernel is
freely generated by the equation vector (g2,-g1,0), and this generator is
compatible with every algebra restriction. No independent normal matrix
or connecting-class comparison is assumed.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false



#print axioms CycleQ2NormalRestriction.naturalNormalMap_restriction
#print axioms CycleQ2NormalRestriction.firstKernelEquiv
#print axioms CycleQ2NormalRestriction.secondKernelEquiv
#print axioms CycleQ2NormalRestriction.kernelParam_restriction
end
end

/- Component: continuation_20261112/SeedGlobalConormal.lean -/
section
/-! Global equation-class bases of the actual seed conormal modules.
These use polynomial regularity and therefore need no Jacobian chart.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedGlobalConormal
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2SeedRegularLeading CycleQ2NaturalNormalMap

section ScalarExtension
variable {S : Type*} [CommRing S] [Algebra WeightedPoly S]

/-- Both sides of the natural dual cotangent map are now expressed in
genuine global equation-class bases. -/
theorem naturalNormalMap_in_global_equation_bases
    [Algebra ℂ S] [IsScalarTower ℂ WeightedPoly S] (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap WeightedPoly S p=0)
    (φ : S ⊗[WeightedPoly] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ((surfaceConormalBasis r θ hI).constr S).symm (naturalNormalMap r θ φ) =
      equationMap (algebraMap WeightedPoly S (originalG1 r))
        (algebraMap WeightedPoly S originalG2) (algebraMap WeightedPoly S (thetaK θ))
        (((seedConormalBasis r θ hI).constr S).symm φ) := by
  change (fun j => naturalNormalMap r θ φ (surfaceConormalBasis r θ hI j)) =
    equationMap _ _ _ (fun i => φ (seedConormalBasis r θ hI i))
  simpa only [surfaceConormalBasis_apply,seedConormalBasis_apply] using
    naturalNormalMap_equation_coordinates (S := S) r θ φ

end ScalarExtension
end CycleQ2SeedGlobalConormal

#print axioms CycleQ2SeedGlobalConormal.seedConormalBasis
#print axioms CycleQ2SeedGlobalConormal.surfaceConormalBasis
#print axioms CycleQ2SeedGlobalConormal.naturalNormalMap_in_global_equation_bases
end
end

/- Component: continuation_20261112/SeedActualNormalCech.lean -/
section
/-!
# The genuine normal connecting class on the two actual seed opens

The two coefficient rings and their overlap are the existing localizations
of the actual curve, with the polynomial algebra structures supplied by
w = -x2². Global equation-class conormal bases realize the local lift
formulas as genuine normal homomorphisms. Their canonical Hom restrictions
have equal target image, so their difference defines an actual kernel
cochain. The kernel Cech quotient is identified with the scalar quotient
by the two restriction images, and the connecting class corresponds to
normalOverlapCoefficient.

This is the ungraded two-open Cech module of the affine cone. Its graded
pieces, projective sheaf interpretation, and Abel–Jacobi comparison are
separate steps. The final residue theorem is an identity on the genuine
connecting representative, using the previously constructed Laurent maps.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ActualNormalCech

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap CycleQ2NormalConnecting
  CycleQ2SeedTrace CycleQ2GenuineNormalConnecting CycleQ2NormalRestriction
  CycleQ2SeedGlobalConormal CycleQ2SeedCechTheta

/-- Altering either local lift by an arbitrary actual kernel section
changes the kernel cochain by a genuine two-open coboundary. -/
theorem connectingClass_change_lifts (r θ : ℂ) (A L : P)
    (a : FirstKernel r θ) (b : SecondKernel r θ) :
    (Submodule.Quotient.mk (connectingRepresentative r θ A L +
      firstKernelRestriction r θ a - secondKernelRestriction r θ b) : NormalCech r θ) =
        connectingClass r θ A L := by
  apply (Submodule.Quotient.eq (normalBoundaries r θ)).mpr
  have ha : firstKernelRestriction r θ a ∈ normalBoundaries r θ :=
    Submodule.mem_sup_left (show firstKernelRestriction r θ a ∈
      LinearMap.range (firstKernelRestriction r θ) from ⟨a, rfl⟩)
  have hb : secondKernelRestriction r θ b ∈ normalBoundaries r θ :=
    Submodule.mem_sup_right (show secondKernelRestriction r θ b ∈
      LinearMap.range (secondKernelRestriction r θ) from ⟨b, rfl⟩)
  change connectingRepresentative r θ A L + firstKernelRestriction r θ a -
    secondKernelRestriction r θ b - connectingRepresentative r θ A L ∈ _
  convert (normalBoundaries r θ).sub_mem ha hb using 1 <;> abel

/-- Scalar boundaries remain boundaries after multiplication by a function
from the actual curve ring; this does not require choosing a polynomial lift. -/
theorem scalarBoundaries_mul_base (r θ : ℂ) (z : Overlap r θ) (p : CurveRing r θ)
    (hz : z ∈ scalarBoundaries r θ) :
    z * algebraMap (CurveRing r θ) (Overlap r θ) p ∈ scalarBoundaries r θ := by
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hz
  apply Submodule.mem_sup.mpr
  refine ⟨firstRestrictionAlg r θ (a * algebraMap (CurveRing r θ) (FirstOpen r θ) p),
    ⟨a * algebraMap (CurveRing r θ) (FirstOpen r θ) p, rfl⟩,
    secondRestrictionAlg r θ (b * algebraMap (CurveRing r θ) (SecondOpen r θ) p),
    ⟨b * algebraMap (CurveRing r θ) (SecondOpen r θ) p, rfl⟩, ?_⟩
  change firstRestriction r θ (a * algebraMap (CurveRing r θ) (FirstOpen r θ) p) +
    secondRestriction r θ (b * algebraMap (CurveRing r θ) (SecondOpen r θ) p) = _
  simp only [map_mul, firstRestriction, secondRestriction,
    IsLocalization.Away.awayToAwayRight_eq, IsLocalization.Away.awayToAwayLeft_eq]
  rw [← add_mul]
  exact congrArg (fun t : Overlap r θ => t * algebraMap (CurveRing r θ) (Overlap r θ) p) hab

theorem coefficient_boundary_of_connectingClass_zero (r θ : ℂ) (A L : P)
    (hz : connectingClass r θ A L = 0) :
    normalOverlapCoefficient r θ A L ∈ scalarBoundaries r θ := by
  have hh := congrArg (normalCechEquivalence r θ) hz
  rw [connectingClass_eq_scalar, map_zero] at hh
  exact (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mp hh

theorem paired_boundary_of_connectingClass_zero (r θ : ℂ) (p : CycleQ2SeedTrace.Poly)
    (hz : connectingClass r θ derivativeA 0 = 0) :
    pairedNormalOverlap r θ p ∈ scalarBoundaries r θ := by
  exact scalarBoundaries_mul_base r θ _ (curveMap r θ p)
    (coefficient_boundary_of_connectingClass_zero r θ derivativeA 0 hz)

/-- Pair the genuine connecting representative with the actual cubic. The
residue comparison here is on representatives, before graded descent. -/
def pairedConnectingRepresentative (r θ : ℂ) (p : CycleQ2SeedTrace.Poly) : Overlap r θ :=
  (overlapKernelEquivalence r θ).symm
      (connectingRepresentative r θ CycleQ2NormalConnecting.derivativeA 0) *
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)

theorem pairedConnectingRepresentative_eq (r θ : ℂ) (p : CycleQ2SeedTrace.Poly) :
    pairedConnectingRepresentative r θ p = CycleQ2NormalConnecting.pairedNormalOverlap r θ p := by
  rw [pairedConnectingRepresentative, connectingRepresentative_eq,
    LinearEquiv.symm_apply_apply]
  rfl

/-- The already computed incidence trace is now evaluated on a genuine
normal connecting representative, via the actual overlap localization. -/
theorem connectingRepresentative_residue (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) :
    CycleQ2SeedCechTheta.endpointResidue r θ false
        (overlapToLaurent r θ false hr
          (pairedConnectingRepresentative r θ (cubicDeformation v))) -
      CycleQ2SeedCechTheta.endpointResidue r θ true
        (overlapToLaurent r θ true hr
          (pairedConnectingRepresentative r θ (cubicDeformation v))) =
      -(3 * r)⁻¹ * derivativeTrace θ v := by
  simp only [pairedConnectingRepresentative_eq]
  exact actual_overlap_trace_deformation r θ hr v

end CycleQ2ActualNormalCech

#print axioms CycleQ2ActualNormalCech.normalCechEquivalence
#print axioms CycleQ2ActualNormalCech.connectingClass_eq_scalar
#print axioms CycleQ2ActualNormalCech.connectingClass_change_lifts
#print axioms CycleQ2ActualNormalCech.pairedConnectingRepresentative_eq

#print axioms CycleQ2ActualNormalCech.connectingRepresentative_residue
end
end

/- Component: continuation_20261112/SeedNormalNonzero.lean -/
section
/-!
# Nonvanishing of the genuine ambient-test normal connecting class

A vanishing genuine kernel Cech class would make its cubic-paired scalar
representative a sum of actual single-open sections. Localization clearing
then gives an unrestricted polynomial boundary witness. Homogeneous
projection produces a boundary in the already checked all-poles canonical
Cech complex, contradicting the computed nonzero residue.

The class here is the ambient test direction (A=x2*x3³*w,L=0). It is distinct
from the vanishing normal obstruction of the fixed-sextic incidence family.
The chosen curve is not itself invariant under the order-three action; an
orbit trace comparison is not asserted here. The test polynomial has
character one, the invariant cubic has character zero, and the ambient
residue volume has character two. The corresponding Serre-dual surface
cohomology component for the eventual comparison is character one.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedNormalNonzero

open CycleQ2NormalConnecting CycleQ2SeedCechTheta CycleQ2ActualNormalCech
  CycleQ2SeedBoundaryProjection CycleQ2SeedLocalizationBoundary

/-- A nonzero cubic trace detects the genuine ambient-test normal class in
the actual two-open kernel quotient, including all ungraded boundaries. -/
theorem ambient_test_connectingClass_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    connectingClass r θ derivativeA 0 ≠ 0 := by
  intro hz
  have hbd := paired_boundary_of_connectingClass_zero r θ (cubicDeformation v) hz
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hbd
  change firstRestriction r θ a + secondRestriction r θ b =
    pairedNormalOverlap r θ (cubicDeformation v) at hab
  obtain ⟨N, M, q, s, hN, hM, hmem⟩ :=
    paired_boundary_witness r θ hr (cubicDeformation v) a b hab.symm
  exact no_unrestricted_boundary r θ hr v hv N M q s hN hM hmem

/-- The existing explicit cubic detects this actual normal class for every
nonzero seed parameter r and every theta. -/
theorem ambient_test_nonzero (r θ : ℂ) (hr : r ≠ 0) :
    connectingClass r θ derivativeA 0 ≠ 0 := by
  apply ambient_test_connectingClass_ne_zero r θ hr selectedTangent
  rw [selectedTangent_trace]
  norm_num

/-- In particular, the literal smooth incidence seed has a nonzero genuine
ambient-test normal connecting class. -/
theorem actual_seed_ambient_test_nonzero :
    connectingClass 57 1 derivativeA 0 ≠ 0 :=
  ambient_test_nonzero 57 1 (by norm_num)

end CycleQ2SeedNormalNonzero

#print axioms CycleQ2SeedNormalNonzero.ambient_test_connectingClass_ne_zero
#print axioms CycleQ2SeedNormalNonzero.ambient_test_nonzero
#print axioms CycleQ2SeedNormalNonzero.actual_seed_ambient_test_nonzero
end
end

/- Component: continuation_20261112/MovingClassBridge.lean -/
section Q2UncompiledNormalKoszulBridge

/-!
# The literal seed quotient maps to the genuine normal Cech module

Development continuation; compilation status is recorded in solution.md.
This extends `CycleQ2SeedNormalNonzero`.

The map sends a polynomial numerator p to p/(g1*g2) on the actual curve
overlap. Each of the five complete-intersection generators is killed:
the three curve equations vanish already in the overlap, and each of the
two remaining generators gives a single-open boundary. Consequently the
map factors through the existing `CycleQ2SeedTrace.SeedAlgebra`.

The target is the existing quotient of actual normal-kernel sections,
identified with scalar sections by `normalCechEquivalence`. This fragment
does not identify that ungraded quotient with projective sheaf cohomology,
construct the surface semiregularity map, or assert a Serre trace comparison.
-/

section
noncomputable section
set_option autoImplicit false

namespace CycleQ2NormalKoszulBridge

open CycleQ2ConormalJacobian CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2ActualNormalCech CycleQ2SeedNormalNonzero

/-- The simple-pole numerator map in the actual overlap localization. -/
def simplePoleRepresentative (r θ : ℂ) : P →ₗ[P] Overlap r θ where
  toFun p := algebraMap P (Overlap r θ) p *
    (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
    (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)
  map_add' p q := by
    simp only [map_add, add_mul]
  map_smul' a p := by
    simp only [smul_eq_mul, Algebra.smul_def, map_mul, mul_assoc, RingHom.id_apply]

@[simp] theorem simplePoleRepresentative_apply (r θ : ℂ) (p : P) :
    simplePoleRepresentative r θ p = algebraMap P (Overlap r θ) p *
      (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
      (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) := rfl

/-- The actual scalar Cech class of the simple-pole representative. -/
def simplePoleClass (r θ : ℂ) : P →ₗ[P] ScalarCech r θ :=
  (scalarBoundaries r θ).mkQ.comp (simplePoleRepresentative r θ)

@[simp] theorem simplePoleClass_apply (r θ : ℂ) (p : P) :
    simplePoleClass r θ p =
      (Submodule.Quotient.mk (simplePoleRepresentative r θ p) : ScalarCech r θ) := rfl

theorem simplePoleRepresentative_zero_of_curve (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) :
    simplePoleRepresentative r θ p = 0 := by
  rw [simplePoleRepresentative_apply, overlap_annihilates r θ p hp,
    zero_mul, zero_mul]

theorem simplePoleClass_zero_of_curve (r θ : ℂ) (p : P)
    (hp : p ∈ ambientCurveIdeal r θ) : simplePoleClass r θ p = 0 := by
  change (scalarBoundaries r θ).mkQ (simplePoleRepresentative r θ p) = 0
  rw [simplePoleRepresentative_zero_of_curve r θ p hp, map_zero]

theorem simplePoleClass_curveEquation (r θ : ℂ) (i : Fin 3) :
    simplePoleClass r θ (curveEquations r θ i) = 0 :=
  simplePoleClass_zero_of_curve r θ _ (curveEquation_mem r θ i)

/-- Cancelling g1 leaves the inverse of g2, a section on the second open. -/
theorem simplePoleRepresentative_g1 (r θ : ℂ) :
    simplePoleRepresentative r θ (originalG1 r) =
      secondRestriction r θ (↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ) := by
  rw [simplePoleRepresentative_apply, ← firstOverlapUnit_value,
    (firstOverlapUnit r θ).mul_inv, one_mul]
  rfl

/-- Cancelling g2 leaves the inverse of g1, a section on the first open. -/
theorem simplePoleRepresentative_g2 (r θ : ℂ) :
    simplePoleRepresentative r θ originalG2 =
      firstRestriction r θ (↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ) := by
  rw [simplePoleRepresentative_apply, ← secondOverlapUnit_value]
  calc
    (secondOverlapUnit r θ : Overlap r θ) *
        (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
        (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) =
        (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
          ((secondOverlapUnit r θ : Overlap r θ) *
            (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ)) := by ring
    _ = (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) := by
      rw [(secondOverlapUnit r θ).mul_inv, mul_one]
    _ = _ := rfl

theorem simplePoleClass_g1 (r θ : ℂ) :
    simplePoleClass r θ (originalG1 r) = 0 := by
  rw [simplePoleClass_apply]
  apply (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mpr
  rw [simplePoleRepresentative_g1]
  exact Submodule.mem_sup_right
    (show secondRestriction r θ (↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ) ∈
      LinearMap.range (secondRestrictionAlg r θ).toLinearMap from
        ⟨(↑((secondOpenUnit r θ)⁻¹) : SecondOpen r θ), rfl⟩)

theorem simplePoleClass_g2 (r θ : ℂ) :
    simplePoleClass r θ originalG2 = 0 := by
  rw [simplePoleClass_apply]
  apply (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mpr
  rw [simplePoleRepresentative_g2]
  exact Submodule.mem_sup_left
    (show firstRestriction r θ (↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ) ∈
      LinearMap.range (firstRestrictionAlg r θ).toLinearMap from
        ⟨(↑((firstOpenUnit r θ)⁻¹) : FirstOpen r θ), rfl⟩)

/-- Every generator of the existing five-generator seed ideal maps to zero.
No abstract quotient-pairing or geometric trace hypothesis is supplied. -/
theorem originalIdeal_le_ker (r : ℂ) :
    originalIdeal r ≤ LinearMap.ker (simplePoleClass r 0) := by
  rw [originalIdeal, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  change simplePoleClass r 0 (originalRelations r i) = 0
  fin_cases i
  · simpa [originalRelations, curveEquations] using
      simplePoleClass_curveEquation r 0 0
  · simpa [originalRelations] using simplePoleClass_g1 r 0
  · simpa [originalRelations, curveEquations] using
      simplePoleClass_curveEquation r 0 1
  · simpa [originalRelations] using simplePoleClass_g2 r 0
  · simpa [originalRelations, curveEquations, thetaH] using
      simplePoleClass_curveEquation r 0 2

/-- The Koszul simple-pole boundary from the literal seed quotient to the
existing scalar Cech module. The construction needs no smoothness premise. -/
def seedScalarBoundary (r : ℂ) : SeedAlgebra r →ₗ[P] ScalarCech r 0 :=
  (originalIdeal r).liftQ (simplePoleClass r 0) (originalIdeal_le_ker r)

@[simp] theorem seedScalarBoundary_mk (r : ℂ) (p : P) :
    seedScalarBoundary r (seedQuotient r p) = simplePoleClass r 0 p := rfl

/-- The same actual boundary with values in genuine normal-kernel sections
modulo the actual restriction boundaries. -/
def seedNormalBoundary (r : ℂ) : SeedAlgebra r →ₗ[P] NormalCech r 0 :=
  (normalCechEquivalence r 0).symm.toLinearMap.comp (seedScalarBoundary r)

@[simp] theorem normalCechEquivalence_seedNormalBoundary (r : ℂ)
    (x : SeedAlgebra r) :
    normalCechEquivalence r 0 (seedNormalBoundary r x) = seedScalarBoundary r x := by
  change normalCechEquivalence r 0
      ((normalCechEquivalence r 0).symm (seedScalarBoundary r x)) = _
  exact (normalCechEquivalence r 0).apply_symm_apply _

/-- The actual normal lift difference has the simple-pole numerator kL-A. -/
theorem normalOverlapCoefficient_eq_simplePole (r θ : ℂ) (A L : P) :
    normalOverlapCoefficient r θ A L =
      simplePoleRepresentative r θ (thetaK θ * L - A) := by
  simp only [normalOverlapCoefficient, overlapCoefficient,
    simplePoleRepresentative_apply, overlap_algebraMap, map_sub, map_mul]
  ring

theorem connectingClass_eq_simplePole (r θ : ℂ) (A L : P) :
    connectingClass r θ A L =
      (normalCechEquivalence r θ).symm
        (simplePoleClass r θ (thetaK θ * L - A)) := by
  apply (normalCechEquivalence r θ).injective
  rw [connectingClass_eq_scalar, LinearEquiv.apply_symm_apply]
  rw [simplePoleClass_apply, normalOverlapCoefficient_eq_simplePole]

/-- The existing normal connecting class factors through the literal seed
algebra. In particular, changing kL-A by any of the five ideal generators
does not change the actual normal class. -/
theorem connectingClass_eq_seedNormalBoundary (r : ℂ) (A L : P) :
    connectingClass r 0 A L =
      seedNormalBoundary r (seedQuotient r (originalK * L - A)) := by
  rw [connectingClass_eq_simplePole]
  change (normalCechEquivalence r 0).symm
      (simplePoleClass r 0 (thetaK 0 * L - A)) =
    (normalCechEquivalence r 0).symm
      (simplePoleClass r 0 (originalK * L - A))
  simp only [thetaK, map_zero, zero_mul, add_zero]

/-- This is an actual nonzero value of the constructed quotient map,
detected by the already proved localization-residue calculation. -/
theorem seedNormalBoundary_test_ne_zero (r : ℂ) (hr : r ≠ 0) :
    seedNormalBoundary r (seedQuotient r (-derivativeA)) ≠ 0 := by
  have h := ambient_test_nonzero r 0 hr
  rw [connectingClass_eq_seedNormalBoundary, mul_zero, zero_sub] at h
  exact h

theorem seedNormalBoundary_ne_zero (r : ℂ) (hr : r ≠ 0) :
    seedNormalBoundary r ≠ 0 := by
  intro hz
  apply seedNormalBoundary_test_ne_zero r hr
  rw [hz, LinearMap.zero_apply]

section DegreeNine

open MvPolynomial CycleQ2SeedCechTheta CycleQ2SeedBoundaryProjection
  CycleQ2SeedLocalizationBoundary

/-- The literal inclusion of the four unweighted coordinates into the
five-variable weighted polynomial ring, before imposing w=-x2^2. -/
def polynomialLift : Poly →ₐ[ℂ] P :=
  MvPolynomial.aeval ![X 0, X 1, X 2, X 3]

@[simp] theorem substitute_polynomialLift (p : Poly) :
    substitute (polynomialLift p) = p := by
  have hh : substitute.comp polynomialLift = AlgHom.id ℂ Poly := by
    ext1 i
    change substitute (polynomialLift (X i)) = X i
    fin_cases i <;> simp [polynomialLift, substitute]
  exact congrArg (fun f : Poly →ₐ[ℂ] Poly => f p) hh

/-- Eliminating w and lifting back does not change the class in the literal
five-variable seed algebra: the eliminated equation is one of its generators. -/
theorem seedQuotient_polynomialLift_substitute (r : ℂ) (p : P) :
    seedQuotient r (polynomialLift (substitute p)) = seedQuotient r p := by
  have hf2 : seedQuotient r originalF2 = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact Ideal.subset_span ⟨2, rfl⟩
  have hw : seedQuotient r (X 4) = -((seedQuotient r (X 2)) ^ 2) := by
    rw [originalF2, map_add, map_pow] at hf2
    exact eq_neg_of_add_eq_zero_left hf2
  have hh : (seedQuotient r).comp (polynomialLift.comp substitute) = seedQuotient r := by
    ext1 i
    change seedQuotient r (polynomialLift (substitute (X i))) = seedQuotient r (X i)
    fin_cases i <;> simp [polynomialLift, substitute, hw]
  exact congrArg (fun f : P →ₐ[ℂ] SeedAlgebra r => f p) hh

theorem simplePoleClass_substitute (r : ℂ) (p : P) :
    simplePoleClass r 0 p = simplePoleClass r 0 (polynomialLift (substitute p)) := by
  have hh := congrArg (seedScalarBoundary r) (seedQuotient_polynomialLift_substitute r p)
  exact hh.symm

private theorem lift_relation_zero (r : ℂ) :
    polynomialLift (relation r 0) = originalF1 r := by
  simp [polynomialLift, relation, originalF1]

private theorem lift_relation_three (r : ℂ) :
    polynomialLift (relation r 3) = originalH := by
  simp [polynomialLift, relation, h, b, originalH, originalB]

private theorem g1_lift_relation (r : ℂ) :
    originalG1 r =
      originalF1 r * (X 0 ^ 2 + C (2 * r) * X 1 * X 3) +
        C (3 * r ^ 2) * polynomialLift (relation r 1) := by
  simp [polynomialLift, relation, originalG1, originalF1, map_mul, map_pow]
  simp only [map_ofNat]
  ring

private theorem g2_lift_relation (r : ℂ) :
    originalG2 = originalF2 * (X 4 - 2 * X 2 ^ 2) +
      C (3 : ℂ) * polynomialLift (relation r 2) := by
  simp [polynomialLift, relation, originalG2, originalF2]
  simp only [map_ofNat]
  ring

private theorem mem_of_constant_mul (I : Ideal P) (c : ℂ) (hc : c ≠ 0)
    (p : P) (hp : C c * p ∈ I) : p ∈ I := by
  have hh := I.mul_mem_left (C (c⁻¹)) hp
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

/-- The four-variable relation ideal maps into the original five-variable
ideal. The only divisions are by 3 and by 3*r^2, with r explicitly nonzero. -/
theorem polynomialLift_relation_mem (r : ℂ) (hr : r ≠ 0) (i : Fin 4) :
    polynomialLift (relation r i) ∈ originalIdeal r := by
  have hg (j : Fin 5) : originalRelations r j ∈ originalIdeal r :=
    Ideal.subset_span ⟨j, rfl⟩
  have hf1 : originalF1 r ∈ originalIdeal r := hg 0
  have hg1 : originalG1 r ∈ originalIdeal r := hg 1
  have hf2 : originalF2 ∈ originalIdeal r := hg 2
  have hg2 : originalG2 ∈ originalIdeal r := hg 3
  fin_cases i
  · change polynomialLift (relation r 0) ∈ originalIdeal r
    rw [lift_relation_zero]
    exact hf1
  · apply mem_of_constant_mul (originalIdeal r) (3 * r ^ 2)
      (mul_ne_zero (by norm_num) (pow_ne_zero _ hr))
    have hh := (originalIdeal r).sub_mem hg1
      ((originalIdeal r).mul_mem_right
        (X 0 ^ 2 + C (2 * r) * X 1 * X 3) hf1)
    rw [g1_lift_relation, add_sub_cancel_left] at hh
    exact hh
  · apply mem_of_constant_mul (originalIdeal r) (3 : ℂ) (by norm_num)
    have hh := (originalIdeal r).sub_mem hg2
      ((originalIdeal r).mul_mem_right (X 4 - 2 * X 2 ^ 2) hf2)
    rw [g2_lift_relation r, add_sub_cancel_left] at hh
    exact hh
  · change polynomialLift (relation r 3) ∈ originalIdeal r
    rw [lift_relation_three]
    exact hg 4

theorem polynomialLift_mem (r : ℂ) (hr : r ≠ 0) {p : Poly}
    (hp : p ∈ reducedIdeal r) : polynomialLift p ∈ originalIdeal r := by
  have hle : reducedIdeal r ≤ Ideal.comap polynomialLift.toRingHom (originalIdeal r) := by
    rw [reducedIdeal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact polynomialLift_relation_mem r hr i
  exact hle hp

/-- An explicit comparison between the two existing quotient algebras,
used here as a complex-linear map. -/
def reducedToSeed (r : ℂ) (hr : r ≠ 0) : ReducedAlgebra r →ₗ[ℂ] SeedAlgebra r :=
  ((reducedIdeal r).restrictScalars ℂ).liftQ
    ((seedQuotient r).toLinearMap.comp polynomialLift.toLinearMap) (by
      intro p hp
      change seedQuotient r (polynomialLift p) = 0
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (polynomialLift_mem r hr hp))

@[simp] theorem reducedToSeed_mk (r : ℂ) (hr : r ≠ 0) (p : Poly) :
    reducedToSeed r hr (reducedQuotient r p) = seedQuotient r (polynomialLift p) := rfl

/-- The actual simple-pole class attached to the four-variable quotient. -/
def reducedScalarBoundary (r : ℂ) (hr : r ≠ 0) :
    ReducedAlgebra r →ₗ[ℂ] ScalarCech r 0 :=
  ((seedScalarBoundary r).restrictScalars ℂ).comp (reducedToSeed r hr)

@[simp] theorem reducedScalarBoundary_mk (r : ℂ) (hr : r ≠ 0) (p : Poly) :
    reducedScalarBoundary r hr (reducedQuotient r p) =
      simplePoleClass r 0 (polynomialLift p) := rfl

/-- The image in the actual Cech module of the distinguished degree-nine
normalization monomial. -/
def normalizationCechClass (r : ℂ) (hr : r ≠ 0) : ScalarCech r 0 :=
  reducedScalarBoundary r hr (normalizationClass r)

/-- The existing quotient trace is the coefficient of the actual simple-pole
class on the degree-nine image. This does not presuppose a Serre trace. -/
theorem reducedScalarBoundary_degreeNine (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) {x : ReducedAlgebra r} (hx : x ∈ degreeNinePiece r) :
    reducedScalarBoundary r hr x =
      reducedTrace r hcube x • normalizationCechClass r hr := by
  calc
    reducedScalarBoundary r hr x = reducedScalarBoundary r hr
        (reducedTrace r hcube x • normalizationClass r) :=
      congrArg (reducedScalarBoundary r hr) (degreeNine_class_eq_trace_smul r hcube hx)
    _ = _ := map_smul (reducedScalarBoundary r hr) _ _

theorem simplePoleClass_degreeNine (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    simplePoleClass r 0 (polynomialLift p) =
      traceLinear r p • normalizationCechClass r hr := by
  simpa only [reducedScalarBoundary_mk, reducedTrace_mk] using
    (reducedScalarBoundary_degreeNine r hr hcube
      (x := reducedQuotient r p) ⟨p, hp, rfl⟩)

/-- Pairing the ambient-test normal class with a cubic is exactly the
simple-pole class of the lifted negative derivative numerator. -/
theorem simplePoleRepresentative_lift_derivative (r θ : ℂ) (p : Poly) :
    simplePoleRepresentative r θ (polynomialLift (-derivativeNumerator p)) =
      pairedNormalOverlap r θ p := by
  simp only [simplePoleRepresentative_apply, overlap_algebraMap, overlapAmbient,
    ambientCurveMap, RingHom.comp_apply, substitute_polynomialLift,
    pairedNormalOverlap, normalOverlapCoefficient, overlapCoefficient,
    map_zero, mul_zero, zero_sub]
  rw [← substitute_derivativeA p]
  simp only [show ∀ x : Poly, substitute.toRingHom (polynomialLift x) = x from
    substitute_polynomialLift]
  simp only [map_neg, map_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  ring

/-- The same all-poles boundary argument used for the genuine normal class
also detects the cubic-paired scalar class itself. -/
theorem pairedScalarClass_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    (Submodule.Quotient.mk
      (pairedNormalOverlap r θ (cubicDeformation v)) : ScalarCech r θ) ≠ 0 := by
  intro hz
  have hbd := (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mp hz
  obtain ⟨x, ⟨a, rfl⟩, y, ⟨b, rfl⟩, hab⟩ := Submodule.mem_sup.mp hbd
  change firstRestriction r θ a + secondRestriction r θ b =
    pairedNormalOverlap r θ (cubicDeformation v) at hab
  obtain ⟨N, M, q, s, hN, hM, hmem⟩ :=
    paired_boundary_witness r θ hr (cubicDeformation v) a b hab.symm
  exact no_unrestricted_boundary r θ hr v hv N M q s hN hM hmem

/-- The distinguished degree-nine image is nonzero in the actual ungraded
Cech quotient, including boundaries with unrestricted pole orders. -/
theorem normalizationCechClass_ne_zero (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) : normalizationCechClass r hr ≠ 0 := by
  intro hz
  have hv : derivativeTrace 0 selectedTangent ≠ 0 := by
    rw [selectedTangent_trace]
    norm_num
  apply pairedScalarClass_ne_zero r 0 hr selectedTangent hv
  rw [← simplePoleRepresentative_lift_derivative]
  change simplePoleClass r 0
    (polynomialLift (-derivativeNumerator (cubicDeformation selectedTangent))) = 0
  rw [simplePoleClass_degreeNine r hr hcube _
    (derivativeNumerator_homogeneous selectedTangent).neg, hz, smul_zero]

/-- The existing finite trace detects vanishing of the genuine simple-pole
class for every homogeneous degree-nine numerator, not just the saved matrix. -/
theorem simplePoleClass_degreeNine_eq_zero_iff (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (p : Poly) (hp : p.IsHomogeneous 9) :
    simplePoleClass r 0 (polynomialLift p) = 0 ↔ traceLinear r p = 0 := by
  rw [simplePoleClass_degreeNine r hr hcube p hp]
  constructor
  · intro hz
    rcases smul_eq_zero.mp hz with hc | hnormalization
    · exact hc
    · exact False.elim ((normalizationCechClass_ne_zero r hr hcube) hnormalization)
  · intro hc
    rw [hc, zero_smul]

/-- The existing five-variable seed trace is now the coefficient of a
specific nonzero class in the genuine scalar Cech quotient. The degree
condition is imposed on the actual eliminated numerator. -/
theorem seedTrace_simplePoleClass (r : ℂ) (hr : r ≠ 0) (hcube : r ^ 3 = 2)
    (p : P) (hp : (substitute p).IsHomogeneous 9) :
    simplePoleClass r 0 p =
      seedTrace r hcube (seedQuotient r p) • normalizationCechClass r hr := by
  rw [simplePoleClass_substitute,
    simplePoleClass_degreeNine r hr hcube (substitute p) hp, seedTrace_mk]

/-- The finite quotient trace and the actual Cech class have exactly the
same vanishing criterion on the canonical degree-nine numerators. -/
theorem seedTrace_eq_zero_iff_simplePoleClass (r : ℂ) (hr : r ≠ 0)
    (hcube : r ^ 3 = 2) (p : P) (hp : (substitute p).IsHomogeneous 9) :
    seedTrace r hcube (seedQuotient r p) = 0 ↔ simplePoleClass r 0 p = 0 := by
  rw [seedTrace_mk, simplePoleClass_substitute,
    simplePoleClass_degreeNine_eq_zero_iff r hr hcube (substitute p) hp]

end DegreeNine

end CycleQ2NormalKoszulBridge
end
end

end Q2UncompiledNormalKoszulBridge
