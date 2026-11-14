import Mathlib.Algebra.MvPolynomial.PDeriv
import Proposal.GeometricSurfaceCoordinates

/-! Source-preserving extraction of the actual seed Jacobian certificates. -/

set_option Elab.async false

/- Component: continuation_20261111/SeedCubicGradient.lean -/
section
/-! Exact characteristic-zero gradient certificates for the literal cubic
smoothH used by the r=57 incidence seed.  These certify the algebraic
projective Jacobian condition; a geometric smoothness criterion is separate. -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace CycleQ2SeedCubicGradient
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def derivativeFormula {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![x2*x3+x1^2+3*x0^2, x2*x3+2*x0*x1-3*i*x1^2,
    3*x2^2+x1*x3+x0*x3, 3*(1-i)*x3^2+x1*x2+x0*x2]

def numerator0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-123842238*i*x1^3 - 269482980*i*x1*x2*x3 + 46094022*i*x3^3 + 1424185737*x0^3 - 474728579*x0*x1^2 - 474728579*x0*x2*x3 - 24958752*x1*x2*x3 - 44711550*x3^3,
    185763357*i*x0*x1^2 + 404224470*i*x0*x2*x3 + 4216836*i*x1*x2*x3 - 74892060*i*x2^3 + 69637752*i*x3^3 + 37438128*x0*x2*x3 - 41280746*x1^3 - 158402621*x1*x2*x3 - 31954605*x2^3 + 15033528*x3^3,
    -138282066*i*x0*x3^2 - 81882645*i*x1^2*x2 - 993438*i*x1*x3^2 + 24964020*i*x2^2*x3 + 134134650*x0*x3^2 + 53588990*x1^2*x2 - 164201706*x1*x3^2 + 10651535*x2^2*x3,
    149784120*i*x1*x2^2 - 14342292*i*x2*x3^2 + 63909210*x1*x2^2 + 24234966*x2*x3^2]

theorem identity0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    4272557211*x0^5 =
      ∑ k, numerator0 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator0 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      4272557211*x0^5 = (i^2+1)*(-557290071*x0*x1^4 - 1212673410*x0*x1^2*x2*x3 - 12650508*x1^3*x2*x3 + 224676180*x1^2*x2^3 - 208913256*x1^2*x3^3 - 449352360*x1*x2^2*x3^2 + 43026876*x2*x3^4) := by
    simp [Fin.sum_univ_succ, numerator0, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![386917466*i*x1*x2*x3 - 65354276*i*x3^3 - 495368952*x1^3 - 126722024*x1*x2*x3 + 17973020*x3^3,
    -580376199*i*x0*x2*x3 + 1114580142*i*x1^3 + 231964681*i*x1*x2*x3 + 100165083*i*x2^3 - 56808496*i*x3^3 + 743053428*x0*x1^2 + 190083036*x0*x2*x3 + 535939118*x1*x2*x3 + 39543024*x2^3 - 49266704*x3^3,
    196062828*i*x0*x3^2 + 106319746*i*x1^2*x2 - 82445836*i*x1*x3^2 - 33388361*i*x2^2*x3 - 53919060*x0*x3^2 - 73803067*x1^2*x2 + 152452468*x1*x3^2 - 13181008*x2^2*x3,
    -200330166*i*x1*x2^2 + 25576076*i*x2*x3^2 - 79086048*x1*x2^2 - 15144848*x2*x3^2]

theorem identity1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    2848371474*x1^5 =
      ∑ k, numerator1 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator1 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      2848371474*x1^5 = (i^2+1)*(1741128597*x0*x1^2*x2*x3 - 3343740426*x1^5 - 695894043*x1^3*x2*x3 - 300495249*x1^2*x2^3 + 170425488*x1^2*x3^3 + 600990498*x1*x2^2*x3^2 - 76728228*x2*x3^4) := by
    simp [Fin.sum_univ_succ, numerator1, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![1043866*i*x1^2*x3 - 148112*i*x1*x2^2 + 808014*x1^2*x3 + 1954376*x1*x2^2,
    -1565799*i*x0*x1*x3 + 222168*i*x0*x2^2 - 1669279*i*x1^2*x3 - 4717897*i*x1*x2^2 - 65130*i*x2*x3^2 - 1212021*x0*x1*x3 - 2931564*x0*x2^2 + 248787*x1^2*x3 - 133175*x1*x2^2 + 1398138*x2*x3^2,
    -297505*i*x1^3 + 1696059*i*x1*x2*x3 + 4199823*x1^3 - 1584255*x1*x2*x3 + 3175442*x2^3,
    641102*i*x1^2*x2 - 222168*i*x2^2*x3 - 400154*x1^2*x2 - 243878*x2^2*x3]

theorem identity2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    9526326*x2^5 =
      ∑ k, numerator2 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator2 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      9526326*x2^5 = (i^2+1)*(4697397*x0*x1^3*x3 - 666504*x0*x1^2*x2^2 + 5007837*x1^4*x3 + 14153691*x1^3*x2^2 - 1727916*x1^2*x2*x3^2 + 666504*x2^2*x3^3) := by
    simp [Fin.sum_univ_succ, numerator2, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-114864*i*x1*x3^2 + 182601*i*x2^2*x3 - 121972*x1*x3^2 + 12935*x2^2*x3,
    172296*i*x0*x3^2 + 214200*i*x1*x3^2 + 516468*i*x2^2*x3 + 182958*x0*x3^2 + 1870*x1*x3^2 + 19630*x2^2*x3,
    -547803*i*x0*x2^2 + 120474*i*x1^2*x3 - 547803*i*x1*x2^2 - 1760017*i*x2*x3^2 - 38805*x0*x2^2 - 520628*x1^2*x3 - 38805*x1*x2^2 - 1770679*x2*x3^2,
    62670*i*x1*x2*x3 + 1643409*i*x2^3 + 1587721*i*x3^3 + 38350*x1*x2*x3 + 116415*x2^3 + 1587721*x3^3]

theorem identity3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    9526326*x3^5 =
      ∑ k, numerator3 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator3 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      9526326*x3^5 = (i^2+1)*(-516888*x0*x1^2*x3^2 - 642600*x1^3*x3^2 - 1549404*x1^2*x2^2*x3 - 188010*x1*x2*x3^3 - 4930227*x2^3*x3^2 - 4763163*x3^5) := by
    simp [Fin.sum_univ_succ, numerator3, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def denominator : Fin 4 → ℕ := ![4272557211, 2848371474, 9526326, 9526326]

def numerators {R : Type*} [CommRing R] (j : Fin 4) (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![numerator0 i x0 x1 x2 x3, numerator1 i x0 x1 x2 x3,
    numerator2 i x0 x1 x2 x3, numerator3 i x0 x1 x2 x3] j

theorem polynomial_derivative (j : Fin 4) :
    pderiv (j.castSucc) (smoothH Complex.I : Poly ℂ) =
      derivativeFormula (C Complex.I) (X 0) (X 1) (X 2) (X 3) j := by
  fin_cases j <;>
    simp [smoothH, smoothB, smoothA, derivativeFormula, Derivation.leibniz,
      Fin.castSucc] <;> ring

theorem coordinate_power_identity (j : Fin 4) :
    (denominator j : Poly ℂ) * X j.castSucc^5 =
      ∑ k, numerators j (C Complex.I) (X 0) (X 1) (X 2) (X 3) k *
        pderiv k.castSucc (smoothH Complex.I : Poly ℂ) := by
  have hi : (C Complex.I : Poly ℂ)^2+1=0 := by
    rw [←map_pow, Complex.I_sq, map_neg, map_one]
    ring
  simp_rw [polynomial_derivative]
  fin_cases j
  · exact identity0 _ _ _ _ _ hi
  · exact identity1 _ _ _ _ _ hi
  · exact identity2 _ _ _ _ _ hi
  · exact identity3 _ _ _ _ _ hi


theorem denominator_ne_zero (j : Fin 4) : (denominator j : ℂ) ≠ 0 := by
  fin_cases j <;> norm_num [denominator]

/-- The explicit identities place every fifth coordinate power in the
literal four-generator Jacobian ideal, over characteristic zero. -/
theorem coordinate_power_mem_gradient_ideal (j : Fin 4) :
    (X j.castSucc : Poly ℂ)^5 ∈
      Ideal.span (Set.range (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) := by
  let J : Ideal (Poly ℂ) :=
    Ideal.span (Set.range (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ)))
  have hsum : (denominator j : Poly ℂ)*X j.castSucc^5 ∈ J := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left J (C ((denominator j : ℂ)⁻¹)) hsum
  have hc : C ((denominator j : ℂ)⁻¹)*(denominator j : Poly ℂ)=1 := by
    rw [←map_natCast C, ←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- Algebraic projective Jacobian criterion for the actual cubic, valid
under every map to a field. No point enumeration or modular hypothesis. -/
theorem nonzero_gradient {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (hx : ∃ j : Fin 4, φ (X j.castSucc) ≠ 0) :
    ∃ j : Fin 4, φ (pderiv j.castSucc (smoothH Complex.I : Poly ℂ)) ≠ 0 := by
  by_contra! hzero
  have hle : Ideal.span (Set.range
      (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) ≤
      RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hzero k
  obtain ⟨j, hj⟩ := hx
  have h := hle (coordinate_power_mem_gradient_ideal j)
  change φ ((X j.castSucc)^5)=0 at h
  rw [map_pow] at h
  exact (pow_ne_zero 5 hj) h

/-- In particular the literal cubic has no projective singular point over
any field extension of the complex coefficients. -/
theorem nonzero_gradient_over_complex_extension {K : Type*} [Field K] [Algebra ℂ K]
    (x : Fin 5 → K) (hx : ∃ j : Fin 4, x j.castSucc ≠ 0) :
    ∃ j : Fin 4, aeval x (pderiv j.castSucc (smoothH Complex.I : Poly ℂ)) ≠ 0 := by
  apply nonzero_gradient (aeval x).toRingHom
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X] using hx

end CycleQ2SeedCubicGradient

#print axioms CycleQ2SeedCubicGradient.coordinate_power_identity

#print axioms CycleQ2SeedCubicGradient.nonzero_gradient_over_complex_extension
end
end
