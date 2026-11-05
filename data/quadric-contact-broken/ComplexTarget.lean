import Proposal.RationalTarget
import Proposal.TargetDenominator
import Proposal.PolynomialLift

/-! Exact coefficient transfer from the rational construction to the protected
complex polynomial ring. Derivatives, degrees, and the strict certificate identity
are transported by the coefficient homomorphism. -/
noncomputable section
namespace QuadricContactComplex
open MvPolynomial HodgeTestbed QuadricContactClearing

def complexMap : BasePoly →+* HodgeComputer.Poly :=
  MvPolynomial.map (algebraMap ℚ ℂ)

def targetA : HodgeComputer.Poly :=
  X 1^2 * X 0 * X 3 * (X 0^2-X 3^2)

@[simp] theorem complexMap_X (i : Fin 6) : complexMap (X i) = X i := by
  exact MvPolynomial.map_X _ i

@[simp] theorem complexMap_C (r : ℚ) :
    complexMap (C r) = C (algebraMap ℚ ℂ r) := by
  exact MvPolynomial.map_C _ r

@[simp] theorem complexMap_F : complexMap QuadricContactTarget.F =
    QuadricContactDenominator.targetF := by
  simp only [QuadricContactTarget.F, QuadricContactDenominator.targetF,
    map_add, map_mul, map_pow, map_ofNat, complexMap_X, complexMap_C]
  norm_num

@[simp] theorem complexMap_A : complexMap QuadricContactTarget.A = targetA := by
  simp only [QuadricContactTarget.A, targetA, map_mul, map_sub, map_pow, complexMap_X]

/-- The numerator in the protected expanded variable order. -/
theorem targetA_expanded : targetA =
    (X 0 : HodgeComputer.Poly)^3 * X 1^2 * X 3 - X 0 * X 1^2 * X 3^3 := by
  unfold targetA
  ring

theorem complexMap_injective : Function.Injective complexMap :=
  MvPolynomial.map_injective (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective

theorem complexMap_ne_zero {P : BasePoly} (hP : P ≠ 0) : complexMap P ≠ 0 := by
  intro h
  apply hP
  exact complexMap_injective (h.trans complexMap.map_zero.symm)

@[simp] theorem complexMap_pderiv (i : Fin 6) (P : BasePoly) :
    complexMap (pderiv i P) = pderiv i (complexMap P) :=
  MvPolynomial.pderiv_map.symm

theorem complexMap_homogeneous {P : BasePoly} {d : ℕ} (hP : P.IsHomogeneous d) :
    (complexMap P).IsHomogeneous d := hP.map _

@[simp] theorem complexMap_directional (P : BasePoly) (N : Fin 6 → BasePoly) :
    complexMap (directional P N) = directional (complexMap P) (fun i => complexMap (N i)) := by
  simp only [directional, map_sum, map_mul, complexMap_pderiv]

@[simp] theorem complexMap_divergence (N : Fin 6 → BasePoly) :
    complexMap (divergence N) = divergence (fun i => complexMap (N i)) := by
  simp only [divergence, map_sum, complexMap_pderiv]

@[simp] theorem complexMap_divergenceNumerator (D : BasePoly) (N : Fin 6 → BasePoly) :
    complexMap (divergenceNumerator D N) =
      divergenceNumerator (complexMap D) (fun i => complexMap (N i)) := by
  simp only [divergenceNumerator, map_sub, map_mul,
    complexMap_directional, complexMap_divergence]

@[simp] theorem complexMap_delta :
    complexMap QuadricContactLift.delta = QuadricContactLift.delta := by
  simp only [QuadricContactLift.delta, map_sub, map_pow, complexMap_X]

@[simp] theorem complexMap_clearing :
    complexMap QuadricContactLift.clearing = QuadricContactLift.clearing := by
  simp only [QuadricContactLift.clearing, map_mul, map_pow, complexMap_X]

@[simp] theorem complexMap_denominator (Q : BasePoly) :
    complexMap (QuadricContactLift.denominator Q) =
      QuadricContactLift.denominator (complexMap Q) := by
  simp only [QuadricContactLift.denominator, map_mul, complexMap_clearing]

@[simp] theorem complexMap_numerators (PS PT PB PC : BasePoly) (i : Fin 6) :
    complexMap (QuadricContactLift.numerators PS PT PB PC i) =
      QuadricContactLift.numerators (complexMap PS) (complexMap PT)
        (complexMap PB) (complexMap PC) i := by
  fin_cases i <;>
    simp [QuadricContactLift.numerators, map_mul, map_add, map_sub, map_pow,
      map_neg, map_ofNat, complexMap_clearing, complexMap_delta]

@[simp] theorem complexMap_horizontalS (P : BasePoly) :
    complexMap (QuadricContactLift.horizontalS P) =
      QuadricContactLift.horizontalS (complexMap P) := by
  simp only [QuadricContactLift.horizontalS, map_sub, map_mul,
    complexMap_X, complexMap_pderiv]

@[simp] theorem complexMap_horizontalT (P : BasePoly) :
    complexMap (QuadricContactLift.horizontalT P) =
      QuadricContactLift.horizontalT (complexMap P) := by
  simp only [QuadricContactLift.horizontalT, map_add, map_mul, map_neg,
    complexMap_X, complexMap_pderiv]

@[simp] theorem complexMap_horizontalB (P : BasePoly) :
    complexMap (QuadricContactLift.horizontalB P) =
      QuadricContactLift.horizontalB (complexMap P) := by
  simp only [QuadricContactLift.horizontalB, map_add, map_mul,
    complexMap_X, complexMap_pderiv]

@[simp] theorem complexMap_horizontalC (P : BasePoly) :
    complexMap (QuadricContactLift.horizontalC P) =
      QuadricContactLift.horizontalC (complexMap P) := by
  simp only [QuadricContactLift.horizontalC, map_add, map_mul,
    complexMap_X, complexMap_pderiv]

@[simp] theorem complexMap_source (F PS PT PB PC : BasePoly) :
    complexMap (QuadricContactLift.source F PS PT PB PC) =
      QuadricContactLift.source (complexMap F) (complexMap PS) (complexMap PT)
        (complexMap PB) (complexMap PC) := by
  simp only [QuadricContactLift.source, map_add, map_mul, map_pow, map_ofNat,
    complexMap_clearing, complexMap_delta, complexMap_X, complexMap_horizontalS,
    complexMap_horizontalT, complexMap_horizontalB, complexMap_horizontalC]

@[simp] theorem complexMap_divergenceCondition (Q PS PT PB PC : BasePoly) :
    complexMap (QuadricContactLift.divergenceCondition Q PS PT PB PC) =
      QuadricContactLift.divergenceCondition (complexMap Q) (complexMap PS)
        (complexMap PT) (complexMap PB) (complexMap PC) := by
  simp only [QuadricContactLift.divergenceCondition, map_add, map_sub, map_mul,
    map_pow, map_ofNat, complexMap_clearing, complexMap_delta, complexMap_X,
    complexMap_horizontalS, complexMap_horizontalT, complexMap_horizontalB,
    complexMap_horizontalC]

/-- All protected verification fields, with denominator legality left explicit. -/
theorem strict_verify (D : BasePoly) (N : Fin 6 → BasePoly) (d : ℕ)
    (hD : D.IsHomogeneous d) (hN : ∀ i, (N i).IsHomogeneous (d+1))
    (hsource : directional QuadricContactTarget.F N = QuadricContactTarget.A * D)
    (hdiv : divergenceNumerator D N = 0)
    (hlegal : IsRelPrime QuadricContactDenominator.targetF (complexMap D)) :
    HodgeComputer.Verify QuadricContactDenominator.targetF targetA 1 d
      (complexMap D) (fun i => complexMap (N i)) 0 := by
  refine ⟨QuadricContactDenominator.denominator_ne_zero_of_legal _ hlegal,
    complexMap_homogeneous hD, ?_, hlegal, ?_⟩
  · intro i
    convert complexMap_homogeneous (hN i) using 1 <;> omega
  · apply HodgeComputer.normalized_identity
    · have h := congrArg complexMap hsource
      simpa only [complexMap_directional, complexMap_F, complexMap_A,
        map_mul, Nat.cast_one, one_mul] using h
    · have h := congrArg complexMap hdiv
      simpa only [complexMap_divergenceNumerator, map_zero, mul_zero] using h

end QuadricContactComplex

#print axioms QuadricContactComplex.strict_verify
