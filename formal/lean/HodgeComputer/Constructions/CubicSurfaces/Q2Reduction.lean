import HodgeTestbed.Algebra
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-! Extracted from `HeadOfNaps`’s holdout-q2 proof (#124).
The coefficient and denominator hypotheses remain explicit. -/

/-!
# Cubic pole-two reduction

This is the cleared form of the Euler correction
`W₂ = (N + G W₁)/2 - (div N) E/6` in four variables.

Everything is proved in the polynomial ring. In particular no fraction-field
or derivation-extension adapter is needed, and no extra denominator is
introduced except the constant factor 6. The input is an actual Jacobian
representation `N(G)=B` and an actual strict certificate for `div N`.
-/

noncomputable section
open scoped BigOperators
open MvPolynomial HodgeTestbed

namespace HodgeComputer.CubicSurfaces.Q2Reduction

variable {σ R : Type*} [Fintype σ] [CommRing R]

 theorem directional_add (F : MvPolynomial σ R)
    (N P : σ → MvPolynomial σ R) :
    directional F (fun i => N i + P i) = directional F N + directional F P := by
  simp only [directional, mul_add, Finset.sum_add_distrib]

 theorem directional_sub (F : MvPolynomial σ R)
    (N P : σ → MvPolynomial σ R) :
    directional F (fun i => N i - P i) = directional F N - directional F P := by
  simp only [directional, mul_sub, Finset.sum_sub_distrib]

 theorem divergence_add (N P : σ → MvPolynomial σ R) :
    divergence (fun i => N i + P i) = divergence N + divergence P := by
  simp only [divergence, map_add, Finset.sum_add_distrib]

 theorem divergence_sub (N P : σ → MvPolynomial σ R) :
    divergence (fun i => N i - P i) = divergence N - divergence P := by
  simp only [divergence, map_sub, Finset.sum_sub_distrib]

 theorem directional_C (r : R) (N : σ → MvPolynomial σ R) :
    directional (C r) N = 0 := by
  simp [directional]

 theorem divergence_C_mul (r : R) (N : σ → MvPolynomial σ R) :
    divergence (fun i => C r * N i) = C r * divergence N := by
  rw [divergence_mul, directional_C, zero_add]

 theorem directional_euler {F : MvPolynomial σ R} {n : ℕ}
    (hF : F.IsHomogeneous n) :
    directional F (fun i => X i) = n * F := by
  simpa only [directional, mul_comm, nsmul_eq_mul] using hF.sum_X_mul_pderiv

 theorem divergence_euler :
    divergence (fun i : Fin 4 => (X i : MvPolynomial (Fin 4) R)) = 4 := by
  simp [divergence]

 theorem divergence_homogeneous {N : σ → MvPolynomial σ R} {n : ℕ}
    (hN : ∀ i, (N i).IsHomogeneous n) :
    (divergence N).IsHomogeneous (n-1) := by
  exact IsHomogeneous.sum Finset.univ _ _ (fun i _ => (hN i).pderiv)

/-- Polynomial numerators for the Euler-corrected pole-two field. -/
def numerators (G D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R) (i : Fin 4) :
    MvPolynomial (Fin 4) R :=
  C (3:R) * (D * N i + G * P i) - (D * divergence N) * X i

/-- The denominator is the old denominator multiplied only by the integer 6. -/
def denominator (D : MvPolynomial (Fin 4) R) : MvPolynomial (Fin 4) R := C (6:R) * D

 theorem numerator_source (G B D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R)
    (hG : G.IsHomogeneous 3)
    (hN : directional G N = B)
    (hP : directional G P = divergence N * D) :
    directional G (numerators G D N P) = C (3:R) * D * B := by
  unfold numerators
  rw [directional_sub, directional_mul, directional_add,
    directional_mul, directional_mul, directional_mul,
    hN, hP, directional_euler hG]
  simp only [map_ofNat]
  ring

 theorem numerator_divergence (G D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R)
    (hNhom : ∀ i, (N i).IsHomogeneous 3)
    (hP : directional G P = divergence N * D) :
    divergence (numerators G D N P) =
      C (3:R) * directional D N + C (3:R) * G * divergence P -
        divergence N * directional D (fun i => X i) := by
  have hh : (divergence N).IsHomogeneous 2 := divergence_homogeneous hNhom
  unfold numerators
  rw [divergence_sub, divergence_C_mul, divergence_add,
    divergence_mul, divergence_mul, divergence_mul,
    directional_product, hP, directional_euler hh, divergence_euler]
  simp only [map_ofNat]
  ring

/-- The two strict polynomial equations for the pole-two field.
The proof requires neither a domain hypothesis nor an invertibility hypothesis. -/
 theorem q2_equations (G B D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R)
    (hG : G.IsHomogeneous 3)
    (hNhom : ∀ i, (N i).IsHomogeneous 3)
    (hN : directional G N = B)
    (hP : directional G P = divergence N * D)
    (hPdiv : divergenceNumerator D P = 0) :
    2 * directional G (numerators G D N P) = B * denominator D ∧
      divergenceNumerator (denominator D) (numerators G D N P) = 0 := by
  constructor
  · rw [numerator_source G B D N P hG hN hP]
    unfold denominator
    simp only [map_ofNat]
    ring
  · have hPdiv' : D * divergence P - directional D P = 0 := hPdiv
    unfold divergenceNumerator denominator
    rw [numerator_divergence G D N P hNhom hP, directional_product,
      directional_C, mul_zero, zero_add]
    unfold numerators
    rw [directional_sub, directional_mul, directional_add,
      directional_mul, directional_mul, directional_mul]
    calc
      _ = C (18:R) * G * (D * divergence P - directional D P) := by
        simp only [map_ofNat]
        ring
      _ = 0 := by rw [hPdiv']; simp


/-- The convenient version consuming the repository's existing certificate
interface directly. -/
 theorem q2_equations_of_certificate (G B D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R)
    (hG : G.IsHomogeneous 3)
    (hNhom : ∀ i, (N i).IsHomogeneous 3)
    (hN : directional G N = B)
    (hP : Equations G (divergence N) D P 0) :
    2 * directional G (numerators G D N P) = B * denominator D ∧
      divergenceNumerator (denominator D) (numerators G D N P) = 0 := by
  apply q2_equations G B D N P hG hNhom hN hP.e1
  simpa using hP.e2

/-- The exact cleared pole-two defect vanishes. This is the algebraic
identity needed by the protected verifier after the endpoint lift. -/
 theorem cleared_defect_zero (G B D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R)
    (hG : G.IsHomogeneous 3)
    (hNhom : ∀ i, (N i).IsHomogeneous 3)
    (hN : directional G N = B)
    (hP : Equations G (divergence N) D P 0) :
    B * denominator D ^ 2 -
        2 * denominator D * directional G (numerators G D N P) +
        G * divergenceNumerator (denominator D) (numerators G D N P) = 0 := by
  obtain ⟨hsrc, hdiv⟩ := q2_equations_of_certificate G B D N P hG hNhom hN hP
  rw [hdiv, mul_zero, add_zero]
  calc
    _ = denominator D * (B * denominator D -
          2 * directional G (numerators G D N P)) := by ring
    _ = 0 := by rw [hsrc]; ring

/-- Homogeneity bookkeeping for the corrected numerator: its degree is the
old denominator degree plus 3, exactly the cubic pole-two degree. -/
 theorem numerators_homogeneous (G D : MvPolynomial (Fin 4) R)
    (N P : Fin 4 → MvPolynomial (Fin 4) R) (d : ℕ)
    (hG : G.IsHomogeneous 3) (hD : D.IsHomogeneous d)
    (hN : ∀ i, (N i).IsHomogeneous 3)
    (hP : ∀ i, (P i).IsHomogeneous d) (i : Fin 4) :
    (numerators G D N P i).IsHomogeneous (d+3) := by
  have hh : (divergence N).IsHomogeneous 2 := divergence_homogeneous hN
  have hGP : (G * P i).IsHomogeneous (d+3) := by
    simpa only [Nat.add_comm] using hG.mul (hP i)
  have hDX : ((D * divergence N) * X i).IsHomogeneous (d+3) := by
    simpa only [Nat.add_assoc] using (hD.mul hh).mul (isHomogeneous_X R i)
  exact (((hD.mul (hN i)).add hGP).C_mul 3).sub hDX

 theorem denominator_homogeneous {D : MvPolynomial (Fin 4) R} {d : ℕ}
    (hD : D.IsHomogeneous d) : (denominator D).IsHomogeneous d := hD.C_mul 6

 theorem denominator_ne_zero [IsDomain R] [CharZero R]
    {D : MvPolynomial (Fin 4) R} (hD : D ≠ 0) : denominator D ≠ 0 := by
  exact mul_ne_zero (by simp) hD

end HodgeComputer.CubicSurfaces.Q2Reduction

#print axioms HodgeComputer.CubicSurfaces.Q2Reduction.q2_equations
#print axioms HodgeComputer.CubicSurfaces.Q2Reduction.numerators_homogeneous
