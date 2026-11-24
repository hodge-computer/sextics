import Proposal.ProtectedHypersurfaceCertificate

/-! # A certificate along the one-term Fermat deformation -/

set_option Elab.async false

/- Component: continuation_2/PureM2Certificate.lean -/
section
/-!+# An exact certificate along the genuine one-term Fermat deformation

For every complex parameter `s`, this module gives a complete certificate for
`sum X_i^6 + s * X₂^3 X₀ X₅ X₃`, with the original protected source monomial.
The denominator is `36 * (X₂^6+X₅^6) * (X₁^6+X₄^6)`.  The factor 36 clears
the rational scalar coefficients of the vector field.  This is a distinct
one-term family, not an assertion about the protected three-term sextic.
-/

noncomputable section
namespace CycleQ2PureM2

set_option maxRecDepth 10000

open MvPolynomial HodgeComputer

abbrev Poly := AmbientPoly 5
abbrev A : Poly := HodgeSubmission.A

def U : Poly := X 2 ^ 6 + X 5 ^ 6
def V : Poly := X 1 ^ 6 + X 4 ^ 6
def M : Poly := X 2 ^ 3 * X 0 * X 5 * X 3
def F (s : ℂ) : Poly :=
  X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6 + C s * M

def D : Poly := C 36 * (U * V)

def N (s : ℂ) : Fin 6 → Poly :=
  ![0, C (-2 * s) * (A * M * X 1), C 3 * (A * V * X 2),
    0, C (-2 * s) * (A * M * X 4), C 3 * (A * V * X 5)]

theorem U_homogeneous : U.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (2 : Fin 6) 6).add (isHomogeneous_X_pow 5 6)

theorem V_homogeneous : V.IsHomogeneous 6 := by
  exact (isHomogeneous_X_pow (1 : Fin 6) 6).add (isHomogeneous_X_pow 4 6)

theorem M_homogeneous : M.IsHomogeneous 6 := by
  have hx (i : Fin 6) : (X i : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ i
  simpa [M] using ((((hx 2).pow 3).mul (hx 0)).mul (hx 5)).mul (hx 3)

theorem F_homogeneous (s : ℂ) : (F s).IsHomogeneous 6 := by
  exact ((((((isHomogeneous_X_pow (0 : Fin 6) 6).add
    (isHomogeneous_X_pow 1 6)).add (isHomogeneous_X_pow 2 6)).add
    (isHomogeneous_X_pow 3 6)).add (isHomogeneous_X_pow 4 6)).add
    (isHomogeneous_X_pow 5 6)).add (M_homogeneous.C_mul s)

theorem D_homogeneous : D.IsHomogeneous 12 := by
  simpa [D] using (U_homogeneous.mul V_homogeneous).C_mul (36 : ℂ)

theorem D_ne_zero : D ≠ 0 := by
  intro h
  have hh := congrArg (MvPolynomial.eval (fun _ : Fin 6 => (1 : ℂ))) h
  norm_num [D, U, V] at hh

theorem D_totalDegree : D.totalDegree = 12 := D_homogeneous.totalDegree D_ne_zero

theorem N_homogeneous (s : ℂ) (i : Fin 6) : (N s i).IsHomogeneous 19 := by
  have hA : A.IsHomogeneous 12 := CycleQ2Workspace.originalA_homogeneous
  have hx (j : Fin 6) : (X j : Poly).IsHomogeneous 1 := isHomogeneous_X ℂ j
  have hU (j : Fin 6) : (C (3 : ℂ) * (A * V * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul V_homogeneous).mul (hx j)).C_mul (3 : ℂ)
  have hM (j : Fin 6) : (C (-2 * s) * (A * M * X j)).IsHomogeneous 19 := by
    simpa using ((hA.mul M_homogeneous).mul (hx j)).C_mul (-2 * s)
  fin_cases i
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 1
  · exact hU 2
  · exact isHomogeneous_zero (Fin 6) ℂ 19
  · exact hM 4
  · exact hU 5

/- The elementary univariate retraction and monic argument also used for the
Fermat subset denominators.  Here the perturbation is linear in `X 0`, so it
preserves monicity and both denominator factors are constant in this variable. -/
private def toUni : Poly →+* Polynomial Poly :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => if i = 0 then Polynomial.X else Polynomial.C (X i))

private def fromUni : Polynomial Poly →+* Poly :=
  Polynomial.eval₂RingHom (RingHom.id Poly) (X 0)

private theorem retract : fromUni.comp toUni = RingHom.id Poly := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [toUni, fromUni]
  · intro i
    by_cases hi : i = 0 <;> simp [toUni, fromUni, hi]

private theorem monic_relPrime_constant {R : Type*} [CommRing R] [IsDomain R]
    {f : Polynomial R} (hf : f.Monic) {c : R} (hc : c ≠ 0) :
    IsRelPrime f (Polynomial.C c) := by
  intro p hpf hpc
  by_contra hunit
  have hpos := Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hf hunit hpf
  have hle := Polynomial.natDegree_le_of_dvd hpc (Polynomial.C_ne_zero.mpr hc)
  simp only [Polynomial.natDegree_C] at hle
  omega

private theorem toUni_F_monic (s : ℂ) : (toUni (F s)).Monic := by
  have hrepr : toUni (F s) = (Polynomial.X : Polynomial Poly) ^ 6 +
      (Polynomial.C (C s * X 2 ^ 3 * X 5 * X 3) * Polynomial.X +
       Polynomial.C (X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6 + X 5 ^ 6)) := by
    simp [toUni, F, M]
    ring
  rw [hrepr]
  apply Polynomial.monic_X_pow_add
  exact (Polynomial.degree_add_le_of_le (Polynomial.degree_C_mul_X_le _)
    Polynomial.degree_C_le).trans_lt (by norm_num)

private theorem toUni_D : toUni D = Polynomial.C D := by
  simp [toUni, D, U, V]

theorem F_ne_zero (s : ℂ) : F s ≠ 0 := by
  intro h
  exact (toUni_F_monic s).ne_zero (by rw [h, map_zero])

theorem denominator_legal (s : ℂ) : IsRelPrime (F s) D := by
  apply HodgeComputer.relPrime_of_retract toUni fromUni retract
  rw [toUni_D]
  exact monic_relPrime_constant (toUni_F_monic s) D_ne_zero

private theorem sum_six (f : Fin 6 → Poly) :
    ∑ i, f i = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + f 5)))) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  rfl

set_option maxHeartbeats 2000000 in
theorem normalized_directional (s : ℂ) :
    (2 : Poly) * HodgeTestbed.directional (F s) (N s) = A * D := by
  unfold HodgeTestbed.directional
  rw [sum_six]
  simp [F, N, A,
    HodgeSubmission.A, D, U, V, M, map_add, pderiv_X, map_mul, map_neg, map_ofNat]
  ring

set_option maxHeartbeats 2000000 in
theorem divergence_zero (s : ℂ) : HodgeTestbed.divergenceNumerator D (N s) = 0 := by
  have h2 (i : Fin 6) : pderiv i (2 : Poly) = 0 := (pderiv i).map_natCast 2
  have h3 (i : Fin 6) : pderiv i (3 : Poly) = 0 := (pderiv i).map_natCast 3
  have h36 (i : Fin 6) : pderiv i (36 : Poly) = 0 := (pderiv i).map_natCast 36
  unfold HodgeTestbed.divergenceNumerator HodgeTestbed.divergence HodgeTestbed.directional
  rw [sum_six, sum_six]
  simp [N, A, HodgeSubmission.A,
    D, U, V, M, map_add, pderiv_mul, pderiv_X,
    h2, h3, h36, map_mul, map_neg, map_ofNat]
  ring

theorem verified (s : ℂ) : Verify (F s) A 6 2 D (N s) 0 where
  hypersurface_ne_zero := F_ne_zero s
  hypersurface_homogeneous := F_homogeneous s
  source_homogeneous := by
    simpa using Homogeneous.of_isHomogeneous CycleQ2Workspace.originalA_homogeneous
  denominator_ne_zero := D_ne_zero
  denominator_homogeneous := by simpa only [D_totalDegree] using D_homogeneous
  numerator_homogeneous := by
    intro i
    simpa [D_totalDegree] using Homogeneous.of_isHomogeneous (N_homogeneous s i)
  denominator_legal := denominator_legal s
  identity := normalized_identity (normalized_directional s) (by
    simpa only [mul_zero] using divergence_zero s)

/-- A complete, unconditional certificate along this one-term family. -/
theorem hasCertificate (s : ℂ) : HasCertificate (F s) 2 HodgeSubmission.A :=
  (verified s).hasCertificate

end CycleQ2PureM2

#print axioms CycleQ2PureM2.denominator_legal
#print axioms CycleQ2PureM2.normalized_directional
#print axioms CycleQ2PureM2.divergence_zero
#print axioms CycleQ2PureM2.hasCertificate
end
end
