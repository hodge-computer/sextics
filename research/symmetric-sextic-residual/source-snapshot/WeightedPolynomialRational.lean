import WeightedPolynomialQuotient

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

namespace WeightedSupport.PolynomialModel
open MvPolynomial

section GeneralCoefficientRing
variable (R : Type*) [CommRing R]

noncomputable def cappedIdeal : Ideal (MvPolynomial (Fin 6) R) :=
  Ideal.span (Set.range fun i : Fin 6 => (X i : MvPolynomial (Fin 6) R) ^ (cap i + 1))

abbrev CappedQuotient := MvPolynomial (Fin 6) R ⧸ cappedIdeal R

theorem coeff_cappedIdeal_zero (e : Exponent) (he : Bounded e)
    (p : MvPolynomial (Fin 6) R) (hp : p ∈ cappedIdeal R) : coeff (exponent e) p = 0 := by
  have hgen (i : Fin 6) (r : MvPolynomial (Fin 6) R) :
      coeff (exponent e) (X i ^ (cap i + 1) * r) = 0 := by
    rw [X_pow_eq_monomial, coeff_monomial_mul']
    have hn : ¬ Finsupp.single i (cap i + 1) ≤ exponent e := by
      simpa only [Finsupp.single_le_iff, exponent_apply] using
        Nat.not_le.mpr (Nat.lt_succ_of_le (he i))
    rw [if_neg hn]
  have haux : ∀ r : MvPolynomial (Fin 6) R, coeff (exponent e) (r * p) = 0 := by
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro r
      rw [mul_comm]
      exact hgen i r
    | zero => intro r; simp
    | add x y hx hy ihx ihy =>
      intro r
      rw [mul_add, MvPolynomial.coeff_add, ihx r, ihy r, zero_add]
    | smul a x hx ih =>
      intro r
      simpa only [smul_eq_mul, mul_assoc] using ih (r * a)
  simpa using haux 1

noncomputable def cappedCoeff (e : Exponent) (p : CappedQuotient R) : R :=
  coeff (exponent e) (Quotient.out p)

theorem cappedCoeff_mk (e : Exponent) (he : Bounded e) (p : MvPolynomial (Fin 6) R) :
    cappedCoeff R e (Ideal.Quotient.mk (cappedIdeal R) p) = coeff (exponent e) p := by
  have h : Ideal.Quotient.mk (cappedIdeal R)
      (Quotient.out (Ideal.Quotient.mk (cappedIdeal R) p)) = Ideal.Quotient.mk (cappedIdeal R) p :=
    Ideal.Quotient.mk_out _
  have hz := coeff_cappedIdeal_zero R e he _ (Ideal.Quotient.eq.mp h)
  rw [coeff_sub, sub_eq_zero] at hz
  exact hz

end GeneralCoefficientRing

noncomputable def changeCoefficients : Poly →+* MvPolynomial (Fin 6) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ)

theorem changeCoefficients_L :
    changeCoefficients L = X 0 + X 1 + X 2 + X 3 + X 4 := by
  rw [L_explicit]
  simp [changeCoefficients]

theorem changeCoefficients_D :
    changeCoefficients D = X 0 - X 1 + X 2 - X 3 := by
  simp [changeCoefficients, D]

theorem changeCoefficients_H :
    changeCoefficients H = X 0 + X 1 + X 2 + X 3 := by
  simp [changeCoefficients, H]

noncomputable def QRationalQuotientMatrix : Matrix (Fin 120) (Fin 82) ℚ := fun i j =>
  cappedCoeff ℚ (qTargetExponent i)
    (Ideal.Quotient.mk (cappedIdeal ℚ) (changeCoefficients (D * (L ^ 2 + X 5) ^ 5)) *
      Ideal.Quotient.mk (cappedIdeal ℚ) (changeCoefficients (orbitPolynomial (sourceExponent j))))

noncomputable def HQRationalQuotientMatrix : Matrix (Fin 74) (Fin 82) ℚ := fun i j =>
  cappedCoeff ℚ (hqTargetExponent i)
    (Ideal.Quotient.mk (cappedIdeal ℚ) (changeCoefficients (H * (D * (L ^ 2 + X 5) ^ 5))) *
      Ideal.Quotient.mk (cappedIdeal ℚ) (changeCoefficients (orbitPolynomial (sourceExponent j))))

theorem Q_rational_quotient_matrix_eq :
    QRationalQuotientMatrix = CheckedRank.QMatrix.map (Int.castRingHom ℚ) := by
  ext i j
  have hold := congrArg (fun (m : Matrix (Fin 120) (Fin 82) ℤ) => m i j) Q_quotient_matrix_eq
  change quotientCoeff _ (_ * _) = _ at hold
  rw [← map_mul, quotientCoeff_mk _ (q_targets_bounded i)] at hold
  change cappedCoeff ℚ _ (_ * _) = _
  rw [← map_mul, cappedCoeff_mk ℚ _ (q_targets_bounded i), ← map_mul]
  change coeff _ (MvPolynomial.map (Int.castRingHom ℚ) _) = _
  rw [MvPolynomial.coeff_map, hold]
  rfl

theorem HQ_rational_quotient_matrix_eq :
    HQRationalQuotientMatrix = CheckedRank.HQMatrix.map (Int.castRingHom ℚ) := by
  ext i j
  have hold := congrArg (fun (m : Matrix (Fin 74) (Fin 82) ℤ) => m i j) HQ_quotient_matrix_eq
  change quotientCoeff _ (_ * _ * _) = _ at hold
  rw [← map_mul, ← map_mul, quotientCoeff_mk _ (hq_targets_bounded i)] at hold
  change cappedCoeff ℚ _ (_ * _) = _
  rw [← map_mul, cappedCoeff_mk ℚ _ (hq_targets_bounded i), ← map_mul]
  change coeff _ (MvPolynomial.map (Int.castRingHom ℚ) _) = _
  rw [MvPolynomial.coeff_map, hold]
  rfl

theorem Q_rational_quotient_rank : QRationalQuotientMatrix.rank = 82 := by
  rw [Q_rational_quotient_matrix_eq]
  exact CheckedRank.Q_rational_rank

theorem HQ_rational_quotient_rank : HQRationalQuotientMatrix.rank = 74 := by
  rw [HQ_rational_quotient_matrix_eq]
  exact CheckedRank.HQ_rational_rank

#print axioms Q_rational_quotient_rank
#print axioms HQ_rational_quotient_rank

end WeightedSupport.PolynomialModel
