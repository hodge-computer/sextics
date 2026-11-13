import HodgeComputer.Constructions.HoldoutCover.ConicCoefficientField
import HodgeComputer.Constructions.HoldoutCover.ConicNormal

/- Source component: ConicPolynomialFamily -/
section
/-!
The exact polynomial family over the finite generic coefficient field.
Its equation and nonsingular coefficient matrix are the original twelve
incidence equations after the proved base change. The polynomial normal
vector is then obtained from those same coefficients.
-/

noncomputable section


namespace HoldoutConicIncidence

open HoldoutConstruction Polynomial

attribute [local instance] fermatCurve_adjoinRoot_isDomain fermat_base_charZero
attribute [local instance] endpoint_adjoinRoot_isDomain endpoint_charZero

def conicSourceMap (p : HoldoutConic.Seed) : FermatEndpointRing →+* ConicCoefficientField p :=
  algebraMap FermatEndpointRing (ConicCoefficientField p)

theorem conicSourceMap_injective (p : HoldoutConic.Seed) :
    Function.Injective (conicSourceMap p) := by
  intro a b h
  apply endpointGenericMap_injective
  apply (algebraMap FermatEndpointField (ConicCoefficientField p)).injective
  change algebraMap FermatEndpointField (ConicCoefficientField p)
      (algebraMap FermatEndpointRing FermatEndpointField a) =
    algebraMap FermatEndpointField (ConicCoefficientField p)
      (algebraMap FermatEndpointRing FermatEndpointField b)
  simpa only [conicSourceMap,
    IsScalarTower.algebraMap_apply FermatEndpointRing FermatEndpointField
      (ConicCoefficientField p)] using h

def conicEndpoint (p : HoldoutConic.Seed) : Fin 5 → ConicCoefficientField p :=
  fun i => conicSourceMap p (fermatEndpoint i)

def conicAlpha (p : HoldoutConic.Seed) : ConicCoefficientField p :=
  conicSourceMap p fermatAlpha

def conicBeta (p : HoldoutConic.Seed) : ConicCoefficientField p :=
  conicSourceMap p fermatBeta

def conicK (p : HoldoutConic.Seed) : ConicCoefficientField p :=
  conicSourceMap p (fermatK p)

def conicCurve (p : HoldoutConic.Seed) : Fin 5 → Polynomial (ConicCoefficientField p) :=
  valueCurve (conicK p) (conicEndpoint p) (conicCoefficients p)

@[simp] theorem conicCurve_constant (p : HoldoutConic.Seed) (i : Fin 5) :
    (conicCurve p i).coeff 0 = conicEndpoint p i :=
  valueCurve_constant (conicK p) (conicEndpoint p) (conicCoefficients p) i

theorem conicSourceMap_base (p : HoldoutConic.Seed) (r : FermatCurveBase) :
    conicSourceMap p (algebraMap FermatCurveBase FermatEndpointRing r) =
      algebraMap FermatBaseField (ConicCoefficientField p)
        (algebraMap FermatCurveBase FermatBaseField r) := by
  change algebraMap FermatEndpointRing (ConicCoefficientField p) _ = _
  rw [IsScalarTower.algebraMap_apply FermatEndpointRing FermatEndpointField
    (ConicCoefficientField p)]
  change algebraMap FermatEndpointField (ConicCoefficientField p)
    (algebraMap (EndpointRing FermatBaseField) FermatEndpointField
      (endpointMap (algebraMap FermatCurveBase FermatBaseField)
        (algebraMap FermatCurveBase FermatEndpointRing r))) = _
  rw [endpointMap_coefficient]
  rw [← IsScalarTower.algebraMap_apply FermatBaseField
    (EndpointRing FermatBaseField) FermatEndpointField]
  rfl

theorem conicSourceMap_root (p : HoldoutConic.Seed) :
    conicEndpoint p 0 = algebraMap FermatEndpointField (ConicCoefficientField p)
      (algebraMap (EndpointRing FermatBaseField) FermatEndpointField endpointRoot) := by
  change algebraMap FermatEndpointRing (ConicCoefficientField p) endpointRoot = _
  rw [IsScalarTower.algebraMap_apply FermatEndpointRing FermatEndpointField
    (ConicCoefficientField p)]
  change algebraMap FermatEndpointField (ConicCoefficientField p)
    (algebraMap (EndpointRing FermatBaseField) FermatEndpointField
      (endpointMap (algebraMap FermatCurveBase FermatBaseField) endpointRoot)) = _
  rw [endpointMap_root]

theorem conicSourceMap_parameter (p : HoldoutConic.Seed) (j : Fin 3) :
    conicSourceMap p (endpointParameter j) =
      algebraMap FermatEndpointField (ConicCoefficientField p)
        (algebraMap (EndpointRing FermatBaseField) FermatEndpointField (endpointParameter j)) := by
  change algebraMap FermatEndpointRing (ConicCoefficientField p) (endpointParameter j) = _
  rw [IsScalarTower.algebraMap_apply FermatEndpointRing FermatEndpointField
    (ConicCoefficientField p)]
  change algebraMap FermatEndpointField (ConicCoefficientField p)
    (algebraMap (EndpointRing FermatBaseField) FermatEndpointField
      (endpointMap (algebraMap FermatCurveBase FermatBaseField) (endpointParameter j))) = _
  rw [endpointMap_parameter]

@[simp] theorem conicEndpoint_one (p : HoldoutConic.Seed) : conicEndpoint p 1 = 0 := by
  simp [conicEndpoint, fermatEndpoint]

theorem conicCurve_middle (p : HoldoutConic.Seed) :
    conicCurve p 1 = C (conicK p)*Polynomial.X := by
  unfold conicCurve
  rw [valueCurve_explicit]
  simp [conicEndpoint_one]

theorem conicAlpha_base (p : HoldoutConic.Seed) :
    conicAlpha p = algebraMap FermatBaseField (ConicCoefficientField p)
      (algebraMap FermatCurveBase FermatBaseField baseAlpha) :=
  conicSourceMap_base p baseAlpha

theorem conicBeta_base (p : HoldoutConic.Seed) :
    conicBeta p = algebraMap FermatBaseField (ConicCoefficientField p)
      (algebraMap FermatCurveBase FermatBaseField baseBeta) :=
  conicSourceMap_base p baseBeta

theorem conicK_base (p : HoldoutConic.Seed) :
    conicK p = algebraMap FermatBaseField (ConicCoefficientField p)
      (algebraMap ℂ FermatBaseField p.k) := by
  unfold conicK fermatK
  rw [IsScalarTower.algebraMap_apply ℂ FermatCurveBase FermatEndpointRing,
    conicSourceMap_base, ← IsScalarTower.algebraMap_apply ℂ FermatCurveBase FermatBaseField]

theorem conicEndpoint_zero_ne (p : HoldoutConic.Seed) : conicEndpoint p 0 ≠ 0 := by
  change conicSourceMap p endpointRoot ≠ 0
  exact fun h => endpointRoot_ne_zero
    ((conicSourceMap_injective p) (h.trans (map_zero (conicSourceMap p)).symm))

theorem conicK_ne_zero (p : HoldoutConic.Seed) : conicK p ≠ 0 := by
  intro h
  have hbase : fermatK p = 0 :=
    conicSourceMap_injective p (h.trans (map_zero (conicSourceMap p)).symm)
  apply p.k_ne_zero
  exact (algebraMap ℂ FermatEndpointRing).injective
    (hbase.trans (map_zero (algebraMap ℂ FermatEndpointRing)).symm)

theorem conicCurve_equation (p : HoldoutConic.Seed) :
    H (C (conicAlpha p)) (C (conicBeta p)) (conicCurve p) = 0 := by
  let e := MvPolynomial.eval₂Hom (conicSourceMap p) (conicCoefficients p)
  let f := (systemPoly fermatAlpha fermatBeta (fermatK p) fermatEndpoint).map e
  have hdeg : f.natDegree ≤ 12 :=
    (Polynomial.natDegree_map_le).trans
      (systemPoly_degree_le fermatAlpha fermatBeta (fermatK p) fermatEndpoint)
  have hpos (i : Index) : f.coeff (equationDegree i) = 0 := by
    rw [Polynomial.coeff_map]
    exact conicCoefficients_equations p i
  have hc : f.coeff 0 = 0 := by
    rw [Polynomial.coeff_map, systemPoly_constant, fermat_endpoint_equation]
    simp
  have hf := eq_constant_of_positive_coefficients f hdeg hpos
  rw [hc, Polynomial.C_0] at hf
  change (systemPoly fermatAlpha fermatBeta (fermatK p) fermatEndpoint).map e = 0 at hf
  rw [systemPoly_eval₂] at hf
  exact hf

theorem conicCurve_jacobian (p : HoldoutConic.Seed) :
    IsUnit (Matrix.det (fun i j : Index => coeffEval (conicCoefficients p)
      (MvPolynomial.pderiv j (equations (conicAlpha p) (conicBeta p)
        (conicK p) (conicEndpoint p) i)))) := by
  let J : Matrix Index Index (ConicCoefficientField p) :=
    fun i j => MvPolynomial.aeval (conicCoefficients p)
      (MvPolynomial.pderiv i (fermatEquations p j))
  have hmat : (fun i j : Index => coeffEval (conicCoefficients p)
      (MvPolynomial.pderiv j (equations (conicAlpha p) (conicBeta p)
        (conicK p) (conicEndpoint p) i))) = J.transpose := by
    funext i j
    rw [equations_pderiv_eval]
    exact (equations_pderiv_eval₂ (conicSourceMap p) fermatAlpha fermatBeta
      (fermatK p) fermatEndpoint (conicCoefficients p) i j).symm
  rw [hmat, Matrix.det_transpose]
  exact conicCoefficients_jacobian p

theorem conicCurve_exists_normal (p : HoldoutConic.Seed) :
    ∃ psi : Fin 5 → Polynomial (ConicCoefficientField p),
      polynomialPairing
        (gradient (C (conicAlpha p)) (C (conicBeta p)) (conicCurve p)) psi = 1 ∧
      ∀ i, (psi i).coeff 0 = if i=0 then (6*conicEndpoint p 0^5)⁻¹ else 0 :=
  exists_polynomial_normal (conicAlpha p) (conicBeta p) (conicK p)
    (conicEndpoint p) (conicCoefficients p) (conicEndpoint_one p)
    (conicEndpoint_zero_ne p) (conicCurve_jacobian p)

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.conicCurve_equation
#print axioms HoldoutConicIncidence.conicCurve_jacobian
#print axioms HoldoutConicIncidence.conicCurve_exists_normal
end
end
