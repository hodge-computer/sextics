import HodgeComputer.Constructions.HoldoutCover.CurveFamily
import HodgeComputer.Constructions.HoldoutCover.CurveSeedIncidence
import HodgeComputer.Constructions.HoldoutCover.EndpointFields
import HodgeComputer.Constructions.HoldoutCover.FermatFields
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence

/- Source component: FermatIncidenceSeed -/
section
/-! The exact conic seed makes the Jacobian-localized incidence over the
Fermat endpoint coordinate ring nontrivial. The seed is evaluated before
passing to any fraction field. -/

noncomputable section

namespace HoldoutConicIncidence

open HoldoutConstruction

abbrev FermatCurveBase := FermatBaseRing ℂ
abbrev FermatEndpointRing := EndpointRing FermatCurveBase

def fermatEndpoint : Fin 5 → FermatEndpointRing :=
  ![endpointRoot, 0, endpointParameter 0, endpointParameter 1, endpointParameter 2]

def fermatAlpha : FermatEndpointRing :=
  algebraMap FermatCurveBase FermatEndpointRing baseAlpha

def fermatBeta : FermatEndpointRing :=
  algebraMap FermatCurveBase FermatEndpointRing baseBeta

def fermatK (p : HoldoutConic.Seed) : FermatEndpointRing :=
  algebraMap ℂ FermatEndpointRing p.k

def fermatEquations (p : HoldoutConic.Seed) : Index → Coeff FermatEndpointRing :=
  equations fermatAlpha fermatBeta (fermatK p) fermatEndpoint

def fermatSeedEval (p : HoldoutConic.Seed) : FermatEndpointRing →+* ℂ :=
  (baseEval p.alpha p.beta p.base_relation).comp endpointSeedEval

@[simp] theorem endpointSeedEval_coefficient {R : Type*} [CommRing R] (r : R) :
    endpointSeedEval (algebraMap R (EndpointRing R) r) = r := by
  change endpointSeedEval (AdjoinRoot.of _ (MvPolynomial.C r)) = r
  simp [endpointSeedEval]

@[simp] theorem fermatSeedEval_alpha (p : HoldoutConic.Seed) :
    fermatSeedEval p fermatAlpha = p.alpha := by
  simp [fermatSeedEval, fermatAlpha]

@[simp] theorem fermatSeedEval_beta (p : HoldoutConic.Seed) :
    fermatSeedEval p fermatBeta = p.beta := by
  simp [fermatSeedEval, fermatBeta]

@[simp] theorem fermatSeedEval_k (p : HoldoutConic.Seed) :
    fermatSeedEval p (fermatK p) = p.k := by
  unfold fermatK
  rw [IsScalarTower.algebraMap_apply ℂ FermatCurveBase FermatEndpointRing]
  simp [fermatSeedEval]

theorem fermatK_ne_zero (p : HoldoutConic.Seed) : fermatK p ≠ 0 := by
  intro h
  have hh := congrArg (fermatSeedEval p) h
  rw [fermatSeedEval_k, map_zero] at hh
  exact p.k_ne_zero hh

@[simp] theorem fermatEndpoint_middle : fermatEndpoint 1 = 0 := rfl

theorem fermatSeedEval_endpoint (p : HoldoutConic.Seed) :
    (fun i => fermatSeedEval p (fermatEndpoint i)) = seedEndpoint := by
  funext i
  fin_cases i <;>
    simp [fermatSeedEval, fermatEndpoint, seedEndpoint,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]

theorem fermat_endpoint_equation : H fermatAlpha fermatBeta fermatEndpoint = 0 := by
  simpa [H, fermatEndpoint] using (endpoint_relation (R := FermatCurveBase))

theorem fermatEquations_seed_eval (p : HoldoutConic.Seed) (i : Index) :
    MvPolynomial.eval₂Hom (fermatSeedEval p) (seedCoefficients p) (fermatEquations p i) = 0 := by
  rw [fermatEquations, equations_eval₂, fermatSeedEval_alpha, fermatSeedEval_beta,
    fermatSeedEval_k, fermatSeedEval_endpoint, seed_system_zero]
  simp

theorem fermatEquations_seed_pderiv (p : HoldoutConic.Seed) (i j : Index) :
    MvPolynomial.eval₂Hom (fermatSeedEval p) (seedCoefficients p)
      (MvPolynomial.pderiv j (fermatEquations p i)) = seedJacobian p i j := by
  rw [fermatEquations, equations_pderiv_eval₂, fermatSeedEval_alpha,
    fermatSeedEval_beta, fermatSeedEval_k, fermatSeedEval_endpoint,
    seed_gradient]
  exact (seedJacobian_entries p i j).symm

/-- The nonsingular conic is a genuine point of the Jacobian-localized
incidence over the endpoint coordinate ring. -/
theorem fermat_incidence_nontrivial (p : HoldoutConic.Seed) :
    Nontrivial (Localization.Away (squareSystemJacobian (fermatEquations p))) := by
  let : Algebra FermatEndpointRing ℂ := (fermatSeedEval p).toAlgebra
  have hx (i : Index) :
      MvPolynomial.aeval (seedCoefficients p) (fermatEquations p i) = 0 := by
    exact fermatEquations_seed_eval p i
  have hm : (fun i j => MvPolynomial.aeval (seedCoefficients p)
      (MvPolynomial.pderiv i (fermatEquations p j))) = (seedJacobian p).transpose := by
    funext i j
    exact fermatEquations_seed_pderiv p j i
  apply square_system_jacobian_nontrivial (fermatEquations p) (seedCoefficients p) hx
  rw [hm, Matrix.det_transpose]
  exact isUnit_iff_ne_zero.mpr (seedJacobian_nonsingular p)

end HoldoutConicIncidence

#print axioms HoldoutConicIncidence.fermat_incidence_nontrivial
end
end
