import Proposal.GeometricLiteralThreefoldResidueGluing
import Proposal.GeometricLiteralAbelJacobiRelativeNormal
import Proposal.GeometricLiteralCanonicalResidueGenerator
import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricHodgeTwistMultiplication
import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricLiteralThreefoldOrbitAction
import Proposal.GeometricChartSectionPullback
import Proposal.GeometricSurfaceCoordinateCubicFrames
import Proposal.GeometricLiteralMovingCurveDifferentialNonzero
import Proposal.GeometricClosedEmbeddingCechOne

/-!
# Restriction of the threefold volume along the cubic surface

The cubic conormal followed by two polynomial differentials wedges to the
ordered augmented Jacobian times the fixed threefold's regular volume.
Evaluation on a moving normal and two vectors tangent to the cubic thus
only uses the cubic component of the normal.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldSurfaceAdjunction

open Module MvPolynomial CycleQ2LiteralThreefoldResidueGluing
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2GeometricExteriorSheaf CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap
  CycleQ2GeometricSurfaceAdjunction CycleQ2ExteriorTopBaseChange

attribute [local irreducible] seedF seedH chartVolume

variable (i : Fin 4)
private abbrev mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
private abbrev basis₄ := Pi.basisFun (T i) (Fin 4)
private abbrev covector (p : P) (j : Fin 4) : T i := mk i (pderiv (coordIndex j) p)
private def toForms : (Fin 4 → T i) →ₗ[T i] KaehlerDifferential ℂ (T i) :=
  (basis₄ i).constr (T i) (coordinateForm i (AlgHom.id ℂ (T i)))

private theorem toForms_basis (j : Fin 4) :
    toForms i (basis₄ i j) = coordinateForm i (AlgHom.id ℂ (T i)) j := by
  simp [toForms]

private theorem toForms_covector (p : P) :
    toForms i (covector i p) = KaehlerDifferential.D ℂ (T i) (mk i p) := by
  rw [← (basis₄ i).sum_repr (covector i p), map_sum]
  simp only [map_smul, toForms_basis, Pi.basisFun_repr]
  exact (Equiv.sum_comp coordIndex (fun j => mk i (pderiv j p) •
    KaehlerDifferential.D ℂ (T i) (mk i (X j)))).trans (differential_polynomial (mk i) p).symm

private theorem toForms_fixed : toForms i (covector i (seedF i)) = 0 := by
  rw [toForms_covector, show mk i (seedF i) = 0 from
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]

/-- The determinant in the original coordinate order: the sextic equation,
the seed cubic, and the two chosen surface coordinates. -/
def jacobian (n t : P) : T i :=
  (basis₄ i).det (Fin.cons (covector i (seedF i)) ![covector i (seedH i), covector i n, covector i t])

/-- Exterior identity inside the fixed threefold, before restricting any coefficients to the surface. -/
theorem jacobian_smul_chartVolume (n t : P) :
    jacobian i n t • chartVolume i =
      exteriorPower.ιMulti (T i) 3 ![KaehlerDifferential.D ℂ (T i) (cubicOnT i),
        KaehlerDifferential.D ℂ (T i) (mk i n), KaehlerDifferential.D ℂ (T i) (mk i t)] := by
  let b := basis₄ i
  let u := ![covector i (seedH i), covector i n, covector i t]
  let v := exteriorPower.ιMulti (T i) 3 (toForms i ∘ u)
  have he : exteriorDifferentialMap (AlgHom.id ℂ (T i)) 3 (chartVolume i) = chartVolume i :=
    exteriorMap_identity (AlgHom.id ℂ (T i)).toRingHom
      (differentialSemilinearMap (AlgHom.id ℂ (T i))) (fun _ => rfl) (fun x => differentialMap_id x) 3 (chartVolume i)
  have h (j : Fin 4) : gradient i j • v = gradient i j • (jacobian i n t • chartVolume i) := by
    have hh := wedge_conormal_det b j (toForms i) _ (toForms_fixed i) u
    have hg := gradient_smul_chartVolume i (AlgHom.id ℂ (T i)) j
    rw [he] at hg
    simp only [b, Basis.coord_apply, Pi.basisFun_repr] at hh
    change gradient i j • v = jacobian i n t • signedOmitted (T i) (toForms i ∘ b) j at hh
    have hcoord : toForms i ∘ b = coordinateForm i (AlgHom.id ℂ (T i)) := funext (toForms_basis i)
    rw [hcoord, ← hg] at hh
    exact hh.trans (smul_comm (jacobian i n t) (gradient i j) (chartVolume i))
  obtain ⟨c, hc⟩ := chartBezout i
  have hw : v = jacobian i n t • chartVolume i := by
    calc
      v = (∑ j, c j * gradient i j) • v := by rw [hc, one_smul]
      _ = (∑ j, c j * gradient i j) • (jacobian i n t • chartVolume i) := by
        simp only [Finset.sum_smul, mul_smul, h]
      _ = _ := by rw [hc, one_smul]
  have hp : toForms i ∘ u = ![KaehlerDifferential.D ℂ (T i) (cubicOnT i),
      KaehlerDifferential.D ℂ (T i) (mk i n), KaehlerDifferential.D ℂ (T i) (mk i t)] := by
    funext j
    fin_cases j <;> exact toForms_covector i _
  exact hw.symm.trans (congrArg (exteriorPower.ιMulti (T i) 3) hp)

section Evaluation

variable {Q S : Type} [CommRing Q] [CommRing S] [Algebra ℂ Q] [Algebra ℂ S] [Algebra Q S] [IsScalarTower ℂ Q S]

private def vectors {d : ℕ} (v : Fin d → Derivation ℂ Q S) :
    KaehlerDifferential ℂ Q →ₛₗ[algebraMap Q S] (Fin d → S) where
  toFun ω j := (v j).liftKaehlerDifferential ω
  map_add' x y := funext fun j => (v j).liftKaehlerDifferential.map_add x y
  map_smul' r x := funext fun j => ((v j).liftKaehlerDifferential.map_smul r x).trans (Algebra.smul_def _ _)

/-- Evaluate an actual exterior differential on an ordered family of vectors along a ring map. -/
def evaluate {d : ℕ} (v : Fin d → Derivation ℂ Q S) :
    (⋀[Q]^d (KaehlerDifferential ℂ Q)) →ₛₗ[algebraMap Q S] S :=
  (topCoordinate (Pi.basisFun S (Fin d))).comp (exteriorMap (algebraMap Q S) (vectors v) d)

theorem evaluate_wedge {d : ℕ} (v : Fin d → Derivation ℂ Q S) (α : Fin d → KaehlerDifferential ℂ Q) :
    evaluate v (exteriorPower.ιMulti Q d α) =
      Matrix.det (Matrix.of fun a b => (v b).liftKaehlerDifferential (α a)) := by
  simp only [evaluate, LinearMap.comp_apply, exteriorMap_wedge, topCoordinate_wedge, ← Basis.det_apply,
    Pi.basisFun_det_apply]
  rfl

theorem evaluate_differentials {d : ℕ} (v : Fin d → Derivation ℂ Q S) (p : Fin d → Q) :
    evaluate v (exteriorPower.ιMulti Q d (fun a => KaehlerDifferential.D ℂ Q (p a))) =
      Matrix.det (Matrix.of fun a b => v b (p a)) := by
  simp only [evaluate_wedge, Derivation.liftKaehlerDifferential_comp_D]

theorem evaluate_swap (v x y : Derivation ℂ Q S) (ω : ⋀[Q]^3 (KaehlerDifferential ℂ Q)) :
    evaluate ![x,v,y] ω = -evaluate ![v,x,y] ω := by
  have hω : ω ∈ Submodule.span Q (Set.range (exteriorPower.ιMulti Q 3)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hω using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨α,rfl⟩ := hz
    simp only [evaluate_wedge, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    ring
  | zero => simp only [map_zero, neg_zero]
  | add z w _ _ hz hw => simp only [map_add, hz, hw, neg_add]
  | smul r z _ hz => simp only [map_smulₛₗ, hz, smul_neg]

theorem evaluate_two (x y : Derivation ℂ Q S) (n a : Q) :
    evaluate ![x,y] (exteriorPower.ιMulti Q 2 ![KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a]) =
      x n * y a - y n * x a := by
  have he := evaluate_differentials ![x,y] (![n,a] : Fin 2 → Q)
  have hf : (fun j : Fin 2 => KaehlerDifferential.D ℂ Q (![n,a] j)) =
      ![KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a] := by
    funext j; fin_cases j <;> rfl
  rw [hf] at he
  simpa only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons] using he

theorem evaluate_conormal_three (v x y : Derivation ℂ Q S) (h n a : Q)
    (hx : x h = 0) (hy : y h = 0) :
    evaluate ![v,x,y] (exteriorPower.ιMulti Q 3
      ![KaehlerDifferential.D ℂ Q h, KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a]) =
      v h * (x n * y a - y n * x a) := by
  have he := evaluate_differentials ![v,x,y] (![h,n,a] : Fin 3 → Q)
  have hf : (fun j : Fin 3 => KaehlerDifferential.D ℂ Q (![h,n,a] j)) =
      ![KaehlerDifferential.D ℂ Q h, KaehlerDifferential.D ℂ Q n, KaehlerDifferential.D ℂ Q a] := by
    funext j; fin_cases j <;> rfl
  rw [hf] at he
  refine he.trans ?_
  simp only [Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hx, hy]
  ring

end Evaluation

section Threefold

variable {S : Type} [CommRing S] [Algebra ℂ S] [Algebra (T i) S] [IsScalarTower ℂ (T i) S]

/-- Only the value on the cubic is retained when the other two vectors are tangent to the surface. -/
theorem tangent_evaluation (v x y : Derivation ℂ (T i) S) (n a : P)
    (hx : x (cubicOnT i) = 0) (hy : y (cubicOnT i) = 0) :
    algebraMap (T i) S (jacobian i n a) * evaluate ![v,x,y] (chartVolume i) =
      v (cubicOnT i) * (x (mk i n) * y (mk i a) - y (mk i n) * x (mk i a)) := by
  have hw := congrArg (evaluate ![v,x,y]) (jacobian_smul_chartVolume i n a)
  rw [map_smulₛₗ, smul_eq_mul, evaluate_conormal_three _ _ _ _ _ _ hx hy] at hw
  exact hw

end Threefold

end CycleQ2LiteralThreefoldSurfaceAdjunction
end

#print axioms CycleQ2LiteralThreefoldSurfaceAdjunction.jacobian_smul_chartVolume
#print axioms CycleQ2LiteralThreefoldSurfaceAdjunction.evaluate_differentials

/-!
# The literal cubic divisor in the ambient hypersurface

The surface used by the marked numerator is the quotient by the same cubic
inside the original sextic quotient.  Multiplication by that cubic is
regular; this follows from the proved monic leading terms of the original
two equations.  The maps below retain the original polynomial coordinates
and identify the quotient, rather than just an isomorphic abstract surface.

These are the coefficient maps needed for the ambient canonical residue
sequence.  Its sheaf adjunction and its degree-two-to-degree-three connecting
map still have to be bound to the canonical frames.  In that comparison the
surface residue generator is x0^2*w^2/(x1*x2*x3); the monic x0-cubic gives
ambient residue w^2/(x0*x1*x2*x3) with coefficient +1.  No global trace or
nonzero ordinary image of the marked supported class is asserted here.
-/

noncomputable section
namespace CycleQ2LiteralCubicDivisor

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2SeedRegularLeading

/-- The original weighted affine cone of the incidence threefold. -/
abbrev Cone (r θ : ℂ) := WeightedPoly ⧸ Ideal.span ({actualSeedEquation r θ} : Set WeightedPoly)

def coneMap (r θ : ℂ) : WeightedPoly →ₐ[ℂ] Cone r θ :=
  Ideal.Quotient.mkₐ ℂ _

def cubicClass (r θ : ℂ) : Cone r θ := coneMap r θ (thetaH θ)

private theorem coneMap_sextic (r θ : ℂ) : coneMap r θ (actualSeedEquation r θ) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The original cubic is regular modulo the original sextic.  The two
leading monomials are supported on distinct variables. -/
theorem cubic_regular_mod_sextic (r θ : ℂ) (p : WeightedPoly)
    (hp : thetaH θ * p ∈ Ideal.span ({actualSeedEquation r θ} : Set WeightedPoly)) :
    p ∈ Ideal.span ({actualSeedEquation r θ} : Set WeightedPoly) :=
  CycleQ2MonicRegular.pair_regular_mod_first auxiliaryOrder
    (F_leading_data r θ).2 (h_leading_data θ).2 (F_h_coprime r θ) p hp

/-- No regularity premise is imposed on the surface inclusion: it is proved
in the actual ambient hypersurface quotient. -/
theorem cubicClass_regular (r θ : ℂ) : IsSMulRegular (Cone r θ) (cubicClass r θ) := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change coneMap r θ (thetaH θ) * coneMap r θ p = 0 at hz
  rw [← map_mul] at hz
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (cubic_regular_mod_sextic r θ p (Ideal.Quotient.eq_zero_iff_mem.mp hz))

/-- Restriction from the original sextic cone to the already defined trace
surface.  Every original coordinate is preserved. -/
def toSurface (r θ : ℂ) : Cone r θ →ₐ[ℂ] SurfaceRing r θ :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ ℂ (surfaceIdeal r θ)) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact surfaceQuotient_F r θ)

@[simp] theorem toSurface_coneMap (r θ : ℂ) (p : WeightedPoly) :
    toSurface r θ (coneMap r θ p) = surfaceQuotient r θ p := rfl

@[simp] theorem toSurface_cubicClass (r θ : ℂ) :
    toSurface r θ (cubicClass r θ) = 0 := surfaceQuotient_h r θ

theorem toSurface_surjective (r θ : ℂ) : Function.Surjective (toSurface r θ) := by
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  exact ⟨coneMap r θ p, rfl⟩

/-- The kernel is the principal ideal of the original cubic, with no extra
equations or localization of the ambient cone. -/
theorem toSurface_ker (r θ : ℂ) :
    RingHom.ker (toSurface r θ) = Ideal.span ({cubicClass r θ} : Set (Cone r θ)) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hp : p ∈ surfaceIdeal r θ := Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [surfaceIdeal_eq_pair] at hp
    obtain ⟨u,v,huv⟩ := Ideal.mem_span_pair.mp hp
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨coneMap r θ v, ?_⟩
    have h := congrArg (coneMap r θ) huv
    simpa only [map_add, map_mul, coneMap_sextic, mul_zero, zero_add, cubicClass] using h
  · apply Ideal.span_le.mpr
    rintro z (rfl : z = cubicClass r θ)
    exact toSurface_cubicClass r θ

/-- The quotient by the cubic is the existing surface algebra, through the
actual restriction map and with the original complex scalar structure. -/
def quotientEquiv (r θ : ℂ) :
    (Cone r θ ⧸ Ideal.span ({cubicClass r θ} : Set (Cone r θ))) ≃ₐ[ℂ] SurfaceRing r θ :=
  (Ideal.quotientEquivAlgOfEq ℂ (toSurface_ker r θ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := toSurface r θ) (toSurface_surjective r θ))

@[simp] theorem quotientEquiv_mk (r θ : ℂ) (z : Cone r θ) :
    quotientEquiv r θ (Ideal.Quotient.mk _ z) = toSurface r θ z := by
  rw [quotientEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

/-- The coefficient sequence for the actual cubic divisor is short exact. -/
theorem coefficient_exact (r θ : ℂ) (z : Cone r θ) :
    toSurface r θ z = 0 ↔ ∃ y : Cone r θ, cubicClass r θ * y = z := by
  change z ∈ RingHom.ker (toSurface r θ) ↔ _
  rw [toSurface_ker, Ideal.mem_span_singleton']
  exact ⟨fun ⟨y,hy⟩ => ⟨y, (mul_comm _ _).trans hy⟩,
    fun ⟨y,hy⟩ => ⟨y, (mul_comm _ _).trans hy⟩⟩

/-- The inverse-ideal frame of the actual cubic inclusion on the cone. -/
def cubicIdealFrame (r θ : ℂ) :
    Cone r θ ≃ₗ[Cone r θ] RingHom.ker (toSurface r θ) :=
  principalIdealEquiv _ (cubicClass r θ) (cubicClass_regular r θ) (toSurface_ker r θ)

/-- The same original cubic remains regular on every principal cone open. -/
theorem cubicClass_regular_away (r θ : ℂ) (g : Cone r θ) :
    IsSMulRegular (Localization.Away g)
      (algebraMap (Cone r θ) (Localization.Away g) (cubicClass r θ)) :=
  regular_after_localizing (cubicClass r θ) g (by
    intro x hx
    rw [(cubicClass_regular r θ).right_eq_zero_of_smul hx, mul_zero])

end CycleQ2LiteralCubicDivisor
end

#print axioms CycleQ2LiteralCubicDivisor.cubicClass_regular
#print axioms CycleQ2LiteralCubicDivisor.toSurface_ker
#print axioms CycleQ2LiteralCubicDivisor.quotientEquiv_mk
#print axioms CycleQ2LiteralCubicDivisor.coefficient_exact

/-!
## A finite lift of the actual canonical residue generator

The four coefficients below divide the literal cubic as `h = Σ xᵢ bᵢ`,
with `b₀ = x₀²`.  On the triple face omitting `i`, use the coefficient
`(-1)^i bᵢ w² / ∏_{j ≠ i} xⱼ`.  Its actual localization Čech boundary is
`h w²/(x₀ x₁ x₂ x₃)`.  All four lifts have weighted degree three, and the
coefficient after division by `h` has weighted degree zero.

The (123) entry restricts, through the original cone quotient map, to the
already constructed canonical residue generator on the surface.  Thus the
normalization is an equality of original fractions and sections, rather
than a choice of an abstract trace.  The sheaf residue-sequence comparison
is still needed to turn this finite lift into a derived connecting-map
identity.
-/

noncomputable section
namespace CycleQ2LiteralCubicResidueLift

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2LiteralCubicDivisor CycleQ2GeometricLocalizedCech
  CycleQ2GeometricFourOpenCech CycleQ2GeometricSeedNormalIdeals

/-- Division of the unchanged literal cubic by the four coordinate opens. -/
def quadric : Fin 4 → WeightedPoly :=
  ![X 0 ^ 2, X 0 * X 1 - C Complex.I * X 1 ^ 2 + X 2 * X 3,
    X 2 ^ 2 + X 0 * X 3, C (1 - Complex.I) * X 3 ^ 2]

theorem cubic_coordinate_division :
    thetaH 1 = ∑ i : Fin 4, X i.castSucc * quadric i := by
  norm_num [thetaH, originalH, originalB, quadric, Fin.sum_univ_succ]
  ring

theorem quadric_homogeneous (i : Fin 4) :
    quadric i ∈ CycleQ2CartierSurfaceGrading.PolynomialGrade 2 := by
  have hx (j : Fin 4) : (X j.castSucc : WeightedPoly).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := by
    simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.weight_castSucc] using
      isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight j.castSucc
  fin_cases i
  · exact (hx 0).pow 2
  · exact (((hx 0).mul (hx 1)).sub (((hx 1).pow 2).C_mul Complex.I)).add
      ((hx 2).mul (hx 3))
  · exact ((hx 2).pow 2).add ((hx 0).mul (hx 3))
  · exact ((hx 3).pow 2).C_mul (1 - Complex.I)

def coordinate (r : ℂ) (i : Fin 4) : Cone r 1 := coneMap r 1 (X i.castSucc)
def denominator (r : ℂ) (s : Finset (Fin 4)) : Cone r 1 := coverProduct (coordinate r) s
abbrev At (r : ℂ) (s : Finset (Fin 4)) := RingAt (coordinate r) s

def polynomial (r : ℂ) (s : Finset (Fin 4)) : WeightedPoly →+* At r s :=
  (algebraMap (Cone r 1) (At r s)).comp (coneMap r 1).toRingHom

/-- An original polynomial divided once by the original face denominator. -/
def fraction (r : ℂ) (s : Finset (Fin 4)) (p : WeightedPoly) : At r s :=
  polynomial r s p * IsLocalization.Away.invSelf (denominator r s)

theorem fraction_spec (r : ℂ) (s : Finset (Fin 4)) (p : WeightedPoly) :
    fraction r s p * algebraMap (Cone r 1) (At r s) (denominator r s) =
      polynomial r s p := by
  rw [fraction, mul_assoc, mul_comm (IsLocalization.Away.invSelf _),
    IsLocalization.Away.mul_invSelf, mul_one]

private theorem denominator_erase (r : ℂ) (i : Fin 4) :
    coordinate r i * denominator r (Finset.univ.erase i) = denominator r Finset.univ :=
  Finset.mul_prod_erase Finset.univ (coordinate r) (Finset.mem_univ i)

/-- Clear the full denominator after the actual face restriction. -/
theorem restricted_fraction_spec (r : ℂ) (s : Finset (Fin 4)) (i : Fin 4)
    (hs : s = Finset.univ.erase i) (p : WeightedPoly) :
    ringRestriction (coordinate r) (Finset.subset_univ s) (fraction r s p) *
        algebraMap (Cone r 1) (At r Finset.univ) (denominator r Finset.univ) =
      polynomial r Finset.univ (X i.castSucc * p) := by
  subst s
  have hf := congrArg (ringRestriction (coordinate r)
    (Finset.subset_univ (Finset.univ.erase i)))
      (fraction_spec r (Finset.univ.erase i) p)
  simp only [map_mul, polynomial, RingHom.comp_apply, ringRestriction_base] at hf
  change _ * _ = algebraMap (Cone r 1) (At r Finset.univ)
    (coneMap r 1 (X i.castSucc * p))
  rw [← denominator_erase r i, map_mul]
  calc
    _ = algebraMap (Cone r 1) (At r Finset.univ) (coordinate r i) *
        (ringRestriction (coordinate r) (Finset.subset_univ (Finset.univ.erase i))
          (fraction r (Finset.univ.erase i) p) *
          algebraMap (Cone r 1) (At r Finset.univ) (denominator r (Finset.univ.erase i))) := by ring
    _ = algebraMap (Cone r 1) (At r Finset.univ) (coordinate r i) *
        polynomial r Finset.univ p := by rw [hf]
    _ = _ := by
      simp only [polynomial, RingHom.comp_apply, map_mul, coordinate]

def system (r : ℂ) : RestrictionSystem (Cone r 1) (At r) where
  res h := (ringRestriction (coordinate r) h).toLinearMap
  res_id s := congrArg AlgHom.toLinearMap (ringRestriction_self (coordinate r) s)
  res_comp hst htu := by
    apply LinearMap.ext
    exact ringRestriction_comp (coordinate r) hst htu

/-- The signed four actual triple-localization lifts. -/
def liftedTwo (r : ℂ) : TwoCochain (At r) :=
  ((fraction r {0,1,2} (-(quadric 3 * X 4 ^ 2)),
    fraction r {0,1,3} (quadric 2 * X 4 ^ 2)),
   (fraction r {0,2,3} (-(quadric 1 * X 4 ^ 2)),
    fraction r {1,2,3} (quadric 0 * X 4 ^ 2)))

/-- The degree-zero ambient residue coefficient with positive normalization. -/
def ambientGenerator (r : ℂ) : At r Finset.univ := fraction r Finset.univ (X 4 ^ 2)

/-- The finite Čech lift has the original cubic times the original ambient
generator as boundary, with coefficient +1. -/
theorem liftedTwo_boundary (r : ℂ) :
    d2 (system r) (liftedTwo r) =
      polynomial r Finset.univ (thetaH 1) * ambientGenerator r := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := At r Finset.univ) (denominator r Finset.univ)).mul_right_cancel
  change (ringRestriction (coordinate r) _ (fraction r {1,2,3} (quadric 0 * X 4 ^ 2)) -
      ringRestriction (coordinate r) _ (fraction r {0,2,3} (-(quadric 1 * X 4 ^ 2))) +
      ringRestriction (coordinate r) _ (fraction r {0,1,3} (quadric 2 * X 4 ^ 2)) -
      ringRestriction (coordinate r) _ (fraction r {0,1,2} (-(quadric 3 * X 4 ^ 2)))) * _ = _
  rw [sub_mul, add_mul, sub_mul,
    restricted_fraction_spec r {1,2,3} 0 (by decide),
    restricted_fraction_spec r {0,2,3} 1 (by decide),
    restricted_fraction_spec r {0,1,3} 2 (by decide),
    restricted_fraction_spec r {0,1,2} 3 (by decide),
    mul_assoc, ambientGenerator, fraction_spec]
  have h : X (0 : Fin 5) * (quadric 0 * X 4 ^ 2) -
      X 1 * (-(quadric 1 * X 4 ^ 2)) +
      X 2 * (quadric 2 * X 4 ^ 2) -
      X 3 * (-(quadric 3 * X 4 ^ 2)) = thetaH 1 * X 4 ^ 2 := by
    rw [cubic_coordinate_division]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    ring
  simpa only [map_sub, map_add, map_mul] using congrArg (polynomial r Finset.univ) h

private theorem triple_denominator (r : ℂ) :
    toSurface r 1 (denominator r {1,2,3}) =
      CycleQ2GeometricSurfaceCoordinates.coordinateProduct r 1 Finset.univ := by
  simp [denominator, coverProduct, coordinate,
    CycleQ2GeometricSurfaceCoordinates.coordinateProduct,
    CycleQ2GeometricSurfaceCoordinates.coordinateElement,
    CycleQ2SeedQuotientFiniteFree.remainingIndex, Fin.prod_univ_succ,
    CycleQ2GeometricSurfaceCoordinates.quotientMap,
    CycleQ2GeometricCartierNormalLift.surfaceQuotient]

/-- Restriction from the ambient (123) cone overlap to the exact triple
localization used by the surface's canonical coefficient map. -/
def tripleToSurface (r : ℂ) : At r {1,2,3} →+*
    CycleQ2GeometricSurfaceCoordinates.CoordinateLocal r 1 Finset.univ :=
  IsLocalization.map (M := Submonoid.powers (denominator r {1,2,3}))
    (T := Submonoid.powers
      (CycleQ2GeometricSurfaceCoordinates.coordinateProduct r 1 Finset.univ))
    (CycleQ2GeometricSurfaceCoordinates.CoordinateLocal r 1 Finset.univ)
    (toSurface r 1).toRingHom (by
      rintro y ⟨n,rfl⟩
      change toSurface r 1 (denominator r {1,2,3} ^ n) ∈ _
      rw [map_pow, triple_denominator]
      exact ⟨n,rfl⟩)

@[simp] theorem tripleToSurface_base (r : ℂ) (a : Cone r 1) :
    tripleToSurface r (algebraMap (Cone r 1) (At r {1,2,3}) a) =
      algebraMap (SurfaceRing r 1)
        (CycleQ2GeometricSurfaceCoordinates.CoordinateLocal r 1 Finset.univ)
        (toSurface r 1 a) := IsLocalization.map_eq _ a

theorem tripleToSurface_fraction (r : ℂ) (p : WeightedPoly) :
    tripleToSurface r (fraction r {1,2,3} p) =
      CycleQ2GeometricCoordinateCharacter.polynomialFraction r 1 p := by
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := CycleQ2GeometricSurfaceCoordinates.CoordinateLocal r 1 Finset.univ)
    (CycleQ2GeometricSurfaceCoordinates.coordinateProduct r 1 Finset.univ)).mul_right_cancel
  have hf := congrArg (tripleToSurface r) (fraction_spec r {1,2,3} p)
  rw [map_mul, tripleToSurface_base, triple_denominator] at hf
  rw [hf]
  rw [polynomial, RingHom.comp_apply, tripleToSurface_base, toSurface_coneMap]
  simpa only [pow_one] using
    (CycleQ2GeometricCoordinateCharacter.polynomialFraction_spec r 1 p).symm

/-- The selected lift restricts to the actual coefficient of the already
normalized canonical section.  This fixes the surface-to-ambient sign. -/
theorem liftedTwo_residueGenerator :
    tripleToSurface 57 ((liftedTwo 57).2.2) =
      CycleQ2CanonicalCoordinateCoefficients.canonicalCoefficient
        CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator := by
  rw [CycleQ2LiteralCanonicalResidueGenerator.canonicalCoefficient_residueGenerator]
  change tripleToSurface 57 (fraction 57 {1,2,3} (quadric 0 * X 4 ^ 2)) = _
  rw [tripleToSurface_fraction]
  rfl

end CycleQ2LiteralCubicResidueLift
end

#print axioms CycleQ2LiteralCubicResidueLift.cubic_coordinate_division
#print axioms CycleQ2LiteralCubicResidueLift.liftedTwo_boundary
#print axioms CycleQ2LiteralCubicResidueLift.liftedTwo_residueGenerator

/-!
## The cubic is Cartier on the actual projective coordinate charts

The Hodge presentation below is already identified with the original fixed
incidence fiber by `literalIso`, including its four weight-one opens.
The surface chart is the existing homogeneous localization of
`SurfaceRing 57 1`.  On these original rings the restriction kernel is
generated by `h/xᵢ³`, and that generator is regular.  Thus the local
coefficient sequence needed by canonical adjunction is now bound on the
projective charts as well as on the affine cone.
-/

noncomputable section
namespace CycleQ2LiteralProjectiveCubicDivisor

open MvPolynomial HomogeneousLocalization CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift

private abbrev A := cone literalEval
private abbrev D := SurfaceRing (57 : ℂ) 1
private abbrev DG := CycleQ2CartierSurfaceGrading.surfaceGrade (57 : ℂ) 1

theorem equation_eq_literal : equation literalEval = actualSeedEquation 57 1 := by
  rw [literalEval, equation_eq, CycleQ2IncidenceChartSeedFiber.literal_pointEquationF,
    ← actualSeedEquation_eq_smoothF]

private theorem quotient_sextic : quotient literalEval (actualSeedEquation 57 1) = 0 := by
  rw [← equation_eq_literal]
  exact equation_zero literalEval

/-- The original cubic in the already identified fixed-threefold cone. -/
def cubic : A := quotient literalEval (thetaH 1)

theorem cubic_regular : IsSMulRegular A cubic := by
  change IsSMulRegular
    (WeightedPoly ⧸ Ideal.span ({equation literalEval} : Set WeightedPoly))
    (Ideal.Quotient.mk _ (thetaH 1))
  rw [equation_eq_literal]
  exact CycleQ2LiteralCubicDivisor.cubicClass_regular 57 1

def toSurface : A →ₐ[ℂ] D :=
  Ideal.Quotient.liftₐ _
    (Ideal.Quotient.mkₐ ℂ (CycleQ2ConormalJacobian.surfaceIdeal 57 1)) (by
      apply (Ideal.span_singleton_le_iff_mem _).mpr
      change surfaceQuotient 57 1 (equation literalEval) = 0
      rw [equation_eq_literal]
      exact surfaceQuotient_F 57 1)

@[simp] theorem toSurface_quotient (p : WeightedPoly) :
    toSurface (quotient literalEval p) = surfaceQuotient 57 1 p := rfl

@[simp] theorem toSurface_cubic : toSurface cubic = 0 := surfaceQuotient_h 57 1

theorem toSurface_ker : RingHom.ker toSurface = Ideal.span ({cubic} : Set A) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
    have hp : p ∈ CycleQ2ConormalJacobian.surfaceIdeal 57 1 :=
      Ideal.Quotient.eq_zero_iff_mem.mp hz
    rw [surfaceIdeal_eq_pair] at hp
    obtain ⟨u,v,huv⟩ := Ideal.mem_span_pair.mp hp
    apply Ideal.mem_span_singleton'.mpr
    refine ⟨quotient literalEval v, ?_⟩
    simpa only [map_add, map_mul, quotient_sextic, mul_zero, zero_add, cubic] using
      congrArg (quotient literalEval) huv
  · apply Ideal.span_le.mpr
    rintro z (rfl : z = cubic)
    exact toSurface_cubic

def gradedToSurface : grade literalEval →+*ᵍ DG where
  toRingHom := toSurface.toRingHom
  map_mem := by
    intro n q hq
    obtain ⟨p,hp,rfl⟩ := hq
    exact ⟨p,hp,rfl⟩

private theorem cubic_mem_grade : cubic ∈ grade literalEval 3 :=
  quotient_mem_grade literalEval (thetaH 1)
    (CycleQ2CartierSurfaceGrading.thetaH_homogeneous 1)

abbrev Chart (i : Fin 4) := ChartRing literalEval i
abbrev SurfaceChart (i : Fin 4) :=
  CycleQ2GeometricSurfaceDehomogenizedCharts.CoordinateRing 57 1 i
private abbrev Ordinary (i : Fin 4) := Localization.Away (coord literalEval i.castSucc)

/-- Restriction of the actual degree-zero coordinate rings. -/
def chartToSurface (i : Fin 4) : Chart i →+* SurfaceChart i :=
  Away.map gradedToSurface (coord literalEval i.castSucc)

theorem chartToSurface_surjective (i : Fin 4) : Function.Surjective (chartToSurface i) := by
  intro z
  obtain ⟨n,b,hb,rfl⟩ := Away.mk_surjective DG
    (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i) z
  obtain ⟨p,hp,rfl⟩ := hb
  refine ⟨Away.mk (grade literalEval) (weightOne_mem_grade literalEval i) n
    (quotient literalEval p) ⟨p,hp,rfl⟩, ?_⟩
  simp only [chartToSurface, Away.map_mk]

/-- The literal equation of the cubic divisor on the ith projective chart. -/
def chartCubic (i : Fin 4) : Chart i :=
  Away.mk (grade literalEval) (weightOne_mem_grade literalEval i) 3 cubic
    (by simpa using cubic_mem_grade)

theorem chartCubic_val_mul (i : Fin 4) :
    (chartCubic i).val * (algebraMap A (Ordinary i) (coord literalEval i.castSucc)) ^ 3 =
      algebraMap A (Ordinary i) cubic := by
  rw [chartCubic, Away.val_mk, Localization.mk_eq_mk', ← map_pow]
  exact IsLocalization.mk'_spec _ _ _

/-- Regularity descends from the actual cone localization to its degree-zero
subring; no extra chart regularity hypothesis is introduced. -/
theorem chartCubic_regular (i : Fin 4) : IsSMulRegular (Chart i) (chartCubic i) := by
  have hr : IsSMulRegular (Ordinary i) (algebraMap A (Ordinary i) cubic) :=
    regular_after_localizing cubic (coord literalEval i.castSucc) (by
      intro x hx
      rw [cubic_regular.right_eq_zero_of_smul hx, mul_zero])
  apply CycleQ2GradedLocalizationProjection.isSMulRegular_of_val (grade literalEval)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  apply hr.right_eq_zero_of_smul
  change algebraMap A (Ordinary i) cubic * z = 0
  rw [← chartCubic_val_mul i]
  calc
    _ = (algebraMap A (Ordinary i) (coord literalEval i.castSucc)) ^ 3 *
        ((chartCubic i).val * z) := by ring
    _ = 0 := by rw [hz, mul_zero]

/-- The actual surface restriction has precisely the normalized original
cubic as its kernel generator on each of the four projective charts. -/
theorem chartToSurface_ker (i : Fin 4) :
    RingHom.ker (chartToSurface i) = Ideal.span ({chartCubic i} : Set (Chart i)) := by
  rw [chartToSurface, CycleQ2UniversalCurveCartier.gradedAwayMap_ker
    (grade literalEval) DG gradedToSurface (coord literalEval i.castSucc)
      (weightOne_mem_grade literalEval i)]
  change ((RingHom.ker toSurface).map (algebraMap A (Ordinary i))).comap
    (algebraMap (Chart i) (Ordinary i)) = _
  rw [toSurface_ker, Ideal.map_span, Set.image_singleton, ← chartCubic_val_mul i,
    Ideal.span_singleton_mul_right_unit
      ((IsLocalization.Away.algebraMap_isUnit (S := Ordinary i)
        (coord literalEval i.castSucc)).pow 3)]
  exact CycleQ2GradedLocalizationProjection.principalIdeal_comap_val
    (grade literalEval) (weightOne_mem_grade literalEval i) (chartCubic i)

def chartIdealFrame (i : Fin 4) :
    Chart i ≃ₗ[Chart i] RingHom.ker (chartToSurface i) :=
  principalIdealEquiv _ (chartCubic i) (chartCubic_regular i) (chartToSurface_ker i)

end CycleQ2LiteralProjectiveCubicDivisor
end

#print axioms CycleQ2LiteralProjectiveCubicDivisor.chartToSurface_surjective
#print axioms CycleQ2LiteralProjectiveCubicDivisor.chartCubic_regular
#print axioms CycleQ2LiteralProjectiveCubicDivisor.chartToSurface_ker

/-!
## The genuine multiplication sequence on the fixed projective threefold

Multiplication by the original homogeneous cubic is injective on every
section of the actual twist sheaves.  Regularity is checked in the
homogeneous prime localizations defining the structure sheaf, and the
existing atlas-kernel description of twists then proves global
injectivity.  Its actual additive cokernel gives a short exact sequence
and the degree-two-to-degree-three connecting map.

The cokernel here is deliberately still the coefficient quotient.  Its
identification with the pushed-forward surface canonical sheaf uses the
separate adjunction frames.  In particular, the negative sign between the
old global threefold volume and the surface's cubic orientation is not
silently absorbed by this coefficient sequence.
-/

noncomputable section
namespace CycleQ2LiteralProjectiveCubicDivisor

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios CycleQ2HodgeAtlasLine
  CycleQ2GeometricModuleLocalIso

abbrev Ambient := threefold literalEval

/-- The original normalized cubic is regular on every subopen of a
weight-one chart, without an affineness assumption on that subopen. -/
theorem normalized_cubic_regular (i : Fin 4) (W : Ambient.Opens)
    (hi : W ≤ U literalEval i) :
    IsSMulRegular Γ(Ambient, W)
      (normalized literalEval i cubic cubic_mem_grade W hi) := by
  intro a b hab
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  let M := q.val.asHomogeneousIdeal.toIdeal.primeCompl
  let d : M := ⟨coord literalEval i.castSucc, hi q.property⟩
  have hv : ((normalized literalEval i cubic cubic_mem_grade W hi).val q).val =
      Localization.mk cubic (d ^ 3) := rfl
  have hq := congrArg (fun s : Γ(Ambient,W) => (s.val q).val) hab
  change (((normalized literalEval i cubic cubic_mem_grade W hi).val q) * a.val q).val =
    (((normalized literalEval i cubic cubic_mem_grade W hi).val q) * b.val q).val at hq
  simp only [HomogeneousLocalization.val_mul, hv] at hq
  have hr : Function.Injective (fun z : Localization M =>
      algebraMap A (Localization M) cubic * z) :=
    CycleQ2SeedImageLocalization.localization_regular M (Localization M) cubic
      (show Function.Injective (fun z : A => cubic * z) from cubic_regular)
  apply hr
  have hnum : Localization.mk cubic (d ^ 3) *
      algebraMap A (Localization M) ((d ^ 3 : M) : A) =
        algebraMap A (Localization M) cubic := by
    rw [Localization.mk_eq_mk']
    exact IsLocalization.mk'_spec _ _ _
  calc
    algebraMap A (Localization M) cubic * (a.val q).val =
        algebraMap A (Localization M) ((d ^ 3 : M) : A) *
          (Localization.mk cubic (d ^ 3) * (a.val q).val) := by rw [← hnum]; ring
    _ = algebraMap A (Localization M) ((d ^ 3 : M) : A) *
        (Localization.mk cubic (d ^ 3) * (b.val q).val) :=
      congrArg (fun z : Localization M => algebraMap A (Localization M) ((d ^ 3 : M) : A) * z) hq
    _ = algebraMap A (Localization M) cubic * (b.val q).val := by rw [← hnum]; ring

/-- Multiplication O(0) → O(3) by the unchanged cubic. -/
def cubicMultiply : twist literalEval 0 ⟶ twist literalEval 3 :=
  multiply literalEval cubic cubic_mem_grade 0 3 (by decide)

theorem cubicMultiply_injective (W : Ambient.Opens) :
    Function.Injective (cubicMultiply.app W) := by
  intro s t hst
  apply component_injective (cocycle literalEval 0) W s t
  intro i
  have h := congrArg (component (cocycle literalEval 3) i W) hst
  change component (cocycle literalEval 3) i W
      (product literalEval 3 0 3 (by decide) W
        (homogeneousSection literalEval cubic cubic_mem_grade W) s) =
    component (cocycle literalEval 3) i W
      (product literalEval 3 0 3 (by decide) W
        (homogeneousSection literalEval cubic cubic_mem_grade W) t) at h
  simp only [product_component, homogeneousSection, component_pack] at h
  exact normalized_cubic_regular i (W ⊓ U literalEval i) inf_le_right h

/-- The same cubic map on the actual underlying additive sheaves. -/
def coefficientInclusion : addSheaf (twist literalEval 0) ⟶ addSheaf (twist literalEval 3) :=
  (SheafOfModules.toSheaf Ambient.ringCatSheaf).map cubicMultiply

theorem coefficientInclusion_injective (W : Ambient.Opens) :
    Function.Injective (coefficientInclusion.hom.app (op W)) :=
  cubicMultiply_injective W

theorem coefficientInclusion_mono : Mono coefficientInclusion :=
  Sheaf.mono_of_injective _ (fun W => coefficientInclusion_injective W.unop)

/-- The actual coefficient quotient by multiplication with the original cubic. -/
abbrev coefficientQuotient := cokernel coefficientInclusion

def coefficientComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Ambient) :=
  ShortComplex.mk coefficientInclusion (cokernel.π _) (cokernel.condition _)

theorem coefficientShortExact : coefficientComplex.ShortExact where
  exact := ShortComplex.exact_cokernel coefficientInclusion
  mono_f := coefficientInclusion_mono
  epi_g := inferInstanceAs (Epi (cokernel.π coefficientInclusion))

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Ambient) AddCommGrpCat.{0}) := HasExt.standard _

/-- The genuine H² → H³ boundary of the original cubic coefficient sequence. -/
def coefficientConnecting (W : Ambient.Opens) :
    coefficientQuotient.H' 2 W →+ (addSheaf (twist literalEval 0)).H' 3 W :=
  CycleQ2GeometricIntrinsicCartierCohomology.openConnecting coefficientShortExact 2 W

theorem coefficientConnecting_apply (W : Ambient.Opens) (z : coefficientQuotient.H' 2 W) :
    coefficientConnecting W z = z.comp coefficientShortExact.extClass rfl := rfl

/-- The middle term of the actual cubic sequence has no degree-two
cohomology on the proper fixed threefold. -/
theorem coefficientPole_hTwo :
    Subsingleton ((addSheaf (twist literalEval 3)).H' 2 ⊤) := by
  letI := (CycleQ2HodgeTwistTorusChart.ordinary_vanishing
    literalEval literal_vertex_unit 3).2
  exact (CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv _
    (addSheaf (twist literalEval 3)) ⊤ isTerminalTop 2).injective.subsingleton

/-- Every nonzero quotient class survives the genuine boundary to ambient
H³.  This uses the already proved O(3) vanishing, rather than a choice of
Čech representative or a further residue-trace hypothesis. -/
theorem coefficientConnecting_injective :
    Function.Injective (coefficientConnecting ⊤) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₃
    (CycleQ2InjectiveCech.freeOpen (⊤ : Ambient.Opens)) coefficientShortExact x rfl hx
  have hy0 : y = 0 := coefficientPole_hTwo.elim _ _
  simpa only [hy0, Ext.zero_comp] using hy.symm

theorem coefficientConnecting_ne_zero (z : coefficientQuotient.H' 2 ⊤)
    (hz : z ≠ 0) : coefficientConnecting ⊤ z ≠ 0 := by
  intro h
  apply hz
  apply coefficientConnecting_injective
  simpa only [map_zero] using h

/-- The positive middle twist also has no degree-three cohomology. -/
theorem coefficientPole_hThree :
    Subsingleton ((addSheaf (twist literalEval 3)).H' 3 ⊤) :=
  CycleQ2HodgeTwistTopCohomology.positive_hThree
    literalEval literal_vertex_unit 3 (by decide)

/-- Every ambient top class is the actual boundary of a cubic quotient
class; the vanishing used here is for the unchanged positive twist. -/
theorem coefficientConnecting_surjective :
    Function.Surjective (coefficientConnecting ⊤) := by
  letI := coefficientPole_hThree
  intro x
  exact Ext.covariant_sequence_exact₁
    (CycleQ2InjectiveCech.freeOpen (⊤ : Ambient.Opens))
    coefficientShortExact x (by subsingleton) rfl

/-- This equivalence is the connecting map itself, rather than an
abstract identification of two one-dimensional groups. -/
def coefficientConnectingEquiv : coefficientQuotient.H' 2 ⊤ ≃+
    (addSheaf (twist literalEval 0)).H' 3 ⊤ :=
  AddEquiv.ofBijective (coefficientConnecting ⊤)
    ⟨coefficientConnecting_injective, coefficientConnecting_surjective⟩

theorem coefficientConnectingEquiv_apply (z : coefficientQuotient.H' 2 ⊤) :
    coefficientConnectingEquiv z = z.comp coefficientShortExact.extClass rfl := rfl

end CycleQ2LiteralProjectiveCubicDivisor
end

#print axioms CycleQ2LiteralProjectiveCubicDivisor.normalized_cubic_regular
#print axioms CycleQ2LiteralProjectiveCubicDivisor.coefficientShortExact
#print axioms CycleQ2LiteralProjectiveCubicDivisor.coefficientConnecting_apply
#print axioms CycleQ2LiteralProjectiveCubicDivisor.coefficientConnecting_injective
#print axioms CycleQ2LiteralProjectiveCubicDivisor.coefficientConnectingEquiv_apply

/-!
## The original surface inclusion in the Hodge presentation

The graded quotient used by the coefficient sequence is the original
projective surface inclusion after the already fixed `literalIso`.
Transporting a bundle of a target and its incoming morphism along the
literal equality of sextic ideals proves this without replacing the
surface map by a map with merely the same point set.
-/

noncomputable section
namespace CycleQ2LiteralProjectiveCubicDivisor

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial HomogeneousLocalization CycleQ2GeometricHodgeThreefold
  CycleQ2GeometricHodgeThreefoldIncidence CycleQ2GeometricIncidenceProj
  CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceCoefficients
  CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian CycleQ2NormalConnecting

abbrev Surface := projectiveSurface (57 : ℂ) 1

theorem gradedToSurface_homogeneous_surjective (n : ℕ) (a : D) (ha : a ∈ DG n) :
    ∃ b : A, b ∈ grade literalEval n ∧ gradedToSurface b = a := by
  obtain ⟨p,hp,rfl⟩ := ha
  exact ⟨quotient literalEval p, ⟨p,hp,rfl⟩, rfl⟩

theorem surface_irrelevant : HomogeneousIdeal.irrelevant DG ≤
    (HomogeneousIdeal.irrelevant (grade literalEval)).map gradedToSurface := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn a ha
  obtain ⟨b,hb,rfl⟩ := gradedToSurface_homogeneous_surjective n a ha
  exact Ideal.mem_map_of_mem gradedToSurface
    (HomogeneousIdeal.mem_irrelevant_of_mem (grade literalEval) hn hb)

/-- The unchanged cubic/sextic projective surface maps by its actual graded
quotient to the full-family presentation of the fixed threefold. -/
def surfaceToAmbient : Surface ⟶ Ambient := Proj.map gradedToSurface surface_irrelevant

theorem surfaceToAmbient_isClosedImmersion : IsClosedImmersion surfaceToAmbient :=
  CycleQ2LiteralAmbientSurface.projectiveMap_closedImmersion
    (grade literalEval) DG gradedToSurface surface_irrelevant
      gradedToSurface_homogeneous_surjective

local instance : IsClosedImmersion surfaceToAmbient := surfaceToAmbient_isClosedImmersion

private abbrev ContainingIdeal :=
  {I : {I : Ideal (MvPolynomial (Fin 5) ℂ) // I.IsHomogeneous (PolynomialGrade ℂ)} //
    I.val ≤ surfaceIdeal 57 1}

private abbrev containingGrade (I : ContainingIdeal) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade (PolynomialGrade ℂ) I.val.val

private instance containingGradedRing (I : ContainingIdeal) : GradedRing (containingGrade I) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing _ _ I.val.property

private def containingMap (I : ContainingIdeal) : containingGrade I →+*ᵍ DG where
  toRingHom := Ideal.Quotient.factor I.property
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩

private theorem containing_irrelevant (I : ContainingIdeal) : HomogeneousIdeal.irrelevant DG ≤
    (HomogeneousIdeal.irrelevant (containingGrade I)).map (containingMap I) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  rintro n hn _ ⟨p,hp,rfl⟩
  exact Ideal.mem_map_of_mem (containingMap I)
    (HomogeneousIdeal.mem_irrelevant_of_mem (containingGrade I) hn
      (show Ideal.Quotient.mk I.val.val p ∈ containingGrade I n from ⟨p,hp,rfl⟩))

private structure SurfaceMorphism where
  target : Scheme.{0}
  map : Surface ⟶ target

private def fromContainingIdeal (I : ContainingIdeal) : SurfaceMorphism :=
  ⟨Proj (containingGrade I), Proj.map (containingMap I) (containing_irrelevant I)⟩

private def movingIdeal : ContainingIdeal :=
  ⟨⟨Ideal.span {equation literalEval}, Ideal.homogeneous_span _ _ (by
      rintro p (rfl : p = equation literalEval)
      exact ⟨6,equation_homogeneous _⟩)⟩, by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [equation_eq_literal]
    exact Ideal.subset_span ⟨0,rfl⟩⟩

private def nativeIdeal : ContainingIdeal :=
  ⟨⟨sexticIdeal CycleQ2LiteralAmbientCylinder.point,
      sexticIdeal_homogeneous CycleQ2LiteralAmbientCylinder.point⟩, by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [← equation_eq CycleQ2LiteralAmbientCylinder.point, equation_eq_literal]
    exact Ideal.subset_span ⟨0,rfl⟩⟩

private theorem containingIdeal_eq : movingIdeal = nativeIdeal := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun p : MvPolynomial (Fin 5) ℂ => Ideal.span {p})
    (equation_eq CycleQ2LiteralAmbientCylinder.point)

private def movingData : SurfaceMorphism := ⟨Ambient,surfaceToAmbient⟩
private def nativeData : SurfaceMorphism :=
  ⟨CycleQ2LiteralAmbientCylinder.Native,CycleQ2LiteralThreefoldOrbitAction.surfaceToNative⟩

private theorem surfaceMorphism_eq : movingData = nativeData := by
  have hm : gradedToSurface = containingMap movingIdeal := by
    apply GradedRingHom.ext
    intro a
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl
  calc
    movingData = fromContainingIdeal movingIdeal := by
      change SurfaceMorphism.mk Ambient (Proj.map gradedToSurface surface_irrelevant) =
        SurfaceMorphism.mk Ambient (Proj.map (containingMap movingIdeal)
          (containing_irrelevant movingIdeal))
      congr 1
      exact CycleQ2IncidenceFamilyContainment.projectiveMap_congr _ _ _ _ hm
    _ = fromContainingIdeal nativeIdeal := congrArg fromContainingIdeal containingIdeal_eq
    _ = nativeData := rfl

private theorem surfaceMorphism_transport {B C : SurfaceMorphism} (h : B = C)
    (e : B.target ≅ C.target) (he : e = eqToIso (congrArg SurfaceMorphism.target h)) :
    B.map ≫ e.hom = C.map := by
  subst C
  subst e
  simp

theorem surfaceToAmbient_toNative :
    surfaceToAmbient ≫ (nativeIso CycleQ2LiteralAmbientCylinder.point).hom =
      CycleQ2LiteralThreefoldOrbitAction.surfaceToNative :=
  surfaceMorphism_transport surfaceMorphism_eq
    (nativeIso CycleQ2LiteralAmbientCylinder.point) (by rfl)

/-- Equality with the original marked surface morphism, including its
scheme structure and all coordinate maps. -/
theorem surfaceToAmbient_toIncidence : surfaceToAmbient ≫ literalIso.hom =
    CycleQ2LiteralAmbientSurface.surfaceToFiber := by
  rw [literalIso, Iso.trans_hom, ← Category.assoc, surfaceToAmbient_toNative,
    CycleQ2LiteralThreefoldOrbitAction.surfaceToNative_toIncidence]

theorem surfaceToAmbient_overComplex :
    surfaceToAmbient ≫ toBase literalEval = projectiveToComplex 57 1 := by
  rw [← literalIso_overComplex, ← Category.assoc, surfaceToAmbient_toIncidence,
    CycleQ2LiteralAmbientSurface.surfaceToFiber_overComplex]

theorem surfaceToAmbient_preimage (i : Fin 4) :
    surfaceToAmbient ⁻¹ᵁ coordinateOpen literalEval i = coordinatePatch 57 1 i.castSucc :=
  Proj.map_preimage_basicOpen gradedToSurface surface_irrelevant (coord literalEval i.castSucc)

/-- The previously proved local quotient maps are the actual scheme
restriction maps for this same surface inclusion. -/
theorem chartToSurface_section_square (i : Fin 4) :
    Proj.awayToSection (grade literalEval) (coord literalEval i.castSucc) ≫
      surfaceToAmbient.appLE (coordinateOpen literalEval i)
        (coordinatePatch 57 1 i.castSucc) (surfaceToAmbient_preimage i).ge =
      CommRingCat.ofHom (chartToSurface i) ≫
        Proj.awayToSection DG
          (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i) :=
  Proj.awayToSection_comp_appLE gradedToSurface surface_irrelevant
    (weightOne_mem_grade literalEval i)

/-- Pullback of an actual homogeneous coefficient is the original surface
polynomial section, on every compatible pair of chart subopens. -/
theorem normalized_toSurface (i : Fin 4) (n : ℕ)
    (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n)
    (W : Ambient.Opens) (hWi : W ≤ coordinateOpen literalEval i)
    (V : Surface.Opens) (hVi : V ≤ coordinatePatch 57 1 i.castSucc)
    (hVW : V ≤ surfaceToAmbient ⁻¹ᵁ W) :
    surfaceToAmbient.appLE W V hVW
      (CycleQ2HodgeTwistRatios.normalized literalEval i (quotient literalEval p)
        (quotient_mem_grade literalEval p hp) W hWi) =
      CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection 57 1 i V hVi p := by
  let a : Chart i := Away.mk (grade literalEval) (weightOne_mem_grade literalEval i)
    n (quotient literalEval p) (by simpa using quotient_mem_grade literalEval p hp)
  have ht := ConcreteCategory.congr_hom (chartToSurface_section_square i) a
  change surfaceToAmbient.appLE (coordinateOpen literalEval i)
      (coordinatePatch 57 1 i.castSucc) (surfaceToAmbient_preimage i).ge
      (Proj.awayToSection (grade literalEval) (coord literalEval i.castSucc) a) =
    Proj.awayToSection DG (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i)
      (chartToSurface i a) at ht
  rw [CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection_fraction
    57 1 i V hVi n p hp, Proj.basicOpenIsoAway_hom]
  calc
    _ = Surface.presheaf.map (homOfLE hVi).op
        (surfaceToAmbient.appLE (coordinateOpen literalEval i)
          (coordinatePatch 57 1 i.castSucc) (surfaceToAmbient_preimage i).ge
          (Proj.awayToSection (grade literalEval) (coord literalEval i.castSucc) a)) :=
      CycleQ2ChartSectionPullback.restriction_square surfaceToAmbient hWi
        (surfaceToAmbient_preimage i).ge hVi hVW _
    _ = Surface.presheaf.map (homOfLE hVi).op
        (Proj.awayToSection DG (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i)
          (chartToSurface i a)) := congrArg (Surface.presheaf.map (homOfLE hVi).op) ht
    _ = _ := by
      apply congrArg (Surface.presheaf.map (homOfLE hVi).op)
      apply congrArg (Proj.awayToSection DG
        (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i))
      exact Away.map_mk gradedToSurface (coord literalEval i.castSucc)
        (weightOne_mem_grade literalEval i) n (quotient literalEval p)
        (by simpa using quotient_mem_grade literalEval p hp)

theorem cubic_toSurface_zero (i : Fin 4) (W : Ambient.Opens)
    (hWi : W ≤ coordinateOpen literalEval i) (V : Surface.Opens)
    (hVi : V ≤ coordinatePatch 57 1 i.castSucc) (hVW : V ≤ surfaceToAmbient ⁻¹ᵁ W) :
    surfaceToAmbient.appLE W V hVW
      (CycleQ2HodgeTwistRatios.normalized literalEval i cubic cubic_mem_grade W hWi) = 0 := by
  rw [normalized_toSurface i 3 (thetaH 1)
    (CycleQ2CartierSurfaceGrading.thetaH_homogeneous 1) W hWi V hVi hVW]
  rw [CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection_fraction
    57 1 i V hVi 3 (thetaH 1)
      (CycleQ2CartierSurfaceGrading.thetaH_homogeneous 1)]
  have hz : CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction 57 1 i 3
      (thetaH 1)
      (CycleQ2CartierSurfaceGrading.thetaH_homogeneous 1) = 0 := by
    apply HomogeneousLocalization.val_injective
    simp only [CycleQ2GeometricSurfaceDehomogenizedCharts.homogeneousFraction_val,
      CycleQ2GeometricCartierNormalLift.surfaceQuotient_h,
      map_zero, zero_mul, HomogeneousLocalization.val_zero]
  rw [hz, map_zero, map_zero]

theorem coordinateOpen_affine (i : Fin 4) :
    IsAffineOpen (coordinateOpen literalEval i) :=
  Proj.isAffineOpen_basicOpen (grade literalEval) (coord literalEval i.castSucc)
    (weightOne_mem_grade literalEval i) (by decide)

/-- On a whole projective coordinate chart, the kernel of the actual
surface pullback is generated by the original normalized cubic. -/
theorem surface_app_chart_kernel (i : Fin 4) :
    RingHom.ker (surfaceToAmbient.app (coordinateOpen literalEval i)).hom =
      Ideal.span {CycleQ2HodgeTwistRatios.normalized literalEval i
        cubic cubic_mem_grade (coordinateOpen literalEval i) le_rfl} := by
  let e : Chart i ≃+* Γ(Ambient, coordinateOpen literalEval i) :=
    (Proj.basicOpenIsoAway (grade literalEval) (coord literalEval i.castSucc)
      (weightOne_mem_grade literalEval i) (by decide)).commRingCatIsoToRingEquiv
  let d : SurfaceChart i ≃+* Γ(Surface, coordinatePatch 57 1 i.castSucc) :=
    (Proj.basicOpenIsoAway DG
      (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i)
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i)
      (by decide)).commRingCatIsoToRingEquiv
  let r := CycleQ2GeometricProjectiveCurve.Twisted.resEquiv Surface.sheaf
    (surfaceToAmbient_preimage i).ge (surfaceToAmbient_preimage i).le
  have hs (a : Chart i) :
      r (surfaceToAmbient.app (coordinateOpen literalEval i) (e a)) =
        d (chartToSurface i a) := by
    have h := ConcreteCategory.congr_hom (chartToSurface_section_square i) a
    change surfaceToAmbient.appLE (coordinateOpen literalEval i)
        (coordinatePatch 57 1 i.castSucc) (surfaceToAmbient_preimage i).ge
        ((Proj.basicOpenIsoAway (grade literalEval) (coord literalEval i.castSucc)
          (weightOne_mem_grade literalEval i) (by decide)).hom a) =
      (Proj.basicOpenIsoAway DG
        (CycleQ2GeometricSurfaceOverlap.coordinateDen 57 1 i)
        (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i)
        (by decide)).hom (chartToSurface i a)
    simpa only [Proj.basicOpenIsoAway_hom] using h
  have hz (a : Chart i) :
      surfaceToAmbient.app (coordinateOpen literalEval i) (e a) = 0 ↔
        chartToSurface i a = 0 := by
    constructor
    · intro h
      apply d.injective
      rw [← hs, h, map_zero, map_zero]
    · intro h
      apply r.injective
      rw [hs, h, map_zero, map_zero]
  have hc : CycleQ2HodgeTwistRatios.normalized literalEval i cubic cubic_mem_grade
      (coordinateOpen literalEval i) le_rfl = e (chartCubic i) := by
    change CycleQ2GeometricProjectiveCurve.Twisted.res Ambient.sheaf le_rfl
        (Proj.awayToSection (grade literalEval) (coord literalEval i.castSucc)
          (chartCubic i)) = _
    rw [CycleQ2GeometricProjectiveCurve.Twisted.res_self]
    change Proj.awayToSection (grade literalEval) (coord literalEval i.castSucc)
        (chartCubic i) =
      (Proj.basicOpenIsoAway (grade literalEval) (coord literalEval i.castSucc)
        (weightOne_mem_grade literalEval i) (by decide)).hom (chartCubic i)
    rw [Proj.basicOpenIsoAway_hom]
  ext s
  obtain ⟨a, rfl⟩ := e.surjective s
  change surfaceToAmbient.app (coordinateOpen literalEval i) (e a) = 0 ↔ _
  rw [hz, hc]
  change a ∈ RingHom.ker (chartToSurface i) ↔ _
  rw [chartToSurface_ker]
  constructor
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    exact Ideal.mem_span_singleton'.mpr ⟨e b,
      by simpa only [map_mul] using congrArg e hb⟩
  · intro ha
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ha
    obtain ⟨c, rfl⟩ := e.surjective b
    exact Ideal.mem_span_singleton'.mpr ⟨c,
      e.injective (by simpa only [map_mul] using hb)⟩

/-- The same principal kernel on every affine subopen follows from the
restriction law of the actual closed-immersion ideal sheaf. -/
theorem surface_app_kernel (i : Fin 4) (W : Ambient.Opens)
    (hW : IsAffineOpen W) (hi : W ≤ coordinateOpen literalEval i) :
    RingHom.ker (surfaceToAmbient.app W).hom =
      Ideal.span {CycleQ2HodgeTwistRatios.normalized literalEval i
        cubic cubic_mem_grade W hi} := by
  let U' : Ambient.affineOpens :=
    ⟨coordinateOpen literalEval i, coordinateOpen_affine i⟩
  let W' : Ambient.affineOpens := ⟨W, hW⟩
  have hu : surfaceToAmbient.ker.ideal U' =
      Ideal.span {CycleQ2HodgeTwistRatios.normalized literalEval i
        cubic cubic_mem_grade (coordinateOpen literalEval i) le_rfl} := by
    rw [Scheme.Hom.ker_apply]
    exact surface_app_chart_kernel i
  calc
    _ = surfaceToAmbient.ker.ideal W' := (surfaceToAmbient.ker_apply W').symm
    _ = (surfaceToAmbient.ker.ideal U').map
        (Ambient.presheaf.map (homOfLE hi).op).hom :=
      (surfaceToAmbient.ker.map_ideal (U := W') (V := U') hi).symm
    _ = _ := by
      rw [hu, Ideal.map_span, Set.image_singleton]
      exact congrArg (fun a : Γ(Ambient,W) => Ideal.span ({a} : Set Γ(Ambient,W)))
        (CycleQ2HodgeTwistRatios.normalized_restrict
          literalEval i cubic cubic_mem_grade le_rfl hi)

/-- A section whose original coefficient vanishes on the surface is
divisible by the cubic, in the actual line-bundle frames. -/
theorem cubicMultiply_preimage (i : Fin 4) (W : Ambient.Opens)
    (hW : IsAffineOpen W) (hi : W ≤ coordinateOpen literalEval i)
    (s : Γ(twist literalEval 3,W))
    (hs : surfaceToAmbient.app W (chartFrame literalEval 3 i W hi s) = 0) :
    ∃ a : Γ(twist literalEval 0,W), cubicMultiply.app W a = s := by
  have hmem : chartFrame literalEval 3 i W hi s ∈
      Ideal.span {CycleQ2HodgeTwistRatios.normalized literalEval i
        cubic cubic_mem_grade W hi} := by
    rw [← surface_app_kernel i W hW hi]
    exact hs
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨(chartFrame literalEval 0 i W hi).symm a,
    (chartFrame literalEval 3 i W hi).injective ?_⟩
  rw [cubicMultiply, multiply_frame, LinearEquiv.apply_symm_apply]
  simpa only [mul_comm] using ha

end CycleQ2LiteralProjectiveCubicDivisor
end

#print axioms CycleQ2LiteralProjectiveCubicDivisor.surfaceToAmbient_toIncidence
#print axioms CycleQ2LiteralProjectiveCubicDivisor.chartToSurface_section_square
#print axioms CycleQ2LiteralProjectiveCubicDivisor.normalized_toSurface
#print axioms CycleQ2LiteralProjectiveCubicDivisor.surface_app_kernel
#print axioms CycleQ2LiteralProjectiveCubicDivisor.cubicMultiply_preimage

/-!
## Restriction to the actual canonical surface sheaf

On the three coordinate opens covering the original surface, restrict an
O(3) coefficient through `surfaceToAmbient` and multiply it by the
established surface orientation (+,-,+).  The original exterior frames
then turn it into a genuine two-form.  Their checked transition agrees
with the O(3) transition.  Together with zero away from the surface, these
maps glue to an actual sheaf morphism on the whole fixed threefold.

This sign is the one obtained from the negative global ambient volume.
The construction below uses the original surface differential sheaf and
the original scheme restriction, rather than a newly named copy of its
coefficient cohomology.
-/

noncomputable section
namespace CycleQ2LiteralCubicCanonicalRestriction

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial CycleQ2LiteralProjectiveCubicDivisor CycleQ2GeometricHodgeThreefold
  CycleQ2GeometricHodgeThreefoldIncidence CycleQ2HodgeThreefoldTwist
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricDifferentialSheaf CycleQ2SurfaceCoordinateFrames
  CycleQ2SurfaceCoordinateCubicFrames CycleQ2SurfaceCoordinateSections

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule
  CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

local instance : IsClosedImmersion surfaceToAmbient := surfaceToAmbient_isClosedImmersion

abbrev Surface := CycleQ2LiteralProjectiveCubicDivisor.Surface
abbrev CanonicalForms := CycleQ2SurfaceCoordinateFrames.CanonicalForms
abbrev CubicSections := twist literalEval 3
abbrev CanonicalTarget := (Scheme.Modules.pushforward surfaceToAmbient).obj CanonicalForms

def chartOpen (i : Fin 3) : Ambient.Opens := coordinateOpen literalEval i.succ

theorem preimage_chartOpen (i : Fin 3) : surfaceToAmbient ⁻¹ᵁ chartOpen i =
    CycleQ2FullSurfaceResidueCover.coordinateOpen i := surfaceToAmbient_preimage i.succ

theorem preimage_le_chart (i : Fin 3) (W : Ambient.Opens) (hW : W ≤ chartOpen i) :
    surfaceToAmbient ⁻¹ᵁ W ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen i :=
  (surfaceToAmbient.preimage_mono hW).trans (preimage_chartOpen i).le

theorem surface_app_restrict {V W : Ambient.Opens} (hWV : W ≤ V) (a : Γ(Ambient,V)) :
    Surface.presheaf.map (homOfLE (surfaceToAmbient.preimage_mono hWV)).op
      (surfaceToAmbient.app V a) =
    surfaceToAmbient.app W (Ambient.presheaf.map (homOfLE hWV).op a) := by
  simpa only [Scheme.Hom.appLE_eq_app] using
    (CycleQ2ChartSectionPullback.restriction_square surfaceToAmbient hWV le_rfl
      (surfaceToAmbient.preimage_mono hWV) le_rfl a).symm

/-- The signed original surface residue frame applied to a restricted
coefficient, on every subopen of a whole ambient coordinate chart. -/
def localRestriction (i : Fin 3) (W : Ambient.Opens) (hW : W ≤ chartOpen i) :
    Γ(CubicSections,W) →ₗ[Γ(Ambient,W)] CanonicalTarget.val.obj (op W) where
  toFun s := ((coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
    (preimage_le_chart i W hW)).symm
      ((orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
        surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hW s))
  map_add' s t := by simp only [map_add, mul_add]
  map_smul' c s := by
    let e := ((coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
      (preimage_le_chart i W hW)).symm
    change e ((orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
        surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hW (c • s))) =
      surfaceToAmbient.app W c • e
        ((orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
          surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hW s))
    rw [map_smul, smul_eq_mul, map_mul]
    rw [show (orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
        (surfaceToAmbient.app W c * surfaceToAmbient.app W
          (chartFrame literalEval 3 i.succ W hW s)) =
      surfaceToAmbient.app W c * ((orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
        surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hW s)) by ring]
    exact e.map_smul _ _

theorem localRestriction_coordinates (i : Fin 3) (W : Ambient.Opens)
    (hW : W ≤ chartOpen i) (s : Γ(CubicSections,W)) :
    (coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W) (preimage_le_chart i W hW)
      (localRestriction i W hW s) =
    (orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) *
      surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hW s) :=
  LinearEquiv.apply_symm_apply _ _

theorem localRestriction_restrict (i : Fin 3) {V W : Ambient.Opens}
    (hWV : W ≤ V) (hV : V ≤ chartOpen i) (s : Γ(CubicSections,V)) :
    CanonicalTarget.val.map (homOfLE hWV).op (localRestriction i V hV s) =
      localRestriction i W (hWV.trans hV) (CubicSections.val.map (homOfLE hWV).op s) := by
  apply ((coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
    (preimage_le_chart i W (hWV.trans hV))).injective
  change (coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W) _
      (CanonicalForms.val.map (homOfLE (surfaceToAmbient.preimage_mono hWV)).op
        (localRestriction i V hV s)) = _
  rw [← (coordinateExteriorFrame i).naturality (surfaceToAmbient.preimage_mono hWV)
    (preimage_le_chart i V hV), localRestriction_coordinates, localRestriction_coordinates]
  change Surface.presheaf.map (homOfLE (surfaceToAmbient.preimage_mono hWV)).op
      ((orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ V)) *
        surfaceToAmbient.app V (chartFrame literalEval 3 i.succ V hV s)) = _
  rw [map_mul, map_intCast, surface_app_restrict]
  exact congrArg (fun a : Γ(Ambient,W) =>
    (orientation i : Γ(Surface,surfaceToAmbient ⁻¹ᵁ W)) * surfaceToAmbient.app W a)
      (CycleQ2HodgeAtlasLine.coordinate_restrict (cocycle literalEval 3) i.succ hV hWV s).symm

theorem localRestriction_overlap (i j : Fin 3) (W : Ambient.Opens)
    (hi : W ≤ chartOpen i) (hj : W ≤ chartOpen j) (s : Γ(CubicSections,W)) :
    localRestriction i W hi s = localRestriction j W hj s := by
  let P := surfaceToAmbient ⁻¹ᵁ W
  have hr : surfaceToAmbient.app W (CycleQ2HodgeTwistRatios.ratio
      literalEval i.succ j.succ W hi) =
      coordinatePolynomialSection 57 1 i.succ P (preimage_le_chart i W hi)
        (X j.succ.castSucc) :=
    normalized_toSurface i.succ 1 (X j.succ.castSucc)
      (by simpa only [CycleQ2CartierSurfaceGrading.weight_castSucc] using
        isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight j.succ.castSucc)
      W hi P (preimage_le_chart i W hi) le_rfl
  have hf : chartFrame literalEval 3 i.succ W hi s =
      CycleQ2HodgeTwistRatios.ratio literalEval i.succ j.succ W hi ^ 3 *
        chartFrame literalEval 3 j.succ W hj s := by
    simpa only [zpow_natCast, Units.val_pow_eq_pow_val, CycleQ2HodgeTwistRatios.transition] using
      chartFrame_transition literalEval 3 i.succ j.succ W hi hj s
  apply ((coordinateExteriorFrame i).app P (preimage_le_chart i W hi)).injective
  rw [localRestriction_coordinates,
    coordinateExteriorFrame_transition i j P (preimage_le_chart i W hi)
      (preimage_le_chart j W hj), localRestriction_coordinates,
    hf, map_mul, map_pow, hr]
  let r := coordinatePolynomialSection 57 1 i.succ P (preimage_le_chart i W hi)
    (X j.succ.castSucc)
  let b := surfaceToAmbient.app W (chartFrame literalEval 3 j.succ W hj s)
  change (orientation i : Γ(Surface,P)) * (r ^ 3 * b) =
    (((orientation i : Γ(Surface,P)) * (orientation j : Γ(Surface,P))) * r ^ 3) *
      ((orientation j : Γ(Surface,P)) * b)
  calc
    _ = ((orientation i : Γ(Surface,P)) *
        ((orientation j : Γ(Surface,P)) * (orientation j : Γ(Surface,P)))) *
          (r ^ 3 * b) := by rw [orientation_mul_self, mul_one]
    _ = _ := by ring

def offSurface : Ambient.Opens :=
  ⟨(Set.range surfaceToAmbient)ᶜ,
    surfaceToAmbient.isClosedEmbedding.isClosed_range.isOpen_compl⟩

theorem preimage_offSurface : surfaceToAmbient ⁻¹ᵁ offSurface = ⊥ := by
  ext x
  change (surfaceToAmbient x ∉ Set.range surfaceToAmbient) ↔ False
  simp

theorem surface_sections_empty_of_le {W : Ambient.Opens} (hW : W ≤ offSurface) :
    Subsingleton Γ(Surface, surfaceToAmbient ⁻¹ᵁ W) := by
  have he : surfaceToAmbient ⁻¹ᵁ W = ⊥ := le_antisymm
    ((surfaceToAmbient.preimage_mono hW).trans preimage_offSurface.le) bot_le
  rw [he]
  have ht : IsTerminal
      ((CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface).obj.obj
        (op (⊥ : Surface.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty
      (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf Surface)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp ht.isZero

def restrictionCover : Option (Fin 3) → Ambient.Opens
  | none => offSurface
  | some i => chartOpen i

theorem restrictionCover_top : (⨆ i, restrictionCover i) = ⊤ := by
  apply le_antisymm le_top
  intro y _
  by_cases hy : ∃ x : Surface, surfaceToAmbient x = y
  · obtain ⟨x,rfl⟩ := hy
    have hx : x ∈ ⨆ i, CycleQ2FullSurfaceResidueCover.coordinateOpen i := by
      rw [CycleQ2FullSurfaceResidueCover.coordinateOpen_cover]
      trivial
    obtain ⟨i,hi⟩ := Opens.mem_iSup.mp hx
    apply le_iSup restrictionCover (some i)
    change x ∈ surfaceToAmbient ⁻¹ᵁ chartOpen i
    rwa [preimage_chartOpen]
  · exact (le_iSup restrictionCover none) hy

theorem target_empty_of_le {W : Ambient.Opens} (hW : W ≤ offSurface) :
    Subsingleton (CanonicalTarget.val.obj (op W)) := by
  have he : surfaceToAmbient ⁻¹ᵁ W = ⊥ := le_antisymm
    ((surfaceToAmbient.preimage_mono hW).trans preimage_offSurface.le) bot_le
  change Subsingleton (CanonicalForms.val.obj (op (surfaceToAmbient ⁻¹ᵁ W)))
  rw [he]
  have ht : IsTerminal ((addSheaf CanonicalForms).obj.obj (op (⊥ : Surface.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (addSheaf CanonicalForms)
  exact AddCommGrpCat.isZero_iff_subsingleton.mp ht.isZero

def localRestrictionHom (i : Fin 3) :
    LocalLinearHom Ambient.sheaf CubicSections CanonicalTarget (chartOpen i) :=
  ⟨{
    app V := AddCommGrpCat.ofHom
      (localRestriction i V.unop.left V.unop.hom.le).toAddMonoidHom
    naturality {V W} f := by
      apply ConcreteCategory.hom_ext
      intro s
      exact (localRestriction_restrict i f.unop.left.le V.unop.hom.le s).symm
  }, by
    intro V r s
    exact (localRestriction i V.left V.hom.le).map_smul r s⟩

def coverRestriction : (i : Option (Fin 3)) →
    LocalLinearHom Ambient.sheaf CubicSections CanonicalTarget (restrictionCover i)
  | none => 0
  | some i => localRestrictionHom i

theorem coverRestriction_compatible : TopCat.Presheaf.IsCompatible
    (addSheaf (moduleHomSheaf Ambient.sheaf CubicSections CanonicalTarget)).obj
    restrictionCover coverRestriction := by
  intro i j
  apply localLinearHom_ext
  intro V s
  cases i with
  | none => exact @Subsingleton.elim _ (target_empty_of_le (V.hom.le.trans inf_le_left)) _ _
  | some i =>
    cases j with
    | none => exact @Subsingleton.elim _ (target_empty_of_le (V.hom.le.trans inf_le_right)) _ _
    | some j => exact localRestriction_overlap i j V.left
        (V.hom.le.trans inf_le_left) (V.hom.le.trans inf_le_right) s

theorem restrictionSection_existsUnique :
    ∃! H : LocalLinearHom Ambient.sheaf CubicSections CanonicalTarget ⊤, ∀ i,
      restrictLocalLinearHom Ambient.sheaf CubicSections CanonicalTarget
        (homOfLE (le_top : restrictionCover i ≤ ⊤)).op H = coverRestriction i := by
  change ∃! H : (addSheaf (moduleHomSheaf Ambient.sheaf CubicSections CanonicalTarget)).obj.obj (op ⊤), ∀ i,
    (addSheaf (moduleHomSheaf Ambient.sheaf CubicSections CanonicalTarget)).obj.map
      (homOfLE (le_top : restrictionCover i ≤ ⊤)).op H = coverRestriction i
  exact (addSheaf (moduleHomSheaf Ambient.sheaf CubicSections CanonicalTarget)).existsUnique_gluing'
    restrictionCover ⊤ (fun _ => homOfLE le_top) restrictionCover_top.ge
      coverRestriction coverRestriction_compatible

def restrictionSection : LocalLinearHom Ambient.sheaf CubicSections CanonicalTarget ⊤ :=
  Classical.choose restrictionSection_existsUnique

theorem restrictionSection_restrict (i : Option (Fin 3)) :
    restrictLocalLinearHom Ambient.sheaf CubicSections CanonicalTarget
      (homOfLE (le_top : restrictionCover i ≤ ⊤)).op restrictionSection = coverRestriction i :=
  (Classical.choose_spec restrictionSection_existsUnique).1 i

/-- The actual O(3) restriction into the pushed-forward original surface
canonical sheaf, with its fixed projective orientation. -/
def canonicalRestriction : CubicSections ⟶ CanonicalTarget :=
  localLinearHomTopEquiv Ambient.sheaf CubicSections CanonicalTarget restrictionSection

theorem canonicalRestriction_local (i : Fin 3) (W : Ambient.Opens)
    (hW : W ≤ chartOpen i) (s : Γ(CubicSections,W)) :
    canonicalRestriction.val.app (op W) s = localRestriction i W hW s := by
  exact congrArg
    (fun f : LocalLinearHom Ambient.sheaf CubicSections CanonicalTarget (chartOpen i) =>
      f.val.app (op (Over.mk (homOfLE hW))) s) (restrictionSection_restrict (some i))

/-- On every affine subopen of an original surface coordinate chart,
the canonical restriction is surjective. This uses the actual closed
immersion on section rings and the already fixed exterior frame. -/
theorem canonicalRestriction_surjective (i : Fin 3) (W : Ambient.Opens)
    (hW : IsAffineOpen W) (hi : W ≤ chartOpen i) :
    Function.Surjective (canonicalRestriction.val.app (op W)) := by
  intro s
  let e := (coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
    (preimage_le_chart i W hi)
  obtain ⟨a, ha⟩ := surfaceToAmbient.app_surjective W hW
    ((orientation i : Γ(Surface, surfaceToAmbient ⁻¹ᵁ W)) * e s)
  refine ⟨(chartFrame literalEval 3 i.succ W hi).symm a, e.injective ?_⟩
  rw [canonicalRestriction_local, localRestriction_coordinates,
    LinearEquiv.apply_symm_apply, ha, ← mul_assoc, orientation_mul_self, one_mul]

theorem localRestriction_cubicMultiply_zero (i : Fin 3) (W : Ambient.Opens)
    (hW : W ≤ chartOpen i) (s : Γ(twist literalEval 0,W)) :
    localRestriction i W hW (cubicMultiply.app W s) = 0 := by
  apply ((coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
    (preimage_le_chart i W hW)).injective
  rw [localRestriction_coordinates, map_zero, cubicMultiply, multiply_frame, map_mul,
    cubic_toSurface_zero i.succ W hW (surfaceToAmbient ⁻¹ᵁ W)
      (preimage_le_chart i W hW) le_rfl, zero_mul, mul_zero]

theorem canonicalRestriction_cubicMultiply_section (W : Ambient.Opens)
    (s : Γ(twist literalEval 0,W)) :
    canonicalRestriction.val.app (op W) (cubicMultiply.app W s) = 0 := by
  apply (addSheaf CanonicalTarget).eq_of_locally_eq'
    (fun i => W ⊓ restrictionCover i) W (fun _ => homOfLE inf_le_left)
    (by rw [← inf_iSup_eq, restrictionCover_top, inf_top_eq])
  intro i
  change CanonicalTarget.val.map
      (homOfLE (show W ⊓ restrictionCover i ≤ W from inf_le_left)).op
      (canonicalRestriction.val.app (op W) (cubicMultiply.app W s)) =
    CanonicalTarget.val.map
      (homOfLE (show W ⊓ restrictionCover i ≤ W from inf_le_left)).op 0
  rw [map_zero]
  refine (PresheafOfModules.naturality_apply canonicalRestriction.val
    (homOfLE (show W ⊓ restrictionCover i ≤ W from inf_le_left)).op
      (cubicMultiply.app W s)).symm.trans ?_
  refine (congrArg (fun v : Γ(CubicSections,W ⊓ restrictionCover i) =>
    canonicalRestriction.val.app (op (W ⊓ restrictionCover i)) v)
      (PresheafOfModules.naturality_apply cubicMultiply.val
        (homOfLE (show W ⊓ restrictionCover i ≤ W from inf_le_left)).op s).symm).trans ?_
  cases i with
  | none => exact @Subsingleton.elim _ (target_empty_of_le (show W ⊓ offSurface ≤ offSurface from inf_le_right)) _ _
  | some i =>
    exact (canonicalRestriction_local i (W ⊓ chartOpen i) inf_le_right _).trans
      (localRestriction_cubicMultiply_zero i (W ⊓ chartOpen i) inf_le_right _)

/-- The original cubic multiplication and canonical restriction have
exact section sequence on each affine chart neighborhood. -/
theorem canonicalRestriction_exact (i : Fin 3) (W : Ambient.Opens)
    (hW : IsAffineOpen W) (hi : W ≤ chartOpen i) :
    Function.Exact (cubicMultiply.app W) (canonicalRestriction.val.app (op W)) := by
  intro s
  constructor
  · intro hs
    have hz := congrArg ((coordinateExteriorFrame i).app (surfaceToAmbient ⁻¹ᵁ W)
      (preimage_le_chart i W hi)) hs
    rw [canonicalRestriction_local, localRestriction_coordinates, map_zero] at hz
    have ha : surfaceToAmbient.app W (chartFrame literalEval 3 i.succ W hi s) = 0 := by
      have h := congrArg (fun a : Γ(Surface, surfaceToAmbient ⁻¹ᵁ W) =>
        (orientation i : Γ(Surface, surfaceToAmbient ⁻¹ᵁ W)) * a) hz
      simpa only [← mul_assoc, orientation_mul_self, one_mul, mul_zero] using h
    exact cubicMultiply_preimage i.succ W hW hi s ha
  · rintro ⟨a, rfl⟩
    exact canonicalRestriction_cubicMultiply_section W a

theorem cubicMultiply_surjective_offSurface (i : Fin 4) (W : Ambient.Opens)
    (hW : IsAffineOpen W) (hi : W ≤ coordinateOpen literalEval i)
    (ho : W ≤ offSurface) : Function.Surjective (cubicMultiply.app W) := by
  letI := surface_sections_empty_of_le ho
  intro s
  exact cubicMultiply_preimage i W hW hi s (Subsingleton.elim _ _)

private theorem exact_neighborhoods (U : Ambient.Opens) (x : Ambient) (hx : x ∈ U) :
    ∃ (V : Ambient.Opens), V ≤ U ∧ x ∈ V ∧
      Function.Injective (cubicMultiply.app V) ∧
      Function.Exact (cubicMultiply.app V) (canonicalRestriction.val.app (op V)) ∧
      Function.Surjective (canonicalRestriction.val.app (op V)) := by
  have hc : x ∈ ⨆ i, restrictionCover i := by rw [restrictionCover_top]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hc
  cases i with
  | none =>
    have ha : x ∈ ⨆ j : Fin 4, coordinateOpen literalEval j := by
      rw [coordinateOpens_cover literalEval literal_vertex_unit]
      trivial
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ha
    let W := (U ⊓ offSurface) ⊓ coordinateOpen literalEval j
    have hxW : x ∈ W := ⟨⟨hx, hi⟩, hj⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Ambient.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    have hVo : V ≤ offSurface := hVW.trans (inf_le_left.trans inf_le_right)
    have hVj : V ≤ coordinateOpen literalEval j := hVW.trans inf_le_right
    have hm := cubicMultiply_surjective_offSurface j V hV hVj hVo
    letI := target_empty_of_le hVo
    refine ⟨V, hVW.trans (inf_le_left.trans inf_le_left), hxV,
      cubicMultiply_injective V, ?_, ?_⟩
    · intro s
      exact ⟨fun _ => hm s, fun _ => Subsingleton.elim _ _⟩
    · intro s
      exact ⟨0, Subsingleton.elim _ _⟩
  | some i =>
    let W := U ⊓ chartOpen i
    have hxW : x ∈ W := ⟨hx, hi⟩
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      Ambient.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    exact ⟨V, hVW.trans inf_le_left, hxV, cubicMultiply_injective V,
      canonicalRestriction_exact i V hV (hVW.trans inf_le_right),
      canonicalRestriction_surjective i V hV (hVW.trans inf_le_right)⟩

theorem cubicMultiply_comp_canonicalRestriction : cubicMultiply ≫ canonicalRestriction = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact canonicalRestriction_cubicMultiply_section W.unop s

def additiveRestriction : addSheaf CubicSections ⟶ addSheaf CanonicalTarget :=
  (SheafOfModules.toSheaf Ambient.ringCatSheaf).map canonicalRestriction

theorem coefficientInclusion_comp_restriction : coefficientInclusion ≫ additiveRestriction = 0 := by
  ext W s
  exact canonicalRestriction_cubicMultiply_section W.unop s

/-- The genuine canonical residue sequence of the original cubic
surface, with its actual restriction morphism and orientation. -/
def canonicalComplex : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} Ambient) :=
  ShortComplex.mk coefficientInclusion additiveRestriction
    coefficientInclusion_comp_restriction

theorem canonicalShortExact : canonicalComplex.ShortExact := by
  let B : Set Ambient.Opens := {V |
    Function.Injective (cubicMultiply.app V) ∧
      Function.Exact (cubicMultiply.app V) (canonicalRestriction.val.app (op V)) ∧
      Function.Surjective (canonicalRestriction.val.app (op V))}
  have hB : Opens.IsBasis B := by
    rw [Opens.isBasis_iff_nbhd]
    intro U x hx
    obtain ⟨V, hVU, hxV, hi, he, hs⟩ := exact_neighborhoods U x hx
    exact ⟨V, ⟨hi, he, hs⟩, hxV, hVU⟩
  exact CycleQ2GeometricSheafLocalExactness.additiveSheaf_shortExact_of_basis
    canonicalComplex B hB (fun _ hV => hV.1)
    (fun _ hV => hV.2.1) (fun _ hV => hV.2.2)

/-- The genuine coefficient cokernel maps to the original pushed-forward
canonical surface sheaf. Its formula is fixed by the actual restriction. -/
def quotientToCanonical : coefficientQuotient ⟶ addSheaf CanonicalTarget :=
  cokernel.desc coefficientInclusion additiveRestriction coefficientInclusion_comp_restriction

theorem quotientToCanonical_π : cokernel.π coefficientInclusion ≫ quotientToCanonical =
    additiveRestriction := cokernel.π_desc _ _ _

/-- The coefficient quotient is the actual pushed-forward canonical
surface sheaf. The isomorphism is fixed by the original restriction. -/
def quotientCanonicalIso : coefficientQuotient ≅ addSheaf CanonicalTarget :=
  (cokernelIsCokernel coefficientInclusion).coconePointUniqueUpToIso
    canonicalShortExact.gIsCokernel

theorem quotientCanonicalIso_hom : quotientCanonicalIso.hom = quotientToCanonical := by
  apply cokernel.hom_ext
  rw [quotientToCanonical_π]
  exact (cokernelIsCokernel coefficientInclusion).comp_coconePointUniqueUpToIso_hom
    canonicalShortExact.gIsCokernel WalkingParallelPair.one

theorem quotientToCanonical_isIso : IsIso quotientToCanonical := by
  rw [← quotientCanonicalIso_hom]
  infer_instance

local instance canonicalHasExt (Z : AlgebraicGeometry.Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}) := HasExt.standard _

/-- The boundary of the actual canonical surface sequence. -/
def canonicalBoundary (W : Ambient.Opens) :
    (addSheaf CanonicalTarget).H' 2 W →+ (addSheaf (twist literalEval 0)).H' 3 W :=
  CycleQ2GeometricIntrinsicCartierCohomology.openConnecting canonicalShortExact 2 W

private def coefficientToCanonical : coefficientComplex ⟶ canonicalComplex where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := quotientToCanonical
  comm₁₂ := by simp only [Category.id_comp, Category.comp_id]
  comm₂₃ := by
    simpa only [Category.id_comp] using quotientToCanonical_π.symm

/-- The quotient identification preserves the actual connecting map;
this is naturality for the displayed morphism of short exact sequences. -/
theorem canonicalBoundary_quotient (W : Ambient.Opens)
    (z : coefficientQuotient.H' 2 W) :
    canonicalBoundary W (z.comp (Ext.mk₀ quotientToCanonical) (add_zero 2)) =
      coefficientConnecting W z := by
  have h := CycleQ2CechTwoNaturality.connecting_naturality
    coefficientShortExact canonicalShortExact coefficientToCanonical 2 z
  simpa only [coefficientToCanonical, Ext.comp_mk₀_id] using h.symm

theorem canonicalBoundary_injective : Function.Injective (canonicalBoundary ⊤) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃
    (CycleQ2InjectiveCech.freeOpen (⊤ : Ambient.Opens)) canonicalShortExact x rfl hx
  have hy0 : y = 0 := coefficientPole_hTwo.elim _ _
  simpa only [hy0, Ext.zero_comp] using hy.symm

theorem canonicalBoundary_surjective : Function.Surjective (canonicalBoundary ⊤) := by
  letI := coefficientPole_hThree
  intro x
  exact Ext.covariant_sequence_exact₁
    (CycleQ2InjectiveCech.freeOpen (⊤ : Ambient.Opens))
    canonicalShortExact x (by subsingleton) rfl

def canonicalBoundaryEquiv : (addSheaf CanonicalTarget).H' 2 ⊤ ≃+
    (addSheaf (twist literalEval 0)).H' 3 ⊤ :=
  AddEquiv.ofBijective (canonicalBoundary ⊤)
    ⟨canonicalBoundary_injective, canonicalBoundary_surjective⟩

/-- Direct image by the original closed surface inclusion, followed by
the canonical residue boundary. Both maps are the actual derived maps. -/
def surfaceGysinEquiv : (addSheaf CanonicalForms).H' 2 ⊤ ≃+
    (addSheaf (twist literalEval 0)).H' 3 ⊤ :=
  (CycleQ2ClosedEmbeddingCohomology.pushHEquiv surfaceToAmbient.base
    surfaceToAmbient.isClosedEmbedding (addSheaf CanonicalForms) 2).trans canonicalBoundaryEquiv

def surfaceGysin : (addSheaf CanonicalForms).H' 2 ⊤ →+
    (addSheaf (twist literalEval 0)).H' 3 ⊤ := surfaceGysinEquiv.toAddMonoidHom

theorem surfaceGysin_apply (z : (addSheaf CanonicalForms).H' 2 ⊤) :
    surfaceGysin z =
      (CycleQ2ClosedEmbeddingCohomology.pushHEquiv surfaceToAmbient.base
        surfaceToAmbient.isClosedEmbedding (addSheaf CanonicalForms) 2 z).comp
          canonicalShortExact.extClass rfl := rfl

theorem surfaceGysin_ne_zero (z : (addSheaf CanonicalForms).H' 2 ⊤) (hz : z ≠ 0) :
    surfaceGysin z ≠ 0 := by
  intro h
  apply hz
  exact surfaceGysinEquiv.injective (by simpa only [map_zero] using h)

end CycleQ2LiteralCubicCanonicalRestriction
end

#print axioms CycleQ2LiteralCubicCanonicalRestriction.localRestriction_overlap
#print axioms CycleQ2LiteralCubicCanonicalRestriction.canonicalRestriction_local
#print axioms CycleQ2LiteralCubicCanonicalRestriction.canonicalShortExact
#print axioms CycleQ2LiteralCubicCanonicalRestriction.quotientToCanonical_π
#print axioms CycleQ2LiteralCubicCanonicalRestriction.quotientCanonicalIso_hom
#print axioms CycleQ2LiteralCubicCanonicalRestriction.canonicalBoundary_quotient
#print axioms CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin_apply

/-!
## Detecting the actual quotient class by the original residue generator

The coefficient quotient has no H′¹ on the four affine coordinate opens.
Consequently a zero two-class has a six-edge Čech primitive. Restriction
of its 12, 13, and 23 edges to the original surface makes its 123 face a
three-open boundary there. The original canonical generator has residue
one, so a quotient cocycle with that face gives a nonzero class and a
nonzero image under the genuine cubic connecting homomorphism.

Only the actual quotient-to-canonical morphism is needed. No cokernel
isomorphism or closed-immersion cohomology comparison is assumed.
-/

noncomputable section
namespace CycleQ2LiteralCubicResidueDetection

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralProjectiveCubicDivisor CycleQ2LiteralCubicCanonicalRestriction
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2HodgeThreefoldTwist CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2GeometricProjectiveHOne

abbrev Ambient := CycleQ2LiteralProjectiveCubicDivisor.Ambient
abbrev Surface := CycleQ2LiteralProjectiveCubicDivisor.Surface
abbrev CanonicalSheaf := CycleQ2CanonicalCoordinateH2.CanonicalSheaf
abbrev surfaceOpen := CycleQ2CanonicalCoordinateH2.CoordinateOpen
abbrev surfaceTriple := CycleQ2CanonicalCoordinateH2.TripleOpen
abbrev ambientCover : Fin 4 → Ambient.Opens := coordinateOpen literalEval

local instance : IsClosedImmersion surfaceToAmbient := surfaceToAmbient_isClosedImmersion

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Ambient) AddCommGrpCat.{0}) := HasExt.standard _
local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) := HasExt.standard _

theorem ambientCover_top : (⨆ i, ambientCover i) = ⊤ :=
  coordinateOpens_cover literalEval literal_vertex_unit

private theorem coordinate_affine (i : Fin 4) : IsAffineOpen (ambientCover i) := by
  have h := CycleQ2HodgeTwistFaces.face_affine literalEval i ∅
  simpa only [CycleQ2HodgeTwistFaces.face_eq, Finset.inf_empty, inf_top_eq] using h

private def additiveFrame (k : ℤ) (i : Fin 4) :
    PatchIso (addSheaf (twist literalEval k)) (structureAdditiveSheaf Ambient)
      (ambientCover i) where
  app V hV := (chartFrame literalEval k i V hV).toAddEquiv
  naturality hWV hV s :=
    (CycleQ2HodgeAtlasLine.coordinate_restrict
      (CycleQ2HodgeThreefoldTwist.cocycle literalEval k) i hV hWV s).symm

private theorem twist_hOne (k : ℤ) (i : Fin 4) :
    Subsingleton ((addSheaf (twist literalEval k)).H' 1 (ambientCover i)) :=
  affineFrameHOne_subsingleton (coordinate_affine i).isoSpec _
    (overIsoOfPatchIso (additiveFrame k i))

private theorem twist_hTwo (k : ℤ) (i : Fin 4) :
    Subsingleton ((addSheaf (twist literalEval k)).H' 2 (ambientCover i)) :=
  affineFrameHTwo_subsingleton (coordinate_affine i).isoSpec _
    (overIsoOfPatchIso (additiveFrame k i))
    (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton _)

/-- Local degree-one vanishing for the genuine coefficient cokernel
follows from the same short exact sequence and the actual affine frames. -/
theorem coefficientQuotient_hOne (i : Fin 4) :
    Subsingleton (coefficientQuotient.H' 1 (ambientCover i)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  have hx : x.comp coefficientShortExact.extClass (show 1 + 1 = 2 from rfl) = 0 :=
    (twist_hTwo 0 i).elim _ _
  obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₃
    (freeOpen (ambientCover i)) coefficientShortExact x rfl hx
  have hy0 : y = 0 := (twist_hOne 3 i).elim _ _
  simpa only [hy0, Ext.zero_comp] using hy.symm

/-- Restriction through the actual coefficient quotient map, to any
surface subopen of the inverse image of the ambient open. -/
def pullCanonical {W : Ambient.Opens} {V : Surface.Opens}
    (hVW : V ≤ surfaceToAmbient ⁻¹ᵁ W) :
    Sections coefficientQuotient W →+ Sections CanonicalSheaf V :=
  (res CanonicalSheaf hVW).comp (app quotientToCanonical W)

theorem pullCanonical_res {P W : Ambient.Opens} {V : Surface.Opens}
    (hVP : V ≤ surfaceToAmbient ⁻¹ᵁ P) (hPW : P ≤ W)
    (s : Sections coefficientQuotient W) :
    pullCanonical hVP (res coefficientQuotient hPW s) =
      pullCanonical (hVP.trans (surfaceToAmbient.preimage_mono hPW)) s := by
  change res CanonicalSheaf hVP
      (app quotientToCanonical P (res coefficientQuotient hPW s)) = _
  rw [app_res]
  exact res_comp CanonicalSheaf (surfaceToAmbient.preimage_mono hPW) hVP _

theorem pullCanonical_restrict {W : Ambient.Opens} {V P : Surface.Opens}
    (hVP : V ≤ P) (hPW : P ≤ surfaceToAmbient ⁻¹ᵁ W)
    (s : Sections coefficientQuotient W) :
    res CanonicalSheaf hVP (pullCanonical hPW s) =
      pullCanonical (hVP.trans hPW) s :=
  res_comp CanonicalSheaf hPW hVP _

theorem pullCanonical_π {W : Ambient.Opens} {V : Surface.Opens}
    (hVW : V ≤ surfaceToAmbient ⁻¹ᵁ W)
    (s : Sections (addSheaf (twist literalEval 3)) W) :
    pullCanonical hVW (app (cokernel.π coefficientInclusion) W s) =
      res CanonicalSheaf hVW (app additiveRestriction W s) := by
  change res CanonicalSheaf hVW
      (app quotientToCanonical W (app (cokernel.π coefficientInclusion) W s)) = _
  rw [app_comp, quotientToCanonical_π]

theorem coordinate_preimage (i : Fin 3) :
    surfaceToAmbient ⁻¹ᵁ ambientCover i.succ = surfaceOpen i := by
  rw [surfaceToAmbient_preimage]
  fin_cases i <;> rfl

theorem pair_le_preimage (i j : Fin 3) :
    surfaceOpen i ⊓ surfaceOpen j ≤
      surfaceToAmbient ⁻¹ᵁ (ambientCover i.succ ⊓ ambientCover j.succ) := by
  change surfaceOpen i ⊓ surfaceOpen j ≤
    (surfaceToAmbient ⁻¹ᵁ ambientCover i.succ) ⊓
      (surfaceToAmbient ⁻¹ᵁ ambientCover j.succ)
  exact inf_le_inf (coordinate_preimage i).ge (coordinate_preimage j).ge

theorem triple_le_preimage : surfaceTriple ≤
    surfaceToAmbient ⁻¹ᵁ ((ambientCover 1 ⊓ ambientCover 2) ⊓ ambientCover 3) := by
  change (surfaceOpen 0 ⊓ surfaceOpen 2) ⊓ (surfaceOpen 1 ⊓ surfaceOpen 2) ≤
    ((surfaceToAmbient ⁻¹ᵁ ambientCover 1) ⊓ (surfaceToAmbient ⁻¹ᵁ ambientCover 2)) ⊓
      (surfaceToAmbient ⁻¹ᵁ ambientCover 3)
  exact le_inf
    (le_inf ((inf_le_left.trans inf_le_left).trans (coordinate_preimage 0).ge)
      ((inf_le_right.trans inf_le_left).trans (coordinate_preimage 1).ge))
    ((inf_le_left.trans inf_le_right).trans (coordinate_preimage 2).ge)

def canonicalEdge (i j : Fin 3)
    (s : Sections coefficientQuotient (ambientCover i.succ ⊓ ambientCover j.succ)) :
    Sections CanonicalSheaf (surfaceOpen i ⊓ surfaceOpen j) :=
  pullCanonical (pair_le_preimage i j) s

/-- The actual surface restriction of the 123 face, on the original
three-open trace domain with its unchanged intersection convention. -/
def canonicalFace (c : Two coefficientQuotient ambientCover) :
    Sections CanonicalSheaf surfaceTriple :=
  pullCanonical triple_le_preimage c.2.2.2

/-- Cohomological restriction through the actual quotient-to-canonical
isomorphism and the inverse of the original closed direct-image map. -/
def surfaceRestriction : coefficientQuotient.H' 2 ⊤ →+ CanonicalSheaf.H' 2 ⊤ :=
  (CycleQ2ClosedEmbeddingCohomology.pushHEquiv surfaceToAmbient.base
    surfaceToAmbient.isClosedEmbedding CanonicalSheaf 2).symm.toAddMonoidHom.comp
      ((Ext.mk₀ quotientToCanonical).postcomp (freeOpen (⊤ : Ambient.Opens)) (add_zero 2))

theorem surfaceGysin_surfaceRestriction (z : coefficientQuotient.H' 2 ⊤) :
    surfaceGysin (surfaceRestriction z) = coefficientConnecting ⊤ z := by
  change canonicalBoundary ⊤
    ((CycleQ2ClosedEmbeddingCohomology.pushHEquiv surfaceToAmbient.base
      surfaceToAmbient.isClosedEmbedding CanonicalSheaf 2)
      ((CycleQ2ClosedEmbeddingCohomology.pushHEquiv surfaceToAmbient.base
        surfaceToAmbient.isClosedEmbedding CanonicalSheaf 2).symm
        (z.comp (Ext.mk₀ quotientToCanonical) (add_zero 2)))) = _
  rw [AddEquiv.apply_symm_apply, canonicalBoundary_quotient]

private theorem surfaceCover_top : (⨆ i : Fin 3, surfaceOpen i) = ⊤ := by
  apply le_antisymm le_top
  rw [← CycleQ2CanonicalCoordinateH2.coordinateCover]
  exact sup_le (sup_le (le_iSup surfaceOpen 0) (le_iSup surfaceOpen 1))
    (le_iSup surfaceOpen 2)

/-- Closed-pushforward comparison and restriction to the original
three-open subcover identify the actual quotient class with its 123
canonical face, with the positive degree-two normalization. -/
theorem surfaceRestriction_cechTwoClass
    (c : Two coefficientQuotient ambientCover) (hc : d2 coefficientQuotient ambientCover c = 0) :
    surfaceRestriction (cechTwoClass ambientCover ambientCover_top c hc) =
      CycleQ2CanonicalCoordinateH2.canonicalConnecting (canonicalFace c) := by
  let f := surfaceToAmbient.base
  let V := CycleQ2FiniteCechOrbitPullback.cover f ambientCover
  have hV := CycleQ2FiniteCechOrbitPullback.cover_top f ambientCover ambientCover_top
  let b := CycleQ2FourToFiniteCech.extendTwo ambientCover c
  have hn := CycleQ2FourToFiniteCech.extendTwo_normalized ambientCover c
  have hb := CycleQ2FourToFiniteCech.extendTwo_closed ambientCover ambientCover_top c hc
  let p := CycleQ2FiniteCechOrbitPullback.pullTwo f quotientToCanonical ambientCover b
  have hpn := CycleQ2FiniteCechOrbitPullback.pullTwo_normalized
    f quotientToCanonical ambientCover b hn
  have hpc := CycleQ2FiniteCechOrbitPullback.pullTwo_closed
    f quotientToCanonical ambientCover b hb
  have hs (i : Fin 3) : surfaceOpen i ≤ V i.succ := (coordinate_preimage i).ge
  let r := CycleQ2FiniteCechRefinement.restrictTwo V surfaceOpen Fin.succ hs p
  have hrn := CycleQ2FiniteCechRefinement.restrictTwo_normalized V surfaceOpen Fin.succ hs p hpn
  have hrc := CycleQ2FiniteCechRefinement.restrictTwo_closed V surfaceOpen Fin.succ hs p hpc
  have hp : surfaceRestriction (cechTwoClass ambientCover ambientCover_top c hc) =
      CycleQ2FiniteCechDescent.cechTwoClass V hV p hpn hpc := by
    have h := CycleQ2ClosedEmbeddingCechTwo.restrict_cech f
      surfaceToAmbient.isClosedEmbedding ambientCover ambientCover_top quotientToCanonical b hn hb
    rw [CycleQ2FourToFiniteCech.finiteClass_eq_fourClass ambientCover ambientCover_top c hc] at h
    exact h
  have hr : CycleQ2FiniteCechDescent.cechTwoClass surfaceOpen surfaceCover_top r hrn hrc =
      CycleQ2FiniteCechDescent.cechTwoClass V hV p hpn hpc :=
    CycleQ2FiniteCechRefinement.cechTwoClass_refinement V surfaceOpen Fin.succ hs
      hV surfaceCover_top p hpn hpc
  have hf : CycleQ2ThreeOpenInjectiveComparison.selectedTriple surfaceOpen r 0 1 2 =
      canonicalFace c := by
    rw [CycleQ2ThreeOpenInjectiveComparison.selectedTriple,
      CycleQ2FiniteCechRefinement.faceValue_restrictTwo]
    rw [CycleQ2FiniteCechOrbitPullback.faceValue_pullTwo f quotientToCanonical ambientCover b
      1 2 3 triple_le_preimage (inf_le_left.trans inf_le_left)
      (inf_le_left.trans inf_le_right) inf_le_right,
      CycleQ2FourToFiniteCech.faceValue_extendTwo]
    change pullCanonical triple_le_preimage
      (res coefficientQuotient le_rfl c.2.2.2) = canonicalFace c
    rw [res_self]
    rfl
  rw [hp, ← hr]
  have ht := CycleQ2FourOpenThreeSubcover.finiteClass_eq_connectingAtTop surfaceOpen
    surfaceCover_top r hrn hrc 0 1 2 CycleQ2CanonicalCoordinateH2.coordinateCover
  rw [hf] at ht
  exact ht

theorem canonicalFace_d1 (b : One coefficientQuotient ambientCover) :
    canonicalFace (d1 coefficientQuotient ambientCover b) =
      CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
        (surfaceOpen 0) (surfaceOpen 1) (surfaceOpen 2)
        (canonicalEdge 0 1 b.2.2.2.1, canonicalEdge 0 2 b.2.2.2.2.1,
          canonicalEdge 1 2 b.2.2.2.2.2) := by
  change pullCanonical triple_le_preimage
      (res coefficientQuotient _ b.2.2.2.2.2 -
        res coefficientQuotient _ b.2.2.2.2.1 +
        res coefficientQuotient _ b.2.2.2.1) =
    res CanonicalSheaf _ (pullCanonical (pair_le_preimage 1 2) b.2.2.2.2.2) -
      res CanonicalSheaf _ (pullCanonical (pair_le_preimage 0 2) b.2.2.2.2.1) +
      res CanonicalSheaf _ (pullCanonical (pair_le_preimage 0 1) b.2.2.2.1)
  rw [map_add, map_sub, pullCanonical_res, pullCanonical_res, pullCanonical_res,
    pullCanonical_restrict, pullCanonical_restrict, pullCanonical_restrict]

/-- The established residue-one generator detects this actual quotient
class. The hypothesis is a single literal face equality, not an abstract
injectivity or nonvanishing assumption about the quotient map. -/
theorem quotientClass_ne_zero_of_residue
    (c : Two coefficientQuotient ambientCover) (hc : d2 coefficientQuotient ambientCover c = 0)
    (hface : canonicalFace c =
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator) :
    cechTwoClass ambientCover ambientCover_top c hc ≠ 0 := by
  apply cechTwoClass_ne_zero ambientCover ambientCover_top c hc coefficientQuotient_hOne
  rintro ⟨b,rfl⟩
  apply CycleQ2LiteralCanonicalResidueGenerator.canonicalConnecting_residueGenerator_ne_zero
  apply (CycleQ2CanonicalCoordinateH2.canonicalConnecting_eq_zero_iff _).mpr
  exact ⟨canonicalEdge 0 1 b.2.2.2.1, canonicalEdge 0 2 b.2.2.2.2.1,
    canonicalEdge 1 2 b.2.2.2.2.2, (canonicalFace_d1 b).symm.trans hface⟩

theorem coefficientConnecting_ne_zero_of_residue
    (c : Two coefficientQuotient ambientCover) (hc : d2 coefficientQuotient ambientCover c = 0)
    (hface : canonicalFace c =
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator) :
    coefficientConnecting ⊤ (cechTwoClass ambientCover ambientCover_top c hc) ≠ 0 :=
  coefficientConnecting_ne_zero _ (quotientClass_ne_zero_of_residue c hc hface)

/-- The four actual pole lifts, reduced through the genuine sheaf cokernel. -/
def quotientTwo (c : Two (addSheaf (twist literalEval 3)) ambientCover) :
    Two coefficientQuotient ambientCover :=
  mapTwo ambientCover (cokernel.π coefficientInclusion) c

theorem quotientTwo_cocycle_of_cubic_boundary
    (c : Two (addSheaf (twist literalEval 3)) ambientCover)
    (a : Three (addSheaf (twist literalEval 0)) ambientCover)
    (hc : d2 (addSheaf (twist literalEval 3)) ambientCover c =
      app coefficientInclusion _ a) :
    d2 coefficientQuotient ambientCover (quotientTwo c) = 0 := by
  rw [quotientTwo, ← mapThree_d2, hc, app_comp, cokernel.condition, app_zero]

theorem canonicalFace_quotientTwo
    (c : Two (addSheaf (twist literalEval 3)) ambientCover) :
    canonicalFace (quotientTwo c) = res CanonicalSheaf triple_le_preimage
      (app additiveRestriction ((ambientCover 1 ⊓ ambientCover 2) ⊓ ambientCover 3) c.2.2.2) :=
  pullCanonical_π triple_le_preimage c.2.2.2

end CycleQ2LiteralCubicResidueDetection
end

#print axioms CycleQ2LiteralCubicResidueDetection.coefficientQuotient_hOne
#print axioms CycleQ2LiteralCubicResidueDetection.canonicalFace_d1
#print axioms CycleQ2LiteralCubicResidueDetection.surfaceRestriction_cechTwoClass
#print axioms CycleQ2LiteralCubicResidueDetection.surfaceGysin_surfaceRestriction
#print axioms CycleQ2LiteralCubicResidueDetection.quotientClass_ne_zero_of_residue
#print axioms CycleQ2LiteralCubicResidueDetection.coefficientConnecting_ne_zero_of_residue
#print axioms CycleQ2LiteralCubicResidueDetection.quotientTwo_cocycle_of_cubic_boundary

/-!
## The literal four-face quotient cocycle

The four quadrics already used in the cone calculation now act on the
actual native partial-fraction sections of O(1). The finite identity
`h = ∑ xᵢ qᵢ` therefore proves the cubic boundary equation on the original
projective cover. Reducing these four O(3) sections through the actual
coefficient cokernel gives a closed two-cochain.
-/

noncomputable section
namespace CycleQ2LiteralCubicProjectiveCocycle

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial CycleQ2LiteralProjectiveCubicDivisor
  CycleQ2LiteralCubicCanonicalRestriction CycleQ2LiteralCubicResidueDetection
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2HodgeThreefoldTwist CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2HodgeTwistTorusChart CycleQ2HodgeTwistCoordinates

abbrev Ambient := CycleQ2LiteralProjectiveCubicDivisor.Ambient
abbrev PoleSheaf := addSheaf (twist literalEval 3)
abbrev RegularSheaf := addSheaf (twist literalEval 0)

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Ambient) AddCommGrpCat.{0}) := HasExt.standard _

def literalQuadrics (i : Fin 4) : cone literalEval :=
  quotient literalEval (CycleQ2LiteralCubicResidueLift.quadric i)

theorem literalQuadrics_homogeneous (i : Fin 4) :
    literalQuadrics i ∈ grade literalEval 2 :=
  quotient_mem_grade literalEval _ (CycleQ2LiteralCubicResidueLift.quadric_homogeneous i)

theorem literal_assembledCubic : assembledCubic literalEval literalQuadrics = cubic := by
  change (∑ i : Fin 4, quotient literalEval (X i.castSucc) *
    quotient literalEval (CycleQ2LiteralCubicResidueLift.quadric i)) =
      quotient literalEval (CycleQ2NormalConnecting.thetaH 1)
  rw [CycleQ2LiteralCubicResidueLift.cubic_coordinate_division, map_sum]
  simp only [map_mul]

/-- The actual native lifts on the four omitted-coordinate faces. -/
def nativeLifts : NativeTopFaces (F := PoleSheaf) (U := ambientCover) :=
  quadricBoundaryLift literalEval literal_vertex_unit literalQuadrics literalQuadrics_homogeneous

theorem nativeLifts_boundary : nativeTopBoundary nativeLifts =
    app coefficientInclusion (CycleQ2HodgeTwistAnchor.torus literalEval)
      (twistTopGenerator literalEval literal_vertex_unit) := by
  have h := quadricBoundaryLift_boundary literalEval literal_vertex_unit
    literalQuadrics literalQuadrics_homogeneous
  rw [literal_assembledCubic] at h
  exact h

private theorem face_zero : (Finset.univ.erase (0 : Fin 4)).inf ambientCover =
    (ambientCover 1 ⊓ ambientCover 2) ⊓ ambientCover 3 := by
  rw [show Finset.univ.erase (0 : Fin 4) = {1,2,3} from by decide]
  simp [inf_assoc]

private theorem face_one : (Finset.univ.erase (1 : Fin 4)).inf ambientCover =
    (ambientCover 0 ⊓ ambientCover 2) ⊓ ambientCover 3 := by
  rw [show Finset.univ.erase (1 : Fin 4) = {0,2,3} from by decide]
  simp [inf_assoc]

private theorem face_two : (Finset.univ.erase (2 : Fin 4)).inf ambientCover =
    (ambientCover 0 ⊓ ambientCover 1) ⊓ ambientCover 3 := by
  rw [show Finset.univ.erase (2 : Fin 4) = {0,1,3} from by decide]
  simp [inf_assoc]

private theorem face_three : (Finset.univ.erase (3 : Fin 4)).inf ambientCover =
    (ambientCover 0 ⊓ ambientCover 1) ⊓ ambientCover 2 := by
  rw [show Finset.univ.erase (3 : Fin 4) = {0,1,2} from by decide]
  simp [inf_assoc]

private theorem full_ordered : Finset.univ.inf ambientCover =
    ((ambientCover 0 ⊓ ambientCover 1) ⊓ ambientCover 2) ⊓ ambientCover 3 := by
  rw [show (Finset.univ : Finset (Fin 4)) = {0,1,2,3} from by decide]
  simp [inf_assoc]

/-- The same four native sections, in the ordered two-cochain convention
used by the proved Čech-to-derived comparison. -/
def liftedTwo : Two PoleSheaf ambientCover :=
  ⟨res PoleSheaf face_three.ge (nativeLifts 3),
    res PoleSheaf face_two.ge (nativeLifts 2),
    res PoleSheaf face_one.ge (nativeLifts 1),
    res PoleSheaf face_zero.ge (nativeLifts 0)⟩

def ambientTop : Three RegularSheaf ambientCover :=
  res RegularSheaf full_ordered.ge (twistTopGenerator literalEval literal_vertex_unit)

theorem liftedTwo_boundary : d2 PoleSheaf ambientCover liftedTwo =
    app coefficientInclusion _ ambientTop := by
  have h : d2 PoleSheaf ambientCover liftedTwo =
      res PoleSheaf full_ordered.ge (nativeTopBoundary nativeLifts) := by
    change res PoleSheaf _ (res PoleSheaf _ (nativeLifts 0)) -
        res PoleSheaf _ (res PoleSheaf _ (nativeLifts 1)) +
        res PoleSheaf _ (res PoleSheaf _ (nativeLifts 2)) -
        res PoleSheaf _ (res PoleSheaf _ (nativeLifts 3)) =
      res PoleSheaf _
        (res PoleSheaf _ (nativeLifts 0) - res PoleSheaf _ (nativeLifts 1) +
          res PoleSheaf _ (nativeLifts 2) - res PoleSheaf _ (nativeLifts 3))
    simp only [map_sub, map_add, res_comp]
  rw [h, nativeLifts_boundary]
  exact (app_res coefficientInclusion full_ordered.ge
    (twistTopGenerator literalEval literal_vertex_unit)).symm

/-- A closed cochain in the genuine coefficient quotient. -/
def residueCocycle : Two coefficientQuotient ambientCover := quotientTwo liftedTwo

theorem residueCocycle_closed : d2 coefficientQuotient ambientCover residueCocycle = 0 :=
  quotientTwo_cocycle_of_cubic_boundary liftedTwo ambientTop liftedTwo_boundary

def residueClass : coefficientQuotient.H' 2 ⊤ :=
  cechTwoClass ambientCover ambientCover_top residueCocycle residueCocycle_closed

end CycleQ2LiteralCubicProjectiveCocycle
end

#print axioms CycleQ2LiteralCubicProjectiveCocycle.literal_assembledCubic
#print axioms CycleQ2LiteralCubicProjectiveCocycle.nativeLifts_boundary
#print axioms CycleQ2LiteralCubicProjectiveCocycle.liftedTwo_boundary
#print axioms CycleQ2LiteralCubicProjectiveCocycle.residueCocycle_closed

noncomputable section
namespace CycleQ2LiteralCubicProjectiveCocycle

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  MvPolynomial CycleQ2LiteralProjectiveCubicDivisor
  CycleQ2LiteralCubicCanonicalRestriction CycleQ2LiteralCubicResidueDetection
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2HodgeThreefoldTwist CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateCubicFrames
  CycleQ2SurfaceCoordinateSections CycleQ2SurfaceSectionCoefficients
  CycleQ2CanonicalCoordinateCoefficients CycleQ2GeometricSurfaceCoordinates
  CycleQ2ProjectiveCoordinateH2 CycleQ2ProjectiveCoordinateCohomology
  CycleQ2GeometricSeedNormalIdeals

abbrev Surface := CycleQ2LiteralProjectiveCubicDivisor.Surface

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Ambient) AddCommGrpCat.{0}) := HasExt.standard _
local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) := HasExt.standard _

def nativeFaceZero : Ambient.Opens := (Finset.univ.erase (0 : Fin 4)).inf ambientCover

theorem nativeFaceZero_le_chart : nativeFaceZero ≤ chartOpen 0 :=
  Finset.inf_le (by decide : (1 : Fin 4) ∈ Finset.univ.erase 0)

theorem surfaceTriple_le_nativeFace : surfaceTriple ≤ surfaceToAmbient ⁻¹ᵁ nativeFaceZero :=
  triple_le_preimage.trans (surfaceToAmbient.preimage_mono face_zero.ge)

theorem surfaceTriple_le_first : surfaceTriple ≤
    CycleQ2FullSurfaceResidueCover.coordinateOpen 0 :=
  (surfaceTriple_le_nativeFace.trans (surfaceToAmbient.preimage_mono nativeFaceZero_le_chart)).trans
    (preimage_chartOpen 0).le

/-- The actual coefficient of the literal 123 pole lift, restricted to
the original surface triple open through the original scheme morphism. -/
def surfacePoleCoefficient : Γ(Surface,surfaceTriple) :=
  surfaceToAmbient.appLE nativeFaceZero surfaceTriple surfaceTriple_le_nativeFace
    (chartFrame literalEval 3 1 nativeFaceZero nativeFaceZero_le_chart (nativeLifts 0))

theorem canonicalFace_native : canonicalFace residueCocycle =
    res CycleQ2LiteralCubicResidueDetection.CanonicalSheaf surfaceTriple_le_nativeFace
      (app additiveRestriction nativeFaceZero (nativeLifts 0)) := by
  rw [residueCocycle, canonicalFace_quotientTwo]
  change res CycleQ2LiteralCubicResidueDetection.CanonicalSheaf triple_le_preimage
      (app additiveRestriction _ (res PoleSheaf face_zero.ge (nativeLifts 0))) = _
  rw [app_res]
  exact res_comp CycleQ2LiteralCubicResidueDetection.CanonicalSheaf
    (surfaceToAmbient.preimage_mono face_zero.ge) triple_le_preimage _

/-- On the first surface chart the signed residue frame has sign +1.
The quotient face therefore has exactly the restricted O(3) coefficient. -/
theorem canonicalFace_firstFrame :
    (coordinateExteriorFrame 0).app surfaceTriple surfaceTriple_le_first
      (canonicalFace residueCocycle) = surfacePoleCoefficient := by
  rw [canonicalFace_native]
  change (coordinateExteriorFrame 0).app surfaceTriple surfaceTriple_le_first
      (CycleQ2LiteralCubicCanonicalRestriction.CanonicalForms.val.map
        (homOfLE surfaceTriple_le_nativeFace).op
        (canonicalRestriction.val.app (op nativeFaceZero) (nativeLifts 0))) = _
  rw [← (coordinateExteriorFrame 0).naturality surfaceTriple_le_nativeFace
    (preimage_le_chart 0 nativeFaceZero nativeFaceZero_le_chart),
    canonicalRestriction_local, localRestriction_coordinates]
  change Surface.presheaf.map (homOfLE surfaceTriple_le_nativeFace).op
      ((1 : Γ(Surface,surfaceToAmbient ⁻¹ᵁ nativeFaceZero)) *
        surfaceToAmbient.app nativeFaceZero
          (chartFrame literalEval 3 1 nativeFaceZero nativeFaceZero_le_chart (nativeLifts 0))) = _
  rw [one_mul]
  simpa only [surfacePoleCoefficient, Scheme.Hom.appLE_eq_app] using
    (ConcreteCategory.congr_hom
    (surfaceToAmbient.appLE_map (show surfaceToAmbient ⁻¹ᵁ nativeFaceZero ≤
      surfaceToAmbient ⁻¹ᵁ nativeFaceZero from le_rfl)
      (homOfLE surfaceTriple_le_nativeFace).op)
      (chartFrame literalEval 3 1 nativeFaceZero nativeFaceZero_le_chart (nativeLifts 0)))

private theorem triple_eq_intersection : surfaceTriple = coordinateIntersection 57 1 Finset.univ :=
  (coordinateIntersection_univ 57 1).symm

def tripleCoefficient : Γ(Surface,surfaceTriple) →+* CoordinateLocal 57 1 Finset.univ :=
  sectionCoefficientAt 57 1 Finset.univ (by simp) surfaceTriple triple_eq_intersection

/-- The unchanged canonical coefficient map reads a section in the
first residue frame by multiplying its ordinary coefficient by x₁³. -/
theorem canonicalCoefficient_firstFrame
    (ω : CycleQ2LiteralCubicResidueDetection.CanonicalSheaf.obj.obj (op surfaceTriple)) :
    canonicalCoefficient ω =
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
        ((coordinateElement 57 1 0)^3) *
      tripleCoefficient ((coordinateExteriorFrame 0).app surfaceTriple surfaceTriple_le_first ω) := by
  suffices ∀ (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 Finset.univ)
      (hfirst : O ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen 0)
      (η : CycleQ2LiteralCubicCanonicalRestriction.CanonicalForms.val.obj (op O)),
      canonicalCoefficientAt Finset.univ (by simp) O hO η =
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
          ((coordinateElement 57 1 0)^3) *
        sectionCoefficientAt 57 1 Finset.univ (by simp) O hO
          ((coordinateExteriorFrame 0).app O hfirst η) from
    this surfaceTriple triple_eq_intersection surfaceTriple_le_first ω
  intro O hO hfirst η
  subst O
  change canonicalCoefficientOn Finset.univ (by simp) η = _
  rw [canonicalCoefficientOn_eq Finset.univ (by simp) 0 (by simp)]
  change (1 : CoordinateLocal 57 1 Finset.univ) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
        ((coordinateElement 57 1 0)^3) *
      sectionCoefficient 57 1 Finset.univ (by simp)
        ((coordinateExteriorFrame 0).app _ hfirst η) = _
  rw [one_mul] <;> rfl

theorem canonicalCoefficient_residueCocycle :
    canonicalCoefficient (canonicalFace residueCocycle) =
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
        ((coordinateElement 57 1 0)^3) * tripleCoefficient surfacePoleCoefficient := by
  rw [canonicalCoefficient_firstFrame, canonicalFace_firstFrame]

private theorem tripleCoefficient_homogeneous (n : ℕ)
    (p : MvPolynomial (Fin 5) ℂ)
    (hp : p.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n) :
    tripleCoefficient
        (coordinatePolynomialSection 57 1 1 surfaceTriple surfaceTriple_le_first p) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
        ((coordinateElement 57 1 0)^n) =
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
        (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) := by
  suffices ∀ (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 Finset.univ)
      (hfirst : O ≤ CycleQ2FullSurfaceResidueCover.coordinateOpen 0),
      sectionCoefficientAt 57 1 Finset.univ (by simp) O hO
          (coordinatePolynomialSection 57 1 1 O hfirst p) *
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
          ((coordinateElement 57 1 0)^n) =
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 Finset.univ)
          (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) from
    this surfaceTriple triple_eq_intersection surfaceTriple_le_first
  intro O hO hfirst
  subst O
  exact sectionCoefficient_homogeneous 57 1 (by simp) 0 (by simp) n p hp

private def faceDenominator : MvPolynomial (Fin 5) ℂ := X 1 * X 2 * X 3
private def faceNumerator : MvPolynomial (Fin 5) ℂ := X 0 ^ 2 * X 4 ^ 2

private theorem faceDenominator_homogeneous :
    faceDenominator.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 3 := by
  have hx (j : Fin 4) : (X j.castSucc : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 := by
    simpa only [CycleQ2GeometricSurfaceDehomogenizedCharts.weight_castSucc] using
      isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight j.castSucc
  exact ((hx 1).mul (hx 2)).mul (hx 3)

private theorem faceNumerator_homogeneous :
    faceNumerator.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight 6 := by
  have h0 : (X (0 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 1 :=
    isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 0
  have h4 : (X (4 : Fin 5) : MvPolynomial (Fin 5) ℂ).IsWeightedHomogeneous
      CycleQ2CartierSurfaceGrading.weight 2 :=
    isWeightedHomogeneous_X ℂ CycleQ2CartierSurfaceGrading.weight 4
  exact (h0.pow 2).mul (h4.pow 2)

private theorem partialDenominator_zero :
    CycleQ2HodgeTwistTorusChart.partialDenominator literalEval 0 =
      quotient literalEval faceDenominator := by
  rw [CycleQ2HodgeTwistTorusChart.partialDenominator,
    show Finset.univ.erase (0 : Fin 4) = {1,2,3} from by decide]
  simp [faceDenominator, CycleQ2GeometricHodgeThreefold.coord, map_mul, mul_assoc]

private theorem literalNumerator :
    literalQuadrics 0 * coord literalEval (Fin.last 4) ^ 2 =
      quotient literalEval faceNumerator := by
  simp [literalQuadrics, CycleQ2LiteralCubicResidueLift.quadric, faceNumerator,
    CycleQ2GeometricHodgeThreefold.coord, map_mul, map_pow]

private theorem nativeLifts_zero : nativeLifts 0 =
    CycleQ2HodgeTwistTorusChart.quadricLift literalEval literal_vertex_unit 0
      (literalQuadrics 0) (literalQuadrics_homogeneous 0) := by
  simp [nativeLifts, CycleQ2HodgeTwistTorusChart.quadricBoundaryLift]

/-- The literal 123 lift satisfies its exact numerator equation on the
whole 123 face. The omitted coordinate x₀ is not inverted. -/
theorem nativeFace_fraction :
    CycleQ2HodgeTwistRatios.normalized literalEval 1 (quotient literalEval faceDenominator)
        (quotient_mem_grade literalEval _ faceDenominator_homogeneous)
        nativeFaceZero nativeFaceZero_le_chart *
      chartFrame literalEval 3 1 nativeFaceZero nativeFaceZero_le_chart (nativeLifts 0) =
    CycleQ2HodgeTwistRatios.normalized literalEval 1 (quotient literalEval faceNumerator)
      (quotient_mem_grade literalEval _ faceNumerator_homogeneous)
      nativeFaceZero nativeFaceZero_le_chart := by
  have h := CycleQ2HodgeTwistTorusChart.quadricLift_fraction literalEval literal_vertex_unit
    0 1 (by decide) (literalQuadrics 0) (literalQuadrics_homogeneous 0)
  rw [partialDenominator_zero, literalNumerator] at h
  rw [nativeLifts_zero]
  exact h

theorem surfacePole_fraction :
    coordinatePolynomialSection 57 1 1 surfaceTriple surfaceTriple_le_first faceDenominator *
      surfacePoleCoefficient =
    coordinatePolynomialSection 57 1 1 surfaceTriple surfaceTriple_le_first faceNumerator := by
  have h := congrArg
    (surfaceToAmbient.appLE nativeFaceZero surfaceTriple surfaceTriple_le_nativeFace)
    nativeFace_fraction
  rw [map_mul,
    normalized_toSurface 1 3 faceDenominator faceDenominator_homogeneous
      nativeFaceZero nativeFaceZero_le_chart surfaceTriple surfaceTriple_le_first
      surfaceTriple_le_nativeFace,
    normalized_toSurface 1 6 faceNumerator faceNumerator_homogeneous
      nativeFaceZero nativeFaceZero_le_chart surfaceTriple surfaceTriple_le_first
      surfaceTriple_le_nativeFace] at h
  exact h

private theorem faceDenominator_toSurface :
    CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 faceDenominator =
      coordinateProduct 57 1 Finset.univ := by
  simp [faceDenominator, coordinateProduct, coordinateElement,
    CycleQ2SeedQuotientFiniteFree.remainingIndex, Fin.prod_univ_succ,
    CycleQ2GeometricSurfaceCoordinates.quotientMap,
    CycleQ2GeometricCartierNormalLift.surfaceQuotient, map_mul, mul_assoc]

/-- Clearing the three original denominator coordinates identifies the
actual quotient face with the original normalized canonical coefficient. -/
theorem canonicalCoefficient_residueFraction :
    canonicalCoefficient (canonicalFace residueCocycle) =
      CycleQ2LiteralCanonicalResidueGenerator.residueFraction := by
  let L := CoordinateLocal 57 1 Finset.univ
  let e : SurfaceRing 57 1 →+* L := algebraMap (SurfaceRing 57 1) L
  let x := e (coordinateElement 57 1 0)
  let d := e (coordinateProduct 57 1 Finset.univ)
  let r := tripleCoefficient surfacePoleCoefficient
  let p := tripleCoefficient
    (coordinatePolynomialSection 57 1 1 surfaceTriple surfaceTriple_le_first faceDenominator)
  let n := tripleCoefficient
    (coordinatePolynomialSection 57 1 1 surfaceTriple surfaceTriple_le_first faceNumerator)
  have hpr : p * r = n := by
    simpa only [map_mul] using congrArg tripleCoefficient surfacePole_fraction
  have hp : p * x^3 = d := by
    simpa only [map_pow, faceDenominator_toSurface] using
      tripleCoefficient_homogeneous 3 faceDenominator faceDenominator_homogeneous
  have hn : n * x^6 = e (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 faceNumerator) := by
    simpa only [map_pow] using
      tripleCoefficient_homogeneous 6 faceNumerator faceNumerator_homogeneous
  have hc : canonicalCoefficient (canonicalFace residueCocycle) * d =
      e (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 faceNumerator) := by
    rw [canonicalCoefficient_residueCocycle, map_pow]
    change (x^3 * r) * d = _
    calc
      (x^3 * r) * d = (p*r) * (x^3*x^3) := by rw [← hp]; ring
      _ = n * x^6 := by rw [hpr]; ring
      _ = _ := hn
  change canonicalCoefficient (canonicalFace residueCocycle) =
    CycleQ2GeometricCoordinateCharacter.polynomialFraction 57 1 faceNumerator
  apply (IsLocalization.Away.algebraMap_isUnit
    (S := CoordinateLocal 57 1 Finset.univ) (coordinateProduct 57 1 Finset.univ)).mul_right_cancel
  exact hc.trans (by simpa only [pow_one] using
    (CycleQ2GeometricCoordinateCharacter.polynomialFraction_spec 57 1 faceNumerator).symm)

/-- The actual 123 face is the original residue-one canonical section,
not merely another nonzero section of the same coefficient space. -/
theorem canonicalFace_residueGenerator : canonicalFace residueCocycle =
    CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator :=
  CycleQ2LiteralCanonicalResidueGenerator.eq_residueGenerator_of_coefficient _
    canonicalCoefficient_residueFraction

theorem residueClass_ne_zero : residueClass ≠ 0 :=
  quotientClass_ne_zero_of_residue residueCocycle residueCocycle_closed
    canonicalFace_residueGenerator

/-- The actual cubic boundary of the explicit quotient cocycle in the
fixed proper threefold's degree-three structure-twist cohomology. -/
def ambientResidueClass : RegularSheaf.H' 3 ⊤ := coefficientConnecting ⊤ residueClass

theorem ambientResidueClass_ne_zero : ambientResidueClass ≠ 0 :=
  coefficientConnecting_ne_zero residueClass residueClass_ne_zero

/-- The genuine cubic connecting image is the third injective-descent
class of the retained scalar coboundary. This makes no comparison of
sign conventions with the separate Mayer--Vietoris construction. -/
theorem ambientResidueClass_eq_cechThreeClass : ambientResidueClass =
    CycleQ2FourOpenTopCoefficientBoundary.cechThreeClass
      ambientCover ambientCover_top ambientTop :=
  CycleQ2FourOpenTopCoefficientBoundary.cechTwoClass_connecting
    ambientCover coefficientShortExact ambientCover_top liftedTwo ambientTop liftedTwo_boundary

/-- The original cubic connecting class has the negative of the native
three-Mayer--Vietoris normalization, with no undetermined scalar. -/
theorem ambientResidueClass_eq_neg_nativeTop : ambientResidueClass =
    -CycleQ2HodgeTwistTopDerived.nativeTopConnecting RegularSheaf
      ambientCover ambientCover_top
      (CycleQ2HodgeTwistTorusChart.twistTopGenerator literalEval literal_vertex_unit) :=
  CycleQ2HodgeTwistTopDerived.coefficient_connecting_nativeTop ambientCover
    coefficientShortExact ambientCover_top liftedTwo
    (CycleQ2HodgeTwistTorusChart.twistTopGenerator literalEval literal_vertex_unit)
    liftedTwo_boundary

/-- The ambient coefficient trace is the actual native top-cohomology
trace for the degree-zero line bundle. -/
def ambientResidueTrace : RegularSheaf.H' 3 ⊤ ≃+ ℂ :=
  CycleQ2HodgeTwistTopDerived.derivedTopTraceEquiv RegularSheaf ambientCover
    (CycleQ2HodgeTwistTorusChart.nativeLaurentSections literalEval literal_vertex_unit 0)
    ambientCover_top
    (CycleQ2HodgeTwistTopCohomology.twist_face_acyclic literalEval 0)

theorem ambientResidueTrace_class : ambientResidueTrace ambientResidueClass = -1 := by
  rw [ambientResidueClass_eq_neg_nativeTop, map_neg]
  change -(CycleQ2HodgeTwistTopDerived.derivedTopTraceEquiv RegularSheaf ambientCover
    (CycleQ2HodgeTwistTorusChart.nativeLaurentSections literalEval literal_vertex_unit 0)
    ambientCover_top (CycleQ2HodgeTwistTopCohomology.twist_face_acyclic literalEval 0)
    (CycleQ2HodgeTwistTopDerived.nativeTopConnecting RegularSheaf ambientCover ambientCover_top
      (CycleQ2HodgeTwistTorusChart.twistTopGenerator literalEval literal_vertex_unit))) = -1
  rw [CycleQ2HodgeTwistTopDerived.derivedTopTrace_connecting,
    CycleQ2HodgeTwistTorusChart.twistTopSectionTrace_generator]

/-- The explicit quotient cocycle restricts to the unchanged normalized
canonical residue class on the original surface. -/
theorem surfaceRestriction_residueClass : surfaceRestriction residueClass =
    CycleQ2CanonicalCoordinateH2.canonicalConnecting
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator := by
  rw [residueClass, surfaceRestriction_cechTwoClass, canonicalFace_residueGenerator]

/-- The original surface generator has exactly the cubic connecting
image computed by the retained four-face lift. -/
theorem surfaceGysin_residueGenerator : surfaceGysin
    (CycleQ2CanonicalCoordinateH2.canonicalConnecting
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator) =
      ambientResidueClass := by
  rw [← surfaceRestriction_residueClass, surfaceGysin_surfaceRestriction]
  rfl

theorem ambientResidueTrace_surfaceGysin_residueGenerator : ambientResidueTrace
    (surfaceGysin (CycleQ2CanonicalCoordinateH2.canonicalConnecting
      CycleQ2LiteralCanonicalResidueGenerator.canonicalResidueGenerator)) = -1 := by
  rw [surfaceGysin_residueGenerator, ambientResidueTrace_class]

end CycleQ2LiteralCubicProjectiveCocycle
end

#print axioms CycleQ2LiteralCubicProjectiveCocycle.canonicalFace_firstFrame
#print axioms CycleQ2LiteralCubicProjectiveCocycle.canonicalCoefficient_residueCocycle
#print axioms CycleQ2LiteralCubicProjectiveCocycle.nativeFace_fraction
#print axioms CycleQ2LiteralCubicProjectiveCocycle.canonicalFace_residueGenerator
#print axioms CycleQ2LiteralCubicProjectiveCocycle.residueClass_ne_zero
#print axioms CycleQ2LiteralCubicProjectiveCocycle.ambientResidueClass_ne_zero
#print axioms CycleQ2LiteralCubicProjectiveCocycle.ambientResidueClass_eq_cechThreeClass
#print axioms CycleQ2LiteralCubicProjectiveCocycle.ambientResidueClass_eq_neg_nativeTop
#print axioms CycleQ2LiteralCubicProjectiveCocycle.ambientResidueTrace_class
#print axioms CycleQ2LiteralCubicProjectiveCocycle.surfaceGysin_residueGenerator
#print axioms CycleQ2LiteralCubicProjectiveCocycle.ambientResidueTrace_surfaceGysin_residueGenerator

/-!
## The original marked surface class uses this same residue face

The existing marked moving-curve computation lands in canonical H² of
the original surface. Its normalized trace determines its multiple of
the residue-one generator. The literal face identification above binds
that statement to the explicit coefficient cocycle, without introducing
an ambient Gysin map or choosing an inverse to an unrelated homomorphism.
-/

noncomputable section
namespace CycleQ2LiteralCubicProjectiveCocycle

open CategoryTheory TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralCubicResidueDetection CycleQ2CanonicalCoordinateH2
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralMovingDivisorChern
  CycleQ2CanonicalCubicDiagram CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralCotangentTrace
  CycleQ2LiteralMovingCurveDifferentialNonzero

local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- The exact retained cubic paired with the actual moving Chern class
is its known marked curve trace times the original quotient residue face. -/
theorem marked_cubic_eq_trace_smul_residueFace
    (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    cubicH2 firstOrderWeightedCubic
        ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl) =
      differentialTrace t ht (curveClass t) •
        canonicalConnecting (canonicalFace residueCocycle) := by
  rw [canonicalFace_residueGenerator, differentialTrace_curveClass]
  exact eq_trace_smul_generator _

/-- The marked canonical surface class survives the original closed
inclusion and the actual canonical residue boundary on the threefold. -/
theorem marked_surfaceGysin_ne_zero
    (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin
      (cubicH2 firstOrderWeightedCubic
        ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) ≠ 0 := by
  apply CycleQ2LiteralCubicCanonicalRestriction.surfaceGysin_ne_zero
  intro hz
  apply CycleQ2LiteralMovingChernTrace.movingClass_cubic_trace_ne_zero t ht
  rw [hz, map_zero]

end CycleQ2LiteralCubicProjectiveCocycle
end

#print axioms CycleQ2LiteralCubicProjectiveCocycle.marked_cubic_eq_trace_smul_residueFace
#print axioms CycleQ2LiteralCubicProjectiveCocycle.marked_surfaceGysin_ne_zero
