import Proposal.GeometricLiteralThreefoldResidueGluing
import Proposal.GeometricLiteralAbelJacobiRelativeNormal
import Proposal.GeometricLiteralCanonicalResidueGenerator
import Proposal.GeometricHodgeThreefoldLiteral

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
