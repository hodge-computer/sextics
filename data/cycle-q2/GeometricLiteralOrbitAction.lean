import Proposal.GeometricLiteralCotangentEpsilon
import Proposal.GeometricIncidenceFamilyContainment

/-!
# The cyclic action on the literal projective deformation

The cyclic coordinate action of the original seed scales the ambient
test polynomial by a cube root of unity. Scaling epsilon by its square
fixes the deformed equation. The resulting graded maps on the original
deformation and closed fibre commute with reduction.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitAction

open CategoryTheory AlgebraicGeometry MvPolynomial
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2CartierProjectiveCover
  CycleQ2SeedCyclicAction CycleQ2LiteralCyclicDeformation
  CycleQ2GeometricSeedNormalizedCoordinates
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedDeformationEquiv
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation

private def diagonal {ι : Type} (e : ι → ℕ) (z : ℂ) :
    MvPolynomial ι ℂ →ₐ[ℂ] MvPolynomial ι ℂ :=
  aeval (fun i => C (z ^ e i) * X i)

private theorem diagonal_X {ι : Type} (e : ι → ℕ) (z : ℂ) (i : ι) :
    diagonal e z (X i) = C (z ^ e i) * X i := aeval_X _ _

private theorem diagonal_C {ι : Type} (e : ι → ℕ) (z c : ℂ) :
    diagonal e z (C c) = C c := aeval_C _ _

private theorem diagonal_comp {ι : Type} (e : ι → ℕ) (z w : ℂ) :
    (diagonal e z).comp (diagonal e w) = diagonal e (z * w) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, diagonal_X, map_mul, diagonal_C, mul_pow]
  ring

private theorem diagonal_cube {ι : Type} (e : ι → ℕ) (z : ℂ) (hz : z^3 = 1)
    (p : MvPolynomial ι ℂ) : diagonal e z (diagonal e z (diagonal e z p)) = p := by
  let f := diagonal e z
  have he : f.comp (f.comp f) = AlgHom.id ℂ (MvPolynomial ι ℂ) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [f, AlgHom.comp_apply, diagonal_X, map_mul, diagonal_C, AlgHom.id_apply]
    have h : (C (z ^ e i) : MvPolynomial ι ℂ)^3 = 1 := by
      rw [← map_pow, ← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow, map_one]
    linear_combination X i * h
  exact AlgHom.congr_fun he p

private theorem diagonal_homogeneous {ι : Type} (w e : ι → ℕ) (z : ℂ)
    {p : MvPolynomial ι ℂ} {n : ℕ} (hp : p.IsWeightedHomogeneous w n) :
    (diagonal e z p).IsWeightedHomogeneous w n := by
  let := MvPolynomial.weightedGradedAlgebra ℂ w
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using isWeightedHomogeneous_zero ℂ w n
  | add p q hp hq ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [diagonal, aeval_monomial]
    have hx (i : ι) : C (z ^ e i) * X i ∈ weightedHomogeneousSubmodule ℂ w (w i) := by
      change (C (z ^ e i) * X i).IsWeightedHomogeneous w (w i)
      simpa only [zero_add] using (isWeightedHomogeneous_C w (z ^ e i)).mul (isWeightedHomogeneous_X ℂ w i)
    have hm : d.prod (fun i k => (C (z ^ e i) * X i) ^ k) ∈ weightedHomogeneousSubmodule ℂ w n := by
      rw [← hd]
      exact SetLike.prod_mem_graded (weightedHomogeneousSubmodule ℂ w)
        (fun i => d i • w i) (fun i => (C (z ^ e i) * X i) ^ d i)
        (fun i _ => SetLike.pow_mem_graded (d i) (hx i))
    simpa only [MvPolynomial.algebraMap_eq, zero_add] using (isWeightedHomogeneous_C w c).mul hm

private def coordinateExponent : Fin 5 → ℕ := ![2,2,1,0,0]

private theorem diagonal_eq_original (z : ℂ) :
    diagonal coordinateExponent z = polynomialAction z := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [diagonal_X, polynomialAction_X]
  fin_cases i <;> simp [coordinateExponent, actionValues]

theorem polynomialAction_weighted (z : ℂ) {n : ℕ} {p : WeightedPoly}
    (hp : p.IsWeightedHomogeneous weight n) :
    (polynomialAction z p).IsWeightedHomogeneous weight n := by
  rw [← diagonal_eq_original]
  exact diagonal_homogeneous weight coordinateExponent z hp

private def thickExponent : Option (Fin 5) → ℕ := Option.elim' 2 coordinateExponent

private theorem diagonal_include (z : ℂ) (p : WeightedPoly) :
    diagonal thickExponent z (includePolynomial p) = includePolynomial (polynomialAction z p) := by
  have h : (diagonal thickExponent z).comp includePolynomial =
      includePolynomial.comp (diagonal coordinateExponent z) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [includePolynomial, diagonal_X, thickExponent]
  rw [← diagonal_eq_original]
  exact AlgHom.congr_fun h p

private theorem cubic_fixed (z : ℂ) (hz : z^3 = 1) :
    polynomialAction z (thetaH 1) = thetaH 1 := by
  rw [← normalizedCubic_eq_thetaH_one (r := (57 : ℂ))]
  exact polynomialAction_cubic z hz

private theorem sextic_fixed (z : ℂ) (hz : z^3 = 1) :
    polynomialAction z (actualSeedEquation 57 1) = actualSeedEquation 57 1 := by
  rw [← normalizedSextic_eq_actualSeedEquation]
  exact polynomialAction_equation z hz

private theorem ambient_preserves (z : ℂ) (hz : z^3 = 1) :
    ambientIdeal ≤ ambientIdeal.comap (diagonal thickExponent z).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change diagonal thickExponent z (relations i) ∈ ambientIdeal
  have hr (j : Fin 3) : relations j ∈ ambientIdeal := Ideal.subset_span ⟨j,rfl⟩
  have he : diagonal thickExponent z epsilonPolynomial = C (z ^ 2) * epsilonPolynomial := diagonal_X _ _ _
  fin_cases i
  · change diagonal thickExponent z (includePolynomial (thetaH 1)) ∈ _
    rw [diagonal_include, cubic_fixed z hz]
    exact hr 0
  · change diagonal thickExponent z (includePolynomial (actualSeedEquation 57 1) -
      epsilonPolynomial * includePolynomial derivativeA) ∈ _
    rw [map_sub, map_mul, he, diagonal_include, diagonal_include, sextic_fixed z hz,
      polynomialAction_perturbation, map_mul]
    have hC : includePolynomial (C z) = C z := rename_C _ _
    rw [hC]
    have hc : (C (z ^ 2) : AmbientPoly) * C z = 1 := by
      rw [← map_mul, ← pow_succ, hz, map_one]
    convert hr 1 using 1
    change _ = includePolynomial (actualSeedEquation 57 1) - epsilonPolynomial * includePolynomial derivativeA
    linear_combination -(epsilonPolynomial * includePolynomial derivativeA) * hc
  · change diagonal thickExponent z (epsilonPolynomial ^ 2) ∈ _
    rw [map_pow, he, mul_pow]
    exact Ideal.mul_mem_left ambientIdeal _ (hr 2)

private theorem closed_preserves (z : ℂ) (hz : z^3 = 1) :
    surfaceIdeal 57 1 ≤ (surfaceIdeal 57 1).comap (polynomialAction z).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  change polynomialAction z (surfaceEquations 57 1 i) ∈ surfaceIdeal 57 1
  have hr (j : Fin 2) : surfaceEquations 57 1 j ∈ surfaceIdeal 57 1 := Ideal.subset_span ⟨j,rfl⟩
  fin_cases i
  · change polynomialAction z (actualSeedEquation 57 1) ∈ _
    rw [sextic_fixed z hz]
    exact hr 0
  · change polynomialAction z (thetaH 1) ∈ _
    rw [cubic_fixed z hz]
    exact hr 1

def thickAction (z : ℂ) (hz : z^3 = 1) : GradedDeformation →ₐ[ℂ] GradedDeformation :=
  Ideal.quotientMapₐ ambientIdeal (diagonal thickExponent z) (ambient_preserves z hz)

def surfaceAction (z : ℂ) (hz : z^3 = 1) : SurfaceRing 57 1 →ₐ[ℂ] SurfaceRing 57 1 :=
  Ideal.quotientMapₐ (surfaceIdeal 57 1) (polynomialAction z) (closed_preserves z hz)

theorem thickAction_polynomial (z : ℂ) (hz : z^3 = 1) (p : WeightedPoly) :
    thickAction z hz (polynomialInGraded p) = polynomialInGraded (polynomialAction z p) :=
  congrArg quotientMap (diagonal_include z p)

theorem thickAction_epsilon (z : ℂ) (hz : z^3 = 1) :
    thickAction z hz epsilonElement = algebraMap ℂ GradedDeformation (z ^ 2) * epsilonElement := by
  change quotientMap (diagonal thickExponent z (X none)) = _
  rw [diagonal_X, map_mul]
  rfl

theorem surfaceAction_polynomial (z : ℂ) (hz : z^3 = 1) (p : WeightedPoly) :
    surfaceAction z hz (surfaceQuotient 57 1 p) = surfaceQuotient 57 1 (polynomialAction z p) := rfl

def thickGradedAction (z : ℂ) (hz : z^3 = 1) : deformationGrade →+*ᵍ deformationGrade where
  toRingHom := (thickAction z hz).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact quotientMap_mem_grade (diagonal_homogeneous ambientWeight thickExponent z hp)

def surfaceGradedAction (z : ℂ) (hz : z^3 = 1) : surfaceGrade 57 1 →+*ᵍ surfaceGrade 57 1 where
  toRingHom := (surfaceAction z hz).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    refine ⟨polynomialAction z p, ?_, rfl⟩
    exact polynomialAction_weighted z hp

theorem thickAction_cube (z : ℂ) (hz : z ^ 3 = 1) (x : GradedDeformation) :
    thickGradedAction z hz (thickGradedAction z hz (thickGradedAction z hz x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg quotientMap (diagonal_cube thickExponent z hz p)

theorem surfaceAction_cube (z : ℂ) (hz : z ^ 3 = 1) (x : SurfaceRing 57 1) :
    surfaceGradedAction z hz (surfaceGradedAction z hz (surfaceGradedAction z hz x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change surfaceQuotient 57 1 (polynomialAction z (polynomialAction z (polynomialAction z p))) = _
  rw [← diagonal_eq_original, diagonal_cube _ z hz]
  rfl

private theorem rawReduction_diagonal (z : ℂ) (hz : z^3 = 1) :
    rawReduction.comp (diagonal thickExponent z) = (surfaceAction z hz).comp rawReduction := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | none =>
    change rawReduction (diagonal thickExponent z epsilonPolynomial) = surfaceAction z hz (rawReduction epsilonPolynomial)
    rw [show diagonal thickExponent z epsilonPolynomial = C (z ^ 2) * epsilonPolynomial from diagonal_X _ _ _,
      map_mul, rawReduction_epsilon, mul_zero, map_zero]
  | some i =>
    have hx : (X (some i) : AmbientPoly) = includePolynomial (X i) := (rename_X _ _).symm
    simp only [AlgHom.comp_apply, hx, diagonal_include, rawReduction_include, surfaceAction_polynomial]

theorem reduction_equivariant (z : ℂ) (hz : z^3 = 1) :
    reductionGraded.comp (thickGradedAction z hz) = (surfaceGradedAction z hz).comp reductionGraded := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun (rawReduction_diagonal z hz) p

section Projective
universe u
variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ 𝒜) (hf : ∀ x : A, f (f (f x)) = x)

include hf in
theorem cyclic_irrelevant_le_map :
    HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f := by
  apply _root_.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le 𝒜).mpr
  intro n hn x hx
  have hy := HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn (f.map_mem (f.map_mem hx))
  exact hf x ▸ Ideal.mem_map_of_mem f hy

def cyclicProjMap : Proj 𝒜 ⟶ Proj 𝒜 :=
  Proj.map f (cyclic_irrelevant_le_map f hf)

theorem cyclicProjMap_cube :
    cyclicProjMap f hf ≫ cyclicProjMap f hf ≫ cyclicProjMap f hf = 𝟙 _ := by
  have he : f.comp (f.comp f) = GradedRingHom.id 𝒜 := by
    apply GradedRingHom.ext
    exact hf
  unfold cyclicProjMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [he, Proj.map_id]

def cyclicProjIso : Proj 𝒜 ≅ Proj 𝒜 where
  hom := cyclicProjMap f hf
  inv := cyclicProjMap f hf ≫ cyclicProjMap f hf
  hom_inv_id := cyclicProjMap_cube f hf
  inv_hom_id := by rw [Category.assoc, cyclicProjMap_cube]

theorem cyclicProjMap_naturality (g : ℬ →+*ᵍ ℬ) (hg : ∀ y : B, g (g (g y)) = y)
    (h : 𝒜 →+*ᵍ ℬ) (hh : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map h)
    (comm : ∀ x : A, g (h x) = h (f x)) :
    Proj.map h hh ≫ cyclicProjMap f hf = cyclicProjMap g hg ≫ Proj.map h hh := by
  have he : g.comp h = h.comp f := by
    apply GradedRingHom.ext
    exact comm
  unfold cyclicProjMap
  rw [← Proj.map_comp, ← Proj.map_comp]
  simp only [he]

end Projective

def projectiveAction (z : ℂ) (hz : z^3 = 1) :
    projectiveDeformation ≅ projectiveDeformation :=
  cyclicProjIso (thickGradedAction z hz) (thickAction_cube z hz)

def closedProjectiveAction (z : ℂ) (hz : z^3 = 1) :
    projectiveSurface 57 1 ≅ projectiveSurface 57 1 :=
  cyclicProjIso (surfaceGradedAction z hz) (surfaceAction_cube z hz)

theorem cubeRoot_mul {z w : ℂ} (hz : z^3 = 1) (hw : w^3 = 1) : (z*w)^3 = 1 := by
  rw [mul_pow, hz, hw, mul_one]

theorem thickGradedAction_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (thickGradedAction z hz).comp (thickGradedAction w hw) =
      thickGradedAction (z*w) (cubeRoot_mul hz hw) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg quotientMap (AlgHom.congr_fun (diagonal_comp thickExponent z w) p)

theorem surfaceGradedAction_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (surfaceGradedAction z hz).comp (surfaceGradedAction w hw) =
      surfaceGradedAction (z*w) (cubeRoot_mul hz hw) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  change surfaceQuotient 57 1 (polynomialAction z (polynomialAction w p)) =
    surfaceQuotient 57 1 (polynomialAction (z*w) p)
  simp only [← diagonal_eq_original]
  exact congrArg (surfaceQuotient 57 1) (AlgHom.congr_fun (diagonal_comp coordinateExponent z w) p)

theorem projectiveAction_hom_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (projectiveAction z hz).hom ≫ (projectiveAction w hw).hom =
      (projectiveAction (z*w) (cubeRoot_mul hz hw)).hom := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  simp only [thickGradedAction_comp]

theorem closedProjectiveAction_hom_comp (z w : ℂ) (hz : z^3 = 1) (hw : w^3 = 1) :
    (closedProjectiveAction z hz).hom ≫ (closedProjectiveAction w hw).hom =
      (closedProjectiveAction (z*w) (cubeRoot_mul hz hw)).hom := by
  change Proj.map _ _ ≫ Proj.map _ _ = Proj.map _ _
  rw [← Proj.map_comp]
  simp only [surfaceGradedAction_comp]

theorem closedProjectiveAction_hom_one : (closedProjectiveAction 1 (one_pow 3)).hom = 𝟙 _ := by
  apply (cancel_epi (closedProjectiveAction 1 (one_pow 3)).hom).mp
  simpa only [mul_one, Category.comp_id] using
    closedProjectiveAction_hom_comp 1 1 (one_pow 3) (one_pow 3)

theorem projectiveAction_hom_one : (projectiveAction 1 (one_pow 3)).hom = 𝟙 _ := by
  apply (cancel_epi (projectiveAction 1 (one_pow 3)).hom).mp
  simpa only [mul_one, Category.comp_id] using
    projectiveAction_hom_comp 1 1 (one_pow 3) (one_pow 3)

theorem closedFiber_equivariant (z : ℂ) (hz : z^3 = 1) :
    closedFiber ≫ (projectiveAction z hz).hom = (closedProjectiveAction z hz).hom ≫ closedFiber :=
  cyclicProjMap_naturality (thickGradedAction z hz) (thickAction_cube z hz)
    (surfaceGradedAction z hz) (surfaceAction_cube z hz) reductionGraded reduction_irrelevant_le
    (fun x => (DFunLike.congr_fun (reduction_equivariant z hz) x).symm)


open CycleQ2GeometricSurfaceCoefficients CycleQ2LiteralProjectiveComplexSplittings
  CycleQ2LiteralProjectiveDualFamily
open scoped DualNumber

theorem thickAction_overComplex (z : ℂ) (hz : z^3 = 1) :
    (projectiveAction z hz).hom ≫ deformationToComplex = deformationToComplex := by
  apply CycleQ2IncidenceFamilyContainment.projectiveMap_coefficientBase
    (thickGradedAction z hz) (cyclic_irrelevant_le_map _ (thickAction_cube z hz))
  ext c
  exact (thickAction z hz).commutes c

theorem surfaceAction_overComplex (z : ℂ) (hz : z^3 = 1) :
    (closedProjectiveAction z hz).hom ≫ projectiveToComplex 57 1 = projectiveToComplex 57 1 := by
  apply CycleQ2IncidenceFamilyContainment.projectiveMap_coefficientBase
    (surfaceGradedAction z hz) (cyclic_irrelevant_le_map _ (surfaceAction_cube z hz))
  ext c
  exact (surfaceAction z hz).commutes c

def dualAction (z : ℂ) : ℂ[ε] →+* ℂ[ε] :=
  CycleQ2GeometricSurfaceFirstOrder.dualMapScaled (RingHom.id ℂ) (z ^ 2)

theorem dualAction_epsilon (z : ℂ) : dualAction z ε = algebraMap ℂ ℂ[ε] (z^2) * ε := by
  apply TrivSqZeroExt.ext
  · change (0 : ℂ) = z^2 * 0
    rw [mul_zero]
  · change z^2 * 1 = z^2 * 1 + 0 * 0
    rw [zero_mul, add_zero]

private theorem dualCoefficient_action (z : ℂ) (hz : z^3 = 1) :
    (thickGradedAction z hz).gradedZeroRingHom.comp dualCoefficient.toRingHom =
      dualCoefficient.toRingHom.comp (dualAction z) := by
  let φ := (thickGradedAction z hz).gradedZeroRingHom
  have hc (c : ℂ) : φ (algebraMap ℂ (deformationGrade 0) c) =
      algebraMap ℂ (deformationGrade 0) c := by
    apply Subtype.ext
    exact (thickAction z hz).commutes c
  have he : φ zeroEpsilon = algebraMap ℂ (deformationGrade 0) (z^2) * zeroEpsilon := by
    apply Subtype.ext
    exact thickAction_epsilon z hz
  apply RingHom.ext
  intro b
  change φ (dualCoefficient b) = dualCoefficient (dualAction z b)
  rw [dualCoefficient_apply, dualCoefficient_apply, map_add, map_mul, he, hc, hc]
  change _ = algebraMap ℂ (deformationGrade 0) b.fst +
    zeroEpsilon * algebraMap ℂ (deformationGrade 0) (z^2 * b.snd)
  rw [map_mul]
  ring

theorem projectiveAction_overDual (z : ℂ) (hz : z^3 = 1) :
    (projectiveAction z hz).hom ≫ firstOrderStructure =
      firstOrderStructure ≫ Spec.map (CommRingCat.ofHom (dualAction z)) := by
  change Proj.map (thickGradedAction z hz) _ ≫
      (Proj.toSpecZero deformationGrade ≫ Spec.map (CommRingCat.ofHom dualCoefficient.toRingHom)) = _
  rw [← Category.assoc, CycleQ2IncidenceFamilyContainment.projectiveMap_toSpecZero, Category.assoc,
    ← Spec.map_comp]
  unfold firstOrderStructure
  rw [Category.assoc, ← Spec.map_comp]
  change Proj.toSpecZero deformationGrade ≫ Spec.map (CommRingCat.ofHom
      ((thickGradedAction z hz).gradedZeroRingHom.comp dualCoefficient.toRingHom)) =
    Proj.toSpecZero deformationGrade ≫ Spec.map (CommRingCat.ofHom
      (dualCoefficient.toRingHom.comp (dualAction z)))
  rw [dualCoefficient_action]

open scoped DualNumber
open CategoryTheory AlgebraicGeometry CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveDualFamily CycleQ2LiteralProjectiveCotangent CycleQ2LiteralCotangentEpsilon

theorem globalDualCoefficient_constant (c : ℂ) :
    globalDualCoefficient (algebraMap ℂ ℂ[ε] c) = totalGlobalCoefficient c := by
  have h := congrArg (fun f : projectiveDeformation ⟶ Spec (CommRingCat.of ℂ) =>
    f.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv c)) firstOrderStructure_overComplex
  have hn := ConcreteCategory.congr_hom (C := CommRingCat)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap ℂ ℂ[ε]))) c
  exact (congrArg (fun x => firstOrderStructure.appTop x) hn).trans h

theorem globalEpsilonAction (f : projectiveDeformation ⟶ projectiveDeformation)
    (r : ℂ[ε] →+* ℂ[ε])
    (h : f ≫ firstOrderStructure = firstOrderStructure ≫ Spec.map (CommRingCat.ofHom r))
    (c : ℂ) (hr : r ε = algebraMap ℂ ℂ[ε] c * ε) :
    f.appTop totalEpsilon = totalGlobalCoefficient c * totalEpsilon := by
  have he := congrArg (fun g : projectiveDeformation ⟶ Spec (CommRingCat.of ℂ[ε]) =>
    g.appTop ((Scheme.ΓSpecIso (CommRingCat.of ℂ[ε])).inv ε)) h
  have hn := ConcreteCategory.congr_hom (C := CommRingCat)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom r)).symm (ε : ℂ[ε])
  have hp : f.appTop totalEpsilon = globalDualCoefficient (r ε) :=
    he.trans (congrArg (fun x => firstOrderStructure.appTop x) hn)
  rw [hp, hr, map_mul, globalDualCoefficient_constant]
  rfl

theorem projectiveAction_epsilon (z : ℂ) (hz : z^3 = 1) :
    (projectiveAction z hz).hom.appTop totalEpsilon = totalGlobalCoefficient (z^2) * totalEpsilon :=
  globalEpsilonAction _ _ (projectiveAction_overDual z hz) _ (dualAction_epsilon z)

end CycleQ2LiteralOrbitAction
end

#print axioms CycleQ2LiteralOrbitAction.thickAction_cube
#print axioms CycleQ2LiteralOrbitAction.surfaceAction_cube
#print axioms CycleQ2LiteralOrbitAction.reduction_equivariant

#print axioms CycleQ2LiteralOrbitAction.closedProjectiveAction_hom_comp
#print axioms CycleQ2LiteralOrbitAction.projectiveAction_hom_comp
#print axioms CycleQ2LiteralOrbitAction.closedFiber_equivariant

#print axioms CycleQ2LiteralOrbitAction.projectiveAction_overDual

#print axioms CycleQ2LiteralOrbitAction.projectiveAction_epsilon
