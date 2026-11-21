import Proposal.GeometricResidueFrames
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Actual transport between the two affine curve charts

The two rings are the literal affine chart quotients from
`GeometricAffineCurveCharts`, each localized at its middle coordinate.
The substitutions `(a,b,c) ↦ (a/b,1/b,c/b)` and its inverse are proved
to descend to these quotients and localizations. Their mutually inverse
algebra homomorphisms retain both parameters without specialization.

The differential comparison is induced by the universal Kähler derivation
of these actual rings. This is a local comparison; global sheaf gluing,
the canonical-sheaf identification, and the geometric trace remain separate.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricAffineOverlap

open MvPolynomial CycleQ2GeometricAffineCurveCharts
open CycleQ2GeometricAdjunctionOverlap CycleQ2GeometricResidueFrames

def chartMap (v : Fin 2 → AffinePoly) : AffinePoly →ₐ[ℂ] ChartRing v :=
  Ideal.Quotient.mkₐ ℂ (chartIdeal v)

def middle (v : Fin 2 → AffinePoly) : ChartRing v := chartMap v (X 1)

abbrev CoordinateOverlap (v : Fin 2 → AffinePoly) := Localization.Away (middle v)

def polynomialMap (v : Fin 2 → AffinePoly) : AffinePoly →ₐ[ℂ] CoordinateOverlap v :=
  (IsScalarTower.toAlgHom ℂ (ChartRing v) (CoordinateOverlap v)).comp (chartMap v)

def coordinate (v : Fin 2 → AffinePoly) (j : Fin 3) : CoordinateOverlap v :=
  polynomialMap v (X j)

def middleUnit (v : Fin 2 → AffinePoly) : (CoordinateOverlap v)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (middle v)).unit

@[simp] theorem middleUnit_val (v : Fin 2 → AffinePoly) :
    (middleUnit v : CoordinateOverlap v) = coordinate v 1 :=
  (IsLocalization.Away.algebraMap_isUnit (middle v)).unit_spec

def inverse (v : Fin 2 → AffinePoly) : CoordinateOverlap v := ↑((middleUnit v)⁻¹)

@[simp] theorem coordinate_mul_inverse (v : Fin 2 → AffinePoly) :
    coordinate v 1 * inverse v = 1 := by
  rw [← middleUnit_val]
  exact (middleUnit v).mul_inv

@[simp] theorem inverse_mul_coordinate (v : Fin 2 → AffinePoly) :
    inverse v * coordinate v 1 = 1 := by
  rw [mul_comm]
  exact coordinate_mul_inverse v

theorem polynomialMap_relation (v : Fin 2 → AffinePoly) (i : Fin 2) :
    polynomialMap v (v i) = 0 := by
  have h : chartMap v (v i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  change algebraMap (ChartRing v) (CoordinateOverlap v) (chartMap v (v i)) = 0
  rw [h, map_zero]

/-- Maps out of the actual localization are fixed by its three coordinates. -/
theorem coordinate_algHom_ext (v : Fin 2 → AffinePoly)
    {S : Type*} [CommSemiring S] [Algebra ℂ S]
    {f g : CoordinateOverlap v →ₐ[ℂ] S}
    (h : ∀ j, f (coordinate v j) = g (coordinate v j)) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middle v))
  apply Ideal.Quotient.algHom_ext ℂ
  apply MvPolynomial.algHom_ext
  exact h

abbrev firstEquations (r θ : ℂ) : Fin 2 → AffinePoly := ![firstQuadric r, firstCubic θ]
abbrev secondEquations (r θ : ℂ) : Fin 2 → AffinePoly := ![secondQuadric r, secondCubic θ]
abbrev FirstOverlap (r θ : ℂ) := CoordinateOverlap (firstEquations r θ)
abbrev SecondOverlap (r θ : ℂ) := CoordinateOverlap (secondEquations r θ)

section EvaluationFormulas
variable {S : Type*} [CommRing S] [Algebra ℂ S] (f : AffinePoly →ₐ[ℂ] S)

theorem map_firstQuadric (r : ℂ) :
    f (firstQuadric r) = quadricOne (algebraMap ℂ S r) (f (X 0)) (f (X 1)) (f (X 2)) := by
  simp [firstQuadric, quadricOne]

theorem map_firstCubic (θ : ℂ) :
    f (firstCubic θ) = cubicOne (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
      (f (X 0)) (f (X 1)) (f (X 2)) := by
  simp [firstCubic, cubicOne]

theorem map_secondQuadric (r : ℂ) :
    f (secondQuadric r) = quadricTwo (algebraMap ℂ S r) (f (X 0)) (f (X 1)) (f (X 2)) := by
  simp [secondQuadric, quadricTwo]

theorem map_secondCubic (θ : ℂ) :
    f (secondCubic θ) = cubicTwo (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
      (f (X 0)) (f (X 1)) (f (X 2)) := by
  simp [secondCubic, cubicTwo]

end EvaluationFormulas

theorem first_quadric_zero (r θ : ℂ) :
    quadricOne (algebraMap ℂ (FirstOverlap r θ) r)
      (coordinate (firstEquations r θ) 0) (coordinate (firstEquations r θ) 1)
      (coordinate (firstEquations r θ) 2) = 0 := by
  have h := polynomialMap_relation (firstEquations r θ) 0
  change polynomialMap (firstEquations r θ) (firstQuadric r) = 0 at h
  rw [map_firstQuadric] at h
  exact h

theorem first_cubic_zero (r θ : ℂ) :
    cubicOne (algebraMap ℂ (FirstOverlap r θ) Complex.I)
      (algebraMap ℂ (FirstOverlap r θ) θ)
      (coordinate (firstEquations r θ) 0) (coordinate (firstEquations r θ) 1)
      (coordinate (firstEquations r θ) 2) = 0 := by
  have h := polynomialMap_relation (firstEquations r θ) 1
  change polynomialMap (firstEquations r θ) (firstCubic θ) = 0 at h
  rw [map_firstCubic] at h
  exact h

theorem second_quadric_zero (r θ : ℂ) :
    quadricTwo (algebraMap ℂ (SecondOverlap r θ) r)
      (coordinate (secondEquations r θ) 0) (coordinate (secondEquations r θ) 1)
      (coordinate (secondEquations r θ) 2) = 0 := by
  have h := polynomialMap_relation (secondEquations r θ) 0
  change polynomialMap (secondEquations r θ) (secondQuadric r) = 0 at h
  rw [map_secondQuadric] at h
  exact h

theorem second_cubic_zero (r θ : ℂ) :
    cubicTwo (algebraMap ℂ (SecondOverlap r θ) Complex.I)
      (algebraMap ℂ (SecondOverlap r θ) θ)
      (coordinate (secondEquations r θ) 0) (coordinate (secondEquations r θ) 1)
      (coordinate (secondEquations r θ) 2) = 0 := by
  have h := polynomialMap_relation (secondEquations r θ) 1
  change polynomialMap (secondEquations r θ) (secondCubic θ) = 0 at h
  rw [map_secondCubic] at h
  exact h

section ReverseScaling
variable {R : Type*} [CommRing R]

theorem quadratic_reverse_scaling (r a b c t : R) (ht : b * t = 1) :
    quadricOne r (a * t) t (c * t) = t ^ 2 * quadricTwo r a b c := by
  dsimp [quadricOne, quadricTwo]
  linear_combination r * c * t * ht

theorem cubic_reverse_scaling (i θ a b c t : R) (ht : b * t = 1) :
    cubicOne i θ (a * t) t (c * t) = t ^ 3 * cubicTwo i θ a b c := by
  dsimp [cubicOne, cubicTwo]
  linear_combination
    (i * ((b * t) ^ 2 + b * t + 1) - c * t ^ 2 - a * t * (b * t + 1)) * ht

end ReverseScaling

def changeEvaluation (v : Fin 2 → AffinePoly) : AffinePoly →ₐ[ℂ] CoordinateOverlap v :=
  aeval ![coordinate v 0 * inverse v, inverse v, coordinate v 2 * inverse v]

@[simp] theorem changeEvaluation_X0 (v : Fin 2 → AffinePoly) :
    changeEvaluation v (X 0) = coordinate v 0 * inverse v := by simp [changeEvaluation]
@[simp] theorem changeEvaluation_X1 (v : Fin 2 → AffinePoly) :
    changeEvaluation v (X 1) = inverse v := by simp [changeEvaluation]
@[simp] theorem changeEvaluation_X2 (v : Fin 2 → AffinePoly) :
    changeEvaluation v (X 2) = coordinate v 2 * inverse v := by simp [changeEvaluation]

theorem second_relations_change_zero (r θ : ℂ) (i : Fin 2) :
    changeEvaluation (firstEquations r θ) (secondEquations r θ i) = 0 := by
  fin_cases i
  · change changeEvaluation (firstEquations r θ) (secondQuadric r) = 0
    rw [map_secondQuadric, changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
    rw [quadratic_scaling]
    have hz := first_quadric_zero r θ
    change quadricOne _ _ 0 _ = 0 at hz
    rw [hz, mul_zero]
  · change changeEvaluation (firstEquations r θ) (secondCubic θ) = 0
    rw [map_secondCubic, changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
    rw [cubic_scaling _ _ _ _ _ _ (coordinate_mul_inverse _), first_cubic_zero, mul_zero]

theorem first_relations_change_zero (r θ : ℂ) (i : Fin 2) :
    changeEvaluation (secondEquations r θ) (firstEquations r θ i) = 0 := by
  fin_cases i
  · change changeEvaluation (secondEquations r θ) (firstQuadric r) = 0
    rw [map_firstQuadric, changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
    rw [quadratic_reverse_scaling _ _ _ _ _ (coordinate_mul_inverse _),
      second_quadric_zero, mul_zero]
  · change changeEvaluation (secondEquations r θ) (firstCubic θ) = 0
    rw [map_firstCubic, changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
    rw [cubic_reverse_scaling _ _ _ _ _ _ (coordinate_mul_inverse _),
      second_cubic_zero, mul_zero]

def quotientLift (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) : ChartRing v →ₐ[ℂ] CoordinateOverlap w :=
  Ideal.Quotient.liftₐ _ (changeEvaluation w) (by
    change chartIdeal v ≤ RingHom.ker (changeEvaluation w).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact h i)

@[simp] theorem quotientLift_chartMap (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) (p : AffinePoly) :
    quotientLift v w h (chartMap v p) = changeEvaluation w p := rfl

def localizationLift (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) :
    CoordinateOverlap v →ₐ[ℂ] CoordinateOverlap w :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (middle v))
    (f := quotientLift v w h) (by
      rintro ⟨_, n, rfl⟩
      rw [map_pow]
      apply IsUnit.pow n
      change IsUnit (changeEvaluation w (X 1))
      rw [changeEvaluation_X1]
      exact ((middleUnit w)⁻¹).isUnit)

@[simp] theorem localizationLift_coordinate (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) (j : Fin 3) :
    localizationLift v w h (coordinate v j) = changeEvaluation w (X j) := by
  change IsLocalization.lift _ (algebraMap (ChartRing v) (CoordinateOverlap v)
    (chartMap v (X j))) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp] theorem localizationLift_polynomialMap (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) (p : AffinePoly) :
    localizationLift v w h (polynomialMap v p) = changeEvaluation w p := by
  change IsLocalization.lift _ (algebraMap (ChartRing v) (CoordinateOverlap v)
    (chartMap v p)) = _
  rw [IsLocalization.lift_eq]
  rfl

@[simp] theorem localizationLift_inverse (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0) :
    localizationLift v w h (inverse v) = coordinate w 1 := by
  have hh := congrArg (localizationLift v w h) (coordinate_mul_inverse v)
  rw [map_mul, localizationLift_coordinate, changeEvaluation_X1, map_one] at hh
  calc
    localizationLift v w h (inverse v) =
        coordinate w 1 * (inverse w * localizationLift v w h (inverse v)) := by
      rw [← mul_assoc, coordinate_mul_inverse, one_mul]
    _ = coordinate w 1 := by rw [hh, mul_one]

def secondToFirst (r θ : ℂ) : SecondOverlap r θ →ₐ[ℂ] FirstOverlap r θ :=
  localizationLift (secondEquations r θ) (firstEquations r θ)
    (second_relations_change_zero r θ)

def firstToSecond (r θ : ℂ) : FirstOverlap r θ →ₐ[ℂ] SecondOverlap r θ :=
  localizationLift (firstEquations r θ) (secondEquations r θ)
    (first_relations_change_zero r θ)

theorem localizationLift_inverse_comp (v w : Fin 2 → AffinePoly)
    (h : ∀ i, changeEvaluation w (v i) = 0)
    (h' : ∀ i, changeEvaluation v (w i) = 0) :
    (localizationLift w v h').comp (localizationLift v w h) =
      AlgHom.id ℂ (CoordinateOverlap v) := by
  apply coordinate_algHom_ext v
  intro j
  fin_cases j <;>
    simp [map_mul, mul_assoc]

/-- The actual overlap pullback, with an explicitly constructed inverse. -/
def overlapEquiv (r θ : ℂ) : SecondOverlap r θ ≃ₐ[ℂ] FirstOverlap r θ :=
  { secondToFirst r θ with
    invFun := firstToSecond r θ
    left_inv := fun x => AlgHom.congr_fun (localizationLift_inverse_comp
      (secondEquations r θ) (firstEquations r θ)
      (second_relations_change_zero r θ) (first_relations_change_zero r θ)) x
    right_inv := fun x => AlgHom.congr_fun (localizationLift_inverse_comp
      (firstEquations r θ) (secondEquations r θ)
      (first_relations_change_zero r θ) (second_relations_change_zero r θ)) x }

@[simp] theorem overlapEquiv_coordinate0 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) 0) =
      coordinate (firstEquations r θ) 0 * inverse (firstEquations r θ) := by
  exact (localizationLift_coordinate _ _ _ 0).trans (changeEvaluation_X0 _)

@[simp] theorem overlapEquiv_coordinate1 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) 1) =
      inverse (firstEquations r θ) := by
  exact (localizationLift_coordinate _ _ _ 1).trans (changeEvaluation_X1 _)

@[simp] theorem overlapEquiv_coordinate2 (r θ : ℂ) :
    overlapEquiv r θ (coordinate (secondEquations r θ) 2) =
      coordinate (firstEquations r θ) 2 * inverse (firstEquations r θ) := by
  exact (localizationLift_coordinate _ _ _ 2).trans (changeEvaluation_X2 _)

section KaehlerFunctoriality

variable {A B C' : Type*} [CommRing A] [CommRing B] [CommRing C']
variable [Algebra ℂ A] [Algebra ℂ B] [Algebra ℂ C']

/-- The universal Kähler map along an explicit algebra homomorphism. -/
def differentialMap (f : A →ₐ[ℂ] B) :
    KaehlerDifferential ℂ A →ₗ[ℂ] KaehlerDifferential ℂ B := by
  letI := f.toRingHom.toAlgebra
  letI : IsScalarTower ℂ A B := IsScalarTower.of_algHom f
  exact (KaehlerDifferential.map ℂ ℂ A B).restrictScalars ℂ

@[simp] theorem differentialMap_D (f : A →ₐ[ℂ] B) (a : A) :
    differentialMap f (KaehlerDifferential.D ℂ A a) =
      KaehlerDifferential.D ℂ B (f a) := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.map_D ℂ ℂ A B a

@[simp] theorem differentialMap_smul (f : A →ₐ[ℂ] B)
    (a : A) (ω : KaehlerDifferential ℂ A) :
    differentialMap f (a • ω) = f a • differentialMap f ω := by
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ A B := IsScalarTower.of_algHom f
  change KaehlerDifferential.map ℂ ℂ A B (a • ω) =
    algebraMap A B a • KaehlerDifferential.map ℂ ℂ A B ω
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul (R := A) (A := B) a
    (KaehlerDifferential.map ℂ ℂ A B ω)).symm

theorem differentialMap_comp (f : A →ₐ[ℂ] B) (g : B →ₐ[ℂ] C')
    (ω : KaehlerDifferential ℂ A) :
    differentialMap g (differentialMap f ω) = differentialMap (g.comp f) ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [differentialMap_D, AlgHom.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [differentialMap_smul, hx, AlgHom.comp_apply]

theorem differentialMap_id (ω : KaehlerDifferential ℂ A) :
    differentialMap (AlgHom.id ℂ A) ω = ω := by
  have hω : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℂ A)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [differentialMap_D, AlgHom.id_apply]
  | zero => exact map_zero _
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul a x _ hx => simp only [differentialMap_smul, hx, AlgHom.id_apply]

/-- An algebra equivalence transports actual universal differentials in
both directions. Its semilinearity is recorded by `differentialMap_smul`. -/
def differentialEquiv (e : A ≃ₐ[ℂ] B) :
    KaehlerDifferential ℂ A ≃ₗ[ℂ] KaehlerDifferential ℂ B :=
  { differentialMap e.toAlgHom with
    invFun := differentialMap e.symm.toAlgHom
    left_inv := fun ω => by
      change differentialMap e.symm.toAlgHom (differentialMap e.toAlgHom ω) = ω
      rw [differentialMap_comp]
      have h : e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id ℂ A := by ext; simp
      rw [h, differentialMap_id]
    right_inv := fun ω => by
      change differentialMap e.toAlgHom (differentialMap e.symm.toAlgHom ω) = ω
      rw [differentialMap_comp]
      have h : e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id ℂ B := by ext; simp
      rw [h, differentialMap_id] }

@[simp] theorem differentialEquiv_D (e : A ≃ₐ[ℂ] B) (a : A) :
    differentialEquiv e (KaehlerDifferential.D ℂ A a) =
      KaehlerDifferential.D ℂ B (e a) := differentialMap_D e.toAlgHom a

@[simp] theorem differentialEquiv_smul (e : A ≃ₐ[ℂ] B)
    (a : A) (ω : KaehlerDifferential ℂ A) :
    differentialEquiv e (a • ω) = e a • differentialEquiv e ω :=
  differentialMap_smul e.toAlgHom a ω

end KaehlerFunctoriality

/-- Transport between the two literal overlap rings, not an assumed map. -/
def overlapDifferentialEquiv (r θ : ℂ) :
    KaehlerDifferential ℂ (SecondOverlap r θ) ≃ₗ[ℂ]
      KaehlerDifferential ℂ (FirstOverlap r θ) :=
  differentialEquiv (overlapEquiv r θ)

theorem differential_inverse (v : Fin 2 → AffinePoly) :
    KaehlerDifferential.D ℂ (CoordinateOverlap v) (inverse v) =
      -(inverse v ^ 2) • KaehlerDifferential.D ℂ (CoordinateOverlap v) (coordinate v 1) := by
  simpa only [inverse, middleUnit_val] using
    derivation_unit_inverse (KaehlerDifferential.D ℂ (CoordinateOverlap v)) (middleUnit v)

theorem overlapDifferential_coordinate0 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 0)) =
      inverse (firstEquations r θ) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) 0) -
      (coordinate (firstEquations r θ) 0 * inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) 1) := by
  rw [overlapDifferentialEquiv, differentialEquiv_D, overlapEquiv_coordinate0,
    Derivation.leibniz, differential_inverse]
  rw [smul_smul, mul_neg, neg_smul, sub_eq_add_neg]
  exact add_comm _ _

theorem overlapDifferential_coordinate1 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 1)) =
      -(inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) 1) := by
  rw [overlapDifferentialEquiv, differentialEquiv_D, overlapEquiv_coordinate1,
    differential_inverse]

theorem overlapDifferential_coordinate2 (r θ : ℂ) :
    overlapDifferentialEquiv r θ
      (KaehlerDifferential.D ℂ (SecondOverlap r θ) (coordinate (secondEquations r θ) 2)) =
      inverse (firstEquations r θ) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) 2) -
      (coordinate (firstEquations r θ) 2 * inverse (firstEquations r θ) ^ 2) •
        KaehlerDifferential.D ℂ (FirstOverlap r θ) (coordinate (firstEquations r θ) 1) := by
  rw [overlapDifferentialEquiv, differentialEquiv_D, overlapEquiv_coordinate2,
    Derivation.leibniz, differential_inverse]
  rw [smul_smul, mul_neg, neg_smul, sub_eq_add_neg]
  exact add_comm _ _

/-! ## The actual middle-coordinate Jacobian minor -/

def middleMinorPolynomial (v : Fin 2 → AffinePoly) : AffinePoly :=
  jacobianMinors (fun j => pderiv j (v 0)) (fun j => pderiv j (v 1)) 1

def middleMinor (v : Fin 2 → AffinePoly) : CoordinateOverlap v :=
  polynomialMap v (middleMinorPolynomial v)

theorem first_middleMinorPolynomial (r θ : ℂ) :
    middleMinorPolynomial (firstEquations r θ) =
      jacobianMinors (gradQuadricOne (C r) (X 0))
        (gradCubicOne (C Complex.I) (C θ) (X 0) (X 1) (X 2)) 1 := by
  change jacobianMinors (fun j => pderiv j (firstQuadric r))
    (fun j => pderiv j (firstCubic θ)) 1 = _
  rw [firstQuadric_gradient, firstCubic_gradient]

theorem second_middleMinorPolynomial (r θ : ℂ) :
    middleMinorPolynomial (secondEquations r θ) =
      jacobianMinors (gradQuadricTwo (C r) (X 0) (X 1) (X 2))
        (gradCubicTwo (C Complex.I) (C θ) (X 0) (X 1) (X 2)) 1 := by
  change jacobianMinors (fun j => pderiv j (secondQuadric r))
    (fun j => pderiv j (secondCubic θ)) 1 = _
  rw [secondQuadric_gradient, secondCubic_gradient]

section MinorEvaluation
variable {S : Type*} [CommRing S] [Algebra ℂ S] (f : AffinePoly →ₐ[ℂ] S)

theorem map_first_middleMinor (r θ : ℂ) :
    f (middleMinorPolynomial (firstEquations r θ)) =
      jacobianMinors (gradQuadricOne (algebraMap ℂ S r) (f (X 0)))
        (gradCubicOne (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
          (f (X 0)) (f (X 1)) (f (X 2))) 1 := by
  rw [first_middleMinorPolynomial]
  have hf2 : f (2 : AffinePoly) = (2 : S) := map_natCast f 2
  have hf3 : f (3 : AffinePoly) = (3 : S) := map_natCast f 3
  simp [jacobianMinors, gradQuadricOne, gradCubicOne, hf2, hf3]

theorem map_second_middleMinor (r θ : ℂ) :
    f (middleMinorPolynomial (secondEquations r θ)) =
      jacobianMinors (gradQuadricTwo (algebraMap ℂ S r) (f (X 0)) (f (X 1)) (f (X 2)))
        (gradCubicTwo (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
          (f (X 0)) (f (X 1)) (f (X 2))) 1 := by
  rw [second_middleMinorPolynomial]
  have hf2 : f (2 : AffinePoly) = (2 : S) := map_natCast f 2
  have hf3 : f (3 : AffinePoly) = (3 : S) := map_natCast f 3
  simp [jacobianMinors, gradQuadricTwo, gradCubicTwo, hf2, hf3]

end MinorEvaluation

theorem middleMinor_scaling {R : Type*} [CommRing R]
    (r i θ a b c t : R) (ht : b * t = 1) :
    jacobianMinors (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) 1 =
      t ^ 3 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 1 := by
  dsimp [jacobianMinors, gradQuadricOne, gradCubicOne, gradQuadricTwo, gradCubicTwo]
  linear_combination (r * c + 2 * a + 2 * a ^ 2) * t ^ 2 * ht

/-- The actual Jacobian cofactors transform in the actual overlap ring. -/
theorem overlapEquiv_middleMinor (r θ : ℂ) :
    overlapEquiv r θ (middleMinor (secondEquations r θ)) =
      inverse (firstEquations r θ) ^ 3 * middleMinor (firstEquations r θ) := by
  change localizationLift _ _ _ (polynomialMap _ (middleMinorPolynomial _)) =
    inverse (firstEquations r θ) ^ 3 * polynomialMap _ (middleMinorPolynomial _)
  rw [localizationLift_polynomialMap, map_second_middleMinor,
    map_first_middleMinor, changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
  exact middleMinor_scaling _ _ _ _ _ _ _ (coordinate_mul_inverse _)

/-- All three signed cofactors transform on the curve. This form is valid
over any commutative ring, so it also applies in residue fields of primes. -/
theorem cofactor_change_on_curve {R : Type*} [CommRing R]
    (r i θ a b c t : R) (ht : b * t = 1)
    (hf : quadricOne r a b c = 0) (hh : cubicOne i θ a b c = 0) :
    jacobianMinors (gradQuadricTwo r (a * t) t (c * t))
      (gradCubicTwo i θ (a * t) t (c * t)) =
      ![-t ^ 2 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 0 +
          a * t ^ 3 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
        t ^ 3 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 1,
        -t ^ 2 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 2 +
          c * t ^ 3 * jacobianMinors (gradQuadricOne r a) (gradCubicOne i θ a b c) 1] := by
  funext j
  fin_cases j
  · dsimp [jacobianMinors, gradQuadricOne, gradCubicOne, gradQuadricTwo, gradCubicTwo,
      quadricOne, cubicOne] at hf hh ⊢
    linear_combination 3 * r * t ^ 3 * hh +
      t ^ 3 * (6 * (1 - i) * c ^ 2 + 2 * b + 2 * a * b) * hf -
      r * t ^ 2 * (3 * b ^ 2 + c) * ht
  · exact middleMinor_scaling r i θ a b c t ht
  · dsimp [jacobianMinors, gradQuadricOne, gradCubicOne, gradQuadricTwo, gradCubicTwo,
      quadricOne, cubicOne] at hf hh ⊢
    linear_combination 6 * a * t ^ 3 * hh -
      t ^ 3 * (2 * b * c + 2 + 6 * θ * a ^ 2) * hf -
      t ^ 2 * (4 * a * c + 2 * a ^ 2 * c + 6 * a * b ^ 2 + r * c ^ 2) * ht

def chartMinors (v : Fin 2 → AffinePoly) (k : Fin 3) : CoordinateOverlap v :=
  polynomialMap v (jacobianMinors (fun j => pderiv j (v 0)) (fun j => pderiv j (v 1)) k)

@[simp] theorem chartMinors_one (v : Fin 2 → AffinePoly) :
    chartMinors v 1 = middleMinor v := rfl

section AllMinorEvaluation
variable {S : Type*} [CommRing S] [Algebra ℂ S] (f : AffinePoly →ₐ[ℂ] S)

theorem map_first_minors (r θ : ℂ) (k : Fin 3) :
    f (jacobianMinors (fun j => pderiv j (firstEquations r θ 0))
      (fun j => pderiv j (firstEquations r θ 1)) k) =
      jacobianMinors (gradQuadricOne (algebraMap ℂ S r) (f (X 0)))
        (gradCubicOne (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
          (f (X 0)) (f (X 1)) (f (X 2))) k := by
  change f (jacobianMinors (fun j => pderiv j (firstQuadric r))
    (fun j => pderiv j (firstCubic θ)) k) = _
  rw [firstQuadric_gradient, firstCubic_gradient]
  have hf2 : f (2 : AffinePoly) = (2 : S) := map_natCast f 2
  have hf3 : f (3 : AffinePoly) = (3 : S) := map_natCast f 3
  fin_cases k <;> simp [jacobianMinors, gradQuadricOne, gradCubicOne, hf2, hf3]

theorem map_second_minors (r θ : ℂ) (k : Fin 3) :
    f (jacobianMinors (fun j => pderiv j (secondEquations r θ 0))
      (fun j => pderiv j (secondEquations r θ 1)) k) =
      jacobianMinors (gradQuadricTwo (algebraMap ℂ S r) (f (X 0)) (f (X 1)) (f (X 2)))
        (gradCubicTwo (algebraMap ℂ S Complex.I) (algebraMap ℂ S θ)
          (f (X 0)) (f (X 1)) (f (X 2))) k := by
  change f (jacobianMinors (fun j => pderiv j (secondQuadric r))
    (fun j => pderiv j (secondCubic θ)) k) = _
  rw [secondQuadric_gradient, secondCubic_gradient]
  have hf2 : f (2 : AffinePoly) = (2 : S) := map_natCast f 2
  have hf3 : f (3 : AffinePoly) = (3 : S) := map_natCast f 3
  fin_cases k <;> simp [jacobianMinors, gradQuadricTwo, gradCubicTwo, hf2, hf3]

end AllMinorEvaluation

/-- The full cofactor transformation is bound to the constructed ring
equivalence and the actual polynomial partial derivatives on both charts. -/
theorem overlapEquiv_allMinors (r θ : ℂ) :
    (fun j => overlapEquiv r θ (chartMinors (secondEquations r θ) j)) =
      ![-inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 0 +
          coordinate (firstEquations r θ) 0 * inverse (firstEquations r θ) ^ 3 *
            chartMinors (firstEquations r θ) 1,
        inverse (firstEquations r θ) ^ 3 * chartMinors (firstEquations r θ) 1,
        -inverse (firstEquations r θ) ^ 2 * chartMinors (firstEquations r θ) 2 +
          coordinate (firstEquations r θ) 2 * inverse (firstEquations r θ) ^ 3 *
            chartMinors (firstEquations r θ) 1] := by
  have hh := cofactor_change_on_curve
    (algebraMap ℂ (FirstOverlap r θ) r) (algebraMap ℂ (FirstOverlap r θ) Complex.I)
    (algebraMap ℂ (FirstOverlap r θ) θ)
    (coordinate (firstEquations r θ) 0) (coordinate (firstEquations r θ) 1)
    (coordinate (firstEquations r θ) 2) (inverse (firstEquations r θ))
    (coordinate_mul_inverse _) (first_quadric_zero r θ) (first_cubic_zero r θ)
  funext j
  change localizationLift _ _ _ (polynomialMap _ _) = _
  rw [localizationLift_polynomialMap, map_second_minors]
  simp only [changeEvaluation_X0, changeEvaluation_X1, changeEvaluation_X2]
  simpa only [chartMinors, map_first_minors, coordinate] using congrFun hh j

/-! ## Transport after inverting the actual Jacobian minors -/

section AssociatedLocalizations
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]

private theorem associatedLocalization (e : A ≃ₐ[ℂ] B) (x : A) (y : B) (u : Bˣ)
    (h : e x = (u : B) * y) : IsLocalization.Away (e x) (Localization.Away y) := by
  have ha : Associated y (e x) := by
    rw [h]
    exact associated_unit_mul_right y (u : B) u.isUnit
  exact IsLocalization.Away.of_associated ha

/-- Localizing equivalent rings at elements that correspond up to a unit
gives an actual algebra equivalence of the two localizations. -/
def awayEquivOfUnit (e : A ≃ₐ[ℂ] B) (x : A) (y : B) (u : Bˣ)
    (h : e x = (u : B) * y) : Localization.Away x ≃ₐ[ℂ] Localization.Away y := by
  letI := associatedLocalization e x y u h
  exact IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers x) (T := Submonoid.powers (e x))
    (Localization.Away x) (Localization.Away y) e (by simp)

@[simp] theorem awayEquivOfUnit_base (e : A ≃ₐ[ℂ] B) (x : A) (y : B) (u : Bˣ)
    (h : e x = (u : B) * y) (a : A) :
    awayEquivOfUnit e x y u h (algebraMap A (Localization.Away x) a) =
      algebraMap B (Localization.Away y) (e a) := by
  let := associatedLocalization e x y u h
  exact IsLocalization.algEquivOfAlgEquiv_eq _ a

end AssociatedLocalizations

abbrev SmoothOverlap (v : Fin 2 → AffinePoly) := Localization.Away (middleMinor v)

def smoothMap (v : Fin 2 → AffinePoly) : CoordinateOverlap v →ₐ[ℂ] SmoothOverlap v :=
  IsScalarTower.toAlgHom ℂ (CoordinateOverlap v) (SmoothOverlap v)

def smoothCoordinate (v : Fin 2 → AffinePoly) (j : Fin 3) : SmoothOverlap v :=
  smoothMap v (coordinate v j)

def smoothInverse (v : Fin 2 → AffinePoly) : SmoothOverlap v := smoothMap v (inverse v)

def smoothMiddleUnit (v : Fin 2 → AffinePoly) : (SmoothOverlap v)ˣ :=
  Units.map (smoothMap v).toMonoidHom (middleUnit v)

@[simp] theorem smoothMiddleUnit_val (v : Fin 2 → AffinePoly) :
    (smoothMiddleUnit v : SmoothOverlap v) = smoothCoordinate v 1 := by
  change smoothMap v (middleUnit v : CoordinateOverlap v) = _
  rw [middleUnit_val]
  rfl

@[simp] theorem smoothMiddleUnit_inv (v : Fin 2 → AffinePoly) :
    (↑((smoothMiddleUnit v)⁻¹) : SmoothOverlap v) = smoothInverse v := rfl

def minorUnit (v : Fin 2 → AffinePoly) : (SmoothOverlap v)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (middleMinor v)).unit

@[simp] theorem minorUnit_val (v : Fin 2 → AffinePoly) :
    (minorUnit v : SmoothOverlap v) = smoothMap v (middleMinor v) :=
  (IsLocalization.Away.algebraMap_isUnit (middleMinor v)).unit_spec

/-- Both Jacobian inverses are supplied by the actual localizations. -/
def smoothOverlapEquiv (r θ : ℂ) :
    SmoothOverlap (secondEquations r θ) ≃ₐ[ℂ] SmoothOverlap (firstEquations r θ) :=
  awayEquivOfUnit (overlapEquiv r θ) (middleMinor (secondEquations r θ))
    (middleMinor (firstEquations r θ)) ((middleUnit (firstEquations r θ))⁻¹ ^ 3)
    (by simpa only [Units.val_pow_eq_pow_val, inverse] using overlapEquiv_middleMinor r θ)

@[simp] theorem smoothOverlapEquiv_base (r θ : ℂ) (a : SecondOverlap r θ) :
    smoothOverlapEquiv r θ (smoothMap (secondEquations r θ) a) =
      smoothMap (firstEquations r θ) (overlapEquiv r θ a) :=
  awayEquivOfUnit_base _ _ _ _ _ a

@[simp] theorem smoothOverlapEquiv_coordinate1 (r θ : ℂ) :
    smoothOverlapEquiv r θ (smoothCoordinate (secondEquations r θ) 1) =
      smoothInverse (firstEquations r θ) := by
  rw [smoothCoordinate, smoothOverlapEquiv_base, overlapEquiv_coordinate1]
  rfl

theorem smoothOverlapEquiv_minor (r θ : ℂ) :
    smoothOverlapEquiv r θ (minorUnit (secondEquations r θ) : SmoothOverlap _) =
      smoothInverse (firstEquations r θ) ^ 3 * (minorUnit (firstEquations r θ) : SmoothOverlap _) := by
  rw [minorUnit_val, smoothOverlapEquiv_base, overlapEquiv_middleMinor, map_mul, map_pow,
    minorUnit_val]
  rfl

def smoothDifferentialEquiv (r θ : ℂ) :
    KaehlerDifferential ℂ (SmoothOverlap (secondEquations r θ)) ≃ₗ[ℂ]
      KaehlerDifferential ℂ (SmoothOverlap (firstEquations r θ)) :=
  differentialEquiv (smoothOverlapEquiv r θ)

theorem smoothDifferential_inverse (v : Fin 2 → AffinePoly) :
    KaehlerDifferential.D ℂ (SmoothOverlap v) (smoothInverse v) =
      -(smoothInverse v ^ 2) •
        KaehlerDifferential.D ℂ (SmoothOverlap v) (smoothCoordinate v 1) := by
  simpa only [smoothMiddleUnit_inv, smoothMiddleUnit_val] using
    derivation_unit_inverse (KaehlerDifferential.D ℂ (SmoothOverlap v)) (smoothMiddleUnit v)

/-- A signed-minor normalized differential in the actual localized ring. -/
def normalizedForm (v : Fin 2 → AffinePoly) : KaehlerDifferential ℂ (SmoothOverlap v) :=
  (↑((minorUnit v)⁻¹) : SmoothOverlap v) •
    KaehlerDifferential.D ℂ (SmoothOverlap v) (smoothCoordinate v 1)

private theorem normalized_unit_change {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (b u v : Rˣ) (hv : (v : R) = (↑(b⁻¹) : R) ^ 3 * (u : R)) (ω : M) :
    (↑(v⁻¹) : R) • (-(↑(b⁻¹) : R) ^ 2 • ω) =
      (b : R) • (-((↑(u⁻¹) : R) • ω)) := by
  have hv' : v = b⁻¹ ^ 3 * u := Units.ext hv
  subst v
  simp only [mul_inv_rev, inv_pow, inv_inv, Units.val_mul, Units.val_pow_eq_pow_val,
    smul_smul, smul_neg, neg_smul]
  have hp : (b : R) ^ 3 * (↑(b⁻¹) : R) ^ 2 = (b : R) := by
    calc
      (b : R) ^ 3 * (↑(b⁻¹) : R) ^ 2 = (b : R) * ((b : R) * (↑(b⁻¹) : R)) ^ 2 := by ring
      _ = (b : R) := by rw [b.mul_inv, one_pow, mul_one]
  congr 1
  apply congrArg (fun z : R => z • ω)
  calc
    (↑(u⁻¹) : R) * (b : R) ^ 3 * (↑(b⁻¹) : R) ^ 2 =
        (↑(u⁻¹) : R) * ((b : R) ^ 3 * (↑(b⁻¹) : R) ^ 2) := by ring
    _ = (b : R) * (↑(u⁻¹) : R) := by rw [hp]; ring

/-- The actual normalized differential changes by minus the middle
coordinate before the projective orientation signs are included. -/
theorem normalizedForm_transport (r θ : ℂ) :
    smoothDifferentialEquiv r θ (normalizedForm (secondEquations r θ)) =
      smoothCoordinate (firstEquations r θ) 1 • (-normalizedForm (firstEquations r θ)) := by
  rw [smoothDifferentialEquiv, normalizedForm, differentialEquiv_smul,
    differentialEquiv_D, smoothOverlapEquiv_coordinate1, smoothDifferential_inverse]
  let v : (SmoothOverlap (firstEquations r θ))ˣ :=
    Units.map (smoothOverlapEquiv r θ).toMonoidHom (minorUnit (secondEquations r θ))
  have hv : (v : SmoothOverlap (firstEquations r θ)) =
      (↑((smoothMiddleUnit (firstEquations r θ))⁻¹) : SmoothOverlap _) ^ 3 *
        (minorUnit (firstEquations r θ) : SmoothOverlap _) := by
    exact smoothOverlapEquiv_minor r θ
  exact normalized_unit_change (smoothMiddleUnit (firstEquations r θ))
    (minorUnit (firstEquations r θ)) v hv _

def firstOrientedForm (r θ : ℂ) :
    KaehlerDifferential ℂ (SmoothOverlap (firstEquations r θ)) :=
  -normalizedForm (firstEquations r θ)

def secondOrientedForm (r θ : ℂ) :
    KaehlerDifferential ℂ (SmoothOverlap (secondEquations r θ)) :=
  normalizedForm (secondEquations r θ)

/-- Deleting projective coordinates 1 and 2 gives orientation signs -1
and +1. The resulting genuine differential frames therefore differ by
the unit x2/x1, as required for the canonical O(1) transition. -/
theorem oriented_normalizedForm_transport (r θ : ℂ) :
    smoothDifferentialEquiv r θ (secondOrientedForm r θ) =
      smoothCoordinate (firstEquations r θ) 1 • firstOrientedForm r θ :=
  normalizedForm_transport r θ

#print axioms overlapEquiv
#print axioms overlapDifferentialEquiv
#print axioms overlapDifferential_coordinate0
#print axioms overlapDifferential_coordinate1
#print axioms overlapDifferential_coordinate2
#print axioms overlapEquiv_middleMinor
#print axioms cofactor_change_on_curve
#print axioms overlapEquiv_allMinors
#print axioms smoothOverlapEquiv
#print axioms oriented_normalizedForm_transport

end CycleQ2GeometricAffineOverlap

end
