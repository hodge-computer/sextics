import Proposal.GeometricLiteralThreefoldExteriorDerivative

/-!
# Exterior differentiation of one-forms in an exact threefold frame

The actual Kähler basis defines an additive differential by differentiating
its coefficients. Commutation of the three coordinate derivations proves
that exact one-forms and logarithmic differentials are closed. The formula
on arbitrary a db also proves independence of the chosen exact frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ThreefoldExteriorOneFrame
open Module CycleQ2LiteralThreefoldCartan
open CycleQ2LiteralThreefoldExteriorDerivative (partials_commute)
open CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap
variable {A : Type} [CommRing A] [Algebra ℂ A]

def wedge (α β : OneForms A) : Forms A 2 := exteriorPower.ιMulti A 2 ![α,β]

def wedgeLeft (β : OneForms A) : OneForms A →ₗ[A] Forms A 2 where
  toFun α := wedge α β
  map_add' α γ := (exteriorPower.ιMulti A 2).map_vecCons_add ![β] α γ
  map_smul' a α := (exteriorPower.ιMulti A 2).map_vecCons_smul ![β] a α

def wedgeRight (α : OneForms A) : OneForms A →ₗ[A] Forms A 2 where
  toFun β := wedge α β
  map_add' β γ := ((exteriorPower.ιMulti A 2).curryLeft α).map_vecCons_add ![] β γ
  map_smul' a β := ((exteriorPower.ιMulti A 2).curryLeft α).map_vecCons_smul ![] a β

theorem wedge_self (α : OneForms A) : wedge α α = 0 :=
  (exteriorPower.ιMulti A 2).map_eq_zero_of_eq ![α,α] (by rfl : ![α,α] (0 : Fin 2) = ![α,α] 1) (by decide)

theorem wedge_swap (α β : OneForms A) : wedge β α = -wedge α β := by
  have he : ![β,α] = ![α,β] ∘ Equiv.swap (0 : Fin 2) 1 := by funext i; fin_cases i <;> rfl
  unfold wedge
  rw [he,AlternatingMap.map_swap _ _ (by decide : (0 : Fin 2) ≠ 1)]

variable (b : Basis (Fin 3) A (OneForms A))

def differential : OneForms A →+ Forms A 2 :=
  ∑ i : Fin 3, (wedgeLeft (b i)).toAddMonoidHom.comp
    ((KaehlerDifferential.D ℂ A).toLinearMap.toAddMonoidHom.comp (b.coord i).toAddMonoidHom)

theorem differential_apply (ω : OneForms A) :
    differential b ω = ∑ i : Fin 3, wedge (KaehlerDifferential.D ℂ A (b.coord i ω)) (b i) := by
  simp [differential,wedgeLeft]

private theorem derivative_expansion (f : A) :
    KaehlerDifferential.D ℂ A f = ∑ i : Fin 3, coordinateDerivation b i f • b i :=
  (b.sum_repr _).symm

theorem differential_D (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (f : A) :
    differential b (KaehlerDifferential.D ℂ A f) = 0 := by
  rw [differential_apply]
  change (∑ i : Fin 3, wedge (KaehlerDifferential.D ℂ A (coordinateDerivation b i f)) (b i)) = 0
  simp_rw [derivative_expansion b]
  change (∑ i : Fin 3, wedgeLeft (b i) (∑ j : Fin 3,
    coordinateDerivation b j (coordinateDerivation b i f) • b j)) = 0
  simp only [map_sum,map_smul]
  change (∑ i : Fin 3, ∑ j : Fin 3,
    coordinateDerivation b j (coordinateDerivation b i f) • wedge (b j) (b i)) = 0
  simp only [Fin.sum_univ_three,wedge_self,smul_zero,zero_add,add_zero]
  rw [wedge_swap (b 1) (b 0),wedge_swap (b 2) (b 0),wedge_swap (b 2) (b 1),
    partials_commute b u hu 1 0,partials_commute b u hu 2 0,partials_commute b u hu 2 1]
  simp only [smul_neg]
  abel

theorem differential_smul (a : A) (ω : OneForms A) :
    differential b (a • ω) = a • differential b ω + wedge (KaehlerDifferential.D ℂ A a) ω := by
  rw [differential_apply]
  simp only [map_smul,smul_eq_mul,Derivation.leibniz]
  change (∑ i : Fin 3, wedgeLeft (b i)
    (a • KaehlerDifferential.D ℂ A (b.coord i ω) + b.coord i ω • KaehlerDifferential.D ℂ A a)) = _
  simp only [map_add,map_smul,Finset.sum_add_distrib,← Finset.smul_sum]
  change a • differential b ω + (∑ i : Fin 3, b.coord i ω • wedgeRight (KaehlerDifferential.D ℂ A a) (b i)) = _
  simp only [← map_smul,← map_sum]
  have he : (∑ i : Fin 3, b.coord i ω • b i) = ω := b.sum_repr ω
  rw [he]
  rfl

theorem differential_symbol (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (a f : A) :
    differential b (a • KaehlerDifferential.D ℂ A f) =
      wedge (KaehlerDifferential.D ℂ A a) (KaehlerDifferential.D ℂ A f) := by
  rw [differential_smul,differential_D b u hu,smul_zero,zero_add]

theorem differential_log (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i)) (v : Aˣ) :
    differential b ((v⁻¹ : Aˣ).val • KaehlerDifferential.D ℂ A (v : A)) = 0 := by
  rw [differential_symbol b u hu]
  have hv : KaehlerDifferential.D ℂ A ((v⁻¹ : Aˣ).val) =
      -((v⁻¹ : Aˣ).val ^ 2) • KaehlerDifferential.D ℂ A (v : A) :=
    (KaehlerDifferential.D ℂ A).leibniz_of_mul_eq_one (by simp)
  rw [hv]
  change wedgeLeft (KaehlerDifferential.D ℂ A (v : A))
    (-((v⁻¹ : Aˣ).val ^ 2) • KaehlerDifferential.D ℂ A (v : A)) = 0
  rw [map_smul]
  change -((v⁻¹ : Aˣ).val ^ 2) • wedge (KaehlerDifferential.D ℂ A (v : A)) (KaehlerDifferential.D ℂ A (v : A)) = 0
  rw [wedge_self,smul_zero]

theorem differential_scalar_log (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (c : ℂ) (v : Aˣ) :
    differential b (algebraMap ℂ A c • ((v⁻¹ : Aˣ).val • KaehlerDifferential.D ℂ A (v : A))) = 0 := by
  rw [differential_smul,differential_log b u hu,smul_zero,zero_add,Derivation.map_algebraMap]
  exact map_zero (wedgeLeft _)

/-- Pullback of one-forms commutes with the actual differential for any
pair of exact coordinate frames. -/
theorem differential_natural {B : Type} [CommRing B] [Algebra ℂ B]
    (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (f : A →ₐ[ℂ] B) (c : Basis (Fin 3) B (OneForms B))
    (v : Fin 3 → B) (hv : ∀ i, c i = KaehlerDifferential.D ℂ B (v i)) (ω : OneForms A) :
    exteriorDifferentialMap f 2 (differential b ω) = differential c (differentialMap f ω) := by
  rw [← b.sum_repr ω]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hu,differential_symbol b u hu,differentialMap_smul,differentialMap_D,
    differential_symbol c v hv]
  unfold wedge
  rw [exteriorDifferentialMap_wedge]
  congr 1
  funext j
  fin_cases j <;> exact differentialMap_D f _

/-- The next exterior differential kills the derivative of every one-form. -/
theorem differential_two_one (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (ω : OneForms A) :
    CycleQ2LiteralThreefoldExteriorDerivative.additive b (differential b ω) = 0 := by
  rw [← b.sum_repr ω,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hu,differential_symbol b u hu]
  have he := CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_exact_wedge b u hu
    1 (b.coord i ω) (u i)
  rw [one_smul,Derivation.map_one_eq_zero] at he
  have hz : exteriorPower.ιMulti A 3 ![0,KaehlerDifferential.D ℂ A (b.coord i ω),
      KaehlerDifferential.D ℂ A (u i)] = 0 := by
    exact (exteriorPower.ιMulti A 3).map_coord_zero 0 (by rfl)
  exact he.trans hz

end CycleQ2ThreefoldExteriorOneFrame
end
#print axioms CycleQ2ThreefoldExteriorOneFrame.differential_D
#print axioms CycleQ2ThreefoldExteriorOneFrame.differential_symbol
#print axioms CycleQ2ThreefoldExteriorOneFrame.differential_scalar_log

#print axioms CycleQ2ThreefoldExteriorOneFrame.differential_natural
#print axioms CycleQ2ThreefoldExteriorOneFrame.differential_two_one
