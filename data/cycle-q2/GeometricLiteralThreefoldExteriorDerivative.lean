import Proposal.GeometricLiteralThreefoldCartan
import Proposal.GeometricSurfaceResidueFunctoriality
import Mathlib.RingTheory.Derivation.Lie

/-!
# Intrinsic exterior differentiation of two-forms in dimension three

For an exact coordinate basis, the three partial derivations commute.
Consequently the chartwise Cartan operator sends `f dg ∧ dh` to
`df ∧ dg ∧ dh`. These forms generate additively, giving independence
of the exact frame and compatibility with pullback of differential forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldExteriorDerivative

open CycleQ2HodgeEulerContraction CycleQ2LiteralThreefoldCartan
  CycleQ2ResidueWedgeLinear CycleQ2ExteriorSectionNaturality CycleQ2GeometricAffineOverlap

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (b : Module.Basis (Fin 3) A (OneForms A))
local notation "d₁" => KaehlerDifferential.D ℂ A

private theorem coord_coordinate (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i))
    (i j : Fin 3) :
    coordinateDerivation b i (u j) = if j = i then 1 else 0 := by
  change b.coord i (d₁ (u j)) = _
  rw [← hu]
  simp [Module.Basis.coord_apply, Finsupp.single_apply]

/-- Mixed partials commute for an exact Kähler basis. -/
theorem partials_commute (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i))
    (i j : Fin 3) (f : A) :
    coordinateDerivation b i (coordinateDerivation b j f) =
      coordinateDerivation b j (coordinateDerivation b i f) := by
  let D := ⁅coordinateDerivation b i, coordinateDerivation b j⁆
  have h : D.liftKaehlerDifferential = 0 := by
    apply b.ext
    intro k
    rw [hu, Derivation.liftKaehlerDifferential_comp_D]
    simp only [D, Derivation.commutator_apply, coord_coordinate b u hu, LinearMap.zero_apply]
    split <;> split <;> simp
  apply sub_eq_zero.mp
  change D f = 0
  rw [← Derivation.liftKaehlerDifferential_comp_D D, h]
  rfl

private theorem complementaryCoefficient (v : Fin 2 → OneForms A) (j : Fin 3) :
    (contractionEquiv b).symm (exteriorPower.ιMulti A 2 v) (b j) =
      (-1 : A)^j.val *
        ((Matrix.of fun (k l : Fin 2) => b.coord (j.succAbove l) (v k)).det) := by
  change (b.constr A (fun t => (-1 : A)^t.val *
    (twoBasis b).repr (exteriorPower.ιMulti A 2 v) t)) (b j) = _
  rw [b.constr_basis]
  congr 1
  rw [twoBasis, Module.Basis.repr_reindex_apply, exteriorPower.basis_repr_apply,
    exteriorPower.ιMultiDual_apply_ιMulti]
  apply congrArg Matrix.det
  ext k l
  change b.coord (({j}ᶜ : Finset (Fin 3)).orderEmbOfFin _ l) (v k) = _
  rw [Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb]
  rfl

private theorem scaledCoefficient (f g h : A) (j : Fin 3) :
    (contractionEquiv b).symm (f • exteriorPower.ιMulti A 2 ![d₁ g, d₁ h]) (b j) =
      f * ((-1 : A)^j.val *
        (coordinateDerivation b (j.succAbove 0) g * coordinateDerivation b (j.succAbove 1) h -
          coordinateDerivation b (j.succAbove 1) g * coordinateDerivation b (j.succAbove 0) h)) := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, complementaryCoefficient, Matrix.det_fin_two]
  rfl

/-- The chartwise two-form derivative satisfies the exterior derivative
formula on arbitrary multiples of wedges of exact differentials. -/
theorem exteriorD2_exact_wedge (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i)) (f g h : A) :
    exteriorD2 b (f • exteriorPower.ιMulti A 2 ![d₁ g, d₁ h]) =
      exteriorPower.ιMulti A 3 ![d₁ f, d₁ g, d₁ h] := by
  rw [exteriorD2, topWedge_eq_det_smul b ![d₁ f, d₁ g, d₁ h]]
  change _ • orderedVolume b = _ • orderedVolume b
  congr 1
  simp only [scaledCoefficient, Fin.sum_univ_three, Matrix.det_fin_three,
    Module.Basis.toMatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, show (0 : Fin 3).succAbove 0 = 1 by decide,
    show (0 : Fin 3).succAbove 1 = 2 by decide, show (1 : Fin 3).succAbove 0 = 0 by decide,
    show (1 : Fin 3).succAbove 1 = 2 by decide, show (2 : Fin 3).succAbove 0 = 0 by decide,
    show (2 : Fin 3).succAbove 1 = 1 by decide, Fin.val_zero, Fin.val_one, show (2 : Fin 3).val = 2 by rfl, Fin.isValue,
    pow_zero, pow_one, neg_one_mul, one_mul, neg_one_sq, Derivation.leibniz, map_sub,
    map_neg, smul_eq_mul]
  have hδ (i : Fin 3) (x : A) : b.repr (d₁ x) i = coordinateDerivation b i x := rfl
  simp only [hδ, Derivation.map_one_eq_zero, partials_commute b u hu 1 0, partials_commute b u hu 2 0,
    partials_commute b u hu 2 1]
  ring

/-- Exterior differentiation is additive, including over finite sums of generators. -/
def additive : Forms A 2 →+ Forms A 3 where
  toFun := exteriorD2 b
  map_zero' := by simp [exteriorD2]
  map_add' α β := by simp [exteriorD2, Finset.sum_add_distrib, add_smul]

private theorem exact_generators {N : Type*} [AddCommMonoid N]
    (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i)) (F G : Forms A 2 →+ N)
    (heq : ∀ f g h : A, F (f • exteriorPower.ιMulti A 2 ![d₁ g, d₁ h]) =
      G (f • exteriorPower.ιMulti A 2 ![d₁ g, d₁ h])) (η : Forms A 2) :
    F η = G η := by
  rw [← (twoBasis b).sum_repr η, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : j.removeNth b = ![d₁ (u (j.succAbove 0)), d₁ (u (j.succAbove 1))] := by
    funext k
    fin_cases k <;> apply hu
  rw [twoBasis_apply, hj]
  apply heq

/-- Exterior differentiation is independent of the chosen exact frame. -/
theorem exteriorD2_basis_independent (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i))
    (c : Module.Basis (Fin 3) A (OneForms A)) (w : Fin 3 → A) (hw : ∀ i, c i = d₁ (w i))
    (η : Forms A 2) : exteriorD2 b η = exteriorD2 c η := by
  apply exact_generators b u hu (additive b) (additive c) _ η
  intro f g h
  exact (exteriorD2_exact_wedge b u hu f g h).trans (exteriorD2_exact_wedge c w hw f g h).symm

variable {B : Type} [CommRing B] [Algebra ℂ B]

private theorem map_exact_pair (φ : A →ₐ[ℂ] B) (g h : A) :
    exteriorDifferentialMap φ 2 (exteriorPower.ιMulti A 2 ![d₁ g, d₁ h]) =
      exteriorPower.ιMulti B 2 ![KaehlerDifferential.D ℂ B (φ g), KaehlerDifferential.D ℂ B (φ h)] := by
  rw [exteriorDifferentialMap_wedge]
  congr 1
  funext k
  fin_cases k <;> apply differentialMap_D

private theorem map_exact_triple (φ : A →ₐ[ℂ] B) (f g h : A) :
    exteriorDifferentialMap φ 3 (exteriorPower.ιMulti A 3 ![d₁ f, d₁ g, d₁ h]) =
      exteriorPower.ιMulti B 3 ![KaehlerDifferential.D ℂ B (φ f),
        KaehlerDifferential.D ℂ B (φ g), KaehlerDifferential.D ℂ B (φ h)] := by
  rw [exteriorDifferentialMap_wedge]
  congr 1
  funext k
  fin_cases k <;> apply differentialMap_D

/-- Pullback under any complex algebra map between exact-framed threefold
charts commutes with exterior differentiation of every two-form. -/
theorem exteriorD2_natural (u : Fin 3 → A) (hu : ∀ i, b i = d₁ (u i))
    (φ : A →ₐ[ℂ] B) (c : Module.Basis (Fin 3) B (OneForms B)) (w : Fin 3 → B)
    (hw : ∀ i, c i = KaehlerDifferential.D ℂ B (w i)) (η : Forms A 2) :
    exteriorD2 c (exteriorDifferentialMap φ 2 η) = exteriorDifferentialMap φ 3 (exteriorD2 b η) := by
  apply exact_generators b u hu ((additive c).comp (exteriorDifferentialMap φ 2).toAddMonoidHom)
    ((exteriorDifferentialMap φ 3).toAddMonoidHom.comp (additive b)) _ η
  intro f g h
  change exteriorD2 c (exteriorDifferentialMap φ 2 _) =
    exteriorDifferentialMap φ 3 (exteriorD2 b _)
  rw [LinearMap.map_smulₛₗ, map_exact_pair, exteriorD2_exact_wedge b u hu, map_exact_triple]
  exact exteriorD2_exact_wedge c w hw (φ f) (φ g) (φ h)

end CycleQ2LiteralThreefoldExteriorDerivative
end
#print axioms CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_exact_wedge

#print axioms CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_basis_independent
#print axioms CycleQ2LiteralThreefoldExteriorDerivative.exteriorD2_natural
