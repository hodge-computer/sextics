import Proposal.GeometricAffineDifferentialSheaf

/-!
# Arbitrary complex derivations on actual localization rings

Localization of the universal Kähler module extends any complex derivation.
No rank or differential-frame hypothesis is imposed. The extension agrees
on the original ring and satisfies the literal fraction rule, including
when the original ring or the localization has zero divisors.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricLocalizedDerivations

variable {A : Type} [CommRing A] [Algebra ℂ A]
variable (M : Submonoid A) (B : Type) [CommRing B] [Algebra ℂ B] [Algebra A B]
  [IsScalarTower ℂ A B] [IsLocalization M B]

def localizedLinear (δ : Derivation ℂ A A) : KaehlerDifferential ℂ B →ₗ[B] B :=
  IsLocalizedModule.mapExtendScalars M (KaehlerDifferential.map ℂ ℂ A B)
    (Algebra.linearMap A B) B δ.liftKaehlerDifferential

theorem localizedLinear_map (δ : Derivation ℂ A A) (ω : KaehlerDifferential ℂ A) :
    localizedLinear M B δ (KaehlerDifferential.map ℂ ℂ A B ω) =
      algebraMap A B (δ.liftKaehlerDifferential ω) := by
  exact IsLocalizedModule.map_apply M (KaehlerDifferential.map ℂ ℂ A B)
    (Algebra.linearMap A B) δ.liftKaehlerDifferential ω

def localizedDerivation (δ : Derivation ℂ A A) : Derivation ℂ B B :=
  (localizedLinear M B δ).compDer (KaehlerDifferential.D ℂ B)

theorem localizedDerivation_algebraMap (δ : Derivation ℂ A A) (a : A) :
    localizedDerivation M B δ (algebraMap A B a) = algebraMap A B (δ a) := by
  change localizedLinear M B δ (KaehlerDifferential.D ℂ B (algebraMap A B a)) = _
  rw [← KaehlerDifferential.map_D ℂ ℂ A B, localizedLinear_map]
  rw [Derivation.liftKaehlerDifferential_comp_D]

theorem localizedDerivation_fraction (δ : Derivation ℂ A A) (a : A) (s : M) :
    localizedDerivation M B δ (IsLocalization.mk' B a s) =
      (IsLocalization.mk' B 1 s) ^ 2 *
        (algebraMap A B (s : A) * algebraMap A B (δ a) -
          algebraMap A B a * algebraMap A B (δ (s : A))) := by
  let d := localizedDerivation M B δ
  have ht : IsLocalization.mk' B 1 s * algebraMap A B (s : A) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  have hinv := d.leibniz_of_mul_eq_one ht
  have hpow : (IsLocalization.mk' B 1 s) ^ 2 * algebraMap A B (s : A) =
      IsLocalization.mk' B 1 s := by
    rw [pow_two, mul_assoc, ht, mul_one]
  change d (IsLocalization.mk' B a s) = _
  rw [IsLocalization.mk'_eq_mul_mk'_one, Derivation.leibniz, hinv]
  simp only [d, localizedDerivation_algebraMap, smul_eq_mul]
  calc
    _ = (IsLocalization.mk' B 1 s) ^ 2 * algebraMap A B (s : A) * algebraMap A B (δ a) -
        (IsLocalization.mk' B 1 s) ^ 2 * algebraMap A B a * algebraMap A B (δ (s : A)) := by
      rw [hpow]
      ring
    _ = _ := by ring

theorem localizedDerivation_mk (δ : Derivation ℂ A A) (a : A) (s : M) :
    localizedDerivation M (LocalizedModule M A) δ (LocalizedModule.mk a s) =
      LocalizedModule.mk ((s : A) * δ a - a * δ (s : A)) (s * s) := by
  rw [CycleQ2GeometricStructureDerivation.localizedModule_mk_eq,
    CycleQ2GeometricStructureDerivation.localizedModule_mk_eq,
    localizedDerivation_fraction, ← map_mul, ← map_mul, ← map_sub, pow_two,
    ← IsLocalization.mk'_mul, one_mul, mul_comm, ← IsLocalization.mk'_eq_mul_mk'_one]

end CycleQ2GeometricLocalizedDerivations

end

#print axioms CycleQ2GeometricLocalizedDerivations.localizedDerivation_algebraMap
#print axioms CycleQ2GeometricLocalizedDerivations.localizedDerivation_mk

/-!
# Localization over an arbitrary ground ring

The arithmetic coefficient models are algebras over the integers, not over
the complex numbers. The same Kähler construction therefore needs its
ground ring as a parameter. Agreement on the original ring determines
compatibility of localized derivations after any coefficient map.
-/

noncomputable section
namespace CycleQ2GeometricLocalizedDerivations

section ArbitraryBase

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (M : Submonoid A) (B : Type*) [CommRing B] [Algebra k B] [Algebra A B]
  [IsScalarTower k A B] [IsLocalization M B]

def localizedBaseLinear (δ : Derivation k A A) : KaehlerDifferential k B →ₗ[B] B :=
  IsLocalizedModule.mapExtendScalars M (KaehlerDifferential.map k k A B)
    (Algebra.linearMap A B) B δ.liftKaehlerDifferential

theorem localizedBaseLinear_map (δ : Derivation k A A) (ω : KaehlerDifferential k A) :
    localizedBaseLinear M B δ (KaehlerDifferential.map k k A B ω) =
      algebraMap A B (δ.liftKaehlerDifferential ω) :=
  IsLocalizedModule.map_apply M (KaehlerDifferential.map k k A B)
    (Algebra.linearMap A B) δ.liftKaehlerDifferential ω

/-- Extension of a derivation through any commutative-ring localization. -/
def localizedBaseDerivation (δ : Derivation k A A) : Derivation k B B :=
  (localizedBaseLinear M B δ).compDer (KaehlerDifferential.D k B)

theorem localizedBaseDerivation_algebraMap (δ : Derivation k A A) (a : A) :
    localizedBaseDerivation M B δ (algebraMap A B a) = algebraMap A B (δ a) := by
  change localizedBaseLinear M B δ (KaehlerDifferential.D k B (algebraMap A B a)) = _
  rw [← KaehlerDifferential.map_D k k A B,localizedBaseLinear_map]
  rw [Derivation.liftKaehlerDifferential_comp_D]

end ArbitraryBase

/-- A ring map between two differential rings commutes with the derivations
on a localization as soon as it does so on the original ring. -/
theorem derivation_commutes_of_algebraMap
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B]
    (D : Derivation ℤ B B) (E : Derivation ℤ C C) (φ : B →+* C)
    (h : ∀ a : A, E (φ (algebraMap A B a)) = φ (D (algebraMap A B a))) (b : B) :
    E (φ b) = φ (D b) := by
  obtain ⟨⟨a,s⟩,hs⟩ := IsLocalization.surj M b
  have he := congrArg (fun z : B => E (φ z)) hs
  simp only [map_mul,Derivation.leibniz,smul_eq_mul,h] at he
  have hd := congrArg (fun z : B => φ (D z)) hs
  simp only [Derivation.leibniz,smul_eq_mul,map_add,map_mul] at hd
  exact ((IsLocalization.map_units B s).map φ).mul_left_cancel
    (add_left_cancel (he.trans hd.symm))

end CycleQ2GeometricLocalizedDerivations
end

#print axioms CycleQ2GeometricLocalizedDerivations.localizedBaseDerivation_algebraMap
#print axioms CycleQ2GeometricLocalizedDerivations.derivation_commutes_of_algebraMap
