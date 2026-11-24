import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.Module
import Mathlib.Tactic.Ring

/-!
# Localization-compatible frames of the actual differential module

A trivialization of the genuine Kähler module over an affine algebra induces
a trivialization after any actual localization. The construction uses
Mathlib's theorem that the universal Kähler map is a localization of modules,
then its universal linear equivalence and extension of scalars.

The localized frame is the image of the original frame under the actual
universal differential map. Its coefficient formula and compatibility with
further localization do not assume a new freeness or comparison statement.
The base ring is arbitrary; in the curve application it is the complex field.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2GeometricLocalizedDifferentials

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

section AlgebraMap
variable (S : Type*) [CommRing S] [Algebra R S] [Algebra A S] [IsScalarTower R A S]
variable (e : KaehlerDifferential R A ≃ₗ[A] A)

/-- Coefficients of original differentials, mapped to the target algebra. -/
def coefficientMap : KaehlerDifferential R A →ₗ[A] S :=
  (Algebra.linearMap A S).comp e.toLinearMap

/-- The universal image of the original frame, without any freeness premise
on the target algebra. -/
def localizedFrame : KaehlerDifferential R S :=
  KaehlerDifferential.map R R A S (e.symm 1)

end AlgebraMap

section Localization
variable (M : Submonoid A) (S : Type*) [CommRing S]
  [Algebra R S] [Algebra A S] [IsScalarTower R A S] [IsLocalization M S]
variable (e : KaehlerDifferential R A ≃ₗ[A] A)

/-- The localization theorem constructs the actual target trivialization. -/
def localEquiv : KaehlerDifferential R S ≃ₗ[S] S := by
  letI : IsLocalizedModule M (coefficientMap S e) :=
    IsLocalizedModule.of_linearEquiv_right M (Algebra.linearMap A S) e
  exact (IsLocalizedModule.linearEquiv M (KaehlerDifferential.map R R A S)
    (coefficientMap S e)).extendScalarsOfIsLocalization M S

@[simp] theorem localEquiv_map (ω : KaehlerDifferential R A) :
    localEquiv M S e (KaehlerDifferential.map R R A S ω) = algebraMap A S (e ω) := by
  let : IsLocalizedModule M (coefficientMap S e) :=
    IsLocalizedModule.of_linearEquiv_right M (Algebra.linearMap A S) e
  exact IsLocalizedModule.linearEquiv_apply M (KaehlerDifferential.map R R A S)
    (coefficientMap S e) ω

@[simp] theorem localEquiv_localizedFrame : localEquiv M S e (localizedFrame S e) = 1 := by
  rw [localizedFrame, localEquiv_map, LinearEquiv.apply_symm_apply, map_one]

@[simp] theorem localEquiv_symm_one : (localEquiv M S e).symm 1 = localizedFrame S e := by
  apply (localEquiv M S e).injective
  rw [LinearEquiv.apply_symm_apply, localEquiv_localizedFrame]

/-- Every genuine localized differential has a unique coefficient in this frame. -/
theorem reconstruction (ω : KaehlerDifferential R S) :
    ω = localEquiv M S e ω • localizedFrame S e := by
  apply (localEquiv M S e).injective
  rw [map_smul, localEquiv_localizedFrame, smul_eq_mul, mul_one]

theorem coefficient_unique (s : S) (ω : KaehlerDifferential R S)
    (hω : ω = s • localizedFrame S e) : localEquiv M S e ω = s := by
  rw [hω, map_smul, localEquiv_localizedFrame, smul_eq_mul, mul_one]

include M in
theorem frame_smul_bijective :
    Function.Bijective (fun s : S => s • localizedFrame S e) := by
  constructor
  · intro a b h
    have h' := congrArg (localEquiv M S e) h
    simpa only [map_smul, localEquiv_localizedFrame, smul_eq_mul, mul_one] using h'
  · intro ω
    exact ⟨localEquiv M S e ω, (reconstruction M S e ω).symm⟩

/-- The coefficient of an actual differential of an original ring element. -/
@[simp] theorem localEquiv_D_algebraMap (a : A) :
    localEquiv M S e (KaehlerDifferential.D R S (algebraMap A S a)) =
      algebraMap A S (e (KaehlerDifferential.D R A a)) := by
  rw [← KaehlerDifferential.map_D R R A S, localEquiv_map]

include M in
theorem differential_algebraMap (a : A) :
    KaehlerDifferential.D R S (algebraMap A S a) =
      algebraMap A S (e (KaehlerDifferential.D R A a)) • localizedFrame S e := by
  simpa only [localEquiv_D_algebraMap] using
    reconstruction M S e (KaehlerDifferential.D R S (algebraMap A S a))

/-- The coordinate coefficient map is itself a genuine derivation. -/
def coefficientDerivation : Derivation R S S :=
  (localEquiv M S e).toLinearMap.compDer (KaehlerDifferential.D R S)

@[simp] theorem coefficientDerivation_algebraMap (a : A) :
    coefficientDerivation M S e (algebraMap A S a) =
      algebraMap A S (e (KaehlerDifferential.D R A a)) :=
  localEquiv_D_algebraMap M S e a

/-- The usual fraction derivative, expressed inside an arbitrary actual
localization ring. The denominator inverse is `IsLocalization.mk' S 1 s`. -/
theorem localEquiv_D_fraction (a : A) (s : M) :
    localEquiv M S e (KaehlerDifferential.D R S (IsLocalization.mk' S a s)) =
      (IsLocalization.mk' S 1 s) ^ 2 *
        (algebraMap A S (s : A) * algebraMap A S (e (KaehlerDifferential.D R A a)) -
          algebraMap A S a * algebraMap A S (e (KaehlerDifferential.D R A (s : A)))) := by
  let δ := coefficientDerivation M S e
  have ht : IsLocalization.mk' S 1 s * algebraMap A S (s : A) = 1 := by
    rw [IsLocalization.mk'_spec, map_one]
  have hinv := δ.leibniz_of_mul_eq_one ht
  have hpow : (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S (s : A) =
      IsLocalization.mk' S 1 s := by
    rw [pow_two, mul_assoc, ht, mul_one]
  change δ (IsLocalization.mk' S a s) = _
  rw [IsLocalization.mk'_eq_mul_mk'_one, Derivation.leibniz, hinv]
  simp only [δ, coefficientDerivation_algebraMap, smul_eq_mul]
  calc
    _ = (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S (s : A) *
        algebraMap A S (e (KaehlerDifferential.D R A a)) -
      (IsLocalization.mk' S 1 s) ^ 2 * algebraMap A S a *
        algebraMap A S (e (KaehlerDifferential.D R A (s : A))) := by
      rw [hpow]
      ring
    _ = _ := by ring

end Localization

section Functoriality
variable {S T : Type*} [CommRing S] [CommRing T]
  [Algebra R S] [Algebra A S] [IsScalarTower R A S]
  [Algebra R T] [Algebra A T] [IsScalarTower R A T]
  [Algebra S T] [IsScalarTower A S T] [IsScalarTower R S T]

/-- Functoriality of the actual universal map, with all scalar structures fixed. -/
theorem universalMap_comp (ω : KaehlerDifferential R A) :
    KaehlerDifferential.map R R S T (KaehlerDifferential.map R R A S ω) =
      KaehlerDifferential.map R R A T ω := by
  have h : (KaehlerDifferential.map R R S T).restrictScalars A ∘ₗ
      KaehlerDifferential.map R R A S = KaehlerDifferential.map R R A T := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map R R S T
      (KaehlerDifferential.map R R A S (KaehlerDifferential.D R A a)) =
        KaehlerDifferential.map R R A T (KaehlerDifferential.D R A a)
    simp only [KaehlerDifferential.map_D, ← IsScalarTower.algebraMap_apply A S T]
  exact LinearMap.congr_fun h ω

/-- Localization transports the original frame through any compatible algebra tower. -/
theorem localizedFrame_naturality (e : KaehlerDifferential R A ≃ₗ[A] A) :
    KaehlerDifferential.map R R S T (localizedFrame S e) = localizedFrame T e :=
  universalMap_comp (e.symm 1)

/-- The coordinate map is compatible with a further localization. -/
theorem localEquiv_naturality (M : Submonoid A) (P : Submonoid A)
    [IsLocalization M S] [IsLocalization P T] (e : KaehlerDifferential R A ≃ₗ[A] A)
    (ω : KaehlerDifferential R S) :
    localEquiv P T e (KaehlerDifferential.map R R S T ω) =
      algebraMap S T (localEquiv M S e ω) := by
  calc
    _ = localEquiv P T e (KaehlerDifferential.map R R S T
        (localEquiv M S e ω • localizedFrame S e)) :=
      congrArg (fun η => localEquiv P T e (KaehlerDifferential.map R R S T η))
        (reconstruction M S e ω)
    _ = localEquiv P T e (algebraMap S T (localEquiv M S e ω) • localizedFrame T e) := by
      rw [map_smul, localizedFrame_naturality]
      rw [IsScalarTower.algebraMap_smul (R := S) (A := T)]
    _ = _ := by rw [map_smul, localEquiv_localizedFrame, smul_eq_mul, mul_one]

/-- Iterating the frame construction gives the actual direct image of the
original frame, for every compatible algebra tower. -/
theorem iteratedFrame_eq (M : Submonoid A) [IsLocalization M S]
    (e : KaehlerDifferential R A ≃ₗ[A] A) :
    localizedFrame T (localEquiv M S e) = localizedFrame T e := by
  change KaehlerDifferential.map R R S T ((localEquiv M S e).symm 1) = _
  rw [localEquiv_symm_one, localizedFrame_naturality]

/-- Direct and iterated localization yield the same actual coefficient map. -/
theorem iteratedLocalEquiv_eq (M : Submonoid A) (N : Submonoid S) (P : Submonoid A)
    [IsLocalization M S] [IsLocalization N T] [IsLocalization P T]
    (e : KaehlerDifferential R A ≃ₗ[A] A) :
    localEquiv N T (localEquiv M S e) = localEquiv P T e := by
  ext ω
  calc
    _ = localEquiv N T (localEquiv M S e)
        (localEquiv P T e ω • localizedFrame T e) :=
      congrArg (localEquiv N T (localEquiv M S e)) (reconstruction P T e ω)
    _ = _ := by
      rw [map_smul, ← iteratedFrame_eq (S := S) (T := T) M e, localEquiv_localizedFrame, smul_eq_mul, mul_one]

end Functoriality

/-- Canonical quotient localization specialization. -/
def localizationEquiv (M : Submonoid A) (e : KaehlerDifferential R A ≃ₗ[A] A) :
    KaehlerDifferential R (Localization M) ≃ₗ[Localization M] Localization M :=
  localEquiv M (Localization M) e

/-- Principal localization specialization used by affine basic opens. -/
def awayEquiv (a : A) (e : KaehlerDifferential R A ≃ₗ[A] A) :
    KaehlerDifferential R (Localization.Away a) ≃ₗ[Localization.Away a] Localization.Away a :=
  localEquiv (Submonoid.powers a) (Localization.Away a) e

#print axioms localEquiv
#print axioms localEquiv_D_algebraMap
#print axioms frame_smul_bijective
#print axioms localizedFrame_naturality
#print axioms localEquiv_D_fraction
#print axioms localEquiv_naturality
#print axioms iteratedLocalEquiv_eq
#print axioms awayEquiv

end CycleQ2GeometricLocalizedDifferentials
end
