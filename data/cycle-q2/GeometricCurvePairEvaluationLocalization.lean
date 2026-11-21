import Proposal.GeometricCurvePairEvaluationSections
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Restriction of the original affine evaluation to a distinguished curve pair

On the principal open the two localized rings are the actual rings of
functions on the moving and reduced affine schemes. Their constant and
velocity components agree by the universal property of localization,
including on inverse coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1300000

noncomputable section
namespace CycleQ2CurvePairEvaluationLocalization

open AlgebraicGeometry CategoryTheory Opposite
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
  CycleQ2GeometricAffineCotangentReduction CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2LiteralAbelJacobiContraction CycleQ2CurvePairEvaluationSections
  CycleQ2GeometricSurfaceFirstOrder

private abbrev Jet (S : Type) := TrivSqZeroExt S S

section LocalFunctions

variable {R : Type} [CommRing R] (s : R) (P : Type) [CommRing P] [Algebra R P]
  [IsLocalization.Away s P]

abbrev openAt := (PrimeSpectrum.basicOpen s : (Spec (CommRingCat.of R)).Opens)

/-- The distinguished-open sections of the original scheme, written in
any of the canonical models of the localization. -/
def localizedSections : P ≃ₐ[R] AffineSections R (openAt s) :=
  IsLocalization.algEquiv (Submonoid.powers s) P (AffineSections R (openAt s))

@[simp] theorem localizedSections_original (r : R) :
    localizedSections s P (algebraMap R P r) = algebraMap R (AffineSections R (openAt s)) r :=
  (localizedSections s P).commutes r

theorem localizedSections_constants [Algebra ℂ R] [Algebra ℂ P] [IsScalarTower ℂ R P] :
    compatible (openAt s) (localizedSections s P).toRingEquiv.toRingHom := by
  intro z
  change localizedSections s P (algebraMap ℂ P z) = _
  rw [IsScalarTower.algebraMap_apply ℂ R P, localizedSections_original]
  rfl

/-- The same localized coordinate functions restricted to a smaller open. -/
abbrev localizedSectionsOn (O : (Spec (CommRingCat.of R)).Opens) (hO : O ≤ openAt s) :
    P →+* AffineSections R O :=
  ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hO).op).hom.comp
    (localizedSections s P).toRingEquiv.toRingHom

theorem localizedSectionsOn_constants [Algebra ℂ R] [Algebra ℂ P] [IsScalarTower ℂ R P]
    (O : (Spec (CommRingCat.of R)).Opens) (hO : O ≤ openAt s) :
    compatible O (localizedSectionsOn s P O hO) := by
  intro z
  refine (congrArg
    (fun x : AffineSections R (openAt s) =>
      ((Spec (CommRingCat.of R)).presheaf.map (homOfLE hO).op) x)
    (localizedSections_constants s P z)).trans ?_
  exact (CategoryTheory.congr_fun
    ((CycleQ2GeometricDifferentialSheaf.coefficientMap (Spec.structureSheaf R)
      (affineCoefficient R)).naturality (homOfLE hO).op) z).symm

end LocalFunctions

private def jetHom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (d : R →+ S)
    (h₁ : d 1 = 0) (h₂ : ∀ a b, d (a*b) = f a * d b + f b * d a) : R →+* Jet S where
  toFun a := (f a,d a)
  map_zero' := TrivSqZeroExt.ext (map_zero f) (map_zero d)
  map_one' := TrivSqZeroExt.ext (map_one f) h₁
  map_add' a b := TrivSqZeroExt.ext (map_add f a b) (map_add d a b)
  map_mul' a b := TrivSqZeroExt.ext (map_mul f a b) ((h₂ a b).trans (by
    change f a * d b + f b * d a = f a * d b + d a * f b
    rw [mul_comm (f b) (d a)]))

variable {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A]
  [IsScalarTower ℂ B A]

private def affineJet (v : Derivation ℂ B A) : B →+* Jet A :=
  jetHom (algebraMap B A) v.toLinearMap.toAddMonoidHom v.map_one_eq_zero
    (fun x y => by
      change v (x*y) = algebraMap B A x * v y + algebraMap B A y * v x
      simpa only [Algebra.smul_def] using v.leibniz x y)

private def sectionJet (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens) :
    AffineSections B U →+* Jet (AffineSections A (reduction B A ⁻¹ᵁ U)) :=
  jetHom ((reduction B A).app U).hom ((velocity v).d (X := op U)) ((velocity v).d_one (op U))
    (fun x y => (velocity v).d_mul x y)

theorem reduction_original (U : (Spec (CommRingCat.of B)).Opens) (r : B) :
    (reduction B A).app U (algebraMap B (AffineSections B U) r) =
      algebraMap A (AffineSections A (reduction B A ⁻¹ᵁ U)) (algebraMap B A r) := by
  let j := reduction B A
  have h := ConcreteCategory.congr_hom (j.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)
    (algebraMap B (AffineSections B ⊤) r)
  have htop := affineMap_original (IsScalarTower.toAlgHom ℂ B A) r
  change (j.app (⊤ : (Spec (CommRingCat.of B)).Opens)) _ = _ at htop
  change _ = (Spec (CommRingCat.of A)).presheaf.map _ (j.app ⊤ _) at h
  rw [htop] at h
  exact h

private theorem velocity_original (v : Derivation ℂ B A) (U : (Spec (CommRingCat.of B)).Opens) (r : B) :
    velocityOn v U (algebraMap B (AffineSections B U) r) =
      algebraMap A (AffineSections A (reduction B A ⁻¹ᵁ U)) (v r) := by
  have h := velocityOn_restrict v (homOfLE (show U ≤ ⊤ from le_top)) (algebraMap B (AffineSections B ⊤) r)
  rw [velocityOn_top] at h
  exact h

variable (s : B) (P Q : Type) [CommRing P] [CommRing Q] [Algebra ℂ P] [Algebra ℂ Q]
  [Algebra B P] [Algebra A Q] [Algebra P Q] [Algebra B Q] [IsScalarTower ℂ B P]
  [IsScalarTower ℂ A Q] [IsScalarTower ℂ P Q] [IsScalarTower B P Q] [IsScalarTower B A Q]
  [IsLocalization.Away s P] [IsLocalization.Away (algebraMap B A s) Q]

private abbrev U := openAt s
private abbrev V := reduction B A ⁻¹ᵁ openAt s
private abbrev φ := (localizedSections s P).toRingEquiv.toRingHom
private abbrev ψ := (localizedSections (algebraMap B A s) Q).toRingEquiv.toRingHom

variable (v : Derivation ℂ B A) (w : Derivation ℂ P Q)
  (hw : ∀ b : B, w (algebraMap B P b) = algebraMap A Q (v b))

include hw in
private theorem local_jets :
    (sectionJet v (U s)).comp (φ s P) = (dualMap (ψ (A := A) s Q)).comp (affineJet w) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers s)
  apply RingHom.ext
  intro b
  apply TrivSqZeroExt.ext
  · change (reduction B A).app (U s) (localizedSections s P (algebraMap B P b)) =
      localizedSections (algebraMap B A s) Q (algebraMap P Q (algebraMap B P b))
    rw [localizedSections_original, ← IsScalarTower.algebraMap_apply B P Q,
      IsScalarTower.algebraMap_apply B A Q, localizedSections_original]
    exact reduction_original _ _
  · change velocityOn v (U s) (localizedSections s P (algebraMap B P b)) =
      localizedSections (algebraMap B A s) Q (w (algebraMap B P b))
    rw [localizedSections_original, hw, localizedSections_original]
    exact velocity_original _ _ _

include hw in
/-- The sheaf evaluation from the original affine chart on its actual
distinguished open agrees with the localized velocity on all ordinary two-forms. -/
theorem localized_evaluation (ω : ⋀[P]^2 (KaehlerDifferential ℂ P)) :
    (evaluation v).val.app (op (U s)) (twoSection (U s) (φ s P) (localizedSections_constants s P) ω) =
      oneSection (V (A := A) s) (ψ (A := A) s Q) (localizedSections_constants (algebraMap B A s) Q)
        (contractRestrict w ω) := by
  let h := local_jets s P Q v w hw
  exact realized_evaluation (U s) _ _ _ _ v w
    (fun x => congrArg TrivSqZeroExt.fst (RingHom.congr_fun h x))
    (fun x => congrArg TrivSqZeroExt.snd (RingHom.congr_fun h x)) ω

include hw in
/-- Evaluation on any subopen of the projective pair, with both systems of
localized coordinate functions restricted by the usual sheaf maps. -/
theorem localized_evaluation_on (O : (Spec (CommRingCat.of B)).Opens) (hO : O ≤ U s)
    (ω : ⋀[P]^2 (KaehlerDifferential ℂ P)) :
    (evaluation v).val.app (op O) (twoSection O (localizedSectionsOn s P O hO)
      (localizedSectionsOn_constants s P O hO) ω) =
      oneSection (reduction B A ⁻¹ᵁ O)
        (localizedSectionsOn (algebraMap B A s) Q _ ((reduction B A).preimage_mono hO))
        (localizedSectionsOn_constants (algebraMap B A s) Q _ ((reduction B A).preimage_mono hO))
        (contractRestrict w ω) := by
  let h := local_jets s P Q v w hw
  apply realized_evaluation
  · intro x
    have e := congrArg TrivSqZeroExt.fst (RingHom.congr_fun h x)
    have h' := ConcreteCategory.congr_hom ((reduction B A).naturality (homOfLE hO).op) (φ s P x)
    exact h'.trans (congrArg ((Spec (CommRingCat.of A)).presheaf.map
      (homOfLE ((reduction B A).preimage_mono hO)).op) e)
  · intro x
    have e := congrArg TrivSqZeroExt.snd (RingHom.congr_fun h x)
    exact (velocityOn_restrict v (homOfLE hO) (φ s P x)).trans
      (congrArg ((Spec (CommRingCat.of A)).presheaf.map (homOfLE ((reduction B A).preimage_mono hO)).op) e)

end CycleQ2CurvePairEvaluationLocalization
end

#print axioms CycleQ2CurvePairEvaluationLocalization.localized_evaluation

#print axioms CycleQ2CurvePairEvaluationLocalization.localized_evaluation_on
