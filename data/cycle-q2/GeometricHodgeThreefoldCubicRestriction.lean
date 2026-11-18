import Proposal.GeometricHodgeThreefoldCubic
import Mathlib.RingTheory.Localization.Module

/-!
# Cubic coordinates on chart intersections

Localize the weight-one affine base coordinates on a weight-one chart.
The original powers of the weight-two root still form a basis. The ordinary
localization maps for inclusions of multiplicative sets act on each of the
three coefficients by the corresponding restriction of base functions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2GeometricHodgeThreefoldCubic

open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)
  (h : IsUnit (φ vertexCoefficient))

abbrev Stage := AdjoinRoot (cubic φ i h)
abbrev AwayBase (S : Submonoid (Base R)) := Localization S
abbrev AwayStage (S : Submonoid (Base R)) :=
  Localization (Algebra.algebraMapSubmonoid (Stage φ i h) S)

variable (S T : Submonoid (Base R))

def localizedBasis [Nontrivial R] : Module.Basis (Fin 3) (AwayBase S) (AwayStage φ i h S) :=
  (basis φ i h).localizationLocalization (AwayBase S) S (AwayStage φ i h S)

theorem localizedBasis_apply [Nontrivial R] (j : Fin 3) :
    localizedBasis φ i h S j =
      algebraMap (Stage φ i h) (AwayStage φ i h S) ((AdjoinRoot.root (cubic φ i h)) ^ j.val) := by
  rw [← basis_apply φ i h j]
  exact Module.Basis.localizationLocalization_apply _ _ _ _ _

variable {S T}

/-- The images of the original denominators are units on a smaller affine open. -/
abbrev Inverts {A : Type} [CommRing A] (U V : Submonoid A) :=
  ∀ u : U, IsUnit (algebraMap A (Localization V) u.val)

theorem inverts_of_dvd {A : Type} [CommRing A] {a b : A} (h : a ∣ b) :
    Inverts (Submonoid.powers a) (Submonoid.powers b) := by
  have hu : IsUnit (algebraMap A (Localization.Away b) a) :=
    isUnit_of_dvd_unit (map_dvd (algebraMap A (Localization.Away b)) h)
      (IsLocalization.Away.algebraMap_isUnit b)
  rintro ⟨_, n, rfl⟩
  simpa only [map_pow] using hu.pow n

/-- The canonical restriction of a localized ring. -/
def extend {A : Type} [CommRing A] {U V : Submonoid A} (b : Inverts U V) :
    Localization U →+* Localization V :=
  IsLocalization.lift (M := U) (g := algebraMap A (Localization V)) b

@[simp] theorem extend_base {A : Type} [CommRing A] {U V : Submonoid A} (b : Inverts U V) (a : A) :
    extend b (algebraMap A (Localization U) a) = algebraMap A (Localization V) a :=
  IsLocalization.lift_eq _ _

private theorem stageInverts (b : Inverts S T) :
    Inverts (Algebra.algebraMapSubmonoid (Stage φ i h) S)
      (Algebra.algebraMapSubmonoid (Stage φ i h) T) := by
  rintro ⟨_, z, hz, rfl⟩
  have hu := (b ⟨z, hz⟩).map (algebraMap (AwayBase T) (AwayStage φ i h T))
  simpa only [← IsScalarTower.algebraMap_apply] using hu

def extendStage (b : Inverts S T) : AwayStage φ i h S →+* AwayStage φ i h T :=
  extend (stageInverts φ i h b)

theorem extendStage_scalar (b : Inverts S T) (a : AwayBase S) :
    extendStage φ i h b (algebraMap _ (AwayStage φ i h S) a) =
      algebraMap _ (AwayStage φ i h T) (extend b a) := by
  have hh : (extendStage φ i h b).comp (algebraMap (AwayBase S) (AwayStage φ i h S)) =
      (algebraMap (AwayBase T) (AwayStage φ i h T)).comp (extend b) := by
    apply IsLocalization.ringHom_ext S
    apply RingHom.ext
    intro z
    simp only [RingHom.comp_apply, extend_base, ← IsScalarTower.algebraMap_apply]
    rw [IsScalarTower.algebraMap_apply (Base R) (Stage φ i h) (AwayStage φ i h S)]
    rw [extendStage, extend_base, ← IsScalarTower.algebraMap_apply]
  exact DFunLike.congr_fun hh a

theorem localizedBasis_restrict [Nontrivial R] (b : Inverts S T) (x : AwayStage φ i h S) (j : Fin 3) :
    (localizedBasis φ i h T).repr (extendStage φ i h b x) j =
      extend b ((localizedBasis φ i h S).repr x j) := by
  let BS := localizedBasis φ i h S
  let BT := localizedBasis φ i h T
  have hs (k : Fin 3) : extendStage φ i h b (BS k) = BT k := by
    rw [show BS k = _ from localizedBasis_apply φ i h S k,
      show BT k = _ from localizedBasis_apply φ i h T k, extendStage, extend_base]
  have he : extendStage φ i h b x = ∑ k : Fin 3, extend b (BS.repr x k) • BT k := by
    conv_lhs => rw [← BS.sum_repr x]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, extendStage_scalar, hs]
  change BT.repr (extendStage φ i h b x) j = extend b (BS.repr x j)
  rw [he]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

end CycleQ2GeometricHodgeThreefoldCubic
end

#print axioms CycleQ2GeometricHodgeThreefoldCubic.localizedBasis_restrict
