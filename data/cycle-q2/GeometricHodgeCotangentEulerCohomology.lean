import Proposal.GeometricHodgeCotangentEulerExact
import Proposal.GeometricOpenCoverAdditiveExactness
import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricCanonicalCechBoundary
import Proposal.GeometricCartierDeformation

/-!
# The actual Euler connecting map generates ambient cotangent H-one

The five negative twists have vanishing ordinary H-one, as proved by
their actual Laurent charts. Finite products preserve this vanishing.
The genuine Euler short exact sequence therefore makes its connecting
map from global O(0) sections onto H-one of the actual Euler kernel.
This concerns the ambient kernel; comparison with intrinsic cotangent
cohomology still requires exactness of the conormal complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 3000
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentEulerCohomology

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace CategoryTheory.Abelian
open CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeCotangentEulerSheaf
open CycleQ2HodgeCotangentEulerExact
open CycleQ2HodgeThreefoldTwist
open CycleQ2GeometricOpenCoverAdditiveExactness (additiveComplex)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv)
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2GenericSexticGradient (CoeffRing)
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
local instance (X : TopCat.{0}) : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance (Y : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)

abbrev Add (M : (threefold φ).Modules) :=
  (SheafOfModules.toSheaf (threefold φ).ringCatSheaf).obj M
abbrev H (M : (threefold φ).Modules) (n : ℕ) := Sheaf.H'.{1} (Add φ M) n ⊤
abbrev addEuler := additiveComplex (eulerSequence φ)

theorem addEuler_shortExact (h : IsUnit (φ vertexCoefficient)) : (addEuler φ).ShortExact := by
  let F := SheafOfModules.toSheaf.{0} (threefold φ).ringCatSheaf
  letI : F.PreservesZeroMorphisms :=
    CycleQ2GeometricSheafLocalExactness.moduleSheaf_toSheaf_preservesZeroMorphisms
      (X := (threefold φ : TopCat)) (threefold φ).ringCatSheaf
  letI : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf.{0} (threefold φ).ringCatSheaf))
  have hs := euler_shortExact φ h
  have he := hs.exact.map_of_mono_of_preservesKernel F hs.mono_f inferInstance
  refine { exact := he, mono_f := ?_, epi_g := ?_ }
  · change Mono (F.map (kernel.ι (eulerMap φ)))
    infer_instance
  · exact euler_additive_epi φ h

def connecting (h : IsUnit (φ vertexCoefficient)) : Γ(twist φ 0,⊤) →+ H φ (ambient φ) 1 :=
  (CycleQ2GeometricIntrinsicCartierCohomology.openConnecting (addEuler_shortExact φ h) 0 ⊤).comp
    (sectionsEquiv (addEuler φ).X₃ ⊤).symm.toAddMonoidHom

def rawHEquiv (n : ℕ) : H φ (raw φ) n ≃+ (∀ j, H φ (pieces φ j) n) := by
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  let Z := fun j => F.obj (pieces φ j)
  let A := freeOpen (⊤ : (threefold φ).Opens)
  let e := PreservesProduct.iso F (pieces φ) ≪≫ (biproduct.isoProduct Z).symm
  exact (((extFunctorObj A n).mapIso e).addCommGroupIsoToAddEquiv).trans
    (Ext.addEquivBiproduct A (biproduct.isBilimit Z) n)

theorem piece_hOne (h : IsUnit (φ vertexCoefficient)) (j : Fin 5) :
    Subsingleton (H φ (pieces φ j) 1) := by
  letI := (CycleQ2HodgeTwistTorusChart.ordinary_vanishing φ h (-(CycleQ2GeometricIncidenceProj.geometricWeight j : ℤ))).1
  exact (CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv _
    (Add φ (pieces φ j)) ⊤ isTerminalTop 1).injective.subsingleton

theorem raw_hOne (h : IsUnit (φ vertexCoefficient)) : Subsingleton (H φ (raw φ) 1) := by
  letI (j : Fin 5) : Subsingleton (H φ (pieces φ j) 1) := piece_hOne φ h j
  exact (rawHEquiv φ 1).injective.subsingleton

/-- Every genuine ambient-kernel H-one class is the Euler boundary of a global section. -/
theorem connecting_surjective (h : IsUnit (φ vertexCoefficient)) : Function.Surjective (connecting φ h) := by
  intro c
  have hr := raw_hOne φ h
  obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (freeOpen (⊤ : (threefold φ).Opens))
    (addEuler_shortExact φ h) c (hr.elim _ _) rfl
  refine ⟨sectionsEquiv (addEuler φ).X₃ ⊤ b, ?_⟩
  change CycleQ2GeometricIntrinsicCartierCohomology.openConnecting (addEuler_shortExact φ h) 0 ⊤
    ((sectionsEquiv (addEuler φ).X₃ ⊤).symm ((sectionsEquiv (addEuler φ).X₃ ⊤) b)) = c
  rw [AddEquiv.symm_apply_apply]
  exact hb

end CycleQ2HodgeCotangentEulerCohomology
end

#print axioms CycleQ2HodgeCotangentEulerCohomology.addEuler_shortExact
#print axioms CycleQ2HodgeCotangentEulerCohomology.raw_hOne
#print axioms CycleQ2HodgeCotangentEulerCohomology.connecting_surjective
