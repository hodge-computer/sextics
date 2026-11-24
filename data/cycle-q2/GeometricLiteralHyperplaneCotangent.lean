import Proposal.GeometricLiteralCotangentConnecting

/-!
# The hyperplane twist lifts on the actual ambient deformation

The coordinate frames have transition X_v/X_u on the thick native intersections.
Their logarithmic differentials lift the corresponding closed-fibre Chern cocycle.
This shows why the hyperplane twist contributes zero to the cotangent boundary.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralHyperplaneCotangent

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne CycleQ2FiniteCechConnecting
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeCupSectionValues
  CycleQ2LiteralNativeCotangent CycleQ2LiteralCotangentOrderedLift
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeCupDerivedClass CycleQ2LiteralSheafOneClasses
  CycleQ2LiteralSheafChernKodairaSpencerCup CycleQ2LiteralCotangentShortExact
  CycleQ2LiteralCotangentRestriction

open scoped TensorProduct
open CycleQ2LiteralNativeTransitionUnits CycleQ2LiteralNativeTransitionNaturality
  CycleQ2LiteralNativeCartierTransitions CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2GeometricSquareZeroSplittings
  CycleQ2GeometricAffineOverlap CycleQ2GeometricSquareZeroReducedCotangent

open CycleQ2CechTwoToDerived (app app_res)

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

private theorem coordinateRatio_cocycle (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    coordinateRatio s u v hu hv * coordinateRatio s v w hv hw = coordinateRatio s u w hu hw := by
  have hratio (i j : Vertex) (hi : i ∈ s) (hj : j ∈ s) :
      valueUnit s (coordinateRatio s i j hi hj) = coordinateUnit s j hj / coordinateUnit s i hi :=
    calc
      _ = valueUnit s (coordinateRatio s i j hi hj) * coordinateUnit s i hi * (coordinateUnit s i hi)⁻¹ := by simp
      _ = _ := by rw [coordinateRatio_mul, div_eq_mul_inv]
  have h : valueUnit s (coordinateRatio s u v hu hv * coordinateRatio s v w hv hw) =
      valueUnit s (coordinateRatio s u w hu hw) := by
    rw [map_mul, hratio, hratio, hratio]
    simp only [div_eq_mul_inv]
    calc
      _ = (coordinateUnit s v hv * (coordinateUnit s v hv)⁻¹) *
          (coordinateUnit s w hw * (coordinateUnit s u hu)⁻¹) := by ac_rfl
      _ = _ := by simp
  apply Units.ext
  apply HomogeneousLocalization.val_injective
  exact congrArg (fun e : (ThickCone s)ˣ => (e : ThickCone s)) h

/-- The actual logarithmic differential of the coordinate transition to the kth power. -/
def tensorLog (k : ℕ) (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    NativeCotangent s :=
  (1 : ClosedRing s) ⊗ₜ[ThickRing s] logDifferential (K := ℂ) (coordinateRatio s u v hu hv ^ k)

theorem tensorLog_restrict (k : ℕ) {s t : Finset Vertex} (hst : s ⊆ t)
    (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    nativeTensorRestriction hst (tensorLog k s u v hu hv) = tensorLog k t u v (hst hu) (hst hv) := by
  rw [tensorLog, nativeTensorRestriction_tmul, map_one, differentialMap_logDifferential]
  change (1 : ClosedRing t) ⊗ₜ[ThickRing t] logDifferential (K := ℂ)
    (restrictThickUnit hst (coordinateRatio s u v hu hv ^ k)) = _
  rw [map_pow, coordinateRatio_restrict]
  rfl

theorem tensorLog_cocycle (k : ℕ) (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    tensorLog k s u w hu hw = tensorLog k s u v hu hv + tensorLog k s v w hv hw := by
  let a := coordinateRatio s u v hu hv
  let b := coordinateRatio s v w hv hw
  have hp : coordinateRatio s u w hu hw ^ k = a ^ k * b ^ k :=
    (congrArg (fun x : (ThickRing s)ˣ => x ^ k)
      (coordinateRatio_cocycle s u v w hu hv hw).symm).trans (mul_pow a b k)
  have hlog := (congrArg (logDifferential (K := ℂ)) hp).trans
    (logDifferential_mul (K := ℂ) (a ^ k) (b ^ k))
  exact (congrArg (fun ω : KaehlerDifferential ℂ (ThickRing s) =>
    (1 : ClosedRing s) ⊗ₜ[ThickRing s] ω) hlog).trans (TensorProduct.tmul_add _ _ _)

theorem tensorLog_reduce (k : ℕ) (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    nativeCotangentReduction s (tensorLog k s u v hu hv) =
      logDifferential (K := ℂ) (reduceUnit s (coordinateRatio s u v hu hv ^ k)) := by
  unfold nativeCotangentReduction tensorLog reductionMap
  rw [LinearMap.liftBaseChange_tmul, one_smul]
  exact differentialMap_logDifferential (nativeReductionAlgHom s) _

abbrev restrictedAddSheaf : AbSheaf Surface := cotangentAdditiveComplex.X₂

def thickHyperplaneOne (k : ℕ) : One restrictedAddSheaf cover := fun u v =>
  res restrictedAddSheaf (common_le_pair u v (cover u ⊓ cover v) inf_le_left inf_le_right)
    (nativeTensorToSheaf {u,v} (by simp) (tensorLog k {u,v} u v (by simp) (by simp)))

def hyperplaneOne (k : ℕ) : One differentialAddSheaf cover := fun u v =>
  res differentialAddSheaf (common_le_pair u v (cover u ⊓ cover v) inf_le_left inf_le_right)
    (nativeFormToSheaf {u,v} (by simp) (logDifferential (K := ℂ)
      (reduceUnit {u,v} (coordinateRatio {u,v} u v (by simp) (by simp) ^ k))))

private theorem thickHyperplane_common (k : ℕ) (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (W : Opens Surface) (hW : W ≤ closedOpen s)
    (hU : W ≤ cover u) (hV : W ≤ cover v) :
    edgeValue restrictedAddSheaf cover (thickHyperplaneOne k) u v W hU hV =
      res restrictedAddSheaf hW (nativeTensorToSheaf s hs (tensorLog k s u v hu hv)) := by
  have hst : ({u,v} : Finset Vertex) ⊆ s := by
    simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu hv
  have hr (z : NativeCotangent {u,v}) :
      res restrictedAddSheaf (closedOpen_mono hst) (nativeTensorToSheaf {u,v} (by simp) z) =
        nativeTensorToSheaf s hs (nativeTensorRestriction hst z) :=
    nativeTensorToSheaf_restrict hst (by simp) hs z
  unfold edgeValue thickHyperplaneOne
  rw [res_comp, ← tensorLog_restrict k hst u v (by simp) (by simp), ← hr, res_comp]

theorem thickHyperplane_closed (k : ℕ) : IsOneCocycle restrictedAddSheaf cover (thickHyperplaneOne k) := by
  intro u v w W hu hv hw
  let s : Finset Vertex := {u,v,w}
  have hW : W ≤ closedOpen s := common_le_triple u v w W hu hv hw
  have h (a b : Vertex) (ha : a ∈ s) (hb : b ∈ s) (hA : W ≤ cover a) (hB : W ≤ cover b) :=
    thickHyperplane_common k s (by simp [s]) a b ha hb W hW hA hB
  change edgeValue _ _ _ u w W hu hw = edgeValue _ _ _ u v W hu hv + edgeValue _ _ _ v w W hv hw
  rw [h u w (by simp [s]) (by simp [s]), h u v (by simp [s]) (by simp [s]),
    h v w (by simp [s]) (by simp [s]), tensorLog_cocycle k s u v w (by simp [s]) (by simp [s]) (by simp [s]),
    map_add, map_add]

theorem thickHyperplane_reduces (k : ℕ) :
    mapOne cover cotangentAdditiveComplex.g (thickHyperplaneOne k) = hyperplaneOne k := by
  funext u v
  dsimp only [mapOne, thickHyperplaneOne, hyperplaneOne]
  have hq (z : NativeCotangent {u,v}) :
      app cotangentAdditiveComplex.g (closedOpen {u,v}) (nativeTensorToSheaf {u,v} (by simp) z) =
        nativeFormToSheaf {u,v} (by simp) (nativeCotangentReduction {u,v} z) :=
    nativeTensorToSheaf_reduce {u,v} (by simp) z
  rw [app_res, hq, tensorLog_reduce]
  rfl

theorem hyperplane_closed (k : ℕ) : IsOneCocycle differentialAddSheaf cover (hyperplaneOne k) := by
  rw [← thickHyperplane_reduces]
  exact mapOne_closed cover cotangentAdditiveComplex.g _ (thickHyperplane_closed k)

def hyperplaneClass (k : ℕ) : differentialAddSheaf.H' 1 ⊤ :=
  cechOneClass cover cover_covers (hyperplaneOne k) (hyperplane_closed k)

theorem hyperplaneClass_lift (k : ℕ) :
    (cechOneClass cover cover_covers (thickHyperplaneOne k) (thickHyperplane_closed k)).comp
      (Ext.mk₀ cotangentAdditiveComplex.g) (Nat.add_zero 1) = hyperplaneClass k := by
  rw [cechOneClass_naturality]
  unfold hyperplaneClass
  congr 1
  exact thickHyperplane_reduces k

theorem hyperplaneClass_connecting_zero (k : ℕ) :
    (hyperplaneClass k).comp cotangentAdditiveShortExact.extClass rfl = 0 := by
  rw [← hyperplaneClass_lift, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass,
    Ext.comp_zero]

end CycleQ2LiteralHyperplaneCotangent

end

#print axioms CycleQ2LiteralHyperplaneCotangent.hyperplaneClass_connecting_zero
