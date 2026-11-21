import Proposal.GeometricLiteralThreefoldSurfaceTestLifts

/-!
# Restrictions and chart changes of the native surface test lift

The twelve actual surface lifts commute with restrictions and weighted
coordinate changes. The difference of any pair on the fixed threefold
is the given surface Kodaira–Spencer derivation after every further pullback.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option maxHeartbeats 700000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceTestLifts

open MvPolynomial HomogeneousLocalization CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSquareZeroCoefficientDerivation
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralGradedDeformation CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2IncidenceDehomogenizedChart CycleQ2GeometricIncidenceProj
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2GeometricLiteralDirection CycleQ2GeometricSurfaceAdjunction
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldResidueChartMaps

attribute [local instance] nativeReductionAlgebra thickComplexAlgebra closedComplexAlgebra
  thickComplexSMul closedComplexSMul thickComplexModule closedComplexModule complexReductionTower

private theorem eval_mapLift {S A : Type*} [CommRing S] [Algebra ℂ S] [CommRing A] [Algebra ℂ A]
    {i : Fin 4} (g : S →ₐ[ℂ] A) (x : Lift i S) (p : P) :
    aeval (mapLift g x).x p = jetMap g (aeval x.x p) := by
  have h : aeval (mapLift g x).x = (jetMap g).comp (aeval x.x) := by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, aeval_X, aeval_X]
    rfl
  exact AlgHom.congr_fun h p

theorem mappedSurfaceLift_liesOver {A : Type*} [CommRing A] [Algebra ℂ A]
    (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (a : Fin 4) (ha : Admissible s a)
    (g : ClosedRing s →ₐ[ℂ] A) :
    LiesOver (mapLift g (surfaceLift s v hv a ha)) (g.comp (fixedPoint s v hv)) :=
  fun j => congrArg g (surfaceLift_liesOver s v hv a ha j)

/-- After any further pullback, the intrinsic tangent of the two lifted
points acts on the entire fixed threefold chart by the native surface
Kodaira–Spencer derivation followed by that same pullback. -/
theorem tangent_map_surfaceLift {A : Type*} [CommRing A] [Algebra ℂ A]
    (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (g : ClosedRing s →ₐ[ℂ] A)
    (z : T (chartIndex v)) :
    letI := (g.comp (fixedPoint s v hv)).toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom (g.comp (fixedPoint s v hv))
    tangent (mapLift g (surfaceLift s v hv a ha)) (mapLift g (surfaceLift s v hv b hb))
      (mappedSurfaceLift_liesOver s v hv a ha g) (mappedSurfaceLift_liesOver s v hv b hb g) z =
      g (kodairaSpencer s a b ha hb (fixedPoint s v hv z)) := by
  let _ := (g.comp (fixedPoint s v hv)).toRingHom.toAlgebra
  let _ := IsScalarTower.of_algHom (g.comp (fixedPoint s v hv))
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  change CycleQ2LiteralThreefoldLiftDifference.tangent _ _ _ _ (q (chartIndex v) p) = _
  rw [tangent_mk, eval_mapLift, eval_mapLift]
  change g _ - g _ = _
  rw [← map_sub, surfaceLift_difference]
  rfl

private theorem epsilon_coefficient (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) (x : ThickRing s) :
    epsilonCoefficient s (coefficient s a ha x) = x - projectiveSplitting s a ha (nativeReduction s x) :=
  epsilon_coefficientDerivation (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha)
    (projectiveSplittingAlgHom_reduction s a ha) x

theorem splitJet_restrict {s t : Finset Vertex} (hst : s ⊆ t) (a : Fin 4) (ha : Admissible s a)
    (x : ThickRing s) : jetMap (closedRestrictionAlgHom hst) (splitJet s a ha x) =
      splitJet t a (admissible_mono hst ha) (thickRestriction hst x) := by
  apply TrivSqZeroExt.ext
  · exact (nativeReduction_restrict hst x).symm
  · change closedRestriction hst (coefficient s a ha x) =
      coefficient t a (admissible_mono hst ha) (thickRestriction hst x)
    apply epsilonCoefficient_injective t
    rw [← epsilonCoefficient_restrict, epsilon_coefficient, map_sub,
      projectiveSplitting_restrict, epsilon_coefficient, nativeReduction_restrict]

theorem thickX_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s) (j : Index) :
    thickRestriction hst (thickX s v hv j) = thickX t v (hst hv) j := by
  cases j with
  | none =>
    simp only [thickX, normalizedCoordinate, map_add, map_pow, normalized_restrict]
  | some k => exact normalized_restrict hst v hv _ (coordinate_mem_grade _)

/-- The lifted point restricts on the original twelve-open cover. -/
theorem surfaceLift_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s)
    (a : Fin 4) (ha : Admissible s a) :
    mapLift (closedRestrictionAlgHom hst) (surfaceLift s v hv a ha) =
      surfaceLift t v (hst hv) a (admissible_mono hst ha) := by
  apply lift_ext
  funext j
  change jetMap _ (splitJet s a ha (thickX s v hv j)) = _
  rw [splitJet_restrict, thickX_restrict]
  rfl

theorem fixedPoint_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s) :
    (closedRestrictionAlgHom hst).comp (fixedPoint s v hv) = fixedPoint t v (hst hv) := by
  have h₁ := mappedSurfaceLift_liesOver s v hv v.1 ⟨v.2, hv⟩ (closedRestrictionAlgHom hst)
  rw [surfaceLift_restrict] at h₁
  have h₂ := surfaceLift_liesOver t v (hst hv) v.1 (admissible_mono hst ⟨v.2, hv⟩)
  apply AlgHom.ext
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact (eval_fst _ _ h₁ p).symm.trans (eval_fst _ _ h₂ p)

/-- The homogeneous ratio X_v / X_w, the change-of-chart scale from v to w. -/
def chartScale (s : Finset Vertex) (v w : Vertex) (hw : w ∈ s) : ThickRing s :=
  normalizedCoordinate s w hw (chartIndex v).castSucc

private theorem chartScale_mul_inv (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    (chartScale s v w hw).val * inverseCoordinate s v hv = inverseCoordinate s w hw := by
  rw [chartScale, normalizedCoordinate_val, weight_castSucc, pow_one, chartIndex_castSucc]
  change inverseCoordinate s w hw * coordinateValue s v * _ = _
  rw [← coordinateUnit_value s v hv, mul_assoc]
  change _ * ((coordinateUnit s v hv : ThickCone s) * ↑(coordinateUnit s v hv)⁻¹) = _
  rw [Units.mul_inv, mul_one]

private theorem normalizedCoordinate_change (s : Finset Vertex) (v w : Vertex)
    (hv : v ∈ s) (hw : w ∈ s) (j : Fin 5) :
    normalizedCoordinate s w hw j =
      chartScale s v w hw ^ geometricWeight j * normalizedCoordinate s v hv j := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    normalizedCoordinate_val, normalizedCoordinate_val, ← mul_assoc, ← mul_pow, chartScale_mul_inv]

private theorem linearValues_thick (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) (l : Fin 4) :
    linearValues (chartIndex v) (thickX s v hv) l = normalizedCoordinate s v hv l.castSucc :=
  (eval_linearCoordinate (chartIndex v) (thickX s v hv) l).symm.trans (thickX_linear s v hv l)

theorem chartScale_inverse (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    chartScale s v w hw * linearValues (chartIndex v) (thickX s v hv) (chartIndex w) = 1 := by
  have h := normalizedCoordinate_change s v w hv hw (chartIndex w).castSucc
  rw [weight_castSucc, pow_one, normalized_coordinate_self] at h
  rw [linearValues_thick, ← h]

/-- All four native first-order coordinates obey the genuine weighted change,
including the square factor on the shifted coordinate. -/
theorem thickX_change (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    changedCoordinate (chartIndex v) (chartIndex w) (thickX s v hv) (chartScale s v w hw) =
      thickX s w hw := by
  funext j
  cases j with
  | none =>
    change (normalizedCoordinate s v hv (Fin.last 4) + normalizedCoordinate s v hv (2 : Fin 4).castSucc ^ 2) *
        chartScale s v w hw ^ 2 =
      normalizedCoordinate s w hw (Fin.last 4) + normalizedCoordinate s w hw (2 : Fin 4).castSucc ^ 2
    rw [normalizedCoordinate_change s v w hv hw (Fin.last 4),
      normalizedCoordinate_change s v w hv hw (2 : Fin 4).castSucc, weight_castSucc, weight_last, pow_one]
    ring
  | some k =>
    change linearValues _ (thickX s v hv) _ * chartScale s v w hw = normalizedCoordinate s w hw _
    rw [linearValues_thick, normalizedCoordinate_change s v w hv hw, weight_castSucc, pow_one, mul_comm]

def liftScale (s : Finset Vertex) (v w : Vertex) (hw : w ∈ s) (a : Fin 4) (ha : Admissible s a) :=
  splitJet s a ha (chartScale s v w hw)

theorem liftScale_inverse (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (a : Fin 4) (ha : Admissible s a) :
    liftScale s v w hw a ha * linearValues (chartIndex v) (surfaceLift s v hv a ha).x (chartIndex w) = 1 := by
  have h : linearValues (chartIndex v) (surfaceLift s v hv a ha).x (chartIndex w) =
      splitJet s a ha (linearValues (chartIndex v) (thickX s v hv) (chartIndex w)) := by
    generalize chartIndex w = l
    refine Fin.succAboveCases (chartIndex v) ?_ (fun k => ?_) l
    · simp [linearValues]
    · simp [linearValues, surfaceLift]
  rw [h, liftScale, ← map_mul, chartScale_inverse, map_one]

theorem surfaceLift_change (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (a : Fin 4) (ha : Admissible s a) :
    change (surfaceLift s v hv a ha) (chartIndex w) (liftScale s v w hw a ha)
      (liftScale_inverse s v w hv hw a ha) = surfaceLift s w hw a ha := by
  apply lift_ext
  funext j
  let d := (splitJet s a ha).toRingHom
  change changedCoordinate (chartIndex v) (chartIndex w) (fun l => d (thickX s v hv l))
      (d (chartScale s v w hw)) j = d (thickX s w hw j)
  rw [← congrFun (thickX_change s v w hv hw) j]
  cases j with
  | none =>
    change d (thickX s v hv none) * d (chartScale s v w hw) ^ 2 =
      d (thickX s v hv none * chartScale s v w hw ^ 2)
    rw [map_mul, map_pow]
  | some k =>
    have linear (l : Fin 4) : linearValues (chartIndex v) (fun m => d (thickX s v hv m)) l =
        d (linearValues (chartIndex v) (thickX s v hv) l) := by
      refine Fin.succAboveCases (chartIndex v) ?_ (fun m => ?_) l <;> simp [linearValues]
    change linearValues (chartIndex v) (fun m => d (thickX s v hv m)) ((chartIndex w).succAbove k) *
        d (chartScale s v w hw) = d (linearValues (chartIndex v) (thickX s v hv) ((chartIndex w).succAbove k) *
        chartScale s v w hw)
    rw [linear, map_mul]

theorem surfaceLift_normalizes (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (a : Fin 4) (ha : Admissible s a) :
    Normalizes (surfaceLift s v hv a ha) (surfaceLift s w hw a ha) :=
  ⟨_, liftScale_inverse s v w hv hw a ha, surfaceLift_change s v w hv hw a ha⟩

private theorem reducedScale_inverse (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) :
    nativeReduction s (chartScale s v w hw) * fixedPoint s v hv (q (chartIndex v) (X (some k))) = 1 := by
  have he := chartScale_inverse s v w hv hw
  rw [← h] at he
  simp only [linearValues, Fin.insertNth_apply_succAbove] at he
  rw [fixedPoint_q, aeval_X, ← map_mul, he, map_one]

private theorem reducedCoordinate_unit (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) :
    IsUnit (fixedPoint s v hv (q (chartIndex v) (X (some k)))) :=
  IsUnit.of_mul_eq_one_right _ (reducedScale_inverse s v w hv hw k h)

/-- The genuine reduced map from the fixed threefold overlap to the native
surface intersection carrying both denominators. -/
def fixedOverlapPoint (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) :
    FixedOverlap (chartIndex v) k →ₐ[ℂ] ClosedRing s :=
  overlapLift (chartIndex v) k (fixedPoint s v hv)
    (reducedCoordinate_unit s v w hv hw k h)

theorem fixedOverlapPoint_source (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) :
    (fixedOverlapPoint s v w hv hw k h).comp (sourceMap (chartIndex v) k) = fixedPoint s v hv :=
  AlgHom.ext (overlapLift_source (chartIndex v) k (fixedPoint s v hv) (reducedCoordinate_unit s v w hv hw k h))

theorem fixedOverlapPoint_target (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s)
    (k : Fin 3) (h : (chartIndex v).succAbove k = chartIndex w) (p : P) :
    fixedOverlapPoint s v w hv hw k h (fixedTargetMap (chartIndex v) k (q ((chartIndex v).succAbove k) p)) =
      fixedPoint s w hw (q (chartIndex w) p) := by
  have e : ((fixedOverlapPoint s v w hv hw k h).comp (fixedTargetMap (chartIndex v) k)).comp
      (q ((chartIndex v).succAbove k)) = (fixedPoint s w hw).comp (q (chartIndex w)) := by
    apply MvPolynomial.algHom_ext
    intro l
    change overlapLift _ _ (fixedPoint s v hv) (reducedCoordinate_unit s v w hv hw k h)
      (fixedTargetMap _ _ (q _ (X l))) = _
    rw [overlapLift_target_of_inverse (chartIndex v) k (fixedPoint s v hv) (reducedCoordinate_unit s v w hv hw k h)
      (nativeReduction s (chartScale s v w hw)) (reducedScale_inverse s v w hv hw k h) l, h]
    have hm : (fun b : Index => fixedPoint s v hv (q (chartIndex v) (X b))) =
        fun b => nativeReduction s (thickX s v hv b) := by
      funext b
      rw [fixedPoint_q, aeval_X]
    rw [hm, ← map_changedCoordinate (nativeReduction s) (chartIndex v) (chartIndex w) (thickX s v hv)
      (chartScale s v w hw) l, thickX_change]
    change _ = fixedPoint s w hw (q (chartIndex w) (X l))
    rw [fixedPoint_q, aeval_X]
  exact AlgHom.congr_fun e p

end CycleQ2LiteralThreefoldSurfaceTestLifts
end

#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.surfaceLift_restrict
#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.surfaceLift_change
#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.tangent_map_surfaceLift
#print axioms CycleQ2LiteralThreefoldSurfaceTestLifts.fixedOverlapPoint_target
