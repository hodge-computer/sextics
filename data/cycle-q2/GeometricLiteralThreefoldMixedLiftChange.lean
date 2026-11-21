import Proposal.GeometricThreefoldMixedRestriction

/-!
# The vertex correction on a projective overlap of the moving curve

A pair of actual normalized test lifts has a common ambient tangent on the
intersection. Contracting its oriented three-form with that tangent and
the same transverse motion vector gives the vertex correction in either
coordinate system.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section
namespace CycleQ2LiteralThreefoldMixedLiftChange

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldTangentCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldLiftTransition CycleQ2LiteralThreefoldTriangleLifts
  CycleQ2LiteralThreefoldTangentOverlap CycleQ2ThreefoldMixedCurveForm
  CycleQ2LiteralThreefoldSurfaceNormal CycleQ2LiteralThreefoldMixedChartChange
  CycleQ2LiteralThreefoldNativeMixedEdge CycleQ2LiteralThreefoldTestGauge CycleQ2LiteralThreefoldTestEdges

section Vertex

variable {U C : Type} [CommRing U] [CommRing C] [Algebra ℂ U] [Algebra ℂ C]
  [Algebra U C] [IsScalarTower ℂ U C] {i : Fin 4}

private abbrev ρ := IsScalarTower.toAlgHom ℂ U C

/-- The vertex correction with its actual lift-difference vector, leaving the
second argument as an independent ambient motion on the overlap. -/
def vertexMixed (a : T i →ₐ[ℂ] U) (x y : Lift i C) (hx : LiesOver x (ρ.comp a))
    (hy : LiesOver y (ρ.comp a)) (v : Derivation ℂ U C) : KaehlerDifferential ℂ C := by
  letI := a.toRingHom.toAlgebra
  letI : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  letI := ((ρ (U := U) (C := C)).comp a).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom ((ρ (U := U) (C := C)).comp a)
  letI : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  exact mixed (tangent x y hx hy) (v.compAlgebraMap (T i)) (orientedVolume i)

private theorem vertexMixed_jet (a : T i →ₐ[ℂ] U) (x y : Lift i C) (hx : LiesOver x (ρ.comp a))
    (hy : LiesOver y (ρ.comp a)) (v : Derivation ℂ U C)
    (z : U →ₐ[ℂ] Jet C) (h₀ : ∀ b, (z b).fst = algebraMap U C b)
    (hz : z.comp a = tangentPoint x y (fun b => (hx b).trans (hy b).symm)) :
    vertexMixed a x y hx hy v = chartMixed a (jetDerivation z h₀) v := by
  let := a.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  let := ((ρ (U := U) (C := C)).comp a).toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom ((ρ (U := U) (C := C)).comp a)
  let : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  apply congrArg (fun d : Derivation ℂ (T i) C => mixed d (v.compAlgebraMap (T i)) (orientedVolume i))
  ext r
  exact congrArg TrivSqZeroExt.snd (AlgHom.congr_fun hz r).symm

omit [Algebra U C] [IsScalarTower ℂ U C] in
private theorem aeval_mapLift (g : U →ₐ[ℂ] C) (x : Lift i U) (p : CycleQ2LiteralAbelJacobiMovingNormal.P) :
    aeval (mapLift g x).x p = jetMap g (aeval x.x p) := by
  have h : aeval (mapLift g x).x = (jetMap g).comp (aeval x.x) := by
    apply MvPolynomial.algHom_ext
    intro b
    simpa only [AlgHom.comp_apply, aeval_X] using (show (mapLift g x).x b = jetMap g (x.x b) from rfl)
  exact AlgHom.congr_fun h p

/-- The ambient two-form uses the same specialized lift difference as the
vertex correction formed from the lifts on the curve coefficient ring. -/
theorem value_vertexMixed
    (a : T i →ₐ[ℂ] U) (x y : Lift i U) (hx : LiesOver x a) (hy : LiesOver y a)
    (x' y' : Lift i C) (hx' : LiesOver x' (ρ.comp a)) (hy' : LiesOver y' (ρ.comp a))
    (ex : mapLift ρ x = x') (ey : mapLift ρ y = y') (v : Derivation ℂ U C) :
    contractRestrict v (value x y (fun b => (hx b).trans (hy b).symm)) =
      vertexMixed a x' y' hx' hy' v := by
  subst x'
  subst y'
  let := a.toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) U := IsScalarTower.of_algHom a
  let := ((ρ (U := U) (C := C)).comp a).toRingHom.toAlgebra
  let : IsScalarTower ℂ (T i) C := IsScalarTower.of_algHom ((ρ (U := U) (C := C)).comp a)
  let : IsScalarTower (T i) U C := IsScalarTower.of_algebraMap_eq' rfl
  rw [value_as_along a x y hx hy]
  refine (CycleQ2ThreefoldMixedWedge.two_step_covector (liftCovector a x y hx hy) v (orientedVolume i)).trans ?_
  apply congrArg (fun d : Derivation ℂ (T i) C => mixed d (v.compAlgebraMap (T i)) (orientedVolume i))
  ext r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  change covectorAlong (liftCovector a x y hx hy) (q i p) = tangent _ _ hx' hy' (q i p)
  rw [covectorAlong_apply, liftCovector_D, tangent_mk, aeval_mapLift, aeval_mapLift, map_sub]
  rfl

end Vertex

attribute [local instance] sourceFixedAlgebra sourceFixedTower sourceFixedLocalization

/-- A chart point and an invertible projective coordinate alone determine the
coefficient action of the ambient overlap and the unique extension of its vector. -/
theorem overlap_vector_of_unit {C : Type} [CommRing C] [Algebra ℂ C] (i : Fin 4) (k : Fin 3)
    [Algebra (T i) C] [IsScalarTower ℂ (T i) C] (v : Derivation ℂ (T i) C)
    (h : IsUnit (algebraMap (T i) C (q i (X (some k))))) :
    let f := overlapLift i k (IsScalarTower.toAlgHom ℂ (T i) C) h
    letI := f.toRingHom.toAlgebra
    letI : IsScalarTower ℂ (FixedOverlap i k) C := IsScalarTower.of_algHom f
    letI : IsScalarTower (T i) (FixedOverlap i k) C := IsScalarTower.of_algebraMap_eq
      (fun a => (overlapLift_source i k (IsScalarTower.toAlgHom ℂ (T i) C) h a).symm)
    ∃! u : Derivation ℂ (FixedOverlap i k) C, u.compAlgebraMap (T i) = v := by
  let f := overlapLift i k (IsScalarTower.toAlgHom ℂ (T i) C) h
  let := f.toRingHom.toAlgebra
  let : IsScalarTower ℂ (FixedOverlap i k) C := IsScalarTower.of_algHom f
  let : IsScalarTower (T i) (FixedOverlap i k) C := IsScalarTower.of_algebraMap_eq
    (fun a => (overlapLift_source i k (IsScalarTower.toAlgHom ℂ (T i) C) h a).symm)
  exact existsUnique_overlap_vector i k v

variable {C : Type} [CommRing C] [Algebra ℂ C]
  (i : Fin 4) (k : Fin 3) [Algebra (FixedOverlap i k) C] [IsScalarTower ℂ (FixedOverlap i k) C]

/-- Projective normalization of both lifts preserves the actual vertex
correction, including the transverse moving-curve slot. -/
theorem vertexMixed_normalizes {x y : Lift i C} {x' y' : Lift (i.succAbove k) C}
    (hx : LiesOver x (ρ.comp (sourceMap i k))) (hy : LiesOver y (ρ.comp (sourceMap i k)))
    (hx' : LiesOver x' (ρ.comp (fixedTargetMap i k))) (hy' : LiesOver y' (ρ.comp (fixedTargetMap i k)))
    (hnx : Normalizes x x') (hny : Normalizes y y') (v : Derivation ℂ (FixedOverlap i k) C) :
    vertexMixed (fixedTargetMap i k) x' y' hx' hy' v = vertexMixed (sourceMap i k) x y hx hy v := by
  obtain ⟨u,hu,rfl⟩ := hnx
  obtain ⟨u',hu',rfl⟩ := hny
  let h := fun a => (hx a).trans (hy a).symm
  obtain ⟨z,h',hs,ht⟩ := exists_overlap_jet i k x y h u u' hu hu'
  have h₀ : ∀ b, (z b).fst = algebraMap (FixedOverlap i k) C b := by
    let f := (TrivSqZeroExt.fstHom ℂ C C).comp z
    have hf : f.toRingHom = algebraMap (FixedOverlap i k) C := by
      apply IsLocalization.ringHom_ext (Submonoid.powers (q i (X (some k))))
      apply RingHom.ext
      intro b
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective b
      change ((z.comp (sourceMap i k)) (q i p)).fst = (ρ.comp (sourceMap i k)) (q i p)
      rw [hs, tangentPoint_mk]
      exact eval_fst x _ hx p
    exact RingHom.congr_fun hf
  exact (vertexMixed_jet _ _ _ hx' hy' v z h₀ ht).trans
    ((CycleQ2ThreefoldMixedRestriction.chartMixed_change i k (jetDerivation z h₀) v).trans (vertexMixed_jet _ x y hx hy v z h₀ hs).symm)

omit [Algebra (FixedOverlap i k) C] [IsScalarTower ℂ (FixedOverlap i k) C] in
/-- The same equality after pulling the ambient edge to any intermediate
coefficient ring before contraction by its curve-valued vector. -/
theorem nativeEdge_restrict_vertexMixed {U : Type} [CommRing U] [Algebra ℂ U]
    [Algebra U C] [IsScalarTower ℂ U C] (g : FixedOverlap i k →ₐ[ℂ] U) (v : Derivation ℂ U C) :
    contractRestrict v (CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap g 2 (nativeEdge i k)) =
      vertexMixed (g.comp (fixedTargetMap i k)) (normalizedLift i k (ρ.comp g))
        (canonical _ (ρ.comp (g.comp (fixedTargetMap i k)))) (normalizedLift_fst i k (ρ.comp g))
        (canonical_liesOver _ _) v := by
  rw [nativeEdge_restrict]
  let a := g.comp (fixedTargetMap i k)
  exact value_vertexMixed a (normalizedLift i k g) (canonical _ a)
    (normalizedLift_fst i k g) (canonical_liesOver _ _) _ _
    (normalizedLift_fst i k (ρ.comp g)) (canonical_liesOver _ _)
    (mapLift_normalized i k g ρ) (mapLift_canonical ρ _ a) v

/-- The original native ambient test edge, contracted before restricting the
transverse normal, is precisely the normalized vertex expression in curve
coefficients. -/
theorem nativeEdge_vertexMixed (v : Derivation ℂ (FixedOverlap i k) C) :
    contractRestrict v (nativeEdge i k) = vertexMixed (fixedTargetMap i k)
      (normalizedLift i k ρ) (canonical _ (ρ.comp (fixedTargetMap i k)))
      (normalizedLift_fst i k ρ) (canonical_liesOver _ _) v := by
  let e := AlgHom.id ℂ (FixedOverlap i k)
  let a := fixedTargetMap i k
  let x := normalizedLift i k e
  let y := canonical _ a
  exact value_vertexMixed a x y (normalizedLift_fst i k e) (canonical_liesOver _ _)
    _ _ (normalizedLift_fst i k ρ) (canonical_liesOver _ _)
    (mapLift_normalized i k e ρ) (mapLift_canonical ρ _ a) v

end CycleQ2LiteralThreefoldMixedLiftChange
end

#print axioms CycleQ2LiteralThreefoldMixedLiftChange.overlap_vector_of_unit
#print axioms CycleQ2LiteralThreefoldMixedLiftChange.vertexMixed_normalizes

#print axioms CycleQ2LiteralThreefoldMixedLiftChange.nativeEdge_vertexMixed
#print axioms CycleQ2LiteralThreefoldMixedLiftChange.nativeEdge_restrict_vertexMixed
