import Proposal.GeometricMarkedProjectionSurvives

/-! The schematic ideal of the proper marked graph on its dense parameter test.
The comparison is the base change of the original relative incidence embedding.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MarkedDenseTestIdeal
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericSmoothCurveGraph
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeCylinder
open CycleQ2LiteralIncidenceRelativeEmbedding (joint joint_toTime joint_toAmbient)
open CycleQ2RelativeGraphClosure (productMap product_square productMap_fst productMap_snd)
abbrev Kpoint := CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint
abbrev T := pullback.snd ambientStructure Kpoint
abbrev β := pullback.fst ambientStructure Kpoint

variable {V : parameterScheme.Opens} {C D : Scheme} (t : Fin 3 → ℂ)
  (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
  (hc : r ≫ structureMap V = c ≫ Kpoint) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ inclusion V)

abbrev denseProduct := pullback (j ≫ c) T
abbrev toProduct := productMap (j ≫ c) c T j rfl

include hc ha in
private theorem time_eq : a ≫ timeMap toRaw V = (j ≫ c) ≫ Kpoint := by
  rw [← inclusion_over V,← Category.assoc,← ha,Category.assoc,hc,Category.assoc]

def relativeProductMap : denseProduct c j ⟶ CycleQ2LiteralIncidenceRelativeEmbedding.Product toRaw V :=
  pullback.lift (pullback.fst (j ≫ c) T ≫ a) (pullback.snd (j ≫ c) T ≫ β) (by
    change (pullback.fst (j ≫ c) T ≫ a) ≫ timeMap toRaw V = (pullback.snd (j ≫ c) T ≫ β) ≫ ambientStructure
    rw [Category.assoc,time_eq c r hc j a ha,pullback.condition_assoc,Category.assoc,
      pullback.condition (f := ambientStructure) (g := Kpoint)])

private theorem relativeProduct_square :
    IsPullback (pullback.fst (j ≫ c) T) (relativeProductMap c r hc j a ha)
      a (pullback.fst (timeMap toRaw V) ambientStructure) := by
  apply IsPullback.of_bot _ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback _ _)
  have h := (IsPullback.of_hasPullback (j ≫ c) T).paste_vert (IsPullback.of_hasPullback ambientStructure Kpoint).flip
  simpa only [relativeProductMap,pullback.lift_snd,time_eq c r hc j a ha] using h

private theorem rawAmbient :
    target V t r c hc ≫ β = toGraph V t r ≫ ambientProjection V t := by
  simp only [target, β, Category.assoc, genericAmbientProjection,
    CycleQ2CoefficientBaseChange.changeMap_fst, toGenericGraph, pullback.lift_fst_assoc]

private theorem test_proj :
    pullback.fst a (curveMap toRaw V t) ≫ j =
      (fromTest V t r j a ha ≫ embeddingGeneric V t r c hc) ≫ pullback.fst c T := by
  rw [Category.assoc,embeddingGeneric_toCurve]
  exact (test_square V t r j a ha).w

def denseEmbedding : TestSurface V t a ⟶ denseProduct c j :=
  (product_square (j ≫ c) c T j rfl).lift (pullback.fst a (curveMap toRaw V t))
    (fromTest V t r j a ha ≫ embeddingGeneric V t r c hc) (test_proj t c r hc j a ha)

private theorem dense_fst : denseEmbedding t c r hc j a ha ≫ pullback.fst (j ≫ c) T = pullback.fst a _ :=
  IsPullback.lift_fst _ _ _ _
private theorem dense_toProduct : denseEmbedding t c r hc j a ha ≫ toProduct c j =
    fromTest V t r j a ha ≫ embeddingGeneric V t r c hc := IsPullback.lift_snd _ _ _ _

theorem dense_relative_square :
    IsPullback (denseEmbedding t c r hc j a ha) (pullback.snd a (curveMap toRaw V t))
      (relativeProductMap c r hc j a ha) (joint toRaw V t) := by
  have he : denseEmbedding t c r hc j a ha ≫ relativeProductMap c r hc j a ha =
      pullback.snd a (curveMap toRaw V t) ≫ joint toRaw V t := by
    apply pullback.hom_ext
    · simp only [Category.assoc,relativeProductMap,pullback.lift_fst,joint_toTime]
      rw [← Category.assoc,dense_fst,pullback.condition]
    · simp only [Category.assoc,relativeProductMap,pullback.lift_snd,joint_toAmbient]
      have hβ : toProduct c j ≫ pullback.snd c T = pullback.snd (j ≫ c) T := productMap_snd ..
      rw [← hβ,← Category.assoc,← Category.assoc,dense_toProduct]
      rw [Category.assoc,Category.assoc,embeddingGeneric_toAmbient_assoc]
      change fromTest V t r j a ha ≫ (toGenericGraph V t r c hc ≫ genericAmbientProjection V t) ≫ β = _
      rw [show (toGenericGraph V t r c hc ≫ genericAmbientProjection V t) ≫ β = _ from rawAmbient t c r hc]
      exact test_to_original_ambient V t r j a ha
  apply IsPullback.of_right _ he (relativeProduct_square c r hc j a ha)
  simpa only [dense_fst,joint_toTime] using IsPullback.of_hasPullback a (curveMap toRaw V t)

/-- The schematic ideal of the same marked proper closure restricts on the dense
parameter test to the pullback of the original relative incidence embedding's ideal. -/
theorem closure_ker_on_dense_test [IsOpenImmersion j] [IsProper c] :
    ((fromTest V t r j a ha).imageι ≫ embeddingGeneric V t r c hc).ker.comap (toProduct c j) =
      (joint toRaw V t).ker.comap (relativeProductMap c r hc j a ha) := by
  let m := fromTest V t r j a ha
  let G := embeddingGeneric V t r c hc
  let d := denseEmbedding t c r hc j a ha
  let J := toProduct c j
  have : IsOpenImmersion m := MorphismProperty.of_isPullback (test_square V t r j a ha) inferInstance
  have : NoetherianSpace (Graph V t r) := CycleQ2LiteralIncidenceGenericModel.noetherian_of_proper (toCurve V t r ≫ c)
  have : NoetherianSpace (TestSurface V t a) := m.isOpenEmbedding.isInducing.noetherianSpace
  have : IsOpenImmersion J := by dsimp only [J,toProduct]; infer_instance
  have hbase : IsPullback d (𝟙 _) J (d ≫ J) := IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hreal := dense_relative_square t c r hc j a ha
  have : IsClosedImmersion (joint toRaw V t) := CycleQ2LiteralIncidenceRelativeEmbedding.joint_isClosedImmersion ..
  have hd : d.ker = (joint toRaw V t).ker.comap (relativeProductMap c r hc j a ha) := by
    dsimp only [d]
    rw [← hreal.isoPullback_hom_fst,Scheme.Hom.ker_comp_of_isIso,
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  change (m.imageι ≫ G).ker.comap J = _
  rw [Scheme.Hom.ker_comp,Scheme.Hom.imageι,Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.map_ker,← dense_toProduct t c r hc j a ha]
  exact (CycleQ2ImmersionImageClosure.imageKer_baseChange hbase).symm.trans hd

end CycleQ2MarkedDenseTestIdeal
#print axioms CycleQ2MarkedDenseTestIdeal.closure_ker_on_dense_test
