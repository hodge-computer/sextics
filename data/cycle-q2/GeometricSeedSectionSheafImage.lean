import Proposal.GeometricSeedSectionSheafLocal
import Proposal.GeometricSeedSectionSheafGlobal

/-!
# The global evaluation has the original row image on every chart open

The finite dual frame reconstructs an arbitrary section of each original
ideal sheaf from its three literal generators. The unchanged functional
evaluates those generators to the original rows M*t. Thus its image on
every chart subopen is exactly the span of those actual row sections.

The native chart projection of the fixed twisted source is already an
isomorphism on every such subopen. Its surjectivity identifies the image
of the genuine global evaluation with the same original row span. The
curve parameter remains the same complex vector throughout.

Comparison with the structure-map kernel of the already defined
specialized projective curve is a subsequent, distinct step.
Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedSectionSheafImage

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Matrix
open CycleQ2SegreFactorSequence CycleQ2SegreLinkageDuality
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2GeometricSurfaceDehomogenizedCharts CycleQ2SeedSectionInverse
  CycleQ2SeedSectionBalance CycleQ2SeedSectionIdealComparison
  CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafSections
  CycleQ2SeedSectionSheafEvaluation CycleQ2SeedSectionSheafMono
  CycleQ2SeedSectionSheafIdealOverlap CycleQ2SeedSectionSheafLocal
  CycleQ2SeedSectionSheafGlobal

attribute [local instance] CycleQ2SeedSectionSheafSections.patchSectionsCommRing

/-- The literal original matrix rows, with the original complex vector. -/
def sectionRows (t : Fin 3 → ℂ) (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) : Fin 3 → Γ(Surface, V) :=
  fun a => chartSectionMap i V hi
    (((chartFactorData i).matrix *ᵥ
      (fun b => algebraMap ℂ (AffineRing i) (t b))) a)

theorem sectionRows_eq_mulVec (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    sectionRows t i V hi =
      sectionMatrix i V hi *ᵥ (fun b => sectionConstant i V hi (t b)) := by
  funext a
  simp only [sectionRows, Matrix.mulVec, dotProduct, map_sum, map_mul,
    sectionMatrix, sectionConstant, RingHom.mapMatrix_apply]
  rfl

theorem sectionRows_span_eq_map (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    Ideal.span (Set.range (sectionRows t i V hi)) =
      (rowIdeal (chartFactorData i)
        (fun b => algebraMap ℂ (AffineRing i) (t b))).map (chartSectionMap i V hi) := by
  rw [rowIdeal, Ideal.map_span, ← Set.range_comp] <;> rfl

section Generator

variable {R : Type} [CommRing R]

theorem leftGeneratorMap_functional (F : FactorData R) (t : Fin 3 → R) (a : Fin 3) :
    leftGeneratorMap F a ≫ functionalMap F t = scalarMap ((F.matrix *ᵥ t) a) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change sectionFunctional F t (r • leftElement F a) = (F.matrix *ᵥ t) a * r
  rw [map_smul, sectionFunctional_left, smul_eq_mul, mul_comm]

theorem tilde_leftGeneratorMap_functional (F : FactorData R) (t : Fin 3 → R) (a : Fin 3) :
    tilde.map (R := CommRingCat.of R)
        (M := ModuleCat.of R R) (N := ModuleCat.of R F.leftIdeal) (leftGeneratorMap F a) ≫
      tilde.map (R := CommRingCat.of R)
        (M := ModuleCat.of R F.leftIdeal) (N := ModuleCat.of R R) (functionalMap F t) =
      tilde.map (R := CommRingCat.of R)
        (M := ModuleCat.of R R) (N := ModuleCat.of R R) (scalarMap ((F.matrix *ᵥ t) a)) := by
  exact (tilde.map_comp (R := CommRingCat.of R)
    (M := ModuleCat.of R R) (N := ModuleCat.of R F.leftIdeal) (P := ModuleCat.of R R)
    (leftGeneratorMap F a) (functionalMap F t)).symm.trans
      (congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R =>
        tilde.map (R := CommRingCat.of R) (M := ModuleCat.of R R) (N := ModuleCat.of R R) f)
        (leftGeneratorMap_functional F t a))

end Generator

private theorem transportGenerator {C D : Type*} [Category C] [Category D]
    (T : C ⥤ D) {R I : C} {O : D}
    (g : R ⟶ I) (j : I ⟶ R) (L : R ⟶ R) (e : T.obj R ≅ O) (l : O ⟶ O)
    (hgj : g ≫ j = L) (hL : T.map L ≫ e.hom = e.hom ≫ l) :
    (e.inv ≫ T.map g) ≫ (T.map j ≫ e.hom) = l := by
  calc
    _ = e.inv ≫ (T.map g ≫ T.map j) ≫ e.hom := by simp only [Category.assoc]
    _ = e.inv ≫ T.map (g ≫ j) ≫ e.hom := by rw [T.map_comp]
    _ = e.inv ≫ T.map L ≫ e.hom := by rw [hgj]
    _ = e.inv ≫ (e.hom ≫ l) := congrArg (fun k => e.inv ≫ k) hL
    _ = _ := by rw [← Category.assoc, e.inv_hom_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem chartLeftGenerator_evaluation (t : Fin 3 → ℂ) (i : Fin 3) (a : Fin 3) :
    chartLeftGenerator i a ≫ chartEvaluation t i =
      chartScalar i (((chartFactorData i).matrix *ᵥ
        (fun b => algebraMap ℂ (AffineRing i) (t b))) a) := by
  let F := chartFactorData i
  let T := Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom
  let e := Scheme.Modules.restrictUnitIso (coordinateAffineChart 57 1 i.succ).hom
  let v : Fin 3 → AffineRing i := fun b => algebraMap ℂ (AffineRing i) (t b)
  let g : structureModule (Spec (CommRingCat.of (AffineRing i))) ⟶ affineIdeal i :=
    tilde.map (R := CommRingCat.of (AffineRing i))
      (M := ModuleCat.of (AffineRing i) (AffineRing i))
      (N := ModuleCat.of (AffineRing i) F.leftIdeal) (leftGeneratorMap F a)
  let j : affineIdeal i ⟶ structureModule (Spec (CommRingCat.of (AffineRing i))) :=
    tilde.map (R := CommRingCat.of (AffineRing i))
      (M := ModuleCat.of (AffineRing i) F.leftIdeal)
      (N := ModuleCat.of (AffineRing i) (AffineRing i)) (functionalMap F v)
  let L : structureModule (Spec (CommRingCat.of (AffineRing i))) ⟶
      structureModule (Spec (CommRingCat.of (AffineRing i))) :=
    tilde.map (R := CommRingCat.of (AffineRing i))
      (M := ModuleCat.of (AffineRing i) (AffineRing i))
      (N := ModuleCat.of (AffineRing i) (AffineRing i)) (scalarMap ((F.matrix *ᵥ v) a))
  have h := transportGenerator T
    (R := structureModule (Spec (CommRingCat.of (AffineRing i))))
    (I := affineIdeal i) (O := structureModule (Patch i).toScheme)
    g j L e (chartScalar i ((F.matrix *ᵥ v) a))
    (tilde_leftGeneratorMap_functional F v a) (chartScalar_square i ((F.matrix *ᵥ v) a))
  have h₁ : chartLeftGenerator i a ≫ chartEvaluation t i =
      (e.inv ≫ T.map g) ≫ (T.map j ≫ e.hom) := by rfl
  exact h₁.trans h

theorem patchLeftGenerator_evaluation (t : Fin 3 → ℂ) (i : Fin 3) (a : Fin 3) :
    patchLeftGenerator i a ≫ patchEvaluation t i =
      patchScalar i (((chartFactorData i).matrix *ᵥ
        (fun b => algebraMap ℂ (AffineRing i) (t b))) a) := by
  rw [patchLeftGenerator, patchEvaluation, ← Functor.map_comp,
    chartLeftGenerator_evaluation] <;> rfl

/-- The actual chart evaluation, normalized in the original section ring. -/
def evaluationCoordinate (t : Fin 3 → ℂ) (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) :
    Γ(idealPatch i, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) :=
  patchMap (patchEvaluation t i) V hi

theorem generatorSection_evaluation (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (a : Fin 3) :
    evaluationCoordinate t i V hi (generatorSection i V hi a) = sectionRows t i V hi a := by
  have h := congrArg
    (fun f : patchStructure (Patch i) ⟶ patchStructure (Patch i) =>
      patchSectionsEquiv (Patch i) V hi
        (f.app V ((patchSectionsEquiv (Patch i) V hi).symm 1)))
    (patchLeftGenerator_evaluation t i a)
  change evaluationCoordinate t i V hi (generatorSection i V hi a) =
    patchSectionsEquiv (Patch i) V hi
      ((patchScalar i (((chartFactorData i).matrix *ᵥ
        (fun b => algebraMap ℂ (AffineRing i) (t b))) a)).app V
          ((patchSectionsEquiv (Patch i) V hi).symm 1)) at h
  rw [patchScalar_coordinate, RingEquiv.apply_symm_apply, mul_one] at h
  exact h

/-- Injectivity of the literal inclusion lifts its coordinate
reconstruction to an equality of original ideal-sheaf sections. -/
theorem idealSection_reconstruction (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (s : Γ(idealPatch i, V)) :
    s = ∑ q : Fin 3 × Fin 3,
      patchMap (patchFrameCoefficient i q) V hi s • generatorSection i V hi q.1 := by
  apply idealCoordinate_injective i V hi
  rw [map_sum]
  simp only [map_smul, generatorSection_coordinate, smul_eq_mul]
  rw [idealCoordinate_reconstruction]
  apply Finset.sum_congr rfl
  intro q _
  exact mul_comm _ _

theorem evaluationCoordinate_reconstruction (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (s : Γ(idealPatch i, V)) :
    evaluationCoordinate t i V hi s = ∑ q : Fin 3 × Fin 3,
      patchMap (patchFrameCoefficient i q) V hi s * sectionRows t i V hi q.1 := by
  conv_lhs => rw [idealSection_reconstruction i V hi s]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  rw [map_smul, generatorSection_evaluation] <;> rfl

/-- No regularity or image premise is needed for this actual image computation. -/
theorem evaluationCoordinate_range (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    LinearMap.range (evaluationCoordinate t i V hi) =
      Ideal.span (Set.range (sectionRows t i V hi)) := by
  apply le_antisymm
  · rintro _ ⟨s, rfl⟩
    rw [evaluationCoordinate_reconstruction]
    apply Ideal.sum_mem
    intro q _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q.1, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact ⟨generatorSection i V hi a, generatorSection_evaluation t i V hi a⟩

/-- The section map of the already constructed genuine global morphism. -/
def globalEvaluationLinear (t : Fin 3 → ℂ) (V : Surface.Opens) :
    Γ(twistedIdeal, V) →ₗ[Γ(Surface, V)] Γ(Surface, V) :=
  ((globalEvaluation t).val.app (op V)).hom

theorem globalEvaluationLinear_on_patch (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) (s : Γ(twistedIdeal, V)) :
    globalEvaluationLinear t V s =
      evaluationCoordinate t i V hi ((chartProjection i).app V s) :=
  globalEvaluation_on_patch t i V hi s

/-- CLOSED SOURCE-LEVEL ENDPOINT: the actual global evaluation has
exactly the original matrix-row image on every original chart subopen. -/
theorem globalEvaluationLinear_range (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    LinearMap.range (globalEvaluationLinear t V) =
      Ideal.span (Set.range (sectionRows t i V hi)) := by
  have h : LinearMap.range (globalEvaluationLinear t V) =
      LinearMap.range (evaluationCoordinate t i V hi) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      exact ⟨(chartProjection i).app V s,
        (globalEvaluationLinear_on_patch t i V hi s).symm⟩
    · rintro _ ⟨x, rfl⟩
      obtain ⟨s, rfl⟩ := chartProjection_app_surjective i V hi x
      exact ⟨s, globalEvaluationLinear_on_patch t i V hi s⟩
  rw [h, evaluationCoordinate_range]

theorem globalEvaluationLinear_range_matrix (t : Fin 3 → ℂ) (i : Fin 3)
    (V : Surface.Opens) (hi : V ≤ Patch i) :
    LinearMap.range (globalEvaluationLinear t V) =
      Ideal.span (Set.range
        (sectionMatrix i V hi *ᵥ (fun b => sectionConstant i V hi (t b)))) := by
  rw [globalEvaluationLinear_range t i V hi, sectionRows_eq_mulVec]

end CycleQ2SeedSectionSheafImage

end

#print axioms CycleQ2SeedSectionSheafImage.idealSection_reconstruction
#print axioms CycleQ2SeedSectionSheafImage.evaluationCoordinate_range
#print axioms CycleQ2SeedSectionSheafImage.globalEvaluationLinear_range
#print axioms CycleQ2SeedSectionSheafImage.globalEvaluationLinear_range_matrix
