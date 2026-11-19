import Proposal.GeometricHodgeEulerChartBinding
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.AlgebraicGeometry.Pullbacks
import Proposal.GeometricHodgeThreefoldCubicChart
import Proposal.GeometricHodgeThreefoldIncidence
import Proposal.GeometricMonicIncidenceCorrespondence
import Proposal.GeometricUniversalWeightedChart
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Topology.NoetherianSpace
import Proposal.GeometricSmoothImageDimension
import Proposal.GeometricClosedEmbeddingSheafExact
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Proposal.GeometricUniversalWeightedDeRham
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Proposal.GeometricWeightedPoleThree

/-!
# The proper graph has strict support in the native generic threefold

The dense smooth open of the graph has relative dimension two over the
coefficient function field. The native weight-one chart on the ambient
fibre maps dominantly to affine three-space, so a nonempty principal
subopen misses the graph's closed image. Its function point has the
universal weighted residue field. Every complex pushed forward from
the closed support vanishes under the derived stalk at that point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

section

/-! Coefficient base change of the explicit weight-one affine hypersurface chart.
The induced open immersion lies in the scheme-theoretic pullback.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/


noncomputable section
namespace CycleQ2MonicGenericAmbientChartBaseChange

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2HodgeEuler CycleQ2GenericSexticGradient
open scoped TensorProduct

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]

omit [Algebra R S] in
private theorem map_dehom (i : Fin 4) (g : R →+* S) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map g (dehom i p) = dehom i (MvPolynomial.map g p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp only [dehom, aeval_C, MvPolynomial.algebraMap_eq, MvPolynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    by_cases h : j = i.castSucc
    · subst j
      simp only [map_mul, dehom_X_self, map_one, map_X, hp]
    · obtain ⟨t, rfl⟩ := Fin.exists_succAbove_eq h
      simp only [map_mul, dehom_X_succAbove, map_X, hp]

omit [Algebra R S] in
private theorem map_equation (g : R →+* S) (φ : CoeffRing →+* R) (i : Fin 4) :
    MvPolynomial.map g (F φ i) = F (g.comp φ) i := by
  unfold F
  rw [map_dehom, MvPolynomial.map_map]

private abbrev Poly (R : Type) [CommRing R] := MvPolynomial (Fin 4) R

/-- Ground coefficient extension carries the dehomogenized equation to the
dehomogenized equation over the new base. -/
def tensorChartEquiv (φ : CoeffRing →+* R) (i : Fin 4) :
    S ⊗[R] chart φ i ≃ₐ[S] chart ((algebraMap R S).comp φ) i := by
  let e : S ⊗[R] Poly R ≃ₐ[S] Poly S := MvPolynomial.algebraTensorAlgEquiv R S
  let I : Ideal (Poly R) := Ideal.span {F φ i}
  let J : Ideal (Poly S) := Ideal.span {F ((algebraMap R S).comp φ) i}
  let u := Algebra.TensorProduct.includeRight (R := R) (A := S) (B := Poly R)
  have hu : e.toRingHom.comp u.toRingHom = MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change e ((1 : S) ⊗ₜ[R] p) = _
    rw [show e ((1 : S) ⊗ₜ[R] p) = (1 : S) • MvPolynomial.map (algebraMap R S) p from
      MvPolynomial.algebraTensorAlgEquiv_tmul R S 1 p, one_smul]
  have hI : (I.map u.toRingHom).map e.toRingHom = J := by
    rw [Ideal.map_map, hu]
    simp only [I, J, Ideal.map_span, Set.image_singleton, map_equation]
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := R) S (Poly R) S I).trans
    (Ideal.quotientEquivAlg _ J e hI.symm)

theorem congr_fst {X Y Z : Scheme} {f f' : X ⟶ Z} {g g' : Y ⟶ Z}
    (ef : f = f') (eg : g = g') :
    (pullback.congrHom ef eg).hom ≫ pullback.fst f' g' = pullback.fst f g := by
  rw [pullback.congrHom_hom, pullback.lift_fst, Category.comp_id]

section Geometry

variable {A : Type} [CommRing A] [Algebra R A]
  {X : Scheme} (p : X ⟶ Spec (CommRingCat.of R)) (j : Spec (CommRingCat.of A) ⟶ X)
  (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R A)))

/-- The base change of an affine coordinate chart inside the actual fiber. -/
def tensorInclusion :
    Spec (CommRingCat.of (S ⊗[R] A)) ⟶
      pullback (Spec.map (CommRingCat.ofHom (algebraMap R S))) p :=
  (pullbackSpecIso R S A).inv ≫
    (pullback.congrHom (rfl : Spec.map (CommRingCat.ofHom (algebraMap R S)) = _) h.symm).hom ≫
    (pullbackLeftPullbackSndIso _ p j).inv ≫ pullback.fst _ j

instance [IsOpenImmersion j] : IsOpenImmersion (tensorInclusion (S := S) p j h) := by
  unfold tensorInclusion
  infer_instance

theorem tensorInclusion_overBase :
    tensorInclusion (S := S) p j h ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] A))) := by
  simp only [tensorInclusion, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
    congr_fst, pullbackSpecIso_inv_fst']

end Geometry
end CycleQ2MonicGenericAmbientChartBaseChange

#print axioms CycleQ2MonicGenericAmbientChartBaseChange.tensorChartEquiv

end

section

/-! The actual universal threefold over the generic monic coefficient field
contains a three-dimensional affine coordinate open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/


noncomputable section
namespace CycleQ2MonicGenericAmbientChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2GenericSexticGradient
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2IncidenceNormalForm CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment
  CycleQ2LiteralIncidenceCylinderMap CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2MonicGenericAmbientChartBaseChange

open scoped TensorProduct

abbrev Raw := CycleQ2IncidenceTimeCurve.SexticRing
abbrev K := FractionRing MonicRing
abbrev rawPoint : CoeffRing →+* Raw := sexticEval universalPoint

private def rawOpen : Spec (CommRingCat.of (chart rawPoint 0)) ⟶ weightedThreefold universalPoint :=
  (affineChart rawPoint 0).inv ≫ (coordinateOpen rawPoint 0).ι ≫ (nativeIso universalPoint).hom

private instance : IsOpenImmersion rawOpen := by
  unfold rawOpen
  infer_instance

private theorem rawOpen_over : rawOpen ≫ universalAmbientToBase =
    Spec.map (CommRingCat.ofHom (algebraMap Raw (chart rawPoint 0))) := by
  change ((affineChart rawPoint 0).inv ≫ (coordinateOpen rawPoint 0).ι ≫
    (nativeIso universalPoint).hom) ≫ weightedThreefoldToBase universalPoint = _
  rw [Category.assoc, Category.assoc, nativeIso_overBase, affineChart_overBase]

abbrev basePoint : Spec (CommRingCat.of K) ⟶ monicBase :=
  Spec.map (CommRingCat.ofHom (algebraMap MonicRing K))

def genericCoeff : Raw →+* K := (algebraMap MonicRing K).comp rawToMonic

theorem genericCoeff_vertex : (genericCoeff.comp rawPoint) vertexCoefficient = 1 := by
  change genericCoeff ((aeval _ : CoeffRing →ₐ[ℂ] Raw) (X fullSexticLeadingIndex)) = 1
  rw [aeval_X]
  change algebraMap MonicRing K (rawToMonic (X fullSexticLeadingIndex)) = 1
  rw [rawToMonic_X, rawCoordinate_leading, map_one]

private theorem spec_genericCoeff :
    Spec.map (CommRingCat.ofHom genericCoeff) = basePoint ≫ toRaw := by
  change _ = Spec.map (CommRingCat.ofHom (algebraMap MonicRing K)) ≫ Spec.map (CommRingCat.ofHom rawToMonic)
  rw [← Spec.map_comp]
  rfl

@[instance_reducible] private def coefficientAlgebra : Algebra Raw K := genericCoeff.toAlgebra

attribute [local instance] coefficientAlgebra

abbrev genericChartRing := chart (genericCoeff.comp rawPoint) 0

/-- The x₀ coordinate chart after extending the coefficients to the function field. -/
def chartInclusion : Spec (CommRingCat.of genericChartRing) ⟶ ambient (basePoint ≫ toRaw) :=
  (Scheme.Spec.mapIso (tensorChartEquiv (S := K) rawPoint 0).toRingEquiv.toCommRingCatIso.op).hom ≫
    tensorInclusion (S := K) universalAmbientToBase rawOpen rawOpen_over ≫
    (pullback.congrHom spec_genericCoeff (rfl : universalAmbientToBase = _)).hom

instance : IsOpenImmersion chartInclusion := by
  let e : Spec (CommRingCat.of genericChartRing) ≅ Spec (CommRingCat.of (K ⊗[Raw] chart rawPoint 0)) :=
    Scheme.Spec.mapIso (tensorChartEquiv (S := K) rawPoint 0).toRingEquiv.toCommRingCatIso.op
  let f := tensorInclusion (S := K) universalAmbientToBase rawOpen rawOpen_over
  let i := pullback.congrHom spec_genericCoeff (rfl : universalAmbientToBase = _)
  change IsOpenImmersion (e.hom ≫ f ≫ i.hom)
  have : IsOpenImmersion e.hom := inferInstance
  have : IsOpenImmersion f :=
    inferInstanceAs (IsOpenImmersion (tensorInclusion (S := K) universalAmbientToBase rawOpen rawOpen_over))
  have : IsOpenImmersion i.hom := inferInstance
  infer_instance

theorem chartInclusion_overBase :
    chartInclusion ≫ pullback.fst (basePoint ≫ toRaw) universalAmbientToBase =
      Spec.map (CommRingCat.ofHom (algebraMap K genericChartRing)) := by
  change (Spec.map (CommRingCat.ofHom (tensorChartEquiv (S := K) rawPoint 0).toRingHom) ≫
    tensorInclusion (S := K) universalAmbientToBase rawOpen rawOpen_over ≫
    (pullback.congrHom spec_genericCoeff (rfl : universalAmbientToBase = _)).hom) ≫ _ = _
  erw [Category.assoc, Category.assoc, congr_fst, tensorInclusion_overBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (tensorChartEquiv (S := K) rawPoint 0).commutes

end CycleQ2MonicGenericAmbientChart

#print axioms CycleQ2MonicGenericAmbientChart.chartInclusion_overBase

end

section

/-!
# The function field of the generic monic threefold chart

On the integral coefficient slice the equation on the weight-one chart
is the universal monic cubic. Passing to the generic point inverts the
nonzero coefficient polynomials, which preserves its function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2MonicGenericAmbientDomain

open MvPolynomial CycleQ2LiteralIncidenceNormalizedSlice CycleQ2MonicGenericAmbientChart
  CycleQ2MonicWeightedAffineEquation CycleQ2MonicGenericAmbientChartBaseChange
open scoped TensorProduct

abbrev integralChart := CycleQ2HodgeEuler.chart (rawToMonic.comp rawPoint) 0

/-- Separate the weight-two coordinate on the actual chart of the monic slice. -/
def integralChartEquiv : integralChart ≃ₐ[MonicRing] AdjoinRoot universalEquation := by
  apply Ideal.quotientEquivAlg _ _ separate
  rw [Ideal.map_span, Set.image_singleton]
  change Ideal.span {universalEquation} =
    Ideal.span {separate (CycleQ2HodgeEuler.F (rawToMonic.comp rawPoint) 0)}
  have h := congrArg (MvPolynomial.map rawToMonic)
    (CycleQ2GeometricHodgeThreefoldIncidence.equation_eq CycleQ2LiteralIncidenceCylinderMap.universalPoint)
  rw [CycleQ2GeometricHodgeThreefold.equation, MvPolynomial.map_map] at h
  rw [CycleQ2HodgeEuler.F, h, universal_equation, ← chart_eq_dehom, separate_chart_equation]

instance integralChart_domain : IsDomain integralChart :=
  integralChartEquiv.injective.isDomain integralChartEquiv

private theorem coefficient_injective : Function.Injective (algebraMap MonicRing integralChart) := by
  have hi : Function.Injective (algebraMap (Coords MonicRing) (AdjoinRoot universalEquation)) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree (monic _).ne_zero, natDegree]
    decide
  intro x y h
  apply MvPolynomial.C_injective (Fin 3) MonicRing
  apply hi
  exact (integralChartEquiv.commutes x).symm.trans
    ((congrArg integralChartEquiv h).trans (integralChartEquiv.commutes y))

private abbrev denominators := Algebra.algebraMapSubmonoid integralChart (nonZeroDivisors MonicRing)

private theorem denominators_regular : denominators ≤ nonZeroDivisors integralChart :=
  map_le_nonZeroDivisors_of_injective _ coefficient_injective le_rfl

private abbrev genericTensor := K ⊗[MonicRing] integralChart

private def chartBaseChange : genericTensor ≃ₐ[K] genericChartRing :=
  tensorChartEquiv (S := K) (rawToMonic.comp rawPoint) 0

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private def localizationFractionIso {A T : Type} [CommRing A] [IsDomain A] [CommRing T]
    [Algebra A T] (S : Submonoid A) [IsLocalization S T] (hS : S ≤ nonZeroDivisors A) :
    FractionRing T ≃+* FractionRing A := by
  let f := Localization.mapToFractionRing (FractionRing A) S T hS
  let : Algebra T (FractionRing A) := f.toRingHom.toAlgebra
  let : IsScalarTower A T (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : IsFractionRing T (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isLocalization S T (FractionRing A) hS
  exact (FractionRing.algEquiv T (FractionRing A)).toRingEquiv

private theorem localizationFractionIso_apply {A T : Type} [CommRing A] [IsDomain A] [CommRing T]
    [Algebra A T] (S : Submonoid A) [IsLocalization S T] (hS : S ≤ nonZeroDivisors A) (a : A) :
    localizationFractionIso S hS (algebraMap T (FractionRing T) (algebraMap A T a)) =
      algebraMap A (FractionRing A) a := by
  let f := Localization.mapToFractionRing (FractionRing A) S T hS
  let : Algebra T (FractionRing A) := f.toRingHom.toAlgebra
  let : IsScalarTower A T (FractionRing A) :=
    IsScalarTower.of_algebraMap_eq (fun a => (f.commutes a).symm)
  let : IsFractionRing T (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isLocalization S T (FractionRing A) hS
  exact ((FractionRing.algEquiv T (FractionRing A)).commutes (algebraMap A T a)).trans (f.commutes a)

private instance tensor_domain : IsDomain genericTensor :=
  IsLocalization.isDomain_of_le_nonZeroDivisors genericTensor denominators_regular

/-- The affine open inside the actual generic ambient threefold is integral. -/
instance genericChartRing_domain : IsDomain genericChartRing :=
  chartBaseChange.symm.injective.isDomain chartBaseChange.symm

/-- The actual chart map over the inclusion of the monic coefficient ring in its fraction field. -/
def integralToGeneric : integralChart →+* genericChartRing :=
  chartBaseChange.toRingHom.comp (algebraMap integralChart genericTensor)

/-- Inverting the coefficient polynomials preserves the field of rational
functions of the universal monic equation. -/
def functionFieldEquiv :
    FractionRing genericChartRing ≃+* FractionRing (AdjoinRoot universalEquation) := by
  exact (IsFractionRing.ringEquivOfRingEquiv (A := genericChartRing) (B := genericTensor)
    (K := FractionRing genericChartRing) (L := FractionRing genericTensor) chartBaseChange.symm.toRingEquiv).trans
    ((localizationFractionIso (T := genericTensor) denominators denominators_regular).trans
      (IsFractionRing.ringEquivOfRingEquiv (A := integralChart) (B := AdjoinRoot universalEquation)
        integralChartEquiv.toRingEquiv))

/-- On a function already defined over the coefficient ring, the field
identification is the original coordinate change separating the weight-two variable. -/
theorem functionFieldEquiv_integral (a : integralChart) :
    functionFieldEquiv (algebraMap genericChartRing _ (integralToGeneric a)) =
      algebraMap (AdjoinRoot universalEquation) _ (integralChartEquiv a) := by
  have h₁ := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (A := genericChartRing) (B := genericTensor)
    (K := FractionRing genericChartRing) (L := FractionRing genericTensor)
    chartBaseChange.symm.toRingEquiv (integralToGeneric a)
  have h₂ := localizationFractionIso_apply (T := genericTensor) denominators denominators_regular a
  have h₃ := IsFractionRing.ringEquivOfRingEquiv_algebraMap
    (A := integralChart) (B := AdjoinRoot universalEquation)
    (K := FractionRing integralChart) (L := FractionRing (AdjoinRoot universalEquation))
    integralChartEquiv.toRingEquiv a
  unfold functionFieldEquiv
  simp only [RingEquiv.trans_apply]
  rw [h₁]
  have h₄ : chartBaseChange.symm.toRingEquiv (integralToGeneric a) =
      algebraMap integralChart genericTensor a := chartBaseChange.symm_apply_apply _
  rw [h₄, h₂, h₃]
  rfl

end CycleQ2MonicGenericAmbientDomain
end

#print axioms CycleQ2MonicGenericAmbientDomain.integralChartEquiv
#print axioms CycleQ2MonicGenericAmbientDomain.genericChartRing_domain
#print axioms CycleQ2MonicGenericAmbientDomain.functionFieldEquiv

end

section

/-!
# Flat base change of a dominant map from a Noetherian scheme

The images of the finitely many generic points of the source specialize to
every point of the target. A flat morphism lifts each of these generalizations,
so every point of the new base is in the closure of the pullback image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2DominantFlatBaseChange

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u

variable {X Y T : Scheme.{u}} [NoetherianSpace X]

private theorem exists_specialization (j : X ⟶ Y) [IsDominant j] (y : Y) :
    ∃ x : X, j x ⤳ y := by
  have hf : (genericPoints X).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have hd : Dense (j '' genericPoints X) :=
    j.denseRange.dense_image j.continuous (dense_iff_closure_eq.mpr genericPoints.closure)
  have hmem := hd y
  have he : j '' genericPoints X = ⋃ x ∈ genericPoints X, {j x} := by
    ext
    simp [eq_comm]
  rw [he, hf.closure_biUnion] at hmem
  obtain ⟨x, hx⟩ := mem_iUnion.mp hmem
  obtain ⟨_, hy⟩ := mem_iUnion.mp hx
  exact ⟨x, specializes_iff_mem_closure.mpr hy⟩

theorem pullback_snd_dominant (j : X ⟶ Y) (g : T ⟶ Y) [IsDominant j] [Flat g] :
    IsDominant (pullback.snd j g) := by
  refine ⟨fun t => ?_⟩
  obtain ⟨x, hx⟩ := exists_specialization j (g t)
  obtain ⟨t', ht, hg⟩ := Flat.generalizingMap g hx
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback x t' hg.symm
  exact ht.mem_closed isClosed_closure (subset_closure ⟨z, hz⟩)

theorem pullback_fst_dominant (g : T ⟶ Y) (j : X ⟶ Y) [IsDominant j] [Flat g] :
    IsDominant (pullback.fst g j) := by
  have := pullback_snd_dominant j g
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance

end CycleQ2DominantFlatBaseChange

#print axioms CycleQ2DominantFlatBaseChange.pullback_snd_dominant
#print axioms CycleQ2DominantFlatBaseChange.pullback_fst_dominant

end

section

/-!
# The dense smooth surface in the generic proper graph

The marked incidence surface is smooth of relative dimension two. Its
pullback to the coefficient function field stays dense in the proper
graph because the coefficient function field is a flat localization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2GenericProperGraphOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2CoefficientBaseChange
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev surfaceStructure :=
  curveMap toRaw V t ≫ timeMap toRaw V

abbrev graphStructure :=
  timeProjection V t ≫ structureMap V

theorem fromSurface_over :
    fromSurface V t ≫ graphStructure V t = surfaceStructure V t := by
  rw [graphStructure, ← Category.assoc, fromSurface_toTime, Category.assoc, inclusion_over]

abbrev GenericSurface := pullback (surfaceStructure V t) genericPoint

abbrev genericSurfaceStructure : GenericSurface V t ⟶ Spec (CommRingCat.of genericField) :=
  pullback.snd _ _

def graphOpen : GenericSurface V t ⟶ genericCorrespondence V t :=
  changeMap genericPoint (fromSurface V t) (fromSurface_over V t)

theorem graphOpen_square :
    IsPullback (pullback.fst (surfaceStructure V t) genericPoint) (graphOpen V t)
      (fromSurface V t) (pullback.fst (graphStructure V t) genericPoint) := by
  have h₁ : graphOpen V t ≫ toGenericField V t = genericSurfaceStructure V t :=
    changeMap_snd genericPoint (fromSurface V t) (fromSurface_over V t)
  have h₂ : graphOpen V t ≫ pullback.fst (graphStructure V t) genericPoint =
      pullback.fst (surfaceStructure V t) genericPoint ≫ fromSurface V t :=
    changeMap_fst genericPoint (fromSurface V t) (fromSurface_over V t)
  have h : IsPullback (pullback.fst (surfaceStructure V t) genericPoint)
      (graphOpen V t ≫ toGenericField V t) (fromSurface V t ≫ graphStructure V t) genericPoint := by
    rw [h₁, fromSurface_over]
    exact IsPullback.of_hasPullback _ _
  exact h.of_bot h₂.symm (IsPullback.of_hasPullback _ _)

instance : IsOpenImmersion (graphOpen V t) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion) (graphOpen_square V t)
    (inferInstance : IsOpenImmersion (fromSurface V t))

theorem genericPoint_flat : Flat genericPoint := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat genericField (nonZeroDivisors MonicRing))

theorem graphOpen_smooth (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t)) :
    SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) :=
  (smoothOfRelativeDimension_isStableUnderBaseChange 2).of_isPullback
    (IsPullback.of_hasPullback (surfaceStructure V t) genericPoint) hs

theorem graphOpen_dominant (hp : IsProper (graphStructure V t)) :
    IsDominant (graphOpen V t) := by
  let : IsLocallyNoetherian monicBase :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of MonicRing)))
  let : CompactSpace monicBase :=
    inferInstanceAs (CompactSpace (Spec (CommRingCat.of MonicRing)))
  let : IsProper (graphStructure V t) := hp
  let : CompactSpace (Correspondence V t) :=
    QuasiCompact.compactSpace_of_compactSpace (graphStructure V t)
  let : IsNoetherian (Correspondence V t) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (graphStructure V t) }
  let : TopologicalSpace.NoetherianSpace (Surface toRaw V t) :=
    (fromSurface V t).isOpenEmbedding.isInducing.noetherianSpace
  let : Flat genericPoint := genericPoint_flat
  let : Flat (pullback.fst (graphStructure V t) genericPoint) := inferInstance
  let : IsDominant (pullback.snd (fromSurface V t) (pullback.fst (graphStructure V t) genericPoint)) :=
    CycleQ2DominantFlatBaseChange.pullback_snd_dominant _ _
  have h := (graphOpen_square V t).isoPullback_hom_snd
  rw [← h]
  infer_instance

theorem genericSurface_noetherian (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) :
    IsNoetherian (GenericSurface V t) := by
  let : IsProper (graphStructure V t) := hp
  let : IsProper (toGenericField V t) := inferInstance
  let : CompactSpace (genericCorrespondence V t) :=
    QuasiCompact.compactSpace_of_compactSpace (toGenericField V t)
  let : IsLocallyNoetherian (genericCorrespondence V t) :=
    LocallyOfFiniteType.isLocallyNoetherian (toGenericField V t)
  let : IsNoetherian (genericCorrespondence V t) := {}
  let : TopologicalSpace.NoetherianSpace (GenericSurface V t) :=
    (graphOpen V t).isOpenEmbedding.isInducing.noetherianSpace
  let : CompactSpace (GenericSurface V t) := inferInstance
  let : SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) := graphOpen_smooth V t hs
  let : Smooth (genericSurfaceStructure V t) := SmoothOfRelativeDimension.smooth 2 _
  exact
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (genericSurfaceStructure V t) }

theorem dense_projection (hp : IsProper (graphStructure V t)) :
    closure (Set.range (graphOpen V t ≫ genericAmbientProjection V t)) =
      Set.range (genericAmbientProjection V t) := by
  let : IsDominant (graphOpen V t) := graphOpen_dominant V t hp
  have hclosed := genericAmbientProjection_closed V t
  apply le_antisymm
  · refine hclosed.closure_subset_iff.mpr ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨graphOpen V t x, rfl⟩
  · have h := (genericAmbientProjection V t).continuous.range_subset_closure_image_dense
      (graphOpen V t).denseRange
    rw [← Set.range_comp] at h
    exact h

end CycleQ2GenericProperGraphOpen

#print axioms CycleQ2GenericProperGraphOpen.graphOpen_dominant
#print axioms CycleQ2GenericProperGraphOpen.dense_projection

end

section

/-!
# The proper generic graph misses the function point

A smooth surface cannot have dense image in affine three-space. The
first ambient chart is finite over affine three-space by the monic cubic
projection, so the closed image misses an open of that actual chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2GenericProperGraphSupport

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CycleQ2SweptSupport
  CycleQ2LiteralIncidenceRelativeCorrespondence CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericProperGraphOpen
  CycleQ2MonicGenericAmbientChart
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2LiteralIncidenceCylinderMap (universalAmbientToBase)

private def chartAmbientIso : CycleQ2LiteralIncidenceRelativeCylinder.ambient (basePoint ≫ toRaw) ≅
    genericAmbient :=
  (pullbackRightPullbackFstIso toRaw universalAmbientToBase basePoint).symm ≪≫
    pullbackSymmetry genericPoint ambientStructure

/-- The native first affine chart in the same generic ambient fibre used by the proper graph. -/
def chart : Spec (CommRingCat.of genericChartRing) ⟶ genericAmbient :=
  chartInclusion ≫ chartAmbientIso.hom

instance : IsOpenImmersion chart := by
  unfold chart
  infer_instance

theorem chart_over :
    chart ≫ pullback.snd ambientStructure genericPoint =
      Spec.map (CommRingCat.ofHom (algebraMap K genericChartRing)) := by
  have h : chartAmbientIso.hom ≫ pullback.snd ambientStructure genericPoint =
      pullback.fst (basePoint ≫ toRaw) universalAmbientToBase := by
    change ((pullbackRightPullbackFstIso toRaw universalAmbientToBase basePoint).inv ≫
      (pullbackSymmetry genericPoint ambientStructure).hom) ≫
        pullback.snd ambientStructure genericPoint = _
    erw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackRightPullbackFstIso_inv_fst]
  exact (Category.assoc chartInclusion chartAmbientIso.hom _).trans
    ((congrArg (fun a => chartInclusion ≫ a) h).trans chartInclusion_overBase)

open CycleQ2GeometricHodgeThreefoldCubic in
private def cubicChart := chartEquivAdjoinRoot (genericCoeff.comp rawPoint) 0
  (by rw [genericCoeff_vertex]; exact isUnit_one)

private abbrev polynomialRing := MvPolynomial (Fin 3) K

open CycleQ2GeometricHodgeThreefoldCubic in
private def cubicMap : polynomialRing →+* genericChartRing :=
  cubicChart.symm.toRingHom.comp (algebraMap polynomialRing
    (AdjoinRoot (cubic (genericCoeff.comp rawPoint) 0
      (by rw [genericCoeff_vertex]; exact isUnit_one))))

private def chartProjection : Spec (CommRingCat.of genericChartRing) ⟶ affineSpace K 3 :=
  Spec.map (CommRingCat.ofHom cubicMap)

private def polynomialStructure : affineSpace K 3 ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* polynomialRing))

private theorem chartProjection_over :
    chartProjection ≫ polynomialStructure = chart ≫ pullback.snd ambientStructure genericPoint := by
  rw [chart_over, chartProjection, polynomialStructure, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact cubicChart.symm.commutes

open CycleQ2GeometricHodgeThreefoldCubic in
private theorem chartProjection_dense : DenseRange chartProjection := by
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical cubicMap).mpr
  have h : IsUnit ((genericCoeff.comp rawPoint) CycleQ2GeometricHodgeThreefold.vertexCoefficient) := by
    rw [genericCoeff_vertex]
    exact isUnit_one
  have hi : Function.Injective (algebraMap polynomialRing
      (AdjoinRoot (cubic (genericCoeff.comp rawPoint) 0 h))) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree (cubic_monic _ _ _).ne_zero, cubic_natDegree]
    decide
  rw [(RingHom.injective_iff_ker_eq_bot cubicMap).mp (cubicChart.symm.injective.comp hi)]
  exact bot_le

private theorem polynomial_smooth : SmoothOfRelativeDimension 3 polynomialStructure := by
  let P : Algebra.SubmersivePresentation K polynomialRing (Fin 3) Empty :=
    { toPreSubmersivePresentation :=
        { toGenerators := Algebra.Generators.mvPolynomial K (Fin 3)
          relation := Empty.elim
          span_range_relation_eq_ker := by rw [Algebra.Generators.ker_mvPolynomial]; simp
          map := Empty.elim
          map_inj := fun a => a.elim }
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hs : Algebra.IsStandardSmoothOfRelativeDimension 3 K polynomialRing :=
    P.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Fin 3) - Nat.card Empty = 3
      simp [Nat.card_eq_fintype_card])
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 3)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 3).mpr hs)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev projection := genericAmbientProjection V t
private abbrev surfaceProjection := graphOpen V t ≫ projection V t
private abbrev chartOpen := chart.opensRange
private abbrev sourceOpen := surfaceProjection V t ⁻¹ᵁ chartOpen

private def restrictedProjection : (sourceOpen V t).toScheme ⟶ Spec (CommRingCat.of genericChartRing) :=
  (surfaceProjection V t ∣_ chartOpen) ≫ chart.isoOpensRange.inv

private theorem restrictedProjection_fac :
    restrictedProjection V t ≫ chart = (sourceOpen V t).ι ≫ surfaceProjection V t := by
  simp only [restrictedProjection, Category.assoc, Scheme.Hom.isoOpensRange_inv_comp,
    morphismRestrict_ι]

private theorem surfaceProjection_over :
    surfaceProjection V t ≫ pullback.snd ambientStructure genericPoint = genericSurfaceStructure V t := by
  have hg : projection V t ≫ pullback.snd ambientStructure genericPoint = toGenericField V t := by
    unfold projection genericAmbientProjection
    exact CycleQ2CoefficientBaseChange.changeMap_snd _ _ _
  exact (Category.assoc (graphOpen V t) (projection V t) _).trans
    ((congrArg (fun f => graphOpen V t ≫ f) hg).trans
      (CycleQ2CoefficientBaseChange.changeMap_snd _ _ _))

private theorem restrict_dense (h : Set.range chart ⊆ closure (Set.range (surfaceProjection V t))) :
    DenseRange (restrictedProjection V t) := by
  have hr : Set.range (surfaceProjection V t ∣_ chartOpen) =
      (chartOpen.ι) ⁻¹' Set.range (surfaceProjection V t) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨(sourceOpen V t).ι x, ?_⟩
      exact (congrArg (fun f : (sourceOpen V t).toScheme ⟶ genericAmbient => f x)
        (morphismRestrict_ι (surfaceProjection V t) chartOpen)).symm
    · rintro ⟨x, hx⟩
      have hmem : surfaceProjection V t x ∈ chartOpen := by rw [hx]; exact y.property
      let x' : (sourceOpen V t).toScheme := ⟨x, hmem⟩
      refine ⟨x', chartOpen.ι.isOpenEmbedding.injective ?_⟩
      exact (congrArg (fun f : (sourceOpen V t).toScheme ⟶ genericAmbient => f x')
        (morphismRestrict_ι (surfaceProjection V t) chartOpen)).trans hx
  have hd : DenseRange (surfaceProjection V t ∣_ chartOpen) := by
    intro x
    rw [hr, ← chartOpen.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage
      chartOpen.ι.continuous]
    exact h (show chartOpen.ι x ∈ Set.range chart from x.property)
  exact chart.isoOpensRange.inv.surjective.denseRange.comp hd chart.isoOpensRange.inv.continuous

/-- The closed image on the native first chart is proper. -/
theorem chart_not_contained (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) : ¬ Set.range chart ⊆ Set.range (projection V t) := by
  intro h
  have hd := restrict_dense V t (show Set.range chart ⊆ closure (Set.range (surfaceProjection V t)) by
    rw [dense_projection V t hp]
    exact h)
  let g : (sourceOpen V t).toScheme ⟶ affineSpace K 3 := restrictedProjection V t ≫ chartProjection
  let p : (sourceOpen V t).toScheme ⟶ Spec (CommRingCat.of K) :=
    (sourceOpen V t).ι ≫ genericSurfaceStructure V t
  have hs' : SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) := graphOpen_smooth V t hs
  let : SmoothOfRelativeDimension 2 p := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 2 (sourceOpen V t).ι
      (genericSurfaceStructure V t)
  let : IsNoetherian (GenericSurface V t) := genericSurface_noetherian V t hs hp
  let : TopologicalSpace.NoetherianSpace (GenericSurface V t) := inferInstance
  let : TopologicalSpace.NoetherianSpace (sourceOpen V t).toScheme :=
    (sourceOpen V t).ι.isOpenEmbedding.isInducing.noetherianSpace
  let : SmoothOfRelativeDimension 3 polynomialStructure := polynomial_smooth
  have hg : g ≫ polynomialStructure = p :=
    calc
      g ≫ polynomialStructure = restrictedProjection V t ≫ chartProjection ≫ polynomialStructure :=
        Category.assoc _ _ _
      _ = restrictedProjection V t ≫ chart ≫ pullback.snd ambientStructure genericPoint :=
        congrArg (fun a => restrictedProjection V t ≫ a) chartProjection_over
      _ = ((sourceOpen V t).ι ≫ surfaceProjection V t) ≫ pullback.snd ambientStructure genericPoint :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun a => a ≫ pullback.snd ambientStructure genericPoint)
            (restrictedProjection_fac V t))
      _ = p := (Category.assoc _ _ _).trans
        (congrArg (fun a => (sourceOpen V t).ι ≫ a) (surfaceProjection_over V t))
  exact closure_range_ne_univ (X := (sourceOpen V t).toScheme) (Y := affineSpace K 3) 2 3 (by decide) p polynomialStructure (genericPolynomialPoint K 3) g hg
    (denseRange_iff_closure_range.mp
      (chartProjection_dense.comp hd chartProjection.continuous))

/-- The open complement of the image of the proper graph. -/
def complement : genericAmbient.Opens :=
  ⟨(Set.range (projection V t))ᶜ, (genericAmbientProjection_closed V t).isOpen_compl⟩

theorem exists_basic_open (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) :
    ∃ s : genericChartRing, s ≠ 0 ∧
      PrimeSpectrum.basicOpen s ≤ chart ⁻¹ᵁ complement V t := by
  obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Set.not_subset.mp (chart_not_contained V t hs hp)
  let U := chart ⁻¹ᵁ complement V t
  have hx' : x ∈ U := hx
  obtain ⟨_, ⟨s, rfl⟩, hxs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
    U.isOpen x hx'
  refine ⟨s, ?_, hsub⟩
  intro he
  exact (PrimeSpectrum.mem_basicOpen s x).mp hxs (he.symm ▸ x.asIdeal.zero_mem)

end CycleQ2GenericProperGraphSupport

#print axioms CycleQ2GenericProperGraphSupport.chart_not_contained
#print axioms CycleQ2GenericProperGraphSupport.exists_basic_open

end

section

/-!
# Locality of the generic graph support at the rational function point

The function point of the first affine chart belongs to the open
complement of the graph's scheme-theoretic image. A complex supported
on that closed image has zero derived stalk at this point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2GenericGraphFunctionStalk

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2MonicGenericAmbientChart CycleQ2MonicGenericAmbientDomain
  CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericProperGraphOpen
  CycleQ2GenericProperGraphSupport
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2MonicWeightedPrimitiveSpecialization (Fld)
open CycleQ2UniversalWeightedTransfer (separate_universal)

abbrev chartField := FractionRing genericChartRing

/-- The fraction field of the native chart is the field of the universal weighted residue. -/
def weightedFieldEquiv : chartField ≃+* Fld universalAffine := by
  change chartField ≃+* FractionRing (AdjoinRoot (CycleQ2MonicWeightedAffineEquation.separate universalAffine))
  rw [separate_universal]
  exact functionFieldEquiv

def functionPoint : Spec (CommRingCat.of chartField) ⟶ genericAmbient :=
  Spec.map (CommRingCat.ofHom (algebraMap genericChartRing chartField)) ≫ chart

variable {V : parameterScheme.Opens} {t : Fin 3 → ℂ}

theorem functionPoint_mem (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) (x : Spec (CommRingCat.of chartField)) :
    functionPoint x ∈ complement V t := by
  obtain ⟨s, hs', hle⟩ := exists_basic_open V t hs hp
  apply hle
  apply (PrimeSpectrum.mem_basicOpen s _).mpr
  change algebraMap genericChartRing chartField s ∉ x.asIdeal
  have hne : algebraMap genericChartRing chartField s ≠ 0 := fun h =>
    hs' (IsFractionRing.injective genericChartRing chartField (h.trans (map_zero _).symm))
  exact fun h => x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem h hne.isUnit)

def functionPointLift (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) : Spec (CommRingCat.of chartField) ⟶ (complement V t).toScheme :=
  IsOpenImmersion.lift (complement V t).ι functionPoint <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨_, functionPoint_mem hs hp x⟩, rfl⟩

theorem functionPointLift_fac (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) :
    functionPointLift hs hp ≫ (complement V t).ι = functionPoint :=
  IsOpenImmersion.lift_fac _ _ _

abbrev support (V : parameterScheme.Opens) (t : Fin 3 → ℂ) := (projection V t).image
abbrev supportInclusion (V : parameterScheme.Opens) (t : Fin 3 → ℂ) : support V t ⟶ genericAmbient :=
  (projection V t).imageι

theorem support_range (V : parameterScheme.Opens) (t : Fin 3 → ℂ) :
    Set.range (supportInclusion V t) = Set.range (projection V t) := by
  let : IsProper (projection V t) := genericAmbientProjection_proper V t
  change Set.range ((projection V t).ker.subschemeι) = _
  rw [Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
    (genericAmbientProjection_closed V t).closure_eq]

attribute [local instance] HasDerivedCategory.standard

abbrev sheaves (S : Scheme.{0}) := (show TopCat from S).Sheaf AddCommGrpCat.{0}

abbrev stalkAt (x : genericAmbient) : sheaves genericAmbient ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat (show TopCat from genericAmbient) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat x

abbrev functionStalk := stalkAt (functionPoint (default : Spec (CommRingCat.of chartField)))

abbrev supportedComplex (C : CochainComplex (sheaves (support V t)) ℤ) :=
  ((push (supportInclusion V t).base).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

theorem supportedSheaf_stalk_zero {x : genericAmbient} (hx : x ∈ complement V t)
    (F : sheaves (support V t)) :
    IsZero ((stalkAt x).obj ((push (supportInclusion V t).base).obj F)) := by
  let G := (push (supportInclusion V t).base).obj F
  let U : Opens (show TopCat from genericAmbient) := complement V t
  suffices hy : ∀ W ≤ U, Subsingleton (G.obj.obj (op W)) by
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    have hzero (a : TopCat.Presheaf.stalk (C := AddCommGrpCat) G.obj x) : a = 0 := by
      obtain ⟨R, hxR, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.obj a
      let W := R ⊓ U
      have hWR : W ≤ R := inf_le_left
      have hres := (hy W inf_le_right).elim (G.obj.map (homOfLE hWR).op s) 0
      rw [← TopCat.Presheaf.germ_res_apply G.obj (homOfLE hWR) x (show x ∈ W from ⟨hxR, hx⟩),
        hres, map_zero]
    exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  intro W hW
  have hbot : (Opens.map (supportInclusion V t).base).obj W = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro y hy
    have hy' : (supportInclusion V t) y ∈ U := hW hy
    have hmem : (supportInclusion V t) y ∈ Set.range (projection V t) := by
      rw [← support_range V t]
      exact ⟨y, rfl⟩
    exact (hy' hmem).elim
  exact AddCommGrpCat.isZero_iff_subsingleton.mp (F.isTerminalOfEqEmpty hbot).isZero

theorem supportedComplex_stalk_zero {x : genericAmbient} (hx : x ∈ complement V t)
    (C : CochainComplex (sheaves (support V t)) ℤ) :
    IsZero (((stalkAt x).mapHomologicalComplex (ComplexShape.up ℤ)).obj (supportedComplex C)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro n
  exact (supportedSheaf_stalk_zero hx (C.X n)).eq_of_src _ _

theorem derivedStalk_off {x : genericAmbient} (hx : x ∈ complement V t)
    (C : CochainComplex (sheaves (support V t)) ℤ) :
    IsZero ((stalkAt x).mapDerivedCategory.obj (DerivedCategory.Q.obj (supportedComplex C))) :=
  ((stalkAt x).mapDerivedCategoryFactors.app (supportedComplex C)).isZero_iff.mpr
    (DerivedCategory.Q.map_isZero (supportedComplex_stalk_zero hx C))

/-- A morphism that factors through a complex on the swept image is killed by the actual
derived stalk at the function point of the monic threefold. -/
theorem derivedStalk_factor_zero (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t))
    (C : CochainComplex (sheaves (support V t)) ℤ)
    {A B : DerivedCategory (sheaves genericAmbient)}
    (a : A ⟶ DerivedCategory.Q.obj (supportedComplex C))
    (b : DerivedCategory.Q.obj (supportedComplex C) ⟶ B) :
    functionStalk.mapDerivedCategory.map (a ≫ b) = 0 := by
  have hzero := derivedStalk_off (functionPoint_mem hs hp default) C
  rw [Functor.map_comp, hzero.eq_of_tgt (functionStalk.mapDerivedCategory.map a) 0, zero_comp]

open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

local instance (X : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from X)) :=
  HasExt.standard _

/-- The same marked family gives the nonzero fixed-fibre class and a strict closed generic support. -/
theorem exists_supported_marked_family :
    ∃ (t : Fin 3 → ℂ) (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      AlgebraicIndependent ℚ t ∧
      SmoothOfRelativeDimension 2 (surfaceStructure V t) ∧
      IsProper (graphStructure V t) ∧
      Nonempty (support V t) ∧
      (∃ s : genericChartRing, s ≠ 0 ∧ PrimeSpectrum.basicOpen s ≤ chart ⁻¹ᵁ complement V t) ∧
      CycleQ2LiteralAbelJacobiQPullbackDerived.qHodge V t
        CycleQ2LiteralThreefoldTestClass.ambientTestClass ≠ 0 := by
  obtain ⟨t, ht, hreg, _, _, _⟩ := CycleQ2LiteralAbelJacobiTimeFamily.exists_smooth_time_family
  obtain ⟨V, hV, _, hs, _, hcurve, _, hbase⟩ :=
    CycleQ2LiteralIncidenceRelativeCompletion.exists_surjective_completion t ht
  have hp : IsProper (graphStructure V t) := by
    unfold graphStructure
    infer_instance
  have hsurj := CycleQ2LiteralIncidenceRelativeCorrespondence.timeProjection_surjective V t hcurve
  let : Surjective (CycleQ2LiteralIncidenceRelativeCompletion.structureMap V) := hbase
  let : Surjective (graphStructure V t) :=
    ⟨(CycleQ2LiteralIncidenceRelativeCompletion.structureMap V).surjective.comp hsurj⟩
  have hg := (toGenericField V t).surjective
  obtain ⟨x, _⟩ := hg (default : Spec (CommRingCat.of genericField))
  exact ⟨t, V, hV, ht, hs, hp, ⟨(projection V t).toImage x⟩, exists_basic_open V t hs hp,
    CycleQ2LiteralNonzeroSweptRestriction.pull_nonzero t ht hreg V hV⟩

end CycleQ2GenericGraphFunctionStalk

#print axioms CycleQ2GenericGraphFunctionStalk.weightedFieldEquiv
#print axioms CycleQ2GenericGraphFunctionStalk.derivedStalk_factor_zero
#print axioms CycleQ2GenericGraphFunctionStalk.exists_supported_marked_family

end

section

noncomputable section

/-!
# The exact Kähler frame on the native weighted normal open

The original generic chart is a monic cubic over the three free
coordinates. Localizing its normal derivative gives a usual standard
étale algebra. The three polynomial-coordinate differentials then give
an exact Kähler basis on this actual nonempty affine open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NormalWeightedCotangent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
  CycleQ2MonicGenericAmbientChart CycleQ2MonicGenericAmbientDomain
  CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2GenericProperGraphSupport (chart chart_over)

abbrev B := MvPolynomial (Fin 3) K

private theorem vertex_unit : IsUnit ((genericCoeff.comp rawPoint) CycleQ2GeometricHodgeThreefold.vertexCoefficient) := by
  rw [genericCoeff_vertex]
  exact isUnit_one

abbrev polynomial : B[X] := cubic (genericCoeff.comp rawPoint) 0 vertex_unit

private theorem monic : polynomial.Monic := cubic_monic _ _ _

private theorem degree : polynomial.natDegree = 3 := cubic_natDegree _ _ _

abbrev Cubic := AdjoinRoot polynomial

def cubicIso : genericChartRing ≃ₐ[K] Cubic :=
  chartEquivAdjoinRoot (genericCoeff.comp rawPoint) 0 vertex_unit

instance : IsDomain Cubic := cubicIso.symm.injective.isDomain cubicIso.symm

def normal : Cubic := AdjoinRoot.mk polynomial polynomial.derivative

theorem normal_ne_zero : normal ≠ 0 := by
  have hder : polynomial.derivative.natDegree = 2 := by rw [natDegree_derivative, degree]
  have hn : polynomial.derivative ≠ 0 := fun h => by
    have hzero : polynomial.derivative.natDegree = 0 := (congrArg natDegree h).trans natDegree_zero
    exact (by decide : (0 : ℕ) ≠ 2) (hzero.symm.trans hder)
  intro h
  have hd : polynomial ∣ polynomial.derivative :=
    (AdjoinRoot.mk_eq_zero).mp h
  exact monic.not_dvd_of_natDegree_lt hn (by rw [degree, hder]; decide) hd

abbrev A := Localization.Away normal

private def pair : StandardEtalePair B where
  f := polynomial
  monic_f := monic
  g := polynomial.derivative
  cond := ⟨1, 0, 1, by rw [mul_one, mul_zero, add_zero, pow_one]⟩

instance : Algebra.Etale B A :=
  Algebra.Etale.of_equiv pair.equivAwayAdjoinRoot

abbrev coordinate (i : Fin 3) : A := algebraMap B A (MvPolynomial.X i)

def basis : Module.Basis (Fin 3) A Ω[A⁄K] :=
  ((KaehlerDifferential.mvPolynomialBasis K (Fin 3)).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K B A)

theorem basis_apply (i : Fin 3) : basis i = KaehlerDifferential.D K A (coordinate i) := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K B A
  apply e.symm.injective
  change e.symm (e (((KaehlerDifferential.mvPolynomialBasis K (Fin 3)).baseChange A) i)) =
    e.symm (KaehlerDifferential.D K A (algebraMap B A (MvPolynomial.X i)))
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K B A _).symm

/-- The normal chart maps into the original generic projective threefold. -/
def inclusion : Spec (CommRingCat.of A) ⟶ CycleQ2LiteralIncidenceGenericCorrespondence.genericAmbient :=
  Spec.map (CommRingCat.ofHom ((algebraMap Cubic A).comp cubicIso.toRingHom)) ≫ chart

theorem algebraMap_normal_isUnit : IsUnit (algebraMap Cubic A normal) :=
  IsLocalization.Away.algebraMap_isUnit normal

end CycleQ2NormalWeightedCotangent

#print axioms CycleQ2NormalWeightedCotangent.normal_ne_zero
#print axioms CycleQ2NormalWeightedCotangent.basis_apply

end

section

noncomputable section

/-!
# The actual function-field identification is coefficient-linear

The native generic chart and the weighted residue field use the same
coefficient extension. This is checked on the common integral chart
and then on fractions of coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NativeWeightedFieldAlgebra

open CycleQ2MonicGenericAmbientDomain CycleQ2MonicGenericAmbientChart
  CycleQ2MonicGenericAmbientChartBaseChange CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2MonicWeightedAffineEquation CycleQ2GenericGraphFunctionStalk
open CycleQ2UniversalWeightedDeRham (W coefficients)
open CycleQ2GenericWeightedSpatialDenominator (universalAffine)
open CycleQ2UniversalWeightedTransfer (separate_universal)
open CycleQ2MonicWeightedPrimitiveSpecialization (ChartRing fieldValue)
open scoped TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

theorem integralToGeneric_scalar (a : MonicRing) :
    integralToGeneric (algebraMap MonicRing integralChart a) =
      algebraMap K genericChartRing (algebraMap MonicRing K a) := by
  let T := K ⊗[MonicRing] integralChart
  let e : T ≃ₐ[K] genericChartRing :=
    tensorChartEquiv (S := K) (rawToMonic.comp rawPoint) 0
  have h :
      algebraMap integralChart T (algebraMap MonicRing integralChart a) =
        algebraMap K T (algebraMap MonicRing K a) :=
    ((IsScalarTower.algebraMap_apply MonicRing integralChart T a).symm).trans
      (IsScalarTower.algebraMap_apply MonicRing K T a)
  exact (congrArg e h).trans (e.commutes _)

private def quotientEquiv : AdjoinRoot universalEquation ≃ₐ[MonicRing] ChartRing universalAffine :=
  AdjoinRoot.algEquivOfEq MonicRing _ _ separate_universal.symm

private def fractionsEquiv : FractionRing (AdjoinRoot universalEquation) ≃+* W :=
  IsFractionRing.ringEquivOfRingEquiv quotientEquiv.toRingEquiv

def fieldEquiv : chartField ≃+* W := functionFieldEquiv.trans fractionsEquiv

theorem fieldEquiv_integral (a : integralChart) :
    fieldEquiv (algebraMap genericChartRing chartField (integralToGeneric a)) =
      algebraMap (ChartRing universalAffine) W (quotientEquiv (integralChartEquiv a)) := by
  exact (congrArg fractionsEquiv (functionFieldEquiv_integral a)).trans
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap quotientEquiv.toRingEquiv _)

private theorem coeff_value (a : MonicRing) :
    algebraMap K W (algebraMap MonicRing K a) =
      algebraMap (ChartRing universalAffine) W (algebraMap MonicRing (ChartRing universalAffine) a) := by
  change coefficients (algebraMap MonicRing K a) = _
  have h : coefficients (algebraMap MonicRing K a) = fieldValue universalAffine (MvPolynomial.C a) :=
    IsFractionRing.lift_algebraMap _ _
  have hs : separate (MvPolynomial.C a) = Polynomial.C (MvPolynomial.C a) := separate.commutes a
  exact h.trans (congrArg (fun q => algebraMap (ChartRing universalAffine) W
    (AdjoinRoot.mk (separate universalAffine) q)) hs)

theorem fieldEquiv_coefficients :
    fieldEquiv.toRingHom.comp (algebraMap K chartField) = algebraMap K W := by
  apply IsFractionRing.ringHom_ext (A := MonicRing)
  intro a
  change fieldEquiv (algebraMap K chartField (algebraMap MonicRing K a)) = _
  let e := integralChartEquiv.trans quotientEquiv
  calc
    _ = fieldEquiv (algebraMap genericChartRing chartField
        (integralToGeneric (algebraMap MonicRing integralChart a))) := by
      rw [integralToGeneric_scalar, ← IsScalarTower.algebraMap_apply K genericChartRing chartField]
    _ = algebraMap (ChartRing universalAffine) W (e (algebraMap MonicRing integralChart a)) :=
      fieldEquiv_integral _
    _ = _ := (congrArg (algebraMap (ChartRing universalAffine) W) (e.commutes a)).trans
        (coeff_value a).symm

def fieldAlgEquiv : chartField ≃ₐ[K] W :=
  { fieldEquiv with commutes' := RingHom.congr_fun fieldEquiv_coefficients }

end CycleQ2NativeWeightedFieldAlgebra

#print axioms CycleQ2NativeWeightedFieldAlgebra.fieldEquiv_coefficients

end

section

noncomputable section

/-!
# The weighted residue field is the fraction field on the normal open

The normal open is the derivative localization of the cubic chart.
Its actual map to the universal weighted field is linear over the
monic coefficient field and identifies the latter with its fraction field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NativeNormalFunctionField

open CycleQ2NormalWeightedCotangent CycleQ2NativeWeightedFieldAlgebra
  CycleQ2MonicGenericAmbientChart CycleQ2GenericGraphFunctionStalk
open CycleQ2UniversalWeightedDeRham (W)
open scoped nonZeroDivisors

private def cubicToField : Cubic →ₐ[K] W :=
  fieldAlgEquiv.toAlgHom.comp ((Algebra.ofId genericChartRing chartField).restrictScalars K |>.comp cubicIso.symm.toAlgHom)

private theorem cubicMap_injective : Function.Injective cubicToField :=
  fieldAlgEquiv.injective.comp ((IsFractionRing.injective genericChartRing chartField).comp cubicIso.symm.injective)

private theorem normalUnit : IsUnit (cubicToField normal) :=
  isUnit_iff_ne_zero.mpr ((map_ne_zero_iff cubicToField cubicMap_injective).mpr normal_ne_zero)

def toField : A →ₐ[K] W :=
  IsLocalization.Away.liftAlgHom normal (f := cubicToField) normalUnit

theorem toField_algebraMap (x : Cubic) : toField (algebraMap Cubic A x) = cubicToField x :=
  IsLocalization.Away.lift_eq normal normalUnit x

instance : Algebra A W := toField.toRingHom.toAlgebra

instance cubicAlgebra : Algebra Cubic W := cubicToField.toRingHom.toAlgebra

instance : IsScalarTower K A W := IsScalarTower.of_algebraMap_eq (fun x => (toField.commutes x).symm)

instance : IsScalarTower Cubic A W :=
  IsScalarTower.of_algebraMap_eq (fun x => (toField_algebraMap x).symm)

theorem cubicFractionField : IsFractionRing Cubic W := by
  let J : genericChartRing ≃+* Cubic := cubicIso.toRingEquiv
  let : Algebra genericChartRing W := (fieldEquiv.toRingHom.comp (algebraMap genericChartRing chartField)).toAlgebra
  let F : chartField ≃ₐ[genericChartRing] W := {fieldEquiv with commutes' := fun _ => rfl}
  let : IsFractionRing genericChartRing W := IsFractionRing.of_algEquiv F
  apply IsFractionRing.of_ringEquiv_left J.symm
  intro x
  rfl

instance : IsFractionRing A W := by
  let : IsFractionRing Cubic W := cubicFractionField
  apply IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers normal) A W
  exact Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr normal_ne_zero)

/-- The coefficient-preserving map on the chart is the given native
function-point map composed with the fixed field identification. -/
theorem toField_native (x : genericChartRing) :
    toField (algebraMap Cubic A (cubicIso x)) =
      fieldAlgEquiv (algebraMap genericChartRing chartField x) := by
  rw [toField_algebraMap]
  change fieldAlgEquiv (algebraMap genericChartRing chartField (cubicIso.symm (cubicIso x))) = _
  rw [AlgEquiv.symm_apply_apply]

end CycleQ2NativeNormalFunctionField

#print axioms CycleQ2NativeNormalFunctionField.cubicFractionField
#print axioms CycleQ2NativeNormalFunctionField.toField_native

end

section

noncomputable section

/-!
# A regular representative of the weighted source on the normal open

The top exterior power is a line in the derivative-localized chart.
The fraction-field residue has one coordinate in this line. Clearing
that coordinate's denominator gives a regular form on a further
principal open and allows any prescribed nonzero principal constraint.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NativeNormalResidue

open CycleQ2NormalWeightedCotangent CycleQ2NativeNormalFunctionField
  CycleQ2WeightedCoordinateExterior CycleQ2WeightedRationalRestriction
open CycleQ2MonicGenericAmbientChart (K)
open CycleQ2UniversalWeightedDeRham (W sourceForm)

instance : IsDomain A := IsLocalization.isDomain_of_le_nonZeroDivisors A
  (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr normal_ne_zero))

section LiftBasis

variable (T : Type) [CommRing T] [Algebra A T] [Algebra K T] [IsScalarTower K A T]
  [Algebra.FormallyEtale A T]

def liftedBasis : Module.Basis (Fin 3) T Ω[T⁄K] :=
  (basis.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A T)

theorem liftedBasis_apply (i : Fin 3) :
    liftedBasis T i = KaehlerDifferential.D K T (algebraMap A T (coordinate i)) := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A T
  apply e.symm.injective
  change e.symm (e ((basis.baseChange T) i)) = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_apply, basis_apply]
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K A T _).symm

end LiftBasis

instance : Algebra.FormallyEtale A W :=
  Algebra.FormallyEtale.of_isLocalization (Rₘ := W) (nonZeroDivisors A)

abbrev Patch (s : A) := Localization.Away s

instance (s : A) : Algebra.FormallyEtale A (Patch s) :=
  Algebra.FormallyEtale.of_isLocalization (Rₘ := Patch s) (Submonoid.powers s)

private theorem nonzero_field (s : A) (hs : s ≠ 0) : IsUnit (toField s) :=
  isUnit_iff_ne_zero.mpr ((map_ne_zero_iff toField (IsFractionRing.injective A W)).mpr hs)

def evaluatePatch (s : A) (hs : s ≠ 0) : Patch s →ₐ[K] W :=
  IsLocalization.Away.liftAlgHom s (f := toField) (nonzero_field s hs)

theorem evaluatePatch_algebraMap (s : A) (hs : s ≠ 0) (x : A) :
    evaluatePatch s hs (algebraMap A (Patch s) x) = toField x :=
  IsLocalization.Away.lift_eq s (nonzero_field s hs) x

private theorem evaluate_volume (s : A) (hs : s ≠ 0) :
    evaluate (evaluatePatch s hs) 3 (volume (liftedBasis (Patch s))) = volume (liftedBasis W) := by
  let φ := evaluatePatch s hs
  let a : Fin 3 → Patch s := fun i => algebraMap A (Patch s) (coordinate i)
  let b : Fin 3 → W := fun i => algebraMap A W (coordinate i)
  have ha : volume (liftedBasis (Patch s)) =
      exteriorPower.ιMulti (Patch s) 3 (KaehlerDifferential.D K (Patch s) ∘ a) :=
    congrArg (exteriorPower.ιMulti (Patch s) 3) (funext (liftedBasis_apply (Patch s)))
  have hb : exteriorPower.ιMulti W 3 (KaehlerDifferential.D K W ∘ b) = volume (liftedBasis W) :=
    congrArg (exteriorPower.ιMulti W 3) (funext (liftedBasis_apply W)).symm
  have h : φ ∘ a = b := funext fun i => evaluatePatch_algebraMap s hs (coordinate i)
  exact (congrArg (evaluate φ 3) ha).trans ((evaluate_wedge φ 3 a).trans
    ((congrArg (fun c => exteriorPower.ιMulti W 3 (KaehlerDifferential.D K W ∘ c)) h).trans hb))

private theorem inverse_image (s : A) (hs : s ≠ 0) (q : A)
    (hq : IsUnit (algebraMap A (Patch s) q)) :
    evaluatePatch s hs (↑(hq.unit⁻¹) : Patch s) = (toField q)⁻¹ := by
  have h := (evaluatePatch s hs).isUnit_map hq
  have hh : toField q ≠ 0 := isUnit_iff_ne_zero.mp
    ((evaluatePatch_algebraMap s hs q) ▸ h)
  apply (mul_right_cancel₀ hh)
  have hu : (↑(hq.unit⁻¹) : Patch s) * algebraMap A (Patch s) q = 1 := by
    exact (congrArg (fun r : Patch s => (↑(hq.unit⁻¹) : Patch s) * r) hq.unit_spec.symm).trans
      (Units.inv_mul hq.unit)
  rw [← evaluatePatch_algebraMap s hs q, ← map_mul, hu, map_one,
    evaluatePatch_algebraMap s hs q, inv_mul_cancel₀ hh]

/-- The actual universal form has a regular representative on a principal
subopen in any prescribed nonempty principal open of the normal chart. -/
theorem exists_regular_representative (g : A) (hg : g ≠ 0) :
    ∃ q : A, ∃ hs : g * q ≠ 0, ∃ ω : Form K (Patch (g * q)) 3,
      evaluate (evaluatePatch (g * q) hs) 3 ω = sourceForm := by
  obtain ⟨r,hr⟩ := topForm_scalar (liftedBasis W) sourceForm
  obtain ⟨p,q,hq,he⟩ := IsFractionRing.div_surjective A r
  have hq₀ : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq
  let s := g * q
  have hs : s ≠ 0 := mul_ne_zero hg hq₀
  let P := Patch s
  have hu : IsUnit (algebraMap A P q) := by
    have h : IsUnit (algebraMap A P s) := IsLocalization.Away.algebraMap_isUnit s
    change IsUnit (algebraMap A P (g * q)) at h
    exact isUnit_of_mul_isUnit_right ((map_mul (algebraMap A P) g q) ▸ h)
  let f := algebraMap A P p * (↑(hu.unit⁻¹) : P)
  refine ⟨q,hs,f • volume (liftedBasis P),?_⟩
  have hf : evaluatePatch s hs f = r := by
    rw [show f = algebraMap A P p * (↑(hu.unit⁻¹) : P) from rfl, map_mul,
      evaluatePatch_algebraMap, inverse_image s hs q hu, ← div_eq_mul_inv]
    exact he
  change evaluate (evaluatePatch s hs) 3 (f • volume (liftedBasis P)) = sourceForm
  exact (LinearMap.map_smulₛₗ _ _ _).trans
    ((congrArg₂ (fun (a : W) (b : Form K W 3) => a • b) hf (evaluate_volume s hs)).trans hr.symm)

/-- On each further principal open the actual rank-three exterior
derivative has the exact-wedge rule needed for the rational transfer. -/
theorem exact_wedge_on_patch (s : A) :
    ExactWedgeRule (exteriorD2 (liftedBasis (Patch s))
      (exactFrameDirection (liftedBasis (Patch s)))).toAddMonoidHom := by
  intro a b c
  exact exteriorD2_exactFrame (liftedBasis (Patch s))
    (fun i => algebraMap A (Patch s) (coordinate i)) (liftedBasis_apply _ ) a b c

end CycleQ2NativeNormalResidue

#print axioms CycleQ2NativeNormalResidue.exists_regular_representative
#print axioms CycleQ2NativeNormalResidue.exact_wedge_on_patch

end

section

noncomputable section

/-!
# The actual residue form on an affine open off the generic graph

Choose a principal complement of the strict swept image and impose its
nonvanishing before clearing the source form's denominator. The resulting
regular form lies on a nonempty open of the native generic threefold and
restricts to the original weighted residue at its function point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2NativeResidueOffGraph

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2NormalWeightedCotangent CycleQ2NativeNormalFunctionField
  CycleQ2NativeNormalResidue CycleQ2GenericProperGraphSupport
open CycleQ2MonicGenericAmbientChart (K genericChartRing)
open CycleQ2GenericGraphFunctionStalk (chartField)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2GenericProperGraphOpen (surfaceStructure graphStructure)
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2WeightedCoordinateExterior (Form exactFrameDirection exteriorD2)
open CycleQ2WeightedRationalRestriction (evaluate protected_exact_of_affine_boundary)
open CycleQ2UniversalWeightedDeRham (W sourceForm)

private def normalImage : genericChartRing →+* A :=
  (algebraMap Cubic A).comp cubicIso.toRingHom

private theorem normalImage_injective : Function.Injective normalImage := by
  intro x y h
  have h' : toField (algebraMap Cubic A (cubicIso x)) =
      toField (algebraMap Cubic A (cubicIso y)) := congrArg toField h
  exact (IsFractionRing.injective genericChartRing chartField)
    (CycleQ2NativeWeightedFieldAlgebra.fieldAlgEquiv.injective
      ((toField_native x).symm.trans (h'.trans (toField_native y))))

def patchInclusion (s : A) : Spec (CommRingCat.of (Patch s)) ⟶ genericAmbient :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Patch s))) ≫ inclusion

private theorem normal_open : IsOpenImmersion inclusion := by
  let e := (Scheme.Spec.mapIso cubicIso.toRingEquiv.toCommRingCatIso.op).hom
  have he : IsOpenImmersion e := inferInstance
  have hf : inclusion = Spec.map (CommRingCat.ofHom (algebraMap Cubic A)) ≫ e ≫ chart := by
    unfold inclusion
    change _ = Spec.map (CommRingCat.ofHom (algebraMap Cubic A)) ≫
      Spec.map (CommRingCat.ofHom cubicIso.toRingHom) ≫ chart
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  rw [hf]
  infer_instance

instance (s : A) : IsOpenImmersion (patchInclusion s) := by
  let : IsOpenImmersion inclusion := normal_open
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Patch s))) ≫ inclusion)
  infer_instance

private theorem patch_off {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    {s : genericChartRing} (h : PrimeSpectrum.basicOpen s ≤ chart ⁻¹ᵁ complement V t)
    (q : A) (x : Spec (CommRingCat.of (Patch (normalImage s * q)))) :
    patchInclusion (normalImage s * q) x ∈ complement V t := by
  let g := normalImage s
  let B := Patch (g * q)
  let α : genericChartRing →+* B := (algebraMap A B).comp normalImage
  have hf : patchInclusion (g * q) = Spec.map (CommRingCat.ofHom α) ≫ chart := by
    unfold patchInclusion inclusion
    erw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hu : IsUnit (algebraMap A B (g * q)) := IsLocalization.Away.algebraMap_isUnit (g * q)
  have hg : IsUnit (algebraMap A B g) :=
    isUnit_of_mul_isUnit_left ((map_mul (algebraMap A B) g q) ▸ hu)
  rw [hf, Scheme.Hom.comp_apply]
  let : x.asIdeal.IsPrime := x.isPrime
  have hb : (Spec.map (CommRingCat.ofHom α)) x ∈ PrimeSpectrum.basicOpen s :=
    (PrimeSpectrum.mem_basicOpen s _).mpr (x.asIdeal.notMem_of_isUnit hg)
  exact h hb

/-- A regular representative of the actual weighted source exists on a
nonempty affine open disjoint from the original generic swept image. -/
theorem exists_off_graph {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (hp : IsProper (graphStructure V t)) :
    ∃ s : A, ∃ hs₀ : s ≠ 0,
      (∀ x : Spec (CommRingCat.of (Patch s)), patchInclusion s x ∈ complement V t) ∧
        ∃ ω : Form K (Patch s) 3, evaluate (evaluatePatch s hs₀) 3 ω = sourceForm := by
  obtain ⟨g,hg,hc⟩ := exists_basic_open V t hs hp
  have hga : normalImage g ≠ 0 := (map_ne_zero_iff _ normalImage_injective).mpr hg
  obtain ⟨q, hq, ω, hw⟩ := exists_regular_representative (normalImage g) hga
  exact ⟨normalImage g * q, hq, patch_off hc q, ω, hw⟩

/-- Exactness on the actual affine patch for its ordinary differential
would already discharge the protected exactness obligation. -/
theorem protected_exact_of_boundary {s : A} (hs : s ≠ 0) (ω : Form K (Patch s) 3)
    (hw : evaluate (evaluatePatch s hs) 3 ω = sourceForm)
    (η : Form K (Patch s) 2)
    (h : exteriorD2 (liftedBasis (Patch s)) (exactFrameDirection (liftedBasis (Patch s))) η = ω) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA :=
  protected_exact_of_affine_boundary (evaluatePatch s hs) _
    (exact_wedge_on_patch s) ω hw η h

end CycleQ2NativeResidueOffGraph

#print axioms CycleQ2NativeResidueOffGraph.exists_off_graph
#print axioms CycleQ2NativeResidueOffGraph.protected_exact_of_boundary

end
