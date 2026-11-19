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
import Proposal.GeometricAffineDerivations
import Mathlib.RingTheory.Localization.FractionRing
import Proposal.GeometricLiteralResidueLocalImage
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Proposal.GeometricLiteralDerivedResidue
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.SpreadingOut
import Mathlib.RingTheory.DedekindDomain.Basic

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

section

noncomputable section

/-!
# Relative coordinate derivations under affine localization

The exact frame of a smooth affine chart base changes through a
formally étale algebra. Its coordinate derivations therefore agree
with the original derivations on functions from the chart. This
applies in particular to the fraction field and to the residue
field of the generic point on an integral chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2EtaleFrameDerivations

open CycleQ2WeightedCoordinateExterior
open scoped TensorProduct

variable {K A : Type} [CommRing K] [CommRing A] [Algebra K A]
variable (B : Module.Basis (Fin 3) A Ω[A⁄K])
variable (T : Type) [CommRing T] [Algebra K T] [Algebra A T] [IsScalarTower K A T]
  [Algebra.FormallyEtale A T]

def frame : Module.Basis (Fin 3) T Ω[T⁄K] :=
  (B.baseChange T).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A T)

theorem frame_apply (u : Fin 3 → A) (hu : ∀ i, B i = KaehlerDifferential.D K A (u i))
    (i : Fin 3) :
    frame B T i = KaehlerDifferential.D K T (algebraMap A T (u i)) := by
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A T
  apply e.symm.injective
  change e.symm (e ((B.baseChange T) i)) = _
  rw [LinearEquiv.symm_apply_apply, Module.Basis.baseChange_apply, hu]
  exact (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K A T _).symm

theorem direction_algebraMap (a : A) (i : Fin 3) :
    exactFrameDirection (frame B T) i (algebraMap A T a) =
      algebraMap A T (exactFrameDirection B i a) := by
  rw [exactFrameDirection_apply, exactFrameDirection_apply]
  change (B.baseChange T).repr
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K A T).symm
      (KaehlerDifferential.D K T (algebraMap A T a))) i = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

end CycleQ2EtaleFrameDerivations

#print axioms CycleQ2EtaleFrameDerivations.direction_algebraMap

end

end

section

noncomputable section

/-!
# Evaluation of the affine derivative at the generic point

The local ring at the zero prime of an integral affine scheme is its
fraction ring. Evaluation of regular functions at that point commutes
with the coordinate derivations transported through the actual field
extension.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2AffineGenericEvaluation

open AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2GeometricLocalizedDerivations CycleQ2GeometricAffineDerivations
  CycleQ2WeightedCoordinateExterior CycleQ2EtaleFrameDerivations
open scoped nonZeroDivisors

variable {K A W : Type} [CommRing K] [CommRing A] [IsDomain A] [Field W]
  [Algebra ℂ K] [Algebra ℂ A] [Algebra K A] [IsScalarTower ℂ K A]
  [Algebra K W] [Algebra A W] [IsScalarTower K A W] [IsFractionRing A W]

private abbrev genericPoint : PrimeSpectrum A := ⊥
private abbrev M := (genericPoint (A := A)).asIdeal.primeCompl
private abbrev R := StructureSheaf.Localizations A (genericPoint (A := A))

omit [Algebra ℂ A] in
private theorem denominator_eq : M (A := A) = A⁰ := by
  apply Submonoid.ext
  intro x
  change x ∉ (⊥ : Ideal A) ↔ x ∈ A⁰
  rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.mem_bot]

private instance : IsFractionRing A (R (A := A)) := by
  have h : IsLocalization (M (A := A)) (R (A := A)) := inferInstance
  change IsLocalization A⁰ (R (A := A))
  exact (denominator_eq (A := A)) ▸ h

private def pointEquiv : R (A := A) ≃ₐ[A] W :=
  IsLocalization.algEquiv (A⁰) _ _

def eval {U : Opens (PrimeSpectrum.Top A)} (hx : genericPoint (A := A) ∈ U) :
    AffineSections U →+* W where
  toFun f := pointEquiv (f.1 ⟨genericPoint, hx⟩)
  map_zero' := map_zero pointEquiv
  map_one' := map_one pointEquiv
  map_add' _ _ := map_add pointEquiv _ _
  map_mul' _ _ := map_mul pointEquiv _ _

theorem eval_algebraMap {U : Opens (PrimeSpectrum.Top A)} (hx : genericPoint (A := A) ∈ U)
    (a : A) :
    letI : Algebra A (AffineSections U) := StructureSheaf.openAlgebra A (op U)
    eval (W := W) hx (algebraMap A (AffineSections U) a) = algebraMap A W a :=
  pointEquiv.commutes a

variable (B : Module.Basis (Fin 3) A Ω[A⁄K])

def baseDerivation (i : Fin 3) : Derivation ℂ A A :=
  (exactFrameDirection B i).restrictScalars ℂ

local instance : Algebra.FormallyEtale A W :=
  Algebra.FormallyEtale.of_isLocalization (Rₘ := W) A⁰

def fieldDerivation (i : Fin 3) : Derivation K W W := exactFrameDirection (frame B W) i

private theorem map_localized_derivation (i : Fin 3) (z : R (A := A)) :
    pointEquiv (W := W) (localizedDerivation (M (A := A)) _ (baseDerivation B i) z) =
      fieldDerivation B i (pointEquiv z) := by
  let D := localizedDerivation (M (A := A)) (R (A := A)) (baseDerivation B i)
  let E := fieldDerivation (W := W) B i
  let e := pointEquiv (A := A) (W := W)
  obtain ⟨⟨p, q⟩, h⟩ := IsLocalization.surj (M (A := A)) z
  change z * algebraMap A (R (A := A)) q = algebraMap A (R (A := A)) p at h
  have he : e z * algebraMap A W (q : A) = algebraMap A W p := by
    simpa only [map_mul, e.commutes] using congrArg e h
  have hq : algebraMap A W (q : A) ≠ 0 :=
    isUnit_iff_ne_zero.mp (IsLocalization.map_units W
      (⟨(q : A), denominator_eq (A := A) ▸ q.property⟩ : nonZeroDivisors A))
  have hD := congrArg (fun x => e (D x)) h
  have hE := congrArg E he
  change e (D (z * algebraMap A (R (A := A)) q)) = e (D (algebraMap A (R (A := A)) p)) at hD
  change E (e z * algebraMap A W q) = E (algebraMap A W p) at hE
  have dh (a : A) : D (algebraMap A (R (A := A)) a) =
      algebraMap A (R (A := A)) (exactFrameDirection B i a) :=
    localizedDerivation_algebraMap (M (A := A)) _ (baseDerivation B i) a
  have eh (a : A) : E (algebraMap A W a) = algebraMap A W (exactFrameDirection B i a) :=
    direction_algebraMap B W a i
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, dh, dh, map_add, map_mul, map_mul,
    e.commutes, e.commutes, e.commutes] at hD
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, eh, eh] at hE
  apply (mul_left_cancel₀ hq)
  exact add_left_cancel (hD.trans hE.symm)

theorem eval_sectionDerivative {U : Opens (PrimeSpectrum.Top A)}
    (hx : genericPoint (A := A) ∈ U) (i : Fin 3) (f : AffineSections U) :
    eval hx (sectionDerivative (baseDerivation B i) U f) = fieldDerivation (W := W) B i (eval hx f) :=
  map_localized_derivation B i (f.1 ⟨genericPoint, hx⟩)

end CycleQ2AffineGenericEvaluation

#print axioms CycleQ2AffineGenericEvaluation.eval_sectionDerivative

end

end

section

noncomputable section

/-!
# The top exterior differential on a relative affine threefold chart

In exact coordinates the differential is the divergence of the signed
components of a two-form. Applying the coordinate derivations to the
actual structure sheaf gives an additive morphism out of the associated
two-form sheaf. At the generic point its coefficients are the original
relative coordinate derivations on the fraction field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2AffineRelativeTopSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  CycleQ2GeometricAffineDerivations CycleQ2AffineGenericEvaluation
  CycleQ2WeightedCoordinateExterior CycleQ2EtaleFrameDerivations
open CycleQ2LiteralResidueLocalImage (exists_principal_preimage)

variable {K A : Type} [CommRing K] [CommRing A]
  [Algebra ℂ K] [Algebra ℂ A] [Algebra K A] [IsScalarTower ℂ K A]

abbrev X := Spec (CommRingCat.of A)
abbrev AddSheaf := TopCat.Sheaf AddCommGrpCat.{0} (PrimeSpectrum.Top A)

abbrev twoForms := tilde (R := CommRingCat.of A) (ModuleCat.of A (Form K A 2))
abbrev functions := SheafOfModules.unit.{0} (X (A := A)).ringCatSheaf
abbrev addForms := (SheafOfModules.toSheaf (X (A := A)).ringCatSheaf).obj (twoForms (K := K) (A := A))
abbrev addFunctions := (SheafOfModules.toSheaf (X (A := A)).ringCatSheaf).obj (functions (A := A))

variable (B : Module.Basis (Fin 3) A Ω[A⁄K])

def signedCoordinate (i : Fin 3) : twoForms (K := K) (A := A) ⟶ functions :=
  tilde.map (ModuleCat.ofHom (((-1 : A) ^ i.val) • (twoBasis B).coord i)) ≫
    (tildeSelf (R := CommRingCat.of A)).hom

def derivative (i : Fin 3) : addFunctions (A := A) ⟶ addFunctions (A := A) where
  hom.app U := AddCommGrpCat.ofHom (sectionDerivativeAddHom (baseDerivation B i) U.unop)
  hom.naturality _ _ _ := rfl

/-- The actual additive map in an exact volume frame. -/
def topDifferential : addForms (K := K) (A := A) ⟶ addFunctions (A := A) :=
  ∑ i, (SheafOfModules.toSheaf (X (A := A)).ringCatSheaf).map (signedCoordinate B i) ≫ derivative B i

theorem topDifferential_apply (U : Opens (PrimeSpectrum.Top A))
    (w : (addForms (K := K) (A := A)).obj.obj (op U)) :
    (topDifferential B).hom.app (op U) w =
      ∑ i, sectionDerivative (baseDerivation B i) U ((signedCoordinate B i).val.app (op U) w) := by
  unfold topDifferential
  simp only [Fin.sum_univ_three]
  rfl

def scalarSection (a : A) (U : Opens (PrimeSpectrum.Top A)) : AffineSections U :=
  letI : Algebra A (AffineSections U) := StructureSheaf.openAlgebra A (op U)
  algebraMap A (AffineSections U) a

omit [Algebra ℂ A] in
theorem scalarSection_restrict (a : A) {U V : Opens (PrimeSpectrum.Top A)} (h : V ≤ U) :
    (addFunctions (A := A)).obj.map (homOfLE h).op (scalarSection a U) = scalarSection a V := rfl

section Fraction

variable {W : Type} [IsDomain A] [Field W]
    [Algebra K W] [Algebra A W] [IsScalarTower K A W] [IsFractionRing A W]

local instance : Algebra.FormallyEtale A W := Algebra.FormallyEtale.of_isLocalization (Rₘ := W) (nonZeroDivisors A)

/-- Actual equality with a top exterior derivative on an open through
the generic point gives a primitive of the coefficient times the
ordered volume in the fraction field. -/
theorem exact_of_boundary (a : A) {U : Opens (PrimeSpectrum.Top A)} (hx : (⊥ : PrimeSpectrum A) ∈ U)
    (w : (addForms (K := K) (A := A)).obj.obj (op U))
    (hw : (topDifferential B).hom.app (op U) w = scalarSection a U) :
    ∃ η : Form K W 2,
      exteriorD2 (frame B W) (fieldDerivation B) η = algebraMap A W a • volume (frame B W) := by
  apply (exact_volume_iff_divergence (frame B W) (fieldDerivation B) (algebraMap A W a)).mpr
  refine ⟨fun i => eval hx ((signedCoordinate B i).val.app (op U) w), ?_⟩
  have h := congrArg (eval (W := W) hx) ((topDifferential_apply B U w).symm.trans hw)
  simp only [map_sum] at h
  have he : (∑ i : Fin 3, fieldDerivation (W := W) B i
      (eval hx ((signedCoordinate B i).val.app (op U) w))) =
    ∑ i : Fin 3, eval hx (sectionDerivative (baseDerivation B i) U ((signedCoordinate B i).val.app (op U) w)) :=
    Finset.sum_congr rfl fun i _ => (eval_sectionDerivative (W := W) B hx i _).symm
  exact he.trans (h.trans (eval_algebraMap hx a))

abbrev cokernelPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (PrimeSpectrum.Top A) :=
  (cokernel (topDifferential B)).obj

/-- A zero of the cokernel germ gives an actual local primitive and
therefore a primitive at the function point. -/
theorem exact_of_cokernel_germ (a : A)
    (h : (cokernelPresheaf B).Γgerm (⊥ : PrimeSpectrum A)
      ((cokernel.π (topDifferential B)).hom.app (op ⊤) (scalarSection a ⊤)) = 0) :
    ∃ η : Form K W 2,
      exteriorD2 (frame B W) (fieldDerivation B) η = algebraMap A W a • volume (frame B W) := by
  let x : PrimeSpectrum A := ⊥
  let E := cokernelPresheaf B
  let s := (cokernel.π (topDifferential B)).hom.app (op ⊤) (scalarSection a ⊤)
  have he : E.germ ⊤ x trivial s = E.germ ⊤ x trivial 0 :=
    h.trans (map_zero _).symm
  obtain ⟨U, hx, i, j, hi⟩ := E.germ_eq (U := ⊤) (V := ⊤) x trivial trivial _ _ he
  have hs : (cokernel.π (topDifferential B)).hom.app (op U) (scalarSection a U) = 0 := by
    have hi' : E.map i.op s = 0 := hi.trans (map_zero _)
    rw [← scalarSection_restrict a (leOfHom i)]
    have hn : E.map i.op s =
        (cokernel.π (topDifferential B)).hom.app (op U)
          ((addFunctions (A := A)).obj.map i.op (scalarSection a ⊤)) :=
      (NatTrans.naturality_apply (cokernel.π (topDifferential B)).hom i.op (scalarSection a ⊤)).symm
    exact hn.symm.trans hi'
  obtain ⟨r, hr, hxr, w, hw⟩ :=
    exists_principal_preimage (topDifferential B) U (scalarSection a U) hs x hx
  exact exact_of_boundary B a hxr w (hw.trans (scalarSection_restrict a hr))

end Fraction

end CycleQ2AffineRelativeTopSheaf

#print axioms CycleQ2AffineRelativeTopSheaf.exact_of_cokernel_germ

end

end

section

noncomputable section

/-!
# The actual weighted residue class in an affine cokernel sheaf

On a nonempty native normal patch the top three-form is read in its
exact volume frame. Its additive cokernel germ is a concrete local
criterion for the protected theorem. The fraction-field comparison
uses the exterior derivative in the actual universal field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2WeightedStalkExactness

open AlgebraicGeometry TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
  CycleQ2NormalWeightedCotangent CycleQ2NativeNormalFunctionField CycleQ2NativeNormalResidue
  CycleQ2WeightedCoordinateExterior CycleQ2EtaleFrameDerivations CycleQ2AffineRelativeTopSheaf
  CycleQ2AffineGenericEvaluation
open CycleQ2MonicGenericAmbientChart (K)
open CycleQ2UniversalWeightedDeRham (W sourceForm exteriorDerivative exteriorDerivative_exact_pair
  protected_exact_of_source_exact)
open CycleQ2WeightedRationalRestriction (evaluate evaluate_wedge)
open scoped nonZeroDivisors

variable (s : A) [NeZero s]
abbrev P := Patch s

private abbrev value : P s →ₐ[K] W := evaluatePatch s (NeZero.ne s)

private instance : Algebra (P s) W := (value s).toRingHom.toAlgebra

private instance : IsScalarTower A (P s) W :=
  IsScalarTower.of_algebraMap_eq (fun a => (evaluatePatch_algebraMap s (NeZero.ne s) a).symm)

private instance : IsScalarTower K (P s) W :=
  IsScalarTower.of_algebraMap_eq (fun a => ((value s).commutes a).symm)

private instance : IsDomain (P s) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (P s)
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne s)))

private instance : IsFractionRing (P s) W :=
  IsFractionRing.isFractionRing_of_isLocalization (Submonoid.powers s) (P s) W
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors_iff_ne_zero.mpr (NeZero.ne s)))

private instance : Algebra.FormallyEtale (P s) W :=
  Algebra.FormallyEtale.of_isLocalization (Rₘ := W) (nonZeroDivisors (P s))

private abbrev affineBasis := liftedBasis (P s)
private abbrev fieldBasis := frame (affineBasis s) W
private abbrev affineCoordinate (i : Fin 3) := algebraMap A (P s) (coordinate i)

private theorem weightedVolume_eval :
    evaluate (value s) 3 (volume (affineBasis s)) = volume (fieldBasis s) := by
  let u := affineCoordinate s
  have ha : volume (affineBasis s) = exteriorPower.ιMulti (P s) 3 (KaehlerDifferential.D K (P s) ∘ u) :=
    congrArg (exteriorPower.ιMulti (P s) 3) (funext (liftedBasis_apply (P s)))
  have hw : volume (fieldBasis s) =
      exteriorPower.ιMulti W 3 (KaehlerDifferential.D K W ∘ (value s ∘ u)) :=
    congrArg (exteriorPower.ιMulti W 3)
      (funext (frame_apply (affineBasis s) W u (liftedBasis_apply (P s))))
  exact (congrArg (evaluate (value s) 3) ha).trans
    ((evaluate_wedge (value s) 3 u).trans hw.symm)

/-- The scalar of the original source in the ordinary affine chart's
exact volume frame, interpreted in the universal field. -/
def RepresentsSource (a : P s) : Prop :=
  algebraMap (P s) W a • volume (fieldBasis s) = sourceForm

theorem representative_has_scalar (ω : Form K (P s) 3)
    (h : evaluate (value s) 3 ω = sourceForm) :
    ∃ a : P s, RepresentsSource s a := by
  obtain ⟨a,ha⟩ := topForm_scalar (affineBasis s) ω
  refine ⟨a, ?_⟩
  change (value s) a • volume (fieldBasis s) = sourceForm
  have he := (LinearMap.map_smulₛₗ (evaluate (value s) 3) a (volume (affineBasis s))).trans
    (congrArg (fun x => (value s) a • x) (weightedVolume_eval s))
  exact he.symm.trans ((congrArg (evaluate (value s) 3) ha).symm.trans h)

private theorem same_field_derivative :
    (exteriorD2 (fieldBasis s) (fieldDerivation (affineBasis s))).toAddMonoidHom =
      exteriorDerivative.toAddMonoidHom := by
  let u := affineCoordinate s
  let a : Fin 3 → W := value s ∘ u
  have ha : ∀ i, fieldBasis s i = KaehlerDifferential.D K W (a i) :=
    frame_apply (affineBasis s) W u (liftedBasis_apply (P s))
  apply twoFormMap_ext (fieldBasis s) a ha
  intro f g h
  exact (exteriorD2_exactFrame (fieldBasis s) a ha f g h).trans
    (exteriorDerivative_exact_pair f g h).symm

/-- The actual source section, modulo the honest exterior derivative,
at the generic point of this affine patch. -/
def weightedGerm (a : P s) :=
  (cokernelPresheaf (affineBasis s)).Γgerm (⊥ : PrimeSpectrum (P s))
    ((cokernel.π (topDifferential (affineBasis s))).hom.app (op ⊤) (scalarSection a ⊤))

/-- Vanishing of the germ of a scalar representing the weighted source
is sufficient for the exact protected four-form. -/
theorem protected_exact_of_germ_zero (a : P s) (ha : RepresentsSource s a)
    (h : weightedGerm s a = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  obtain ⟨η, hη⟩ := exact_of_cokernel_germ (W := W) (affineBasis s) a h
  apply protected_exact_of_source_exact
  refine ⟨η, ?_⟩
  have h' := DFunLike.congr_fun (same_field_derivative s) η
  exact h'.symm.trans (hη.trans ha)

/-- The original weighted class has a scalar representative on one
actual affine open disjoint from the generic swept image. -/
theorem exists_source_scalar_off_graph
    {V : CycleQ2IncidenceEtaleParameter.parameterScheme.Opens} {t : Fin 3 → ℂ}
    (h₁ : SmoothOfRelativeDimension 2 (CycleQ2GenericProperGraphOpen.surfaceStructure V t))
    (h₂ : IsProper (CycleQ2GenericProperGraphOpen.graphStructure V t)) :
    ∃ u : A, ∃ hu : u ≠ 0,
      (∀ x : Spec (CommRingCat.of (Patch u)),
        CycleQ2NativeResidueOffGraph.patchInclusion u x ∈ CycleQ2GenericProperGraphSupport.complement V t) ∧
      (letI : NeZero u := ⟨hu⟩
       ∃ a : Patch u, RepresentsSource u a) := by
  obtain ⟨u,hu,hc,ω,hω⟩ := CycleQ2NativeResidueOffGraph.exists_off_graph h₁ h₂
  refine ⟨u,hu,hc,?_⟩
  letI : NeZero u := ⟨hu⟩
  exact representative_has_scalar u ω hω

end CycleQ2WeightedStalkExactness

#print axioms CycleQ2WeightedStalkExactness.representative_has_scalar
#print axioms CycleQ2WeightedStalkExactness.protected_exact_of_germ_zero

end

end

section

noncomputable section

/-!
# From a supported derived vertex value to the protected exact form

A degree-zero map from the free sheaf on the affine patch represents
the scalar of the actual source. Applying the derived stalk at the
generic point and the vertex comparison gives the zero cokernel germ.
The checked affine exactness theorem then produces the protected
rational primitive.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2WeightedDerivedStalkBridge

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
  CycleQ2InjectiveCech CycleQ2WeightedStalkExactness CycleQ2NormalWeightedCotangent
  CycleQ2NativeNormalResidue CycleQ2AffineRelativeTopSheaf CycleQ2CechTwoToDerived

attribute [local instance] HasDerivedCategory.standard

variable (s : A) [NeZero s]

private abbrev Z := PrimeSpectrum.Top (Patch s)
private abbrev C := AbSheaf (Z s)
private abbrev S := DerivedCategory.singleFunctor (C s) 0
private abbrev d := topDifferential (liftedBasis (Patch s))
private abbrev x := (⊥ : PrimeSpectrum (Patch s))

private abbrev stalk (Y : TopCat.{0}) (p : Y) : AbSheaf Y ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} p

private theorem stalkAdditive (Y : TopCat.{0}) (p : Y) : (stalk Y p).Additive := by
  exact inferInstanceAs ((TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} p).Additive)

private theorem stalkLimits (Y : TopCat.{0}) (p : Y) : PreservesFiniteLimits (stalk Y p) := by
  exact inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} p))

private theorem stalkColimits (Y : TopCat.{0}) (p : Y) : PreservesFiniteColimits (stalk Y p) := by
  exact inferInstanceAs (PreservesFiniteColimits (TopCat.Sheaf.forget AddCommGrpCat.{0} Y ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} p))

abbrev stalkAtGeneric : C s ⥤ AddCommGrpCat.{0} := stalk (Z s) (x (s := s))

private instance : (stalkAtGeneric s).Additive := stalkAdditive _ _
private instance : PreservesFiniteLimits (stalkAtGeneric s) := stalkLimits _ _
private instance : PreservesFiniteColimits (stalkAtGeneric s) := stalkColimits _ _

def scalarMap (a : Patch s) : freeOpen (⊤ : Opens (Z s)) ⟶ addFunctions (A := Patch s) :=
  (freeOpenSections (addFunctions (A := Patch s)) ⊤).symm (scalarSection a ⊤)

private theorem scalarMap_app (a : Patch s) :
    app (scalarMap s a) ⊤ (freeOpenSections (freeOpen (⊤ : Opens (Z s))) ⊤ (𝟙 _)) =
      scalarSection a ⊤ := by
  refine (freeOpenSections_postcomp ⊤ (𝟙 _) (scalarMap s a)).trans ?_
  let F := freeOpenSections (addFunctions (A := Patch s)) (⊤ : Opens (Z s))
  exact (congrArg F (Category.id_comp (scalarMap s a))).trans (F.apply_symm_apply _)

private theorem germ_of_cokernel_comp (a : Patch s)
    (h : (stalkAtGeneric s).map (scalarMap s a ≫ cokernel.π (d (s := s))) = 0) :
    weightedGerm s a = 0 := by
  let P := freeOpen (⊤ : Opens (Z s))
  let f : P ⟶ cokernel (d (s := s)) := scalarMap s a ≫ cokernel.π (d (s := s))
  let u := freeOpenSections P ⊤ (𝟙 P)
  let P₀ : TopCat.Presheaf AddCommGrpCat.{0} (Z s) := P.obj
  let e := P₀.Γgerm (x (s := s)) u
  have hg : (stalkAtGeneric s).map f e = 0 := by
    exact ConcreteCategory.congr_hom h e
  have hv : (stalkAtGeneric s).map f e =
      (cokernelPresheaf (liftedBasis (Patch s))).Γgerm (x (s := s))
        (app f ⊤ u) :=
    TopCat.Presheaf.stalkFunctor_map_germ_apply (X := Z s)
      (C := AddCommGrpCat.{0}) ⊤ (x (s := s)) trivial f.hom u
  have ha : app f ⊤ u = app (cokernel.π (d (s := s))) ⊤ (scalarSection a ⊤) :=
    (app_comp (scalarMap s a) (cokernel.π (d (s := s))) ⊤ u).symm.trans
      (congrArg (app (cokernel.π (d (s := s))) ⊤) (scalarMap_app s a))
  exact (congrArg ((cokernelPresheaf (liftedBasis (Patch s))).Γgerm (x (s := s))) ha).symm.trans
    (hv.symm.trans hg)

/-- A derived class with the stated native vertex comparison gives the
protected primitive if its image at the generic point vanishes. -/
theorem protected_exact_of_derived_stalk
    (a : Patch s) (ha : RepresentsSource s a) {M N : DerivedCategory (C s)}
    (vertex : (S s).obj (freeOpen (⊤ : Opens (Z s))) ⟶ M)
    (c : M ⟶ N) (projection : N ⟶ (S s).obj (cokernel (d (s := s))))
    (hvertex : vertex ≫ c ≫ projection =
      (S s).map (scalarMap s a ≫ cokernel.π (d (s := s))))
    (h : (stalkAtGeneric s).mapDerivedCategory.map c = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  have hz : (stalkAtGeneric s).mapDerivedCategory.map
      ((S s).map (scalarMap s a ≫ cokernel.π (d (s := s)))) = 0 := by
    let F := (stalkAtGeneric s).mapDerivedCategory
    have hf : F.map (vertex ≫ c ≫ projection) = F.map vertex ≫ F.map c ≫ F.map projection :=
      (F.map_comp vertex _).trans (congrArg (fun k => F.map vertex ≫ k) (F.map_comp c projection))
    exact (congrArg F.map hvertex.symm).trans (hf.trans
      ((congrArg (fun k => F.map vertex ≫ k ≫ F.map projection) h).trans
        ((congrArg (fun k => F.map vertex ≫ k) zero_comp).trans comp_zero)))
  exact protected_exact_of_germ_zero s a ha
    (germ_of_cokernel_comp s a
      (CycleQ2DerivedVertexExactness.map_zero_of_single_map_zero (stalkAtGeneric s) _ hz))

end CycleQ2WeightedDerivedStalkBridge

#print axioms CycleQ2WeightedDerivedStalkBridge.protected_exact_of_derived_stalk

end

end

section

noncomputable section

/-!
# Finite normalization of complex affine domains

Noether normalization realizes a finite-type complex domain as an algebra
finite over a polynomial subring. The extension of fraction fields is finite
and separable, so the integral closure is finite over the polynomial ring.
The same generators suffice over the original affine domain.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2FiniteTypeNormalization

open scoped nonZeroDivisors

/-- The integral closure of a complex affine domain in any finite extension
of its fraction field is module-finite. -/
theorem finiteExtensionNormalizationFinite (A L : Type*) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Field L] [Algebra A L]
    [Algebra (FractionRing A) L] [IsScalarTower A (FractionRing A) L]
    [FiniteDimensional (FractionRing A) L] :
    Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  let P := MvPolynomial (Fin n) ℂ
  let K := FractionRing A
  let N := integralClosure A L
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : FaithfulSMul P K := (faithfulSMul_iff_algebraMap_injective P K).mpr (by
    rw [IsScalarTower.algebraMap_eq P A K]
    exact (IsFractionRing.injective A K).comp hinj)
  let : Algebra (FractionRing P) K := FractionRing.liftAlgebra P K
  let : FiniteDimensional (FractionRing P) K := Module.Finite.of_isLocalization P A P⁰
  let : Algebra P L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A L := IsScalarTower.of_algebraMap_eq' (R := P) (S := A) (A := L) rfl
  let : IsScalarTower P K L := IsScalarTower.to₁₃₄ P A K L
  let : Algebra (FractionRing P) L :=
    ((algebraMap K L).comp (algebraMap (FractionRing P) K)).toAlgebra
  let : IsScalarTower (FractionRing P) K L :=
    IsScalarTower.of_algebraMap_eq' (R := FractionRing P) (S := K) (A := L) rfl
  let : IsScalarTower P (FractionRing P) L := IsScalarTower.to₁₂₄ P (FractionRing P) K L
  let : FiniteDimensional (FractionRing P) L := Module.Finite.trans K L
  let : Algebra P N := ((algebraMap A N).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A N := IsScalarTower.of_algebraMap_eq' (R := P) (S := A) (A := N) rfl
  let : IsScalarTower P N L := IsScalarTower.of_algebraMap_eq' (R := P) (S := N) (A := L) rfl
  let : IsIntegralClosure N P L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      exact ⟨fun hx => ⟨⟨x, hx.tower_top⟩, rfl⟩,
        fun ⟨y, hy⟩ => hy ▸ isIntegral_trans (R := P) (y : L) y.property⟩ }
  let : Module.Finite P N := IsIntegralClosure.finite P (FractionRing P) L N
  exact Module.Finite.of_restrictScalars_finite P A N

/-- An affine domain of finite type over the complex field has finite normalization. -/
theorem domainNormalizationFinite (A : Type*) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finiteExtensionNormalizationFinite A (FractionRing A)

end CycleQ2FiniteTypeNormalization
end

#print axioms CycleQ2FiniteTypeNormalization.finiteExtensionNormalizationFinite
#print axioms CycleQ2FiniteTypeNormalization.domainNormalizationFinite

end

end

section

noncomputable section

/-!
# Finiteness of normalization across the minimal primes

The total fraction ring of a reduced ring embeds in the product of the
fraction fields of its minimal components. Integral elements land in the
product of the component normalizations. Over a Noetherian ring the finite
component normalizations thus bound the integral closure of every subalgebra
of the total fraction ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

namespace CycleQ2ReducedNormalizationFinite

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A]

local instance prime (p : minimalPrimes A) : p.1.IsPrime := p.2.isPrime

abbrev ComponentRing (p : minimalPrimes A) := A ⧸ p.1
abbrev ComponentField (p : minimalPrimes A) := FractionRing (ComponentRing A p)

private theorem component_denominator (p : minimalPrimes A) (s : A⁰) :
    IsUnit (algebraMap A (ComponentField A p) s) := by
  apply isUnit_iff_ne_zero.mpr
  rw [IsScalarTower.algebraMap_apply A (ComponentRing A p) (ComponentField A p)]
  intro he
  have he' : Ideal.Quotient.mk p.1 s = 0 :=
    (IsFractionRing.injective (ComponentRing A p) (ComponentField A p)) (by simpa using he)
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (Ideal.Quotient.eq_zero_iff_mem.mp he') p.2 s.2

/-- The component fraction maps extend across all non-zero-divisors. -/
def fractionComponent (p : minimalPrimes A) : FractionRing A →ₐ[A] ComponentField A p :=
  IsLocalization.liftAlgHom (f := Algebra.ofId A (ComponentField A p)) (component_denominator A p)

private theorem componentProduct_injective [IsReduced A] :
    Function.Injective (algebraMap A (∀ p : minimalPrimes A, ComponentField A p)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ sInf (minimalPrimes A) := by
    apply Ideal.mem_sInf.mpr
    intro P hP
    let p : minimalPrimes A := ⟨P, hP⟩
    have h := congrFun hx p
    change algebraMap A (ComponentField A p) x = 0 at h
    rw [IsScalarTower.algebraMap_apply A (ComponentRing A p) (ComponentField A p)] at h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective (ComponentRing A p) (ComponentField A p)) (by simpa using h)
  change x ∈ sInf (⊥ : Ideal A).minimalPrimes at hmem
  rw [Ideal.sInf_minimalPrimes] at hmem
  change x ∈ nilradical A at hmem
  rw [nilradical_eq_zero] at hmem
  exact hmem

/-- The minimal-component maps jointly detect elements of the total ring of fractions. -/
theorem fractionComponent_injective [IsReduced A] :
    Function.Injective (AlgHom.pi (fractionComponent A)) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq A⁰ (AlgHom.pi (fractionComponent A)).toRingHom).mpr
  intro x y
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [(IsFractionRing.injective A (FractionRing A)).eq_iff, (componentProduct_injective A).eq_iff]

variable {A} {B : Type*} [CommRing B] [Algebra A B]

/-- Jointly injective component maps suffice for finiteness of integral closure. -/
theorem finite_of_component_embeddings [IsNoetherianRing A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p)))
    (f : ∀ p : minimalPrimes A, B →ₐ[A] ComponentField A p)
    (hf : Function.Injective (AlgHom.pi f)) : Module.Finite A (integralClosure A B) := by
  let : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  let N (p : minimalPrimes A) := integralClosure (ComponentRing A p) (ComponentField A p)
  let (p : minimalPrimes A) : Module.Finite A (N p) :=
    letI := h p
    Module.Finite.trans (ComponentRing A p) (N p)
  let g (p : minimalPrimes A) : integralClosure A B →ₐ[A] N p :=
    ((f p).domRestrict (integralClosure A B)).codRestrict ((N p).restrictScalars A)
      (fun x => (x.2.map (f p)).tower_top)
  apply Module.Finite.of_injective (AlgHom.pi g).toLinearMap
  intro x y he
  apply Subtype.ext
  apply hf
  exact funext (fun p => congrArg Subtype.val (congrFun he p))

variable (A)

/-- The normalization of a reduced Noetherian ring is finite whenever all of
its irreducible component rings have finite normalization. -/
theorem finite_integralClosure_of_domainQuotients [IsNoetherianRing A] [IsReduced A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p))) :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finite_of_component_embeddings h (fractionComponent A) (fractionComponent_injective A)

/-- The same bound applies to the actual ring of sections once it embeds in
the total fraction ring of the reduced affine chart. -/
theorem finite_integralClosure_of_fraction_embedding [IsNoetherianRing A] [IsReduced A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p)))
    (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f) :
    Module.Finite A (integralClosure A B) :=
  finite_of_component_embeddings h (fun p => (fractionComponent A p).comp f)
    ((fractionComponent_injective A).comp hf)

universe u

/-- Finiteness of normalization for finite-type domains over a field extends
to every reduced finite-type algebra and every subalgebra of its total
fraction ring. The minimal-prime quotients carry their induced algebras. -/
theorem finiteType_integralClosure_of_fraction_embedding
    (k : Type*) [Field k]
    (domainFinite : ∀ (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
      [Algebra.FiniteType k D], Module.Finite D (integralClosure D (FractionRing D)))
    (R : Type u) [CommRing R] [IsReduced R] [Algebra k R] [Algebra.FiniteType k R]
    {S : Type*} [CommRing S] [Algebra R S] (f : S →ₐ[R] FractionRing R)
    (hf : Function.Injective f) : Module.Finite R (integralClosure R S) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact finite_integralClosure_of_fraction_embedding R
    (fun p => domainFinite (ComponentRing R p)) f hf

#print axioms fractionComponent_injective
#print axioms finite_integralClosure_of_domainQuotients
#print axioms finite_integralClosure_of_fraction_embedding
#print axioms finiteType_integralClosure_of_fraction_embedding

end CycleQ2ReducedNormalizationFinite
end

end

end

section

noncomputable section

/-!
# Regular sections on a dense open in a reduced affine Noetherian scheme

The complement ideal of the open has zero annihilator. In a Noetherian
ring this implies that the ideal contains a nonzero divisor. Restricting
to its principal open identifies every section with an element of the
total ring of fractions, also when the affine scheme is reducible.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2DenseOpenTotalFractions

open AlgebraicGeometry CategoryTheory Opposite PrimeSpectrum TopologicalSpace

variable (A : Type) [CommRing A] [IsReduced A] [IsNoetherianRing A]

/-- A dense open in a reduced Noetherian spectrum contains a principal open
cut out by a regular element. -/
theorem exists_regular_basicOpen (W : Opens (PrimeSpectrum A))
    (hW : Dense (W : Set (PrimeSpectrum A))) :
    ∃ s ∈ nonZeroDivisors A, basicOpen s ≤ W := by
  classical
  let I := vanishingIdeal (W : Set (PrimeSpectrum A))ᶜ
  have hI : zeroLocus (I : Set A) = (W : Set (PrimeSpectrum A))ᶜ :=
    (zeroLocus_vanishingIdeal_eq_closure _).trans W.isOpen.isClosed_compl.closure_eq
  have hV : vanishingIdeal (W : Set (PrimeSpectrum A)) = ⊥ := by
    rw [← vanishingIdeal_closure, hW.closure_eq, vanishingIdeal_univ, nilradical_eq_zero]
    rfl
  have hi : ((I : Set A) ∩ nonZeroDivisors A).Nonempty := by
    by_contra hn
    obtain ⟨x, hx, hne⟩ := (SetLike.lt_iff_le_and_exists.mp
      (Ideal.bot_lt_annihilator_of_disjoint_nonZeroDivisors (I := I)
        (Set.disjoint_iff_inter_eq_empty.mpr (Set.not_nonempty_iff_eq_empty.mp hn)))).2
    apply hne
    rw [← hV, mem_vanishingIdeal]
    intro p hp
    have hnot : ¬ (I : Set A) ⊆ p.asIdeal := by
      intro h
      exact (hI ▸ (mem_zeroLocus p I).mpr h) hp
    obtain ⟨a, ha, hpa⟩ := Set.not_subset.mp hnot
    have hz : x * a = 0 := congrArg Subtype.val ((Module.mem_annihilator.mp hx) ⟨a, ha⟩)
    exact (p.isPrime.mem_or_mem (hz ▸ p.asIdeal.zero_mem)).resolve_right hpa
  obtain ⟨s, hsi, hs⟩ := hi
  refine ⟨s, hs, ?_⟩
  intro p hp
  by_contra hn
  have : p ∈ zeroLocus (I : Set A) := by rw [hI]; exact hn
  exact hp ((mem_zeroLocus _ _).mp this hsi)

omit [_root_.IsReduced A] [IsNoetherianRing A] in
private theorem dense_regular_basicOpen (s : A) (hs : s ∈ nonZeroDivisors A) :
    Dense (basicOpen s : Set (PrimeSpectrum A)) := by
  have hinj : Function.Injective (algebraMap A (Localization.Away s)) :=
    IsLocalization.injective (Localization.Away s) (Submonoid.powers_le.mpr hs)
  rw [← localization_away_comap_range (Localization.Away s) s]
  apply (denseRange_comap_iff_ker_le_nilRadical _).mpr
  rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
  exact bot_le

/-- Sections on the specified open, with their canonical algebra structure
over the ring of the ambient spectrum. -/
abbrev Sections (W : (Spec (CommRingCat.of A)).Opens) :=
  (Spec.structureSheaf A).obj.obj (op W)

local instance sectionsAlgebra (W : (Spec (CommRingCat.of A)).Opens) :
    Algebra A (Sections A W) :=
  AlgebraicGeometry.StructureSheaf.openAlgebra (R := A) (op W)

/-- The dense principal-open restriction embeds sections in the total
quotient ring as an algebra over the original ring. -/
theorem sections_embedding (W : (Spec (CommRingCat.of A)).Opens)
    (hW : Dense (W : Set (Spec (CommRingCat.of A)))) :
    ∃ φ : Sections A W →ₐ[A] FractionRing A, Function.Injective φ := by
  obtain ⟨s, hs, hle⟩ := exists_regular_basicOpen A W hW
  let X := Spec (CommRingCat.of A)
  let D : X.Opens := basicOpen s
  have : IsDominant D.ι := ⟨by
    change Dense (Set.range D.ι)
    rw [Scheme.Opens.range_ι]
    exact dense_regular_basicOpen A s hs⟩
  have : IsSchemeTheoreticallyDominant D.ι := .of_isDominant _
  let res : Sections A W →ₐ[A] Sections A D :=
    { (X.presheaf.map (homOfLE hle).op).hom with
      commutes' := fun x =>
        congrArg (fun k : CommRingCat.of A ⟶ X.presheaf.obj (op D) => k x)
          (AlgebraicGeometry.StructureSheaf.algebraMap_self_map A (op D) (op W) (homOfLE hle).op) }
  have hinj : Function.Injective res := by
    intro z w h
    apply D.ι.app_injective W
    let i := homOfLE (D.ι_image_le (D.ι ⁻¹ᵁ W))
    have H := congrArg (X.presheaf.map i.op) h
    change (X.presheaf.map (homOfLE hle).op ≫ X.presheaf.map i.op) z =
      (X.presheaf.map (homOfLE hle).op ≫ X.presheaf.map i.op) w at H
    erw [← Functor.map_comp] at H
    exact H
  letI : IsLocalization.Away s (Sections A D) :=
    AlgebraicGeometry.StructureSheaf.IsLocalization.to_basicOpen A s
  let incl : Sections A D →ₐ[A] FractionRing A :=
    IsLocalization.Away.liftAlgHom s (f := Algebra.ofId A (FractionRing A))
      (IsLocalization.map_units (FractionRing A) ⟨s, hs⟩)
  have hi : Function.Injective incl := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (M := Submonoid.powers s) (Sections A D) incl.toRingHom
    intro a ha
    have hzero : algebraMap A (FractionRing A) a = 0 :=
      (incl.commutes a).symm.trans ha
    have hz : a = 0 := IsFractionRing.injective A (FractionRing A)
      (hzero.trans (map_zero (algebraMap A (FractionRing A))).symm)
    simp [hz]
  exact ⟨incl.comp res, hi.comp hinj⟩

end CycleQ2DenseOpenTotalFractions
end

#print axioms CycleQ2DenseOpenTotalFractions.exists_regular_basicOpen
#print axioms CycleQ2DenseOpenTotalFractions.sections_embedding

end

end

section

noncomputable section

/-!
# Sections of a dense open on an affine chart

Intersecting a dense open subscheme with an affine chart gives a dense open
in the spectrum of the chart ring. The induced identification of sections
respects the original coordinate algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2DenseOpenAffineSections
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
variable {V : Y.Opens} (hV : IsAffineOpen V)

def chart : (j ⁻¹ᵁ V).toScheme ⟶ Spec Γ(Y,V) := (j ∣_ V) ≫ hV.isoSpec.hom

instance : IsOpenImmersion (chart j hV) := by unfold chart; infer_instance

def chartOpen : (Spec Γ(Y,V)).Opens := chart j hV ''ᵁ ⊤

theorem dense [IsDominant j] : Dense (chartOpen j hV : Set (Spec Γ(Y, V))) := by
  let : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance V
  let : IsDominant (chart j hV) := by unfold chart; infer_instance
  rw [chartOpen, Scheme.Hom.image_top_eq_opensRange]
  exact (chart j hV).denseRange

def sectionIso : Γ(Spec Γ(Y,V), chartOpen j hV) ≅ Γ(X, j ⁻¹ᵁ V) :=
  ((chart j hV).appIso ⊤) ≪≫ (j ⁻¹ᵁ V).topIso

theorem sectionIso_over :
    CommRingCat.ofHom (algebraMap Γ(Y,V) Γ(Spec Γ(Y,V), chartOpen j hV)) ≫
      (sectionIso j hV).hom = j.app V := by
  let g := chart j hV
  have hle : g ''ᵁ ⊤ ≤ ⊤ := le_top
  have hres : (Spec Γ(Y,V)).presheaf.map (homOfLE hle).op ≫ (g.appIso ⊤).hom = g.appTop := by
    rw [g.appIso_hom', g.map_appLE (g.preimage_image_eq ⊤).ge (homOfLE hle).op]
    exact g.appLE_eq_app (U := ⊤)
  change ((Scheme.ΓSpecIso Γ(Y,V)).inv ≫ (Spec Γ(Y,V)).presheaf.map (homOfLE hle).op) ≫
    (sectionIso j hV).hom = j.app V
  erw [sectionIso, Iso.trans_hom]
  erw [Category.assoc, ← Category.assoc _ (g.appIso ⊤).hom, hres]
  have hg : g.appTop = hV.isoSpec.hom.appTop ≫ (j ∣_ V).appTop :=
    Scheme.Hom.comp_appTop _ _
  erw [hg, hV.isoSpec_hom_appTop, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id_assoc]
  let e := arrowResLEAppIso j V (j ⁻¹ᵁ V) le_rfl
  have he : V.topIso.hom ≫ j.app V =
      (j ∣_ V).appTop ≫ (j ⁻¹ᵁ V).topIso.hom := by
    have h := e.hom.w
    change V.topIso.hom ≫ j.appLE V (j ⁻¹ᵁ V) le_rfl =
      (j.resLE V (j ⁻¹ᵁ V) le_rfl).appTop ≫ (j ⁻¹ᵁ V).topIso.hom at h
    erw [j.resLE_eq_morphismRestrict, ← j.app_eq_appLE] at h
    exact h
  exact (congrArg (fun k => V.topIso.inv ≫ k) he.symm).trans (Iso.inv_hom_id_assoc _ _)

/-- Actual section algebra on the restricted open, in chart coordinates. -/
def sectionEquiv :
    letI := (j.app V).hom.toAlgebra
    Γ(X, j ⁻¹ᵁ V) ≃ₐ[Γ(Y,V)] Γ(Spec Γ(Y,V), chartOpen j hV) := by
  letI := (j.app V).hom.toAlgebra
  let e := (sectionIso j hV).symm.commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := e) ?_
  intro r
  apply (sectionIso j hV).commRingCatIsoToRingEquiv.injective
  exact (e.symm_apply_apply _).trans (ConcreteCategory.congr_hom (sectionIso_over j hV) r).symm

end CycleQ2DenseOpenAffineSections

#print axioms CycleQ2DenseOpenAffineSections.dense
#print axioms CycleQ2DenseOpenAffineSections.sectionEquiv

end

end

section

noncomputable section

/-!
# Finite relative normalization of the monic time compactification

Normalize the projective graph closure in its original smooth time open.
This map is finite and its inverse image of the whole time open is unchanged.
The resulting model stays proper over the original normalized coefficient base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2LiteralIncidenceRelativeNormalization

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeCompletion
open scoped TensorProduct

private theorem reduced_etale_over_domain {P A : Type} [CommRing P] [IsDomain P] [CommRing A]
    [Algebra P A] [Algebra.Etale P A] : _root_.IsReduced A := by
  let K := FractionRing P
  let : _root_.IsReduced (K ⊗[P] A) := Algebra.FormallyUnramified.isReduced_of_field K _
  exact isReduced_of_injective
    (Algebra.TensorProduct.includeRight : A →ₐ[P] K ⊗[P] A)
    (Algebra.TensorProduct.includeRight_injective (IsFractionRing.injective P K))

private theorem reduced_chart {R A : Type} [CommRing R] [IsDomain R] [CommRing A]
    (n : ℕ) (f : R →+* A) (hf : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) f) :
    _root_.IsReduced A := by
  obtain ⟨s, hs, h⟩ := hf
  let (a : s) : _root_.IsReduced (Localization.Away a.val) := by
    obtain ⟨g, _, hg⟩ := (h _ a.property).exists_etale_mvPolynomial
    let := g.toAlgebra
    let : Algebra.Etale (MvPolynomial (Fin n) R) (Localization.Away a.val) := hg.toAlgebra
    exact reduced_etale_over_domain (P := MvPolynomial (Fin n) R)
  exact isReduced_of_injective _ (Localization.algebraMap_injective_of_span_eq_top s hs)

/-- A smooth scheme of fixed relative dimension over an affine integral base is reduced. -/
theorem reduced_of_smooth_over_domain {R : Type} [CommRing R] [IsDomain R] {X : Scheme}
    (n : ℕ) (f : X ⟶ Spec (CommRingCat.of R)) [SmoothOfRelativeDimension n f] :
    AlgebraicGeometry.IsReduced X := by
  apply (IsReduced.iff_of_openCover (X := X) X.affineCover).mpr
  intro a
  let Y := X.affineCover.X a
  let p := X.affineCover.f a ≫ f
  let c := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop
  have hp : SmoothOfRelativeDimension n p := by
    simpa only [Nat.zero_add, p] using smoothOfRelativeDimension_comp 0 n (X.affineCover.f a) f
  have he : Y.toSpecΓ ≫ Spec.map c = p := by
    dsimp only [c]
    rw [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  have h : SmoothOfRelativeDimension n (Spec.map c) := by
    let : SmoothOfRelativeDimension n p := hp
    let e := Y.toSpecΓ
    have hcomp : inv e ≫ p = Spec.map c :=
      (congrArg (fun k => inv e ≫ k) he.symm).trans (IsIso.inv_hom_id_assoc e _)
    rw [← hcomp]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n (inv e) p
  let : _root_.IsReduced Γ(Y, ⊤) := reduced_chart n c.hom
    ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mp h)
  exact isReduced_of_isAffine_isReduced (X := Y)

instance time_reduced (V : parameterScheme.Opens) : AlgebraicGeometry.IsReduced (Time toRaw V) := by
  exact @reduced_of_smooth_over_domain MonicRing _ _ (Time toRaw V) 1
    (timeMap toRaw V) (timeMap_smooth toRaw V)

instance completion_reduced (V : parameterScheme.Opens) : IsReduced (Completion V) := by
  let f := graph V
  apply (IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
  change ∀ W : ProjectiveBundle.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(ProjectiveBundle, W.1) ⧸ f.ker.ideal W)))
  intro W
  apply (affine_isReduced_iff _).mpr
  let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ W.1) :=
    isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective W)
  exact isReduced_of_injective (f.ker.subschemeObjIso W).inv.hom
    (f.ker.subschemeObjIso W).symm.commRingCatIsoToRingEquiv.injective

/-- For a reduced scheme locally of finite type over the complex numbers, normalization
in any quasi-compact dense open is finite. -/
theorem dense_open_normalization_finite {X Y : Scheme} (j : X ⟶ Y)
    [IsOpenImmersion j] [QuasiCompact j] [IsDominant j] [IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] : IsFinite j.fromNormalization := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro V hV
  let A := Γ(Y, V)
  let B := Γ(X, j ⁻¹ᵁ V)
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ V hle
  let : Algebra ℂ A := c.hom.toAlgebra
  let : Algebra.FiniteType ℂ A :=
    (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  let : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  let : Algebra A B := (j.app V).hom.toAlgebra
  obtain ⟨φ, hφ⟩ := CycleQ2DenseOpenTotalFractions.sections_embedding A
    (CycleQ2DenseOpenAffineSections.chartOpen j hV) (CycleQ2DenseOpenAffineSections.dense j hV)
  let C := CycleQ2DenseOpenTotalFractions.Sections A (CycleQ2DenseOpenAffineSections.chartOpen j hV)
  let : Algebra A C := StructureSheaf.openAlgebra (R := A)
    (op (CycleQ2DenseOpenAffineSections.chartOpen j hV))
  let e : B ≃ₐ[A] C := CycleQ2DenseOpenAffineSections.sectionEquiv j hV
  let : Module.Finite A (integralClosure A B) :=
    CycleQ2ReducedNormalizationFinite.finiteType_integralClosure_of_fraction_embedding ℂ
      CycleQ2FiniteTypeNormalization.domainNormalizationFinite A (φ.comp e.toAlgHom)
        (hφ.comp e.injective)
  rw [j.fromNormalization_app hV, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (j.normalizationObjIso hV).symm.commRingCatIsoToRingEquiv.surjective).comp
      (RingHom.finite_algebraMap.mpr inferInstance)

variable (V : parameterScheme.Opens)

abbrev Model := (inclusion V).normalization

def toCompletion : Model V ⟶ Completion V := (inclusion V).fromNormalization

def openInclusion : Time toRaw V ⟶ Model V := (inclusion V).toNormalization

def normalizedMap : Model V ⟶ monicBase := toCompletion V ≫ structureMap V

instance : IsOpenImmersion (openInclusion V) := inferInstanceAs (IsOpenImmersion (inclusion V).toNormalization)

instance : IsDominant (openInclusion V) := inferInstanceAs (IsDominant (inclusion V).toNormalization)

instance : IsFinite (toCompletion V) := by
  have : LocallyOfFiniteType toComplex := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ MonicRing)
  exact dense_open_normalization_finite (inclusion V) (structureMap V ≫ toComplex)

instance : IsProper (normalizedMap V) := by unfold normalizedMap; infer_instance

@[reassoc (attr := simp)] theorem open_toCompletion :
    openInclusion V ≫ toCompletion V = inclusion V := (inclusion V).toNormalization_fromNormalization

@[reassoc (attr := simp)] theorem open_over :
    openInclusion V ≫ normalizedMap V = timeMap toRaw V := by
  rw [normalizedMap, open_toCompletion_assoc, inclusion_over]

/-- The finite proper model contains exactly the original scheme over its marked time open. -/
theorem recovers_time_open : IsIso (pullback.snd (toCompletion V) (inclusion V)) := by
  let f := inclusion V
  change IsIso (pullback.snd f.fromNormalization f)
  rw [← isIso_comp_left_iff (f.normalizationPullback f), f.normalizationPullback_snd,
    ← isIso_comp_left_iff (pullback.snd f f).toNormalization,
    Scheme.Hom.toNormalization_fromNormalization]
  infer_instance

theorem normalized_time_model :
    IsProper (normalizedMap V) ∧ IsFinite (toCompletion V) ∧
      IsIso (pullback.snd (toCompletion V) (inclusion V)) ∧
      SmoothOfRelativeDimension 1 (openInclusion V ≫ normalizedMap V) := by
  refine ⟨inferInstance, inferInstance, recovers_time_open V, ?_⟩
  rw [open_over]
  exact timeMap_smooth _ _

end CycleQ2LiteralIncidenceRelativeNormalization
end

#print axioms CycleQ2LiteralIncidenceRelativeNormalization.normalized_time_model

end

end

section

noncomputable section

/-!
# Integral proper components meeting a prescribed time open

A nonempty open of a Noetherian space contains a nonempty irreducible open.
Taking its schematic image in a proper compactification gives an integral
proper model. Its smooth time open maps openly to the irreducible base, so
the model surjects onto that base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2IncidenceIntegralComponent

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-- Every nonempty open in a Noetherian space contains an irreducible open. -/
theorem exists_irreducible_open {T : Type*} [TopologicalSpace T] [NoetherianSpace T]
    (W : Opens T) (hW : (W : Set T).Nonempty) :
    ∃ U : Opens T, U ≤ W ∧ IsIrreducible (U : Set T) := by
  obtain ⟨w, hw⟩ := hW
  have : NoetherianSpace W := NoetherianSpace.set (W : Set T)
  let Z := irreducibleComponent (⟨w, hw⟩ : W)
  have hZ : Z ∈ irreducibleComponents W := irreducibleComponent_mem_irreducibleComponents _
  obtain ⟨Q, hQ, hn, hQZ⟩ := NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent Z hZ
  have hcut : Z ∩ Q = Q := Set.inter_eq_right.mpr hQZ
  have hd : Z ⊆ closure Q := by
    rw [← hcut]
    exact subset_closure_inter_of_isPreirreducible_of_isOpen hZ.1.2 hQ (hcut.symm ▸ hn)
  have hc : closure Q = Z := (closure_minimal hQZ (isClosed_of_mem_irreducibleComponents _ hZ)).antisymm hd
  have hirr : IsIrreducible Q := isIrreducible_iff_closure.mp (hc.symm ▸ hZ.1)
  exact ⟨⟨Subtype.val '' Q, W.isOpen.isOpenMap_subtype_val _ hQ⟩,
    fun _ ⟨y, _, hy⟩ ↦ hy ▸ y.property, hirr.image _ continuous_subtype_val.continuousOn⟩

universe u
variable {X Y B : Scheme.{u}}

/-- The schematic image of a quasi-compact morphism from an integral scheme is integral. -/
theorem integral_image (f : X ⟶ Y) [QuasiCompact f] [IsIntegral X] : IsIntegral f.image := by
  have hr : IsIrreducible (Set.range f.toImage) := by
    simpa using (IrreducibleSpace.isIrreducible_univ X).image f.toImage f.toImage.continuous.continuousOn
  have hirr : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def _).mpr
    change IsIrreducible (Set.univ : Set f.image)
    rw [← f.toImage.denseRange.closure_range]
    exact hr.closure
  apply (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨hirr, ?_⟩
  apply (IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
  change ∀ V : Y.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(Y, V.1) ⧸ f.ker.ideal V)))
  intro V
  apply (affine_isReduced_iff _).mpr
  let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ V.1) :=
    isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective V)
  exact isReduced_of_injective (f.ker.subschemeObjIso V).inv.hom
    (f.ker.subschemeObjIso V).symm.commRingCatIsoToRingEquiv.injective

variable [NoetherianSpace X] (j : X ⟶ Y) [IsOpenImmersion j]

private instance compact_open_map (U : X.Opens) : QuasiCompact (U.ι ≫ j) := by
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  infer_instance

/-- The schematic closure in the given compactification of the chosen test open. -/
abbrev Model (U : X.Opens) := (U.ι ≫ j).image

def openInclusion (U : X.Opens) : U.toScheme ⟶ Model j U := (U.ι ≫ j).toImage

instance (U : X.Opens) : IsOpenImmersion (openInclusion j U) :=
  inferInstanceAs (IsOpenImmersion (U.ι ≫ j).toImage)

instance (U : X.Opens) : IsDominant (openInclusion j U) :=
  inferInstanceAs (IsDominant (U.ι ≫ j).toImage)

instance (U : X.Opens) : QuasiCompact (openInclusion j U) := by
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set X)
  infer_instance

def toBase (p : Y ⟶ B) (U : X.Opens) : Model j U ⟶ B := (U.ι ≫ j).imageι ≫ p

omit [NoetherianSpace X] [IsOpenImmersion j] in
@[reassoc (attr := simp)] theorem openInclusion_over (p : Y ⟶ B) (U : X.Opens) :
    openInclusion j U ≫ toBase j p U = U.ι ≫ j ≫ p := by
  simp [openInclusion, toBase, ← Category.assoc]

instance proper (p : Y ⟶ B) [IsProper p] (U : X.Opens) : IsProper (toBase j p U) := by
  unfold toBase
  infer_instance

/-- A prescribed nonempty open contains the dense open of an integral proper model
dominating the coefficient space. -/
theorem exists_model [IsReduced X] [IrreducibleSpace B] (p : Y ⟶ B) [IsProper p]
    [SmoothOfRelativeDimension 1 (j ≫ p)] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ U : X.Opens, U ≤ W ∧ IsIntegral U.toScheme ∧ IsIntegral (Model j U) ∧
      SmoothOfRelativeDimension 1 (openInclusion j U ≫ toBase j p U) ∧
      IsDominant (toBase j p U) ∧ Surjective (toBase j p U) := by
  obtain ⟨D, hle, hD⟩ := exists_irreducible_open W hW
  let U : X.Opens := D
  have hU : IsIrreducible (U : Set X) := hD
  have : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hU
  have hint : IsIntegral U.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have hs : SmoothOfRelativeDimension 1 (U.ι ≫ j ≫ p) := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 U.ι (j ≫ p)
  have : Smooth (U.ι ≫ j ≫ p) := SmoothOfRelativeDimension.smooth 1 _
  have hd : IsDominant (openInclusion j U ≫ toBase j p U) := by
    rw [openInclusion_over]
    exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ (U.ι ≫ j ≫ p).isOpenMap⟩
  have hbase := IsDominant.of_comp (openInclusion j U) (toBase j p U)
  refine ⟨U, hle, hint, integral_image (U.ι ≫ j), ?_, hbase, ?_⟩
  · rwa [openInclusion_over]
  · exact surjective_of_isDominant_of_isClosed_range _ (toBase j p U).isClosedMap.isClosed_range

open CategoryTheory.Limits CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

/-- The monic time family has Noetherian underlying space. -/
instance time_noetherian (V : parameterScheme.Opens) : NoetherianSpace (Time toRaw V) := by
  let _ := Algebra.FiniteType.isNoetherianRing SexticRing ParameterAlgebra
  have : NoetherianSpace parameterScheme :=
    inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of ParameterAlgebra)))
  have : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set parameterScheme)
  exact (pullback.snd toRaw (V.ι ≫ parameterToSextics)).isClosedEmbedding.isInducing.noetherianSpace

theorem monic_exists_model (V : parameterScheme.Opens)
    (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ U : (Time toRaw V).Opens, U ≤ W ∧ IsIntegral U.toScheme ∧ IsIntegral (Model (inclusion V) U) ∧
      SmoothOfRelativeDimension 1 (openInclusion (inclusion V) U ≫ toBase (inclusion V) (structureMap V) U) ∧
      IsDominant (toBase (inclusion V) (structureMap V) U) ∧ Surjective (toBase (inclusion V) (structureMap V) U) := by
  have : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  have : SmoothOfRelativeDimension 1 (inclusion V ≫ structureMap V) := by
    rw [inclusion_over]
    exact timeMap_smooth toRaw V
  exact exists_model (inclusion V) (structureMap V) W hW

end CycleQ2IncidenceIntegralComponent

#print axioms CycleQ2IncidenceIntegralComponent.exists_model
#print axioms CycleQ2IncidenceIntegralComponent.monic_exists_model

end

end

section

noncomputable section

/-!
# The fraction field on the inverse image of a nonempty affine under the generic point

The actual map on sections induced by the generic residue-field point factors
as the germ into the function field followed by a ring isomorphism. Thus the
native section ring used by scheme normalization is the affine fraction field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2GenericPointAffineSections

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u
variable (X : Scheme.{u}) [IsIntegral X]

abbrev point := X.fromSpecResidueField (genericPoint X)

abbrev pointScheme := Spec (X.residueField (genericPoint X))

theorem residue_isIso : IsIso (X.residue (genericPoint X)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨(X.residue (genericPoint X)).hom.injective, X.residue_surjective _⟩

variable (U : X.Opens) [Nonempty U]

private theorem generic_mem : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)

private theorem stalkPreimage_eq_top :
    (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U = ⊤ := by
  apply top_unique
  intro s _
  change (X.fromSpecStalk (genericPoint X)) s ∈ U
  let : Subsingleton (Spec (X.presheaf.stalk (genericPoint X))) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  rw [Subsingleton.elim s (IsLocalRing.closedPoint X.functionField), Scheme.fromSpecStalk_closedPoint]
  exact generic_mem X U

private def chartIsoHom : X.functionField ⟶ Γ(pointScheme X, point X ⁻¹ᵁ U) :=
  (Scheme.ΓSpecIso X.functionField).inv ≫
    (Spec X.functionField).presheaf.map (homOfLE
      (show (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U ≤ ⊤ from le_top)).op ≫
      (Spec.map (X.residue (genericPoint X))).app ((X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U)

private instance : IsIso (chartIsoHom X U) := by
  let T := Spec X.functionField
  let V : T.Opens := (X.fromSpecStalk (genericPoint X)) ⁻¹ᵁ U
  let i : V ⟶ ⊤ := homOfLE le_top
  let f := Spec.map (X.residue (genericPoint X))
  let : IsIso i := homOfLE_isIso_of_eq (show V ≤ ⊤ from le_top) (stalkPreimage_eq_top X U)
  let : IsIso (T.presheaf.map i.op) := inferInstance
  let : IsIso (X.residue (genericPoint X)) := residue_isIso X
  let : IsIso f := inferInstanceAs (IsIso (Spec.map (X.residue (genericPoint X))))
  let : IsIso (f.app V) := inferInstance
  change IsIso ((Scheme.ΓSpecIso X.functionField).inv ≫ T.presheaf.map i.op ≫ f.app V)
  exact IsIso.comp_isIso

def chartIso : X.functionField ≅ Γ(pointScheme X, point X ⁻¹ᵁ U) := asIso (chartIsoHom X U)

@[reassoc] theorem germ_chartIso :
    X.germToFunctionField U ≫ (chartIso X U).hom = (point X).app U := by
  change _ = (Spec.map (X.residue (genericPoint X)) ≫ X.fromSpecStalk (genericPoint X)).app U
  rw [Scheme.Hom.comp_app, Scheme.fromSpecStalk_app (generic_mem X U)]
  simp only [chartIso, asIso_hom, chartIsoHom, Category.assoc]
  rfl

theorem native_isField : IsField Γ(pointScheme X, point X ⁻¹ᵁ U) :=
  (chartIso X U).symm.commRingCatIsoToRingEquiv.isField (Field.toIsField X.functionField)

def chartAlgEquiv :
    let := ((point X).app U).hom.toAlgebra
    X.functionField ≃ₐ[Γ(X,U)] Γ(pointScheme X, point X ⁻¹ᵁ U) := by
  let := ((point X).app U).hom.toAlgebra
  exact { (chartIso X U).commRingCatIsoToRingEquiv with
    commutes' := fun a => congrArg (fun f : Γ(X,U) ⟶ _ => f a) (germ_chartIso X U) }

theorem native_isFractionRing (hU : IsAffineOpen U) :
    let := ((point X).app U).hom.toAlgebra
    IsFractionRing Γ(X,U) Γ(pointScheme X, point X ⁻¹ᵁ U) := by
  let := ((point X).app U).hom.toAlgebra
  have := functionField_isFractionRing_of_isAffineOpen X U hU
  exact IsFractionRing.of_algEquiv (chartAlgEquiv X U)

end CycleQ2GenericPointAffineSections
end

#print axioms CycleQ2GenericPointAffineSections.native_isFractionRing

end

end

section

noncomputable section

/-!
# Smoothness of a finite-type Dedekind domain over a perfect field

A local uniformizer at a closed point gives an étale coordinate over the
affine line. Smoothness then follows at every generalization of the point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



open IsLocalRing Polynomial
open scoped Polynomial

namespace CycleQ2NormalCurveSmooth

variable {K A : Type*} [Field K] [PerfectField K] [CommRing A]
  [Algebra K A] [Algebra.FiniteType K A]

/-- A uniformizer on the localization at a nonzero prime can be chosen in the original ring. -/
theorem exists_local_parameter [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ a ∈ q, a ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap A (Localization.AtPrime q) a} := by
  let B := Localization.AtPrime q
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq B
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj q.primeCompl z
  change z * algebraMap A B s = algebraMap A B a at hs
  have ha : Associated z (algebraMap A B a) := by
    rw [← hs]
    exact associated_mul_unit_right _ _ (IsLocalization.map_units B s)
  have hgen := hz.maximalIdeal_eq.trans (Ideal.span_singleton_eq_span_singleton.mpr ha)
  refine ⟨a, (IsLocalization.AtPrime.to_map_mem_maximal_iff B q a).mp ?_, ?_, hgen⟩
  · rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton _)
  · intro he
    exact (ha.irreducible hz).ne_zero (by simp [he])

/-- A uniformizer defines an étale coordinate, giving smoothness at the closed point. -/
theorem isSmoothAt_of_local_parameter [IsDomain A] (q : Ideal A) [q.IsMaximal] (a : A) (ha : a ∈ q)
    (h0 : a ≠ 0) (hgen : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap A (Localization.AtPrime q) a}) : Algebra.IsSmoothAt K q := by
  let : Algebra K[X] A := (aeval a).toAlgebra
  have : IsScalarTower K K[X] A := .of_algebraMap_eq fun x ↦ ((aeval a).commutes x).symm
  have : Algebra.FiniteType K[X] A := .of_restrictScalars_finiteType K _ _
  have : Algebra.FinitePresentation K[X] A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Module.IsTorsionFree K[X] A := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (transcendental_iff_injective.mp fun h ↦ (inferInstance : q.IsPrime).ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ha ((isAlgebraic_iff_isIntegral.mp h).isUnit h0))
  let p := q.under K[X]
  have hX : (X : K[X]) ∈ p := by
    change aeval a (X : K[X]) ∈ q
    simpa using ha
  have : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance fun h ↦
    Polynomial.X_ne_zero (R := K) (by simpa [h] using hX)
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field q
  have : Module.Finite K (K[X] ⧸ p) := finite_of_finite_type_of_isJacobsonRing _ _
  have : PerfectField (K[X] ⧸ p) := Algebra.IsAlgebraic.perfectField K
  have : Module.Finite (K[X] ⧸ p) (A ⧸ q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.IsUnramifiedAt K[X] q := by
    apply (Algebra.isUnramifiedAt_iff_map_eq _ p q).mpr
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply K[X] A (Localization.AtPrime q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr hx
    · rw [hgen, Ideal.span_singleton_le_iff_mem]
      have he : algebraMap K[X] (Localization.AtPrime q) X =
          algebraMap A (Localization.AtPrime q) a := by
        rw [IsScalarTower.algebraMap_apply K[X] A (Localization.AtPrime q)]
        change algebraMap A (Localization.AtPrime q) (aeval a (X : K[X])) = _
        rw [aeval_X]
      rw [← he]
      exact Ideal.mem_map_of_mem _ hX
  have := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := K[X]) q
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime q)

/-- A finite-type normal affine curve over a perfect field is smooth. -/
theorem smooth_of_isDedekindDomain [IsDedekindDomain A] : Algebra.Smooth K A := by
  have : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  by_cases hF : IsField A
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun x ↦ ?_), ‹_›⟩
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  obtain ⟨a, ha, h0, hgen⟩ := exists_local_parameter m (Ring.ne_bot_of_isMaximal_of_not_isField hm hF)
  have hsm : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus K A :=
    isSmoothAt_of_local_parameter m a ha h0 hgen
  exact ((PrimeSpectrum.le_iff_specializes x ⟨m, hm.isPrime⟩).mp hxm).mem_open
    Algebra.isOpen_smoothLocus hsm

/-- Smoothness written in terms of normality, dimension and finite type on an affine chart. -/
theorem smooth_of_normal_affine_curve (K B : Type*) [Field K] [PerfectField K] [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    [Ring.KrullDimLE 1 B] [IsIntegrallyClosed B] : Algebra.Smooth K B := by
  have : Ring.DimensionLEOne B := ⟨fun hn hp ↦ hp.isMaximal_of_ne_bot hn⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : IsDedekindDomain B := { ‹IsDomain B›, ‹IsNoetherianRing B›,
    ‹Ring.DimensionLEOne B›, ‹IsIntegrallyClosed B› with }
  exact smooth_of_isDedekindDomain

/-- The finite integral closure of an affine curve domain in a field is smooth
over its perfect coefficient field. -/
theorem smooth_finite_integralClosure (K R L : Type*) [Field K] [PerfectField K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [Ring.KrullDimLE 1 R]
    [Field L] [Algebra R L] [Module.Finite R (integralClosure R L)] :
    let := ((algebraMap R (integralClosure R L)).comp (algebraMap K R)).toAlgebra
    Algebra.Smooth K (integralClosure R L) := by
  have : Ring.DimensionLEOne R := ⟨fun hn hp ↦ hp.isMaximal_of_ne_bot hn⟩
  let B := integralClosure R L
  let := ((algebraMap R B).comp (algebraMap K R)).toAlgebra
  have : IsScalarTower K R B := .of_algebraMap_eq' rfl
  have : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K R) inferInstance
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  exact smooth_of_normal_affine_curve K B

open AlgebraicGeometry CategoryTheory

universe u

/-- Normal affine curve charts cover a smooth scheme over a perfect field. -/
theorem smooth_of_normal_affine_cover (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (C : X.OpenCover)
    (B : C.I₀ → Type u) [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, Algebra K (B i)] [∀ i, Algebra.FiniteType K (B i)]
    [∀ i, Ring.KrullDimLE 1 (B i)] [∀ i, IsIntegrallyClosed (B i)]
    (e : ∀ i, C.X i ≅ Spec (CommRingCat.of (B i)))
    (he : ∀ i, C.f i ≫ f = (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B i)))) :
    Smooth f := by
  have hl : IsZariskiLocalAtSource (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  refine (@IsZariskiLocalAtSource.iff_of_openCover (@Smooth.{u}) hl _ _ f C).mpr fun i ↦ ?_
  rw [he]
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (B i)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (smooth_of_normal_affine_curve K (B i)))
  infer_instance

end CycleQ2NormalCurveSmooth

#print axioms CycleQ2NormalCurveSmooth.smooth_of_normal_affine_curve

#print axioms CycleQ2NormalCurveSmooth.smooth_finite_integralClosure

#print axioms CycleQ2NormalCurveSmooth.smooth_of_normal_affine_cover

end

end

section

noncomputable section

/-!
# Absolute normalization of an integral proper curve

Normalizing in the scheme's own generic residue field gives a finite map.
In dimension at most one its source is smooth over the characteristic-zero
base field, and it is proper whenever the original curve is proper.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2IntegralCurveNormalization

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GenericPointAffineSections
open scoped nonZeroDivisors

/-- Noether normalization and separability give a finite integral closure inside
any chosen fraction field of a finite-type domain over a characteristic-zero field. -/
theorem finite_fraction_integralClosure (k A L : Type*) [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field L] [Algebra A L]
    [IsFractionRing A L] : Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let N := integralClosure A L
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : Algebra P L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A L := .of_algebraMap_eq' rfl
  let : FaithfulSMul P L := (faithfulSMul_iff_algebraMap_injective P L).mpr
    ((IsFractionRing.injective A L).comp hinj)
  let : Algebra (FractionRing P) L := FractionRing.liftAlgebra P L
  let : FiniteDimensional (FractionRing P) L := Module.Finite.of_isLocalization P A P⁰
  let : Algebra P N := ((algebraMap A N).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A N := .of_algebraMap_eq' rfl
  let : IsScalarTower P N L := .of_algebraMap_eq' rfl
  let : IsIntegralClosure N P L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      exact ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩,
        fun ⟨y, hy⟩ => hy ▸ isIntegral_trans (R := P) (y : L) y.property⟩ }
  let : Module.Finite P N := IsIntegralClosure.finite P (FractionRing P) L N
  exact Module.Finite.of_restrictScalars_finite P A N

universe u

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]

abbrev Model (X : Scheme.{u}) [IsIntegral X] := (point X).normalization

abbrev normalize (X : Scheme.{u}) [IsIntegral X] : Model X ⟶ X := (point X).fromNormalization

variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

def coefficientMap (U : X.Opens) : CommRingCat.of k ⟶ Γ(X,U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp)

omit [CharZero k] [IsIntegral X] in
theorem finiteType_coefficients {U : X.Opens} (hU : IsAffineOpen U) :
    (coefficientMap k p U).hom.FiniteType :=
  (p.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)

omit [CharZero k] [IsIntegral X] [LocallyOfFiniteType p] in
theorem fromSpec_over {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (coefficientMap k p U) := by
  rw [coefficientMap, Spec.map_comp]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  exact h.symm

omit [IsIntegral X] in
theorem nonempty_chart {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X,U)] : Nonempty U :=
  Nonempty.map hU.isoSpec.inv (inferInstance : Nonempty (Spec Γ(X,U)))

include p in
theorem finite_chart {U : X.Opens} (hU : IsAffineOpen U) :
    let := ((point X).app U).hom.toAlgebra
    Module.Finite Γ(X,U) (integralClosure Γ(X,U) Γ(pointScheme X, point X ⁻¹ᵁ U)) := by
  let A := Γ(X,U)
  let L := Γ(pointScheme X, point X ⁻¹ᵁ U)
  let : Algebra A L := ((point X).app U).hom.toAlgebra
  rcases subsingleton_or_nontrivial A with h | h
  · let : Subsingleton (integralClosure A L) := Algebra.subsingleton A _
    infer_instance
  let : Nonempty U := nonempty_chart hU
  let : Field L := (native_isField X U).toField
  let : IsFractionRing A L := native_isFractionRing X U hU
  let : Algebra k A := (coefficientMap k p U).hom.toAlgebra
  let : Algebra.FiniteType k A := finiteType_coefficients k p hU
  exact finite_fraction_integralClosure k A L

include p in
theorem finite : IsFinite (normalize X) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  rw [Scheme.Hom.fromNormalization_app _ hU, CommRingCat.hom_comp]
  let := ((point X).app U).hom.toAlgebra
  exact (RingHom.Finite.of_surjective _ ((point X).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.surjective).comp
    (RingHom.finite_algebraMap.mpr (finite_chart k p hU))

omit [LocallyOfFiniteType p] in
theorem proper [IsProper p] : IsProper (normalize X ≫ p) := by
  have := finite k p
  infer_instance

theorem smooth_of_affine_dimension (hdim : ∀ U : X.affineOpens, Ring.KrullDimLE 1 Γ(X, U.1)) :
    Smooth (normalize X ≫ p) := by
  let j := point X
  have hl : IsZariskiLocalAtSource (@Smooth.{u} : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{u}) (Q := RingHom.Smooth)
  apply (@IsZariskiLocalAtSource.iff_of_openCover (@Smooth.{u}) hl _ _
    (j.fromNormalization ≫ p) j.normalizationOpenCover).mpr
  intro i
  let U : X.affineOpens := i
  change Smooth (j.normalizationOpenCover.f U ≫ j.fromNormalization ≫ p)
  erw [j.ι_fromNormalization_assoc, Category.assoc, fromSpec_over k p U.2, ← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  let A := Γ(X,U.1)
  let L := Γ(pointScheme X, j ⁻¹ᵁ U.1)
  let : Algebra A L := (j.app U.1).hom.toAlgebra
  let N := integralClosure A L
  let : Algebra k A := (coefficientMap k p U.1).hom.toAlgebra
  let : Algebra k N := ((algebraMap A N).comp (algebraMap k A)).toAlgebra
  change (algebraMap k N).Smooth
  apply RingHom.smooth_algebraMap.mpr
  rcases subsingleton_or_nontrivial A with h | h
  · let : Subsingleton N := Algebra.subsingleton A _
    infer_instance
  let : Nonempty U.1 := nonempty_chart U.2
  let : Field L := (native_isField X U.1).toField
  let : Algebra.FiniteType k A := finiteType_coefficients k p U.2
  let : Ring.KrullDimLE 1 A := hdim U
  let : Module.Finite A N := finite_chart k p U.2
  exact CycleQ2NormalCurveSmooth.smooth_finite_integralClosure k A L

theorem smooth (hdim : topologicalKrullDim X ≤ 1) : Smooth (normalize X ≫ p) := by
  apply smooth_of_affine_dimension k p
  intro U
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  let : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  exact (U.2.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdim

end CycleQ2IntegralCurveNormalization
end

#print axioms CycleQ2IntegralCurveNormalization.finite
#print axioms CycleQ2IntegralCurveNormalization.proper
#print axioms CycleQ2IntegralCurveNormalization.smooth_of_affine_dimension
#print axioms CycleQ2IntegralCurveNormalization.smooth

end

end

section

noncomputable section

/-!
# Recovering a neighborhood of the generic point through the normalization

The section at the generic stalk spreads to an actual open of the curve.
Pullback by this section recovers the original family on that open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2IntegralCurveNormalization

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GenericPointAffineSections

universe u
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

include p in
/-- A section of the finite normalization exists on an open containing the
actual generic point of the original curve. -/
theorem dominant_section_over_generic_open : ∃ (U : X.Opens), genericPoint X ∈ U ∧
    ∃ σ : U.toScheme ⟶ Model X, IsDominant σ ∧ σ ≫ normalize X = U.ι := by
  have := finite k p
  have := residue_isIso X
  let φ := Spec.map (inv (X.residue (genericPoint X))) ≫ (point X).toNormalization
  have hφ : φ ≫ normalize X = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    rw [Category.comp_id]
    change (_ ≫ (point X).toNormalization) ≫ (point X).fromNormalization = _
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    change Spec.map (inv _) ≫ Spec.map (X.residue (genericPoint X)) ≫ X.fromSpecStalk _ = _
    rw [← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  obtain ⟨U, hU, σ, hφσ, hσ⟩ := spread_out_of_isGermInjective' (𝟙 X) (normalize X) φ hφ
  have : IsDominant φ := by dsimp [φ]; infer_instance
  have : IsDominant (U.fromSpecStalkOfMem _ hU ≫ σ) := by rw [← hφσ]; infer_instance
  exact ⟨U, hU, σ, IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) σ, hσ.trans (Category.comp_id _)⟩

include p in
theorem section_over_generic_open : ∃ (U : X.Opens), genericPoint X ∈ U ∧
    ∃ σ : U.toScheme ⟶ Model X, σ ≫ normalize X = U.ι := by
  obtain ⟨U, hU, σ, _, hσ⟩ := dominant_section_over_generic_open k p
  exact ⟨U, hU, σ, hσ⟩

private theorem restriction_iso_of_dominant_section {N Y : Scheme.{u}} [IsReduced N]
    (ν : N ⟶ Y) [IsSeparated ν] (U : Y.Opens) (σ : U.toScheme ⟶ N) [IsDominant σ]
    (hσ : σ ≫ ν = U.ι) : IsIso (ν ∣_ U) := by
  let h := isPullback_morphismRestrict ν U
  have w : 𝟙 _ ≫ U.ι = σ ≫ ν := by rw [Category.id_comp, hσ]
  let τ := h.lift (𝟙 _) σ w
  have hτ : τ ≫ (ν ∣_ U) = 𝟙 _ := h.lift_fst _ _ _
  have hτ' : τ ≫ (ν ⁻¹ᵁ U).ι = σ := h.lift_snd _ _ _
  have : IsDominant (τ ≫ (ν ⁻¹ᵁ U).ι) := by rw [hτ']; infer_instance
  have : IsDominant τ := IsDominant.of_comp_of_isOpenImmersion _ (ν ⁻¹ᵁ U).ι
  have : IsClosedImmersion (τ ≫ (ν ∣_ U)) := by rw [hτ]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ (ν ∣_ U)
  have : Surjective τ := surjective_of_isDominant_of_isClosed_range τ τ.isClosedEmbedding.isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective τ
  exact IsIso.of_isIso_fac_left hτ

include p in
/-- The absolute normalization is an isomorphism above a neighborhood of the
generic point. The whole inverse image recovers the original open. -/
theorem iso_over_generic_open :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (normalize X ∣_ U) := by
  obtain ⟨U, hU, σ, hdom, hσ⟩ := dominant_section_over_generic_open k p
  have := finite k p
  exact ⟨U, hU, restriction_iso_of_dominant_section (normalize X) U σ hσ⟩

end CycleQ2IntegralCurveNormalization
end

#print axioms CycleQ2IntegralCurveNormalization.section_over_generic_open
#print axioms CycleQ2IntegralCurveNormalization.iso_over_generic_open

end

end

section

noncomputable section

/-!
# Affine chart dimension from a dense smooth curve

A Noether normalization of an affine chart maps its dense smooth open to
affine space. The residue-field transcendence-degree bound for that image
forces the normalization to have at most one polynomial variable.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2CurveChartDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2SweptSupport

private def affinePresentation (K : Type) [Field K] (s : ℕ) :
    Algebra.PreSubmersivePresentation K (MvPolynomial (Fin s) K) (Fin s) Empty where
  toPresentation :=
    { toGenerators := Algebra.Generators.mvPolynomial K (Fin s)
      relation := Empty.elim
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_mvPolynomial]; simp }
  map := Empty.elim
  map_inj := by intro a; exact a.elim

private theorem affine_smooth (K : Type) [Field K] (s : ℕ) : SmoothOfRelativeDimension s
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin s) K))) := by
  let P : Algebra.SubmersivePresentation K (MvPolynomial (Fin s) K) (Fin s) Empty :=
    { toPreSubmersivePresentation := affinePresentation K s
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hs : Algebra.IsStandardSmoothOfRelativeDimension s K (MvPolynomial (Fin s) K) :=
    P.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Fin s) - Nat.card Empty = s
      simp [Nat.card_eq_fintype_card])
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension s)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap s).mpr hs)

private theorem polynomial_dim (K : Type) [Field K] {s : ℕ} (hs : s ≤ 1) :
    Ring.DimensionLEOne (MvPolynomial (Fin s) K) := by
  interval_cases s
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.isEmptyRingEquiv K (Fin 0))
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv

private theorem dim_of_finite {K : Type} [Field K] {s : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (g : MvPolynomial (Fin s) K →ₐ[K] A) (hf : g.IsIntegral) (hs : s ≤ 1) :
    Ring.KrullDimLE 1 A := by
  let P := MvPolynomial (Fin s) K
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hf⟩
  have hP : Ring.DimensionLEOne P := polynomial_dim K hs
  rw [Ring.krullDimLE_iff]
  have hdim : ringKrullDim A ≤ ringKrullDim P :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A)) (fun _ _ h =>
      Ideal.IsIntegral.comap_lt_comap h)
  exact hdim.trans (Ring.krullDimLE_iff.mp inferInstance)

/-- Every affine chart of a finite-type scheme with a dense smooth curve open has dimension at most one. -/
theorem chart_dimension {K : Type} [Field K] {X B : Scheme.{0}} [NoetherianSpace X]
    (j : X ⟶ B) [IsOpenImmersion j] [IsDominant j]
    (p : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    [SmoothOfRelativeDimension 1 (j ≫ p)] {V : B.Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE 1 Γ(B, V) := by
  let A := Γ(B, V)
  rcases subsingleton_or_nontrivial A with h | h
  · exact Ring.krullDimLE_iff.mpr (by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le)
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appLE ⊤ V hle
  let : Algebra K A := c.hom.toAlgebra
  let : Algebra.FiniteType K A := (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp
    (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K A
  apply dim_of_finite g hi
  by_contra! hs
  let Y := (j ⁻¹ᵁ V).toScheme
  let a : Y ⟶ Spec A := CycleQ2DenseOpenAffineSections.chart j hV
  let b := Spec.map (CommRingCat.ofHom g.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin s) K))
  let px := (j ⁻¹ᵁ V).ι ≫ j ≫ p
  let : NoetherianSpace Y := NoetherianSpace.set (j ⁻¹ᵁ V : Set X)
  let : SmoothOfRelativeDimension 1 px := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 (j ⁻¹ᵁ V).ι (j ≫ p)
  let : SmoothOfRelativeDimension s q := affine_smooth K s
  have ha : DenseRange a := by
    have : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance V
    let : IsDominant a := by dsimp [a, CycleQ2DenseOpenAffineSections.chart]; infer_instance
    exact a.denseRange
  have hb : DenseRange b := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.toRingHom).mpr
    rw [(RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hg]
    exact bot_le
  have hc : Spec.map c = hV.fromSpec ≫ p := by
    rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hbq : b ≫ q = Spec.map c := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext g.commutes
  have fac : (a ≫ b) ≫ q = px := by
    rw [Category.assoc, hbq, hc]
    change ((j ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec ≫ p = _
    simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc, Category.assoc,
      morphismRestrict_ι_assoc, px]
  exact (closure_range_ne_univ 1 s hs px q (genericPolynomialPoint K s) (a ≫ b) fac)
    (denseRange_iff_closure_range.mp (hb.comp ha b.continuous))

/-- On an integral scheme of finite type over a field, a single nonempty smooth curve
open bounds the dimension of all affine charts. -/
theorem chart_dimension_of_nonempty_smooth_open {K : Type} [Field K] {B : Scheme.{0}}
    [IsIntegral B] (p : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (U : B.Opens) (hU : (U : Set B).Nonempty) [SmoothOfRelativeDimension 1 (U.ι ≫ p)]
    {V : B.Opens} (hV : IsAffineOpen V) : Ring.KrullDimLE 1 Γ(B, V) := by
  have : IsDominant U.ι := ⟨by
    change Dense (Set.range U.ι)
    simpa using U.isOpen.dense hU⟩
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian B := ⟨⟩
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set B)
  exact chart_dimension U.ι p hV

end CycleQ2CurveChartDimension

#print axioms CycleQ2CurveChartDimension.chart_dimension
#print axioms CycleQ2CurveChartDimension.chart_dimension_of_nonempty_smooth_open

end

end

section

noncomputable section

/-!
# The proper generic parameter curve over the monic sextic function field

On the generic coefficient fiber the original smooth time open is dense in
the finite model. Every affine chart of the proper fiber has Krull dimension
at most one. The generic fiber is nonempty for the marked time neighborhood.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2LiteralIncidenceGenericModel

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeNormalization

abbrev K := FractionRing MonicRing

def genericMorphism : Spec (CommRingCat.of K) ⟶ monicBase :=
  Spec.map (CommRingCat.ofHom (algebraMap MonicRing K))

instance : Flat genericMorphism := by
  apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

theorem generic_value (s : Spec (CommRingCat.of K)) :
    IsGenericPoint (genericMorphism s) Set.univ := by
  have hd : DenseRange genericMorphism := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (algebraMap MonicRing K)).mpr
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective MonicRing K)]
    exact bot_le
  have hr : Set.range genericMorphism = {genericMorphism s} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg genericMorphism (Subsingleton.elim z s)
    · rintro rfl
      exact ⟨s, rfl⟩
  change closure {genericMorphism s} = Set.univ
  rw [← hr]
  exact hd.closure_range

variable (V : parameterScheme.Opens)

abbrev Fiber := pullback genericMorphism (normalizedMap V)

abbrev projection : Fiber V ⟶ Spec (CommRingCat.of K) := pullback.fst _ _

abbrev TimeFiber := pullback (pullback.snd genericMorphism (normalizedMap V)) (openInclusion V)

abbrev inclusion : TimeFiber V ⟶ Fiber V := pullback.fst _ _

theorem noetherian_of_proper {X Y : Scheme} [IsNoetherian Y] (p : X ⟶ Y)
    [IsProper p] : NoetherianSpace X := by
  have := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := ⟨⟩
  infer_instance

instance : IsDominant (inclusion V) := by
  have : IsNoetherian monicBase := inferInstanceAs (IsNoetherian (Spec (CommRingCat.of MonicRing)))
  have : NoetherianSpace (Model V) := noetherian_of_proper (normalizedMap V)
  have : NoetherianSpace (Time toRaw V) :=
    (openInclusion V).isOpenEmbedding.isInducing.noetherianSpace
  exact CycleQ2DominantFlatBaseChange.pullback_fst_dominant _ _

theorem generic_open_smooth {X Y : Scheme} (j : X ⟶ Y) (p : Y ⟶ monicBase)
    (hs : SmoothOfRelativeDimension 1 (j ≫ p)) :
    SmoothOfRelativeDimension 1
      (pullback.fst (pullback.snd genericMorphism p) j ≫ pullback.fst genericMorphism p) := by
  let e := pullbackLeftPullbackSndIso genericMorphism p j
  let q := pullback.fst (pullback.snd genericMorphism p) j ≫ pullback.fst genericMorphism p
  let a := pullback.fst genericMorphism (j ≫ p)
  have he : e.inv ≫ q = a := pullbackLeftPullbackSndIso_inv_fst ..
  have hq : q = e.hom ≫ a := by
    exact (e.hom_inv_id_assoc q).symm.trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => e.hom ≫ k) he))
  have ha : SmoothOfRelativeDimension 1 a :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback genericMorphism (j ≫ p)).flip hs
  letI : SmoothOfRelativeDimension 1 a := ha
  change SmoothOfRelativeDimension 1 q
  rw [hq]
  simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 e.hom a

instance : SmoothOfRelativeDimension 1 (inclusion V ≫ projection V) :=
  generic_open_smooth _ _ (normalized_time_model V).2.2.2

instance : AlgebraicGeometry.IsReduced (TimeFiber V) :=
  reduced_of_smooth_over_domain 1 (inclusion V ≫ projection V)

/-- Any nonempty marked test open survives on the generic coefficient fiber. -/
theorem test_meets_generic (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ x : TimeFiber V, pullback.snd (pullback.snd genericMorphism (normalizedMap V)) (openInclusion V) x ∈ W := by
  have := timeMap_smooth toRaw V
  have : Smooth (timeMap toRaw V) := SmoothOfRelativeDimension.smooth 1 _
  have hg := ((generic_value default).mem_open_set_iff ((timeMap toRaw V).isOpenMap _ W.isOpen)).mpr
    (by simpa only [Set.univ_inter] using hW.image (timeMap toRaw V))
  obtain ⟨y, hy, he⟩ := hg
  have h : genericMorphism default = (openInclusion V ≫ normalizedMap V) y := by
    rw [open_over]
    exact he.symm
  obtain ⟨z, _, hz⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := genericMorphism) (g := openInclusion V ≫ normalizedMap V) default y h
  refine ⟨(pullbackLeftPullbackSndIso genericMorphism (normalizedMap V) (openInclusion V)).inv z, ?_⟩
  rwa [← Scheme.Hom.comp_apply, pullbackLeftPullbackSndIso_inv_snd_snd, hz]

/-- The dimension bound holds on every affine chart, including those meeting the boundary. -/
theorem chart_dimension {W : (Fiber V).Opens} (hW : IsAffineOpen W) :
    Ring.KrullDimLE 1 Γ(Fiber V, W) := by
  have : NoetherianSpace (Fiber V) := noetherian_of_proper (projection V)
  have : NoetherianSpace (TimeFiber V) := (inclusion V).isOpenEmbedding.isInducing.noetherianSpace
  exact CycleQ2CurveChartDimension.chart_dimension (inclusion V) (projection V) hW

/-- A marked neighborhood has a nonempty proper generic fiber and its smooth open is dense. -/
theorem exists_proper_generic_curve (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧ Surjective (projection V) ∧
      IsProper (projection V) ∧ IsDominant (inclusion V) ∧
      SmoothOfRelativeDimension 1 (inclusion V ≫ projection V) ∧
      ∀ W : (Fiber V).affineOpens, Ring.KrullDimLE 1 Γ(Fiber V, W.1) := by
  obtain ⟨W, hW, _, _, _, _, _, hsur⟩ := exists_surjective_completion t hi
  have : IsDominant (openInclusion W ≫ toCompletion W) := by rw [open_toCompletion]; infer_instance
  have := IsDominant.of_comp (openInclusion W) (toCompletion W)
  have : Surjective (toCompletion W) :=
    surjective_of_isDominant_of_isClosed_range _ (toCompletion W).isClosedMap.isClosed_range
  have : Surjective (normalizedMap W) := by unfold normalizedMap; infer_instance
  exact ⟨W, hW, inferInstance, inferInstance, inferInstance, inferInstance, fun U =>
    chart_dimension W U.2⟩

end CycleQ2LiteralIncidenceGenericModel
end

#print axioms CycleQ2LiteralIncidenceGenericModel.test_meets_generic
#print axioms CycleQ2LiteralIncidenceGenericModel.exists_proper_generic_curve

end

end

section

noncomputable section

/-!
# A proper smooth generic curve retaining a prescribed time test

Take the schematic closure of an irreducible open of the generic time fiber
inside the proper fiber and normalize in its function field. A dense open of the
resulting smooth proper integral curve comes from the original test through the
original time and fiber maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


namespace CycleQ2LiteralIncidenceGenericSmoothCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceGenericModel

variable (V : parameterScheme.Opens)

abbrev testMap : TimeFiber V ⟶ Time toRaw V :=
  pullback.snd _ (CycleQ2LiteralIncidenceRelativeNormalization.openInclusion V)

private theorem recover_open {T X : Scheme} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType p] (a : T ⟶ X) [IsOpenImmersion a] [IsDominant a] :
    ∃ D : T.Opens, (D : Set T).Nonempty ∧
      ∃ d : D.toScheme ⟶ CycleQ2IntegralCurveNormalization.Model X,
        IsOpenImmersion d ∧ IsDominant d ∧
        d ≫ CycleQ2IntegralCurveNormalization.normalize X = D.ι ≫ a := by
  let n := CycleQ2IntegralCurveNormalization.normalize X
  obtain ⟨G, hG, hi⟩ := CycleQ2IntegralCurveNormalization.iso_over_generic_open K p
  let D := a ⁻¹ᵁ G
  have hD : (D : Set T).Nonempty := a.denseRange.exists_mem_open G.isOpen ⟨_, hG⟩
  let d := (a ∣_ G) ≫ inv (n ∣_ G) ≫ (n ⁻¹ᵁ G).ι
  have : IsOpenImmersion d := by dsimp only [d]; infer_instance
  have : Nonempty D.toScheme := hD.to_subtype
  have hd : IsDominant d := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ d.isOpenMap⟩
  refine ⟨D, hD, d, inferInstance, hd, ?_⟩
  change (a ∣_ G ≫ inv (n ∣_ G) ≫ (n ⁻¹ᵁ G).ι) ≫ n = D.ι ≫ a
  rw [Category.assoc, Category.assoc, ← morphismRestrict_ι n G,
    ← Category.assoc (inv (n ∣_ G)) (n ∣_ G), IsIso.inv_hom_id, Category.id_comp]
  exact morphismRestrict_ι a G

private instance time_noetherian : NoetherianSpace (TimeFiber V) := by
  have : NoetherianSpace (Fiber V) := noetherian_of_proper (projection V)
  exact (inclusion V).isOpenEmbedding.isInducing.noetherianSpace

/-- The smooth proper generic curve contains a dense open from the original test.
The maps to the compactified fiber and to the test agree with the given projections. -/
theorem test_proper_smooth_curve (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ (U : (TimeFiber V).Opens) (hle : U ≤ (testMap V) ⁻¹ᵁ W), IsIntegral U.toScheme ∧
      ∃ hI : IsIntegral (CycleQ2IncidenceIntegralComponent.Model (inclusion V) U),
        let C := @CycleQ2IntegralCurveNormalization.Model _ hI
        let n := @CycleQ2IntegralCurveNormalization.normalize _ hI
        let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (projection V) U
        IsIntegral C ∧ IsFinite n ∧ IsProper (n ≫ p) ∧ Smooth (n ≫ p) ∧ Surjective (n ≫ p) ∧
        (∀ A : C.affineOpens, Ring.KrullDimLE 1 Γ(C, A.1)) ∧
        ∃ D : U.toScheme.Opens, (D : Set U.toScheme).Nonempty ∧
          ∃ d : D.toScheme ⟶ C, IsOpenImmersion d ∧ IsDominant d ∧
            SmoothOfRelativeDimension 1 (d ≫ n ≫ p) ∧
            d ≫ n = D.ι ≫ CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U ∧
            d ≫ n ≫ (U.ι ≫ inclusion V).imageι = D.ι ≫ U.ι ≫ inclusion V ∧
            (D.ι ≫ (testMap V).resLE W U hle) ≫ W.ι = D.ι ≫ U.ι ≫ testMap V ∧
            ∃ O : C.Opens, Dense (O : Set C) ∧
              ∃ e : D.toScheme ≅ O.toScheme, e.hom ≫ O.ι = d := by
  obtain ⟨x, hx⟩ := test_meets_generic V W hW
  obtain ⟨U, hle, hU, hI, hs, _, _⟩ :=
    CycleQ2IncidenceIntegralComponent.exists_model (inclusion V) (projection V)
      ((testMap V) ⁻¹ᵁ W) ⟨x, hx⟩
  let Y := CycleQ2IncidenceIntegralComponent.Model (inclusion V) U
  let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (projection V) U
  let a := CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U
  let n := CycleQ2IntegralCurveNormalization.normalize Y
  have : IsFinite n := CycleQ2IntegralCurveNormalization.finite K p
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set (TimeFiber V))
  have hdY (A : Y.affineOpens) : Ring.KrullDimLE 1 Γ(Y,A.1) :=
    CycleQ2CurveChartDimension.chart_dimension a p A.2
  have hp := CycleQ2IntegralCurveNormalization.proper K p
  have hsm := CycleQ2IntegralCurveNormalization.smooth_of_affine_dimension K p hdY
  have hsur : Surjective (n ≫ p) :=
    ⟨fun z => ⟨Classical.choice (inferInstance : Nonempty (CycleQ2IntegralCurveNormalization.Model Y)),
      Subsingleton.elim _ z⟩⟩
  obtain ⟨D, hD, d, hdo, hdd, hdn⟩ := recover_open p a
  have : NoetherianSpace D.toScheme := NoetherianSpace.set (D : Set U.toScheme)
  have hdsm : SmoothOfRelativeDimension 1 (d ≫ n ≫ p) := by
    rw [← Category.assoc, hdn, Category.assoc]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 D.ι (a ≫ p)
  refine ⟨U, hle, hU, hI, inferInstance, inferInstance, hp, hsm, hsur, fun A =>
    CycleQ2CurveChartDimension.chart_dimension d (n ≫ p) A.2, D, hD, d, hdo, hdd, hdsm, hdn, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hdn, Category.assoc]
    simp [a, CycleQ2IncidenceIntegralComponent.openInclusion]
  · rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
  · exact ⟨d.opensRange, d.denseRange, d.isoOpensRange, d.isoOpensRange_hom_ι⟩

end CycleQ2LiteralIncidenceGenericSmoothCurve
end

#print axioms CycleQ2LiteralIncidenceGenericSmoothCurve.test_proper_smooth_curve

end

end

section

noncomputable section

/-!
# The actual closed graph over the smooth generic time curve

Pulling back the original closed graph to a generic time model gives a
closed correspondence with the same strict target support. Over any
open which maps to the original time family this base change recovers
the original embedded curves by a cartesian square.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/



namespace CycleQ2GenericSmoothCurveGraph

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
  CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
  CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
  CycleQ2LiteralIncidenceGenericCorrespondence
open CycleQ2IncidenceEtaleParameter (parameterScheme)

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
variable {C : Scheme} (p : C ⟶ Completion V)

abbrev Graph := pullback p (timeProjection V t)

abbrev toCurve : Graph V t p ⟶ C := pullback.fst _ _
abbrev toGraph : Graph V t p ⟶ Correspondence V t := pullback.snd _ _

abbrev product := pullback (p ≫ structureMap V) ambientStructure

private theorem projection_over :
    ambientProjection V t ≫ ambientStructure = timeProjection V t ≫ structureMap V := by
  change (embedding V t ≫ pullback.snd _ _) ≫ ambientStructure =
    (embedding V t ≫ pullback.fst _ _) ≫ structureMap V
  rw [Category.assoc, Category.assoc, pullback.condition]

def embeddingOver : Graph V t p ⟶ product V p :=
  pullback.lift (toCurve V t p) (toGraph V t p ≫ ambientProjection V t) <| by
    have h : toCurve V t p ≫ p = toGraph V t p ≫ timeProjection V t :=
      pullback.condition
    rw [← Category.assoc, h, Category.assoc, Category.assoc, projection_over]

private abbrev mapProduct : product V p ⟶ Product V :=
  CycleQ2RelativeGraphClosure.productMap (p ≫ structureMap V) (structureMap V)
    ambientStructure p rfl

theorem embeddingOver_square :
    IsPullback (embeddingOver V t p) (toGraph V t p) (mapProduct V p) (embedding V t) := by
  have e : embeddingOver V t p ≫ mapProduct V p =
      toGraph V t p ≫ embedding V t := by
    apply pullback.hom_ext
    · simp only [Category.assoc, mapProduct, CycleQ2RelativeGraphClosure.productMap_fst,
        pullback.lift_fst_assoc, embeddingOver]
      change toCurve V t p ≫ p = toGraph V t p ≫ timeProjection V t
      exact pullback.condition
    · simp only [Category.assoc, mapProduct, CycleQ2RelativeGraphClosure.productMap_snd,
        embeddingOver, pullback.lift_snd]
      rfl
  have ef : embeddingOver V t p ≫ pullback.fst _ _ = toCurve V t p :=
    pullback.lift_fst _ _ _
  have h := CycleQ2RelativeGraphClosure.product_square (p ≫ structureMap V)
    (structureMap V) ambientStructure p rfl
  have outer : IsPullback (embeddingOver V t p ≫ pullback.fst _ _) (toGraph V t p) p
      (timeProjection V t) := by
    rw [ef]
    exact IsPullback.of_hasPullback p (timeProjection V t)
  exact outer.of_right e h

instance : IsClosedImmersion (embeddingOver V t p) :=
  MorphismProperty.of_isPullback (embeddingOver_square V t p).flip
    (inferInstance : IsClosedImmersion (embedding V t))

instance : IsProper (toCurve V t p) :=
  IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback p (timeProjection V t)).flip
    (inferInstance : IsProper (timeProjection V t))

variable (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : p ≫ structureMap V = c ≫ genericPoint)

def toGenericGraph : Graph V t p ⟶ genericCorrespondence V t :=
  pullback.lift (toGraph V t p) (toCurve V t p ≫ c) <| by
    have h : toCurve V t p ≫ p = toGraph V t p ≫ timeProjection V t :=
      pullback.condition
    calc
      toGraph V t p ≫ (timeProjection V t ≫ structureMap V) =
          (toGraph V t p ≫ timeProjection V t) ≫ structureMap V := (Category.assoc _ _ _).symm
      _ = (toCurve V t p ≫ p) ≫ structureMap V :=
        congrArg (fun k => k ≫ structureMap V) h.symm
      _ = (toCurve V t p ≫ c) ≫ genericPoint := by
        rw [Category.assoc, hc, Category.assoc]

abbrev target : Graph V t p ⟶ genericAmbient :=
  toGenericGraph V t p c hc ≫ genericAmbientProjection V t

theorem target_in_original_support :
    Set.range (target V t p c hc) ⊆ Set.range (genericAmbientProjection V t) := by
  rintro _ ⟨x, rfl⟩
  exact ⟨toGenericGraph V t p c hc x, rfl⟩

abbrev genericProduct := pullback c (pullback.snd ambientStructure genericPoint)

include hc in
private theorem genericProduct_square :
    IsPullback (pullback.fst c (pullback.snd ambientStructure genericPoint))
      (pullback.snd c (pullback.snd ambientStructure genericPoint) ≫
        pullback.fst ambientStructure genericPoint)
      (p ≫ structureMap V) ambientStructure := by
  rw [hc]
  exact (IsPullback.of_hasPullback c (pullback.snd ambientStructure genericPoint)).paste_vert
    (IsPullback.of_hasPullback ambientStructure genericPoint).flip

/-- The base changed graph is an actual closed subscheme of the product over the coefficient field. -/
def embeddingGeneric : Graph V t p ⟶ genericProduct c :=
  embeddingOver V t p ≫ (genericProduct_square V p c hc).isoPullback.inv

instance : IsClosedImmersion (embeddingGeneric V t p c hc) := by
  unfold embeddingGeneric
  infer_instance

@[reassoc]
theorem embeddingGeneric_toCurve :
    embeddingGeneric V t p c hc ≫ pullback.fst _ _ = toCurve V t p := by
  rw [embeddingGeneric, Category.assoc, (genericProduct_square V p c hc).isoPullback_inv_fst]
  exact pullback.lift_fst _ _ _

@[reassoc]
theorem embeddingGeneric_toAmbient :
    embeddingGeneric V t p c hc ≫ pullback.snd _ _ = target V t p c hc := by
  let α := pullback.snd ambientStructure (CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
  let β := pullback.fst ambientStructure (CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint)
  have hfst : embeddingGeneric V t p c hc ≫ pullback.snd c α ≫ β =
      toGraph V t p ≫ ambientProjection V t := by
    rw [embeddingGeneric, Category.assoc, (genericProduct_square V p c hc).isoPullback_inv_snd]
    exact pullback.lift_snd _ _ _
  have hsnd : embeddingGeneric V t p c hc ≫ pullback.snd c α ≫ α = toCurve V t p ≫ c := by
    rw [← pullback.condition (f := c) (g := α), embeddingGeneric_toCurve_assoc]
  apply pullback.hom_ext
  · rw [Category.assoc, hfst]
    simp only [target, Category.assoc, genericAmbientProjection,
      CycleQ2CoefficientBaseChange.changeMap_fst, toGenericGraph, pullback.lift_fst_assoc]
  · rw [Category.assoc, hsnd]
    simp only [target, Category.assoc, genericAmbientProjection,
      CycleQ2CoefficientBaseChange.changeMap_snd, toGenericGraph, pullback.lift_snd]

theorem target_proper [IsProper c] : IsProper (target V t p c hc) := by
  rw [← embeddingGeneric_toAmbient]
  infer_instance

variable {D : Scheme} (k : D ⟶ C) (u : D ⟶ Time toRaw V)
  (h : k ≫ p = u ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V)

abbrev TestSurface := pullback u (curveMap toRaw V t)

def fromTest : TestSurface V t u ⟶ Graph V t p :=
  pullback.lift (pullback.fst _ _ ≫ k) (pullback.snd _ _ ≫ fromSurface V t) <| by
    rw [Category.assoc, h, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      fromSurface_toTime]

/-- The original time family gives exactly the graph on the retracted test open. -/
theorem test_square :
    IsPullback (pullback.fst u (curveMap toRaw V t)) (fromTest V t p k u h) k (toCurve V t p) := by
  have h₁ : fromTest V t p k u h ≫ toCurve V t p = pullback.fst _ _ ≫ k :=
    pullback.lift_fst _ _ _
  have h₂ : fromTest V t p k u h ≫ toGraph V t p = pullback.snd _ _ ≫ fromSurface V t :=
    pullback.lift_snd _ _ _
  have outer := (IsPullback.of_hasPullback u (curveMap toRaw V t)).flip.paste_horiz
    (timeOpen_pullback V t).flip
  rw [← h, ← h₂] at outer
  exact (outer.of_right h₁ (IsPullback.of_hasPullback p (timeProjection V t)).flip).flip

theorem test_to_original_ambient :
    fromTest V t p k u h ≫ toGraph V t p ≫ ambientProjection V t =
      pullback.snd _ _ ≫ CycleQ2LiteralIncidenceRelativeCylinder.relativeQ toRaw V t := by
  have hs : fromTest V t p k u h ≫ toGraph V t p = pullback.snd _ _ ≫ fromSurface V t :=
    pullback.lift_snd _ _ _
  rw [← Category.assoc, hs, Category.assoc, fromSurface_toAmbient]

section Marked

open CycleQ2LiteralIncidenceGenericModel
open CycleQ2LiteralIncidenceGenericSmoothCurve

variable {V t}

/-- The generic proper graph can be based on a smooth proper integral curve.
Its test open maps into the chosen original time open, and carries the same
embedded surface. -/
theorem exists_smooth_curve_graph (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField)) (r : C ⟶ Completion V)
      (hr : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint),
      IsIntegral C ∧ IsProper c ∧ Smooth c ∧
      IsClosedImmersion (embeddingGeneric V t r c hr) ∧ IsProper (toCurve V t r) ∧
      IsProper (target V t r c hr) ∧
      Set.range (target V t r c hr) ⊆ Set.range (genericAmbientProjection V t) ∧
      ∃ (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
        (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
        IsOpenImmersion j ∧ IsDominant j ∧ Nonempty D ∧ Set.range a ⊆ (W : Set (Time toRaw V)) ∧
        IsPullback (pullback.fst a (curveMap toRaw V t)) (fromTest V t r j a ha) j (toCurve V t r) := by
  obtain ⟨U, hle, hU, hI, hC, _, hp, hs, _, _, E, hE, j, hj, hjd, _, _, hjr, _, _⟩ :=
    test_proper_smooth_curve V W hW
  let n := @CycleQ2IntegralCurveNormalization.normalize _ hI
  let e := (U.ι ≫ CycleQ2LiteralIncidenceGenericModel.inclusion V).imageι
  let f := n ≫ e
  let c := f ≫ projection V
  let r := f ≫ pullback.snd genericMorphism (CycleQ2LiteralIncidenceRelativeNormalization.normalizedMap V) ≫
    CycleQ2LiteralIncidenceRelativeNormalization.toCompletion V
  have hc : r ≫ structureMap V = c ≫ CycleQ2LiteralIncidenceGenericCorrespondence.genericPoint := by
    simp only [r, c, Category.assoc, projection]
    change f ≫ pullback.snd _ _ ≫ CycleQ2LiteralIncidenceRelativeNormalization.normalizedMap V =
      f ≫ pullback.fst _ _ ≫ genericMorphism
    rw [pullback.condition]
  let a := E.ι ≫ U.ι ≫ testMap V
  have ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V := by
    have H : j ≫ f = E.ι ≫ U.ι ≫ CycleQ2LiteralIncidenceGenericModel.inclusion V :=
      (Category.assoc _ _ _).symm.trans hjr
    change j ≫ f ≫ _ = _
    rw [← Category.assoc j f, H]
    simp only [Category.assoc, a, testMap]
    rw [pullback.condition_assoc, CycleQ2LiteralIncidenceRelativeNormalization.open_toCompletion]
  have hpc : IsProper c := by
    dsimp only [c, f]
    rw [Category.assoc]
    exact hp
  have hsc : Smooth c := by
    dsimp only [c, f]
    rw [Category.assoc]
    exact hs
  refine ⟨_, c, r, hc, hC, hpc, hsc, inferInstance, inferInstance,
    target_proper V t r c hc, target_in_original_support V t r c hc, E.toScheme, j, a, ha, hj, hjd, hE.to_subtype, ?_,
    test_square V t r j a ha⟩
  rintro _ ⟨x, rfl⟩
  exact hle ((E.ι x).property)

end Marked

end CycleQ2GenericSmoothCurveGraph

#print axioms CycleQ2GenericSmoothCurveGraph.embeddingOver_square
#print axioms CycleQ2GenericSmoothCurveGraph.test_square
#print axioms CycleQ2GenericSmoothCurveGraph.exists_smooth_curve_graph

end

end
