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
import Proposal.GeometricHodgeEuler
import Proposal.GeometricHodgeEulerChartDerivations
import Proposal.GeometricHodgeEulerContraction
import Proposal.GeometricLiteralThreefoldResidueMinors
import Proposal.GeometricHodgeThreefold
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.CategoryTheory.Sites.IsSheafFor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathlib.Algebra.Homology.Embedding.Extend
import Proposal.GeometricCartierDerivedClass
import Mathlib.Topology.Sheaves.Over
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Embedding.HomEquiv
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Proposal.GeometricSurfaceResidueFunctoriality
import Proposal.GeometricAffineHTwo
import Proposal.GeometricAffineHigherChartRestriction
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Constructors
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.Topology.KrullDimension

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

section

/-!
# The four derivatives generate the unit ideal on each affine sextic chart

The homogeneous gradient contains a power of the chosen degree-one
coordinate on the gradient minor open. This power becomes one on its
normalized affine chart. The Euler relation eliminates the omitted
partial since the corresponding radial coordinate is one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open MvPolynomial CycleQ2GenericSexticGradient CycleQ2HodgeEuler

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)
  (hg : IsUnit (φ gradientOpen)) (i : Fin 4)

include hg

theorem chartGradient_span :
    Ideal.span (Set.range (fun j : Fin 4 => chartMap φ i (pderiv j (F φ i)))) = ⊤ := by
  let J := Ideal.span (Set.range (fun j : Fin 4 => chartMap φ i (pderiv j (F φ i))))
  have hret (j : Fin 4) : conePartial φ i (i.castSucc.succAbove j) ∈ J := by
    rw [partial_succAbove]
    exact Ideal.subset_span (Set.mem_range_self j)
  have he := radial_equation φ i
  rw [Fin.sum_univ_succAbove _ i.castSucc, radial_self, mul_one] at he
  have hall (j : Fin 5) : conePartial φ i j ∈ J := by
    refine Fin.succAboveCases i.castSucc ?_ hret j
    rw [eq_neg_of_add_eq_zero_left he]
    exact J.neg_mem (J.sum_mem fun k _ => J.mul_mem_right _ (hret k))
  let ρ := (chartMap φ i).toRingHom.comp (dehom (R := R) i).toRingHom
  have hI : CycleQ2HomogeneousIdealArithmetic.generatorIdeal
      (fun j => MvPolynomial.map φ (generators j)) ≤ J.comap ρ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change ρ (MvPolynomial.map φ (X j * pderiv j universalF)) ∈ J
    rw [map_mul, map_mul, ← pderiv_map]
    exact J.mul_mem_left _ (hall j)
  apply J.eq_top_iff_one.mpr
  have h := hI (coordinate_power_mem φ hg i.castSucc)
  change ρ ((X i.castSucc)^coordinatePower i.castSucc) ∈ J at h
  simpa [ρ] using h

theorem conePartial_span : Ideal.span (Set.range (conePartial φ i)) = ⊤ := by
  apply top_le_iff.mp
  rw [← chartGradient_span φ hg i]
  apply Ideal.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨i.castSucc.succAbove j, partial_succAbove φ i j⟩

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.chartGradient_span

end

section

/-!
# Residue contraction on the principal gradient charts

Inverting one partial derivative of a four-variable hypersurface gives a
submersive presentation. Its three free Kähler coordinates are the other
three coordinate differentials, in their original order. Dividing their
signed wedge by the chosen partial gives the Poincaré residue. Contraction
with this actual form identifies vector fields with two-forms. The
normalization agrees whenever two partial derivatives are units.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section
namespace CycleQ2HodgeEulerContractionCharts

open MvPolynomial Module CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContraction
open CycleQ2LiteralThreefoldResidueContraction CycleQ2LiteralThreefoldResidueMinors
open scoped KaehlerDifferential

variable {K : Type} [CommRing K]

abbrev gradientEntry (q : Poly K) (j : Fin 4) := mk q (pderiv j q)
abbrev Patch (q : Poly K) (j : Fin 4) := Localization.Away (gradientEntry q j)

private def presentation (q : Poly K) (j : Fin 4) :
    Algebra.PreSubmersivePresentation K (Hyp q) (Fin 4) Unit where
  toPresentation :=
    { toGenerators := Algebra.Generators.naive (I := Ideal.span ({q} : Set (Poly K)))
      relation := fun _ => q
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_naive, Set.range_const] }
  map := fun _ => j
  map_inj := fun _ _ _ => Subsingleton.elim _ _

private theorem jacobian_eq (q : Poly K) (j : Fin 4) :
    (presentation q j).jacobian = gradientEntry q j := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_unique,
    Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  rfl

private def smoothPresentation (q : Poly K) (j : Fin 4) :
    Algebra.SubmersivePresentation K (Patch q j) (Unit ⊕ Fin 4) (Unit ⊕ Unit) where
  toPreSubmersivePresentation :=
    (Algebra.PreSubmersivePresentation.localizationAway (Patch q j) (gradientEntry q j)).comp (presentation q j)
  jacobian_isUnit := by
    rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, jacobian_eq,
      Algebra.PreSubmersivePresentation.localizationAway_jacobian, Algebra.smul_def]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) _).mul
      (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) _)

theorem patch_standardSmooth (q : Poly K) (j : Fin 4) :
    Algebra.IsStandardSmoothOfRelativeDimension 3 K (Patch q j) := by
  apply (smoothPresentation q j).isStandardSmoothOfRelativeDimension
  change Nat.card (Unit ⊕ Fin 4) - Nat.card (Unit ⊕ Unit) = 3
  norm_num [Nat.card_eq_fintype_card]

private def omitted (j : Fin 4) (a : Fin 3) : Unit ⊕ Fin 4 := Sum.inr (j.succAbove a)

private theorem omitted_injective (j : Fin 4) : Function.Injective (omitted j) :=
  Sum.inr_injective.comp j.succAbove_right_injective

private theorem complement (q : Poly K) (j : Fin 4) :
    IsCompl (Set.range (omitted j)) (Set.range (smoothPresentation q j).map) := by
  classical
  have hs : Set.range (smoothPresentation q j).map = {Sum.inl (), Sum.inr j} := by
    ext x
    change (∃ u : Unit ⊕ Unit, Sum.elim (fun _ => Sum.inl ()) (fun _ => Sum.inr j) u = x) ↔ _
    simp [Sum.exists, eq_comm]
  rw [hs]
  apply IsCompl.of_eq
  all_goals
    ext x
    cases x with
    | inl u => simp [omitted]
    | inr n =>
        have h : (∃ k, j.succAbove k = n) ↔ n ≠ j := by
          change n ∈ Set.range j.succAbove ↔ _
          rw [Fin.range_succAbove]
          rfl
        simp [omitted, Set.mem_range, h] <;> exact em _

def basis (q : Poly K) (j : Fin 4) :
    Basis (Fin 3) (Patch q j) Ω[Patch q j⁄K] :=
  (smoothPresentation q j).basisKaehlerOfIsCompl (omitted_injective j) (complement q j)

def dx {S : Type} [CommRing S] [Algebra K S] (q : Poly K) (f : Hyp q →ₐ[K] S) (a : Fin 4) :
    Ω[S⁄K] :=
  KaehlerDifferential.D K S (f (mk q (X a)))

abbrev patchMap (q : Poly K) (j : Fin 4) : Hyp q →ₐ[K] Patch q j :=
  IsScalarTower.toAlgHom K (Hyp q) (Patch q j)

theorem basis_apply (q : Poly K) (j : Fin 4) (a : Fin 3) :
    basis q j a = dx q (patchMap q j) (j.succAbove a) := by
  rw [basis, Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply]
  rfl

section Residue
variable {S : Type} [CommRing S] [Algebra K S] (q : Poly K) (f : Hyp q →ₐ[K] S)

theorem gradient_relation : ∑ a : Fin 4, f (gradientEntry q a) • dx q f a = 0 := by
  have h := CycleQ2PolynomialChainRule.apply (f.comp (mk q)) (KaehlerDifferential.D K S) q
  change KaehlerDifferential.D K S (f (mk q q)) = _ at h
  rw [mk_equation, map_zero, map_zero] at h
  exact h.symm

def residueAlong (j : Fin 4) (h : IsUnit (f (gradientEntry q j))) : ⋀[S]^3 Ω[S⁄K] :=
  (↑h.unit⁻¹ : S) • signedOmitted S (dx q f) j

theorem partial_smul_residueAlong (j : Fin 4) (h : IsUnit (f (gradientEntry q j))) :
    f (gradientEntry q j) • residueAlong q f j h = signedOmitted S (dx q f) j := by
  have hu : f (gradientEntry q j) * (↑h.unit⁻¹ : S) = 1 := by
    simpa only [h.unit_spec] using h.unit.mul_inv
  rw [residueAlong, smul_smul, hu, one_smul]

/-- The signed residue agrees on the overlaps of any two gradient opens. -/
theorem residueAlong_eq (j k : Fin 4) (hj : IsUnit (f (gradientEntry q j))) (hk : IsUnit (f (gradientEntry q k))) :
    residueAlong q f j hj = residueAlong q f k hk := by
  apply (IsUnit.smul_left_cancel hj).mp
  apply (IsUnit.smul_left_cancel hk).mp
  rw [partial_smul_residueAlong, smul_comm (f (gradientEntry q k)) (f (gradientEntry q j)), partial_smul_residueAlong]
  exact signedOmitted_cross _ _ (gradient_relation q f) j k

end Residue

def patchUnit (q : Poly K) (j : Fin 4) : (Patch q j)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j)).unit

def patchResidue (q : Poly K) (j : Fin 4) : ⋀[Patch q j]^3 Ω[Patch q j⁄K] :=
  residueAlong q (patchMap q j) j (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j))

theorem patchResidue_eq (q : Poly K) (j : Fin 4) :
    patchResidue q j =
      ((↑((patchUnit q j)⁻¹ * (-1 : (Patch q j)ˣ)^j.val) : Patch q j)) •
        exteriorPower.ιMulti (Patch q j) 3 (basis q j) := by
  have hb : dx q (patchMap q j) ∘ j.succAbove = basis q j :=
    funext (fun a => (basis_apply q j a).symm)
  simp only [patchResidue, residueAlong, signedOmitted, hb, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, patchUnit, mul_smul]
  rfl

def tangentToTwoForms (q : Poly K) (j : Fin 4) :
    Derivation K (Patch q j) (Patch q j) ≃ₗ[Patch q j] (⋀[Patch q j]^2 Ω[Patch q j⁄K]) :=
  (KaehlerDifferential.linearMapEquivDerivation K (Patch q j)).symm.trans
    (unitContractionEquiv (basis q j) ((patchUnit q j)⁻¹ * (-1 : (Patch q j)ˣ)^j.val))

theorem tangentToTwoForms_apply (q : Poly K) (j : Fin 4) (v : Derivation K (Patch q j) (Patch q j)) :
    tangentToTwoForms q j v = interior 2 v.liftKaehlerDifferential (patchResidue q j) := by
  rw [patchResidue_eq]
  exact unitContractionEquiv_apply _ _ _

/-- In the chart with the degree-one homogeneous coordinate number i set to one,
the oriented Euler volume has the additional sign from omitting that coordinate. -/
def projectiveResidue (q : Poly K) (i j : Fin 4) : ⋀[Patch q j]^3 Ω[Patch q j⁄K] :=
  (-1 : Patch q j)^i.val • patchResidue q j

theorem partial_smul_projectiveResidue (q : Poly K) (i j : Fin 4) :
    patchMap q j (gradientEntry q j) • projectiveResidue q i j =
      (-1 : Patch q j)^(i.val + j.val) • exteriorPower.ιMulti (Patch q j) 3 (basis q j) := by
  have hb : dx q (patchMap q j) ∘ j.succAbove = basis q j :=
    funext (fun a => (basis_apply q j a).symm)
  have hc := partial_smul_residueAlong q (patchMap q j) j
    (IsLocalization.Away.algebraMap_isUnit (S := Patch q j) (gradientEntry q j))
  change patchMap q j (gradientEntry q j) • patchResidue q j =
    (-1 : Patch q j)^j.val • exteriorPower.ιMulti (Patch q j) 3 (dx q (patchMap q j) ∘ j.succAbove) at hc
  rw [hb] at hc
  calc
    _ = (-1 : Patch q j)^i.val • (patchMap q j (gradientEntry q j) • patchResidue q j) :=
      smul_comm _ _ _
    _ = (-1 : Patch q j)^i.val • ((-1 : Patch q j)^j.val • exteriorPower.ιMulti _ 3 (basis q j)) :=
      congrArg (fun w : ⋀[Patch q j]^3 Ω[Patch q j⁄K] => (-1 : Patch q j)^i.val • w) hc
    _ = _ := by rw [pow_add, mul_smul]

def projectiveTangentToTwoForms (q : Poly K) (i j : Fin 4) :
    Derivation K (Patch q j) (Patch q j) ≃ₗ[Patch q j] (⋀[Patch q j]^2 Ω[Patch q j⁄K]) :=
  (tangentToTwoForms q j).trans (LinearEquiv.smulOfUnit ((-1 : (Patch q j)ˣ)^i.val))

theorem projectiveTangentToTwoForms_apply (q : Poly K) (i j : Fin 4)
    (v : Derivation K (Patch q j) (Patch q j)) :
    projectiveTangentToTwoForms q i j v =
      interior 2 v.liftKaehlerDifferential (projectiveResidue q i j) := by
  change ((↑((-1 : (Patch q j)ˣ)^i.val) : Patch q j)) • tangentToTwoForms q j v = _
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, tangentToTwoForms_apply,
    projectiveResidue, map_smul]

end CycleQ2HodgeEulerContractionCharts
end

#print axioms CycleQ2HodgeEulerContractionCharts.tangentToTwoForms_apply
#print axioms CycleQ2HodgeEulerContractionCharts.residueAlong_eq

end

section

/-!
# The coefficient prime at a point of a weighted projective chart

The original structure map is obtained from degree-zero localization
at one. On points the resulting affine prime consists of the
coefficients whose degree-zero classes lie in the homogeneous prime.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2ProjCoefficientPoint

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem coefficient_mem (a : R) (q : threefold φ) :
    (a ∈ (toBase φ q).asIdeal) ↔ quotient φ (C a) ∈ q.asHomogeneousIdeal.toIdeal := by
  let W : (threefold φ).Opens := Proj.basicOpen (grade φ) 1
  have hW : W = ⊤ := Proj.basicOpen_one (grade φ)
  let e : threefold φ ⟶ W.toScheme :=
    (Scheme.topIso (threefold φ)).inv ≫ (Scheme.isoOfEq (threefold φ) hW).inv
  let x := e q
  have hx : W.ι x = q := by
    change W.ι (e q) = q
    rw [← Scheme.Hom.comp_apply]
    have he : e ≫ W.ι = 𝟙 _ := by
      dsimp only [e]
      rw [Category.assoc, Scheme.isoOfEq_inv_ι, ← Scheme.topIso_hom, Iso.inv_hom_id]
    rw [he]
    rfl
  have hToSpec : Scheme.forgetToLocallyRingedSpace.map (Proj.basicOpenToSpec (grade φ) 1) =
      ProjectiveSpectrum.Proj.toSpec (grade φ) 1 := by
    refine Eq.trans ?_ (ΓSpec.locallyRingedSpaceAdjunction.homEquiv_apply _ _ _).symm
    dsimp [Proj.basicOpenToSpec, Scheme.Opens.toSpecΓ]
    simp only [Category.assoc, ← Spec.map_comp]
    rfl
  have hr : (Proj.basicOpenToSpec (grade φ) 1) x =
      (ProjectiveSpectrum.Proj.toSpec (grade φ) 1).base x :=
    congrArg (fun f => f.base x) hToSpec
  change (a ∈ (Spec.map (CommRingCat.ofHom (coefficient φ))
    (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (grade φ) _))
      ((Proj.basicOpenToSpec (grade φ) 1) x))).asIdeal) ↔ _
  rw [hr]
  change HomogeneousLocalization.fromZeroRingHom (grade φ) _ (coefficient φ a) ∈
    ((ProjectiveSpectrum.Proj.toSpec (grade φ) 1).base x).asIdeal ↔ _
  rw [← hx]
  exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply (grade φ) x
    ⟨0, coefficient φ a, 1, Submonoid.one_mem _⟩

end CycleQ2ProjCoefficientPoint

#print axioms CycleQ2ProjCoefficientPoint.coefficient_mem

end

section

/-!
# The monic generic projective model is smooth

The Fermat specialization factors through the monic coefficients. The
existing good-parameter determinant is one at this specialization,
hence remains invertible over the generic monic coefficient field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2MonicGenericSmooth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold
open CycleQ2MonicGenericAmbientChart
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerContractionCharts

theorem seed_vertex : seedEvaluation vertexCoefficient = 1 := by
  rw [vertexCoefficient, seedEvaluation, eval_X, fermatCoefficients, fullSexticLeadingIndex_exponent]
  simp [CycleQ2FermatJacobian.fermat, X_pow_eq_monomial, coeff_monomial, Finsupp.single_eq_single_iff]

def fermatMonic : MonicRing →+* ℂ := eval (fun j : FullSexticTailIndex => fermatCoefficients j.val)

theorem fermat_factor : fermatMonic.comp rawToMonic = seedEvaluation := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [fermatMonic, seedEvaluation]
  · intro e
    change fermatMonic (rawToMonic (X e)) = seedEvaluation (X e)
    rw [rawToMonic_X]
    by_cases h : (e.val 4).val < 3
    · rw [rawCoordinate_tail (⟨e,h⟩ : FullSexticTailIndex)]
      simp [fermatMonic, seedEvaluation]
    · have he : e = fullSexticLeadingIndex := by
        by_contra he
        exact h ((fullSextic_tail_iff_ne e).mpr he)
      subst e
      rw [rawCoordinate_leading, map_one]
      exact seed_vertex.symm

private theorem rawPoint_identity : (rawPoint : CoeffRing →+* Raw) = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    change (aeval _ : CoeffRing →ₐ[ℂ] Raw) (C c) = C c
    simp
  · intro c
    change (aeval _ : CoeffRing →ₐ[ℂ] Raw) (X c) = X c
    rw [aeval_X]
    rfl

abbrev coeff : CoeffRing →+* K := genericCoeff.comp rawPoint

theorem gradientOpen_unit : IsUnit (coeff gradientOpen) := by
  apply isUnit_iff_ne_zero.mpr
  intro h
  change algebraMap MonicRing K (rawToMonic (rawPoint gradientOpen)) = 0 at h
  have h₀ := (IsFractionRing.injective MonicRing K) (h.trans (map_zero (algebraMap MonicRing K)).symm)
  have hz := congrArg fermatMonic h₀
  rw [rawPoint_identity, RingHom.id_apply, ← RingHom.comp_apply, fermat_factor, gradientOpen_seed,
    map_zero] at hz
  exact one_ne_zero hz

theorem chart_smooth (i : Fin 4) :
    SmoothOfRelativeDimension 3 (Spec.map (CommRingCat.ofHom (algebraMap K (chart coeff i)))) := by
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 3)).mpr
  refine ⟨_, chartGradient_span coeff gradientOpen_unit i, ?_⟩
  rintro _ ⟨j, rfl⟩
  change RingHom.IsStandardSmoothOfRelativeDimension 3
    ((algebraMap (chart coeff i) (Patch (F coeff i) j)).comp (algebraMap K (chart coeff i)))
  rw [← IsScalarTower.algebraMap_eq K (chart coeff i) (Patch (F coeff i) j)]
  exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap 3).mpr (patch_standardSmooth _ _)

theorem explicit_projective_smooth : SmoothOfRelativeDimension 3 (toBase coeff) := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 3) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  apply @IsZariskiLocalAtSource.of_iSup_eq_top (@SmoothOfRelativeDimension 3) hloc _ _ _ _
    (fun i : Fin 4 => coordinateOpen coeff i)
    (coordinateOpens_cover coeff (by rw [genericCoeff_vertex]; exact isUnit_one))
  intro i
  let a := (affineChart coeff i).inv ≫ (coordinateOpen coeff i).ι ≫ toBase coeff
  have ha : SmoothOfRelativeDimension 3 a := by
    change SmoothOfRelativeDimension 3 ((affineChart coeff i).inv ≫ (coordinateOpen coeff i).ι ≫ toBase coeff)
    rw [affineChart_overBase]
    exact chart_smooth i
  have h := smoothOfRelativeDimension_comp 0 3 (affineChart coeff i).hom a
  change SmoothOfRelativeDimension 3 ((affineChart coeff i).hom ≫ (affineChart coeff i).inv ≫
    (coordinateOpen coeff i).ι ≫ toBase coeff) at h
  rwa [Iso.hom_inv_id_assoc] at h

end CycleQ2MonicGenericSmooth

#print axioms CycleQ2MonicGenericSmooth.explicit_projective_smooth

end

section

/-!
# Smoothness of the actual generic ambient fibre

The four weight-one opens cover the native generic fibre. At a point
of that fibre the vertex coefficient is one, so the original homogeneous
prime cannot contain all four weight-one coordinates. Base change of each
affine chart gives the native hypersurface chart, whose Jacobian opens
are standard smooth of relative dimension three.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeGenericSmooth

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TopologicalSpace
open CycleQ2LiteralIncidenceNormalizedSlice CycleQ2MonicGenericAmbientChart
open CycleQ2LiteralIncidenceRelativeCylinder CycleQ2MonicGenericAmbientChartBaseChange
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2IncidenceNormalForm CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open scoped TensorProduct
open CycleQ2LiteralIncidenceCylinderMap (universalPoint universalAmbientToBase)
open CycleQ2GeometricHodgeThreefoldIncidence (nativeIso nativeIso_overBase)

private theorem tail_support (e : FullSexticTailIndex) :
    ∃ j : Fin 4, fullExponentOf e.val.val j.castSucc ≠ 0 := by
  by_contra! h
  have hd := e.val.property.1
  have h4 := e.property
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  simp only [fullExponentOf_apply] at h0 h1 h2 h3
  change ((e.val.val 0).val = 0) at h0
  change ((e.val.val 1).val = 0) at h1
  change ((e.val.val 2).val = 0) at h2
  change ((e.val.val 3).val = 0) at h3
  simp only [fullDegree, h0, h1, h2, h3, zero_add] at hd
  omega

/-- Outside the coefficient vertex hyperplane, the usual four weight-one
charts cover the original projective scheme, also over a non-field ring. -/
theorem weightOne_at_point {R : Type} [CommRing R] (φ : CoeffRing →+* R)
    (q : threefold φ) (hq : φ vertexCoefficient ∉ (toBase φ q).asIdeal) :
    ∃ i : Fin 4, q ∈ coordinateOpen φ i := by
  by_contra! h
  let P := q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := q.isPrime
  let ρ := (Ideal.Quotient.mk P).comp (quotient φ)
  have nz : ρ (C (φ vertexCoefficient)) ≠ 0 := by
    intro he
    exact hq ((CycleQ2ProjCoefficientPoint.coefficient_mem φ _ q).mpr
      (Ideal.Quotient.eq_zero_iff_mem.mp he))
  have hz (j : Fin 4) : ρ (X j.castSucc) = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have hj := h j
    change ¬(coord φ j.castSucc ∉ P) at hj
    exact not_not.mp hj
  have ht (e : FullSexticTailIndex) :
      ρ (monomial (fullExponentOf e.val.val) (φ (X e.val))) = 0 := by
    obtain ⟨j,hj⟩ := tail_support e
    obtain ⟨p,hp⟩ := (MvPolynomial.X_dvd_monomial (r := φ (X e.val))).mpr (Or.inr hj)
    rw [hp, map_mul, hz, zero_mul]
  have he : ρ (equation φ) = 0 := by
    change Ideal.Quotient.mk P (quotient φ (equation φ)) = 0
    rw [equation_zero, map_zero]
  have he' := (congrArg ρ (equation_raw φ)).symm.trans he
  rw [map_add, map_sum, Finset.sum_eq_zero (fun e _ => ht e), add_zero] at he'
  have hmul : ρ (C (φ vertexCoefficient)) * ρ (X (4 : Fin 5)) ^ 3 = 0 := by
    rw [← map_pow, ← map_mul, X_pow_eq_monomial, C_mul_monomial, mul_one]
    exact he'
  have h4 : coord φ 4 ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp
    (eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hmul).resolve_left nz))
  apply q.not_irrelevant_le
  refine (irrelevant_le_coordinateIdeal φ).trans (Ideal.span_le.mpr ?_)
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hz 0)
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hz 1)
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hz 2)
  · exact Ideal.Quotient.eq_zero_iff_mem.mp (hz 3)
  · exact h4

private abbrev base := Spec.map (CommRingCat.ofHom genericCoeff)
private abbrev rawP := toBase rawPoint

abbrev Fibre := pullback base rawP

abbrev toField : Fibre ⟶ Spec (CommRingCat.of K) := pullback.fst _ _

private abbrev rawChart (i : Fin 4) : Spec (CommRingCat.of (chart rawPoint i)) ⟶ threefold rawPoint :=
  (affineChart rawPoint i).inv ≫ (coordinateOpen rawPoint i).ι

private theorem rawChart_over (i : Fin 4) :
    rawChart i ≫ rawP = Spec.map (CommRingCat.ofHom (algebraMap Raw (chart rawPoint i))) :=
  affineChart_overBase rawPoint i

private local instance : Algebra Raw K := genericCoeff.toAlgebra

private def chartIso (i : Fin 4) : Spec (CommRingCat.of (chart CycleQ2MonicGenericSmooth.coeff i)) ≅
    pullback (pullback.snd base rawP) (rawChart i) :=
  Scheme.Spec.mapIso (tensorChartEquiv (S := K) rawPoint i).toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso Raw K (chart rawPoint i)).symm ≪≫
    pullback.congrHom (rfl : base = _) (rawChart_over i).symm ≪≫
    (pullbackLeftPullbackSndIso base rawP (rawChart i)).symm

/-- All four affine charts in the actual pullback, with their native coefficient algebra. -/
def chartIn (i : Fin 4) : Spec (CommRingCat.of (chart CycleQ2MonicGenericSmooth.coeff i)) ⟶ Fibre :=
  (chartIso i).hom ≫ pullback.fst _ _

instance (i : Fin 4) : IsOpenImmersion (chartIn i) := by
  unfold chartIn
  infer_instance

theorem chartIn_over (i : Fin 4) :
    chartIn i ≫ toField =
      Spec.map (CommRingCat.ofHom (algebraMap K (chart CycleQ2MonicGenericSmooth.coeff i))) := by
  change Spec.map (CommRingCat.ofHom (tensorChartEquiv (S := K) rawPoint i).toRingHom) ≫
    tensorInclusion (S := K) rawP (rawChart i) (rawChart_over i) ≫ toField = _
  erw [tensorInclusion_overBase, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (tensorChartEquiv (S := K) rawPoint i).commutes

theorem chartIn_cover : (⨆ i : Fin 4, (chartIn i).opensRange) = ⊤ := by
  apply top_unique
  intro z _
  let q := pullback.snd base rawP z
  have hq : rawP q = base (toField z) := by
    exact congrArg (fun f : Fibre ⟶ Spec (CommRingCat.of Raw) => f z) pullback.condition.symm
  have hne : rawPoint vertexCoefficient ∉ (rawP q).asIdeal := by
    rw [hq]
    change genericCoeff (rawPoint vertexCoefficient) ∉ (toField z).asIdeal
    rw [show genericCoeff (rawPoint vertexCoefficient) = 1 from genericCoeff_vertex]
    intro h
    exact Ideal.IsPrime.ne_top (toField z).isPrime
      ((Ideal.eq_top_iff_one _).mpr h)
  obtain ⟨i, hi⟩ := weightOne_at_point rawPoint q hne
  let a : (coordinateOpen rawPoint i).toScheme := ⟨q,hi⟩
  let v := (affineChart rawPoint i).hom a
  have hv₀ : (affineChart rawPoint i).hom ≫ rawChart i = (coordinateOpen rawPoint i).ι := by
    change (affineChart rawPoint i).hom ≫ (affineChart rawPoint i).inv ≫
      (coordinateOpen rawPoint i).ι = _
    rw [Iso.hom_inv_id_assoc]
  have hv : q = rawChart i v := (congrArg (fun h => h a) hv₀).symm
  obtain ⟨s, hsz, _⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd base rawP) (g := rawChart i) z v hv
  apply Opens.mem_iSup.mpr
  refine ⟨i, (chartIn i).mem_opensRange.mpr ⟨(chartIso i).inv s, ?_⟩⟩
  change ((chartIso i).inv ≫ chartIn i) s = z
  rw [chartIn, Iso.inv_hom_id_assoc]
  exact hsz

private theorem opensRange_smooth (i : Fin 4) :
    SmoothOfRelativeDimension 3 ((chartIn i).opensRange.ι ≫ toField) := by
  have hs : SmoothOfRelativeDimension 3 (chartIn i ≫ toField) := by
    rw [chartIn_over]
    exact CycleQ2MonicGenericSmooth.chart_smooth i
  let e := (chartIn i).isoOpensRange
  have hc : e.inv ≫ chartIn i = (chartIn i).opensRange.ι := by
    calc
      _ = e.inv ≫ e.hom ≫ (chartIn i).opensRange.ι :=
        congrArg (fun h => e.inv ≫ h) (Scheme.Hom.isoOpensRange_hom_ι (chartIn i)).symm
      _ = _ := e.inv_hom_id_assoc _
  have he := smoothOfRelativeDimension_comp 0 3 e.inv (chartIn i ≫ toField)
  change SmoothOfRelativeDimension 3 (e.inv ≫ chartIn i ≫ toField) at he
  rwa [← Category.assoc, hc] at he

theorem fibre_smooth : SmoothOfRelativeDimension 3 toField := by
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 3) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  exact @IsZariskiLocalAtSource.of_iSup_eq_top (@SmoothOfRelativeDimension 3) hloc _ _ _ _
    (fun i => (chartIn i).opensRange) chartIn_cover opensRange_smooth

private theorem spec_eq : base = basePoint ≫ toRaw := by
  change _ = Spec.map (CommRingCat.ofHom (algebraMap MonicRing K)) ≫
    Spec.map (CommRingCat.ofHom rawToMonic)
  rw [← Spec.map_comp]
  rfl

private theorem native_square :
    IsPullback toField (pullback.snd base rawP ≫ (nativeIso universalPoint).hom)
      (basePoint ≫ toRaw) universalAmbientToBase := by
  have h : IsPullback rawP (nativeIso universalPoint).hom (𝟙 _) universalAmbientToBase := by
    apply IsPullback.of_vert_isIso
    exact ⟨(Category.comp_id _).trans (nativeIso_overBase universalPoint).symm⟩
  have e : base ≫ 𝟙 _ = basePoint ≫ toRaw := (Category.comp_id _).trans spec_eq
  exact e ▸ (IsPullback.of_hasPullback base rawP).paste_vert h

/-- Identify the checked smooth pullback with the generic ambient scheme of the closed graph. -/
def nativeComparison : Fibre ≅ genericAmbient :=
  native_square.isoPullback ≪≫
    (pullbackRightPullbackFstIso toRaw universalAmbientToBase basePoint).symm ≪≫
    pullbackSymmetry genericPoint ambientStructure

theorem nativeComparison_over :
    nativeComparison.hom ≫ pullback.snd ambientStructure genericPoint = toField := by
  have h : ((pullbackRightPullbackFstIso toRaw universalAmbientToBase basePoint).inv ≫
      (pullbackSymmetry genericPoint ambientStructure).hom) ≫
      pullback.snd ambientStructure genericPoint =
        pullback.fst (basePoint ≫ toRaw) universalAmbientToBase := by
    erw [Category.assoc, pullbackSymmetry_hom_comp_snd, pullbackRightPullbackFstIso_inv_fst]
  exact (Category.assoc native_square.isoPullback.hom _ _).trans
    ((congrArg (fun a => native_square.isoPullback.hom ≫ a) h).trans
      native_square.isoPullback_hom_fst)

theorem ambient_smooth :
    SmoothOfRelativeDimension 3 (pullback.snd ambientStructure genericPoint) := by
  have he := nativeComparison_over
  have hs : SmoothOfRelativeDimension 3
      (nativeComparison.hom ≫ pullback.snd ambientStructure genericPoint) := he.symm ▸ fibre_smooth
  have h := smoothOfRelativeDimension_comp 0 3 nativeComparison.inv
    (nativeComparison.hom ≫ pullback.snd ambientStructure genericPoint)
  change SmoothOfRelativeDimension 3
    (nativeComparison.inv ≫ nativeComparison.hom ≫ pullback.snd ambientStructure genericPoint) at h
  rwa [Iso.inv_hom_id_assoc] at h

end CycleQ2NativeGenericSmooth

#print axioms CycleQ2NativeGenericSmooth.chartIn_cover
#print axioms CycleQ2NativeGenericSmooth.ambient_smooth

end

section

/-!
# Finite exact affine covers with a prescribed chart

Every point of a smooth scheme over a field has an affine exact frame.
These opens form a basis. A compact scheme admits a finite such cover
containing a prescribed exact affine chart. Every nonempty finite
intersection on a separated scheme is affine and carries the restriction
of an exact frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2FiniteExactAffineAtlas

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Module
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)

def HasFrame (U : X.Opens) : Prop :=
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  ∃ (u : Fin n → Γ(X, U)) (b : Basis (Fin n) Γ(X, U) (KaehlerDifferential K Γ(X, U))),
    ∀ i, b i = KaehlerDifferential.D K Γ(X, U) (u i)

theorem hasFrame_of_affine_le {U V : X.Opens} (h : V ≤ U)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hb : HasFrame f n U) :
    HasFrame f n V := by
  obtain ⟨u,b,hu⟩ := hb
  obtain ⟨c,hc⟩ := exact_on_affine_subopen f h hU hV u b hu
  exact ⟨fun i => restrict f h (u i), c, hc⟩

theorem exists_frame_neighborhood [SmoothOfRelativeDimension n f] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ HasFrame f n U :=
  exists_exact_affine_neighborhood f n x

theorem isBasis [SmoothOfRelativeDimension n f] :
    Opens.IsBasis ({U : X.Opens | IsAffineOpen U ∧ HasFrame f n U} : Set X.Opens) := by
  rw [Opens.isBasis_iff_nbhd]
  intro V x hx
  obtain ⟨U,hU,hxU,hu⟩ := exists_frame_neighborhood f n x
  have hx' : x ∈ U ⊓ V := ⟨hxU,hx⟩
  obtain ⟨W,hW,hxW,hle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) hx'
  exact ⟨W, ⟨hW, hasFrame_of_affine_le f n (hle.trans inf_le_left) hU hW hu⟩,
    hxW, hle.trans inf_le_right⟩

theorem exists_finite_cover [SmoothOfRelativeDimension n f] [CompactSpace X]
    (V : X.Opens) (hV : IsAffineOpen V) (hv : HasFrame f n V) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → X.Opens) (j : ι),
      U j = V ∧ (⨆ i, U i) = ⊤ ∧ ∀ i, IsAffineOpen (U i) ∧ HasFrame f n (U i) := by
  classical
  choose U hU hx hframe using exists_frame_neighborhood f n
  have hcover : (Set.univ : Set X) ⊆ ⋃ i : X, (U i : Set X) := by
    intro x _
    exact Set.mem_iUnion.mpr ⟨x,hx x⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun i => (U i : Set X))
    (fun i => (U i).isOpen) hcover
  let W : Option (↥s) → X.Opens := fun i => i.elim V (fun x => U x)
  refine ⟨Option (↥s), inferInstance, W, none, rfl, ?_, ?_⟩
  · apply top_unique
    intro x _
    have H := hs (Set.mem_univ x)
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp H
    obtain ⟨hiS,hix⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨some ⟨i,hiS⟩, hix⟩
  · intro i
    cases i with
    | none => exact ⟨hV,hv⟩
    | some i => exact ⟨hU i,hframe i⟩

theorem frame_finite_intersection [X.IsSeparated] {ι : Type} [Finite ι] [Nonempty ι]
    (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i) ∧ HasFrame f n (U i)) :
    IsAffineOpen (⨅ i, U i) ∧ HasFrame f n (⨅ i, U i) := by
  have ha := IsAffineOpen.iInf (fun i => (hU i).1)
  let i := Classical.choice (inferInstance : Nonempty ι)
  exact ⟨ha, hasFrame_of_affine_le f n (iInf_le U i) (hU i).1 ha (hU i).2⟩

end CycleQ2FiniteExactAffineAtlas

#print axioms CycleQ2FiniteExactAffineAtlas.isBasis
#print axioms CycleQ2FiniteExactAffineAtlas.exists_finite_cover
#print axioms CycleQ2FiniteExactAffineAtlas.frame_finite_intersection

end

section

/-!
# The coordinate algebra on the original affine open

The coefficient map through a native affine chart is exactly the
specified algebra map of its ordinary coordinate ring. Hence an
exact differential frame of that coordinate ring transports to the
original affine open and can be used as a distinguished vertex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2AffineFrameBinding

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Module
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap CycleQ2FiniteExactAffineAtlas

variable {K A : Type} [Field K] [CommRing A] [Algebra K A] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A)))

private abbrev U := j ''ᵁ ⊤

private def ringIso : Γ(X, U j) ≅ CommRingCat.of A :=
  j.appIso ⊤ ≪≫ Scheme.ΓSpecIso (CommRingCat.of A)

include hj in
theorem ringIso_coefficients (a : K) :
    (ringIso j).hom (sectionCoefficients f (U j) a) = algebraMap K A a := by
  let B := CommRingCat.ofHom (algebraMap K A)
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ (U j)
      (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫ (ringIso j).hom = B := by
    simp only [ringIso, Iso.trans_hom, ← Category.assoc]
    rw [Category.assoc (Scheme.ΓSpecIso (CommRingCat.of K)).inv (f.appLE _ _ _)
      (j.appIso ⊤).hom, Scheme.Hom.appIso_hom',
      Scheme.Hom.appLE_comp_appLE]
    have ha : (j ≫ f).appLE ⊤ ⊤ le_rfl = (j ≫ f).appTop :=
      Scheme.Hom.appLE_eq_app (j ≫ f)
    erw [ha, hj, ← Scheme.ΓSpecIso_inv_naturality B, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun m => m a) he

def sectionEquiv :
    letI : Algebra K Γ(X, U j) := (sectionCoefficients f (U j)).toAlgebra
    Γ(X, U j) ≃ₐ[K] A :=
  letI : Algebra K Γ(X, U j) := (sectionCoefficients f (U j)).toAlgebra
  AlgEquiv.ofRingEquiv (f := (ringIso j).commRingCatIsoToRingEquiv)
    (ringIso_coefficients f j hj)

include hj in
theorem frame_of_chart {n : ℕ} (u : Fin n → A)
    (b : Basis (Fin n) A (KaehlerDifferential K A))
    (hb : ∀ i, b i = KaehlerDifferential.D K A (u i)) :
    HasFrame f n (U j) := by
  letI : Algebra K Γ(X, U j) := (sectionCoefficients f (U j)).toAlgebra
  let e := (sectionEquiv f j hj).symm
  letI : Algebra A Γ(X, U j) := e.toAlgHom.toRingHom.toAlgebra
  letI : IsScalarTower K A Γ(X, U j) := IsScalarTower.of_algHom e.toAlgHom
  letI : Algebra.Etale A Γ(X, U j) := (RingHom.Etale.of_bijective e.bijective).toAlgebra
  exact ⟨fun i => e (u i), baseChangeFrame (B := Γ(X, U j)) b, baseChangeFrame_apply b u hb⟩

end CycleQ2AffineFrameBinding

#print axioms CycleQ2AffineFrameBinding.frame_of_chart

end

section

/-!
# A finite native affine cover retaining the weighted source vertex

The actual generic threefold is smooth, proper and separated. Its
ordinary de Rham cover can include the normal affine patch where the
actual weighted source is regular and the swept graph is absent.
Every nonempty finite intersection remains affine with an exact frame.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeWeightedCover

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2LiteralIncidenceNormalizedSlice CycleQ2GenericProperGraphSupport
open CycleQ2NormalWeightedCotangent CycleQ2NativeNormalResidue CycleQ2NativeResidueOffGraph
open CycleQ2NativeNormalFunctionField CycleQ2FiniteExactAffineAtlas
open CycleQ2WeightedStalkExactness (RepresentsSource exists_source_scalar_off_graph)
open CycleQ2MonicGenericAmbientChart (K genericChartRing)
open CycleQ2IncidenceEtaleParameter (parameterScheme)

abbrev ambientToField : genericAmbient ⟶ Spec (CommRingCat.of K) :=
  pullback.snd ambientStructure genericPoint

theorem ambient_proper : IsProper ambientToField :=
  IsProper.isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback ambientStructure genericPoint)
    (CycleQ2LiteralRelativeAmbientProper.ambient_proper toRaw)

theorem ambient_separated : genericAmbient.IsSeparated := by
  have := ambient_proper
  let q := terminal.from (Spec (CommRingCat.of K))
  have : IsSeparated q := inferInstanceAs (IsSeparated (terminal.from (Spec (CommRingCat.of K))))
  have h : IsSeparated (ambientToField ≫ q) := inferInstance
  refine ⟨?_⟩
  rw [← terminal.comp_from ambientToField]
  exact h

/-- The coefficient algebra of the native patch is the one used by the
weighted normal residue and its signed divergence. -/
theorem patch_over (s : A) :
    patchInclusion s ≫ ambientToField =
      Spec.map (CommRingCat.ofHom (algebraMap K (Patch s))) := by
  simp only [patchInclusion, inclusion, Category.assoc, ambientToField, chart_over, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  change algebraMap A (Patch s) (algebraMap Cubic A (cubicIso (algebraMap K genericChartRing x))) =
    algebraMap K (Patch s) x
  rw [cubicIso.commutes, ← IsScalarTower.algebraMap_apply K Cubic A,
    ← IsScalarTower.algebraMap_apply K A (Patch s)]

theorem native_patch_frame (s : A) :
    HasFrame ambientToField 3 ((patchInclusion s) ''ᵁ ⊤) :=
  CycleQ2AffineFrameBinding.frame_of_chart ambientToField (patchInclusion s) (patch_over s)
    (fun i => algebraMap A (Patch s) (coordinate i)) (liftedBasis (Patch s)) (liftedBasis_apply _)

theorem exists_cover_with_weighted_source {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    (hs : SmoothOfRelativeDimension 2 (CycleQ2GenericProperGraphOpen.surfaceStructure V t))
    (hp : IsProper (CycleQ2GenericProperGraphOpen.graphStructure V t)) :
    ∃ s : A, ∃ h₀ : s ≠ 0,
      ∃ (ι : Type) (_ : Fintype ι) (U : ι → genericAmbient.Opens) (j : ι),
        U j = (patchInclusion s) ''ᵁ ⊤ ∧ (⨆ i, U i) = ⊤ ∧
        (∀ i, IsAffineOpen (U i) ∧ HasFrame ambientToField 3 (U i)) ∧
        (∀ (I : Type) [Finite I] [Nonempty I] (z : I → ι),
          IsAffineOpen (⨅ i, U (z i)) ∧ HasFrame ambientToField 3 (⨅ i, U (z i))) ∧
        U j ≤ complement V t ∧
        (letI : NeZero s := ⟨h₀⟩
         ∃ a : Patch s, RepresentsSource s a) := by
  obtain ⟨s,h₀,hc,ha⟩ := exists_source_scalar_off_graph hs hp
  have : IsProper ambientToField := ambient_proper
  have : CompactSpace genericAmbient := QuasiCompact.compactSpace_of_compactSpace ambientToField
  have : genericAmbient.IsSeparated := ambient_separated
  have : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
  have hA : IsAffineOpen ((patchInclusion s) ''ᵁ ⊤) := by
    rw [(patchInclusion s).image_top_eq_opensRange]
    exact isAffineOpen_opensRange _
  obtain ⟨ι,hι,U,j,hj,hcov,hframes⟩ :=
    exists_finite_cover ambientToField 3 ((patchInclusion s) ''ᵁ ⊤) hA (native_patch_frame s)
  refine ⟨s,h₀,ι,hι,U,j,hj,hcov,hframes,?_,?_,ha⟩
  · intro I _ _ z
    exact frame_finite_intersection ambientToField 3 (fun i => U (z i)) (fun i => hframes (z i))
  · rw [hj]
    rintro _ ⟨x,_,rfl⟩
    exact hc x

end CycleQ2NativeWeightedCover

#print axioms CycleQ2NativeWeightedCover.exists_cover_with_weighted_source

end

section

/-!
# The relative de Rham complex on the dense affine basis

Choose exact frames on the dense basis of affine opens. The ordinary
Kähler pullback powers define the cochain map on every restriction.
Functoriality uses only the actual restriction maps, and an identity
ring map compares any two frame choices. The differentials commute
with restrictions without a separate overlap hypothesis.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2FramedAffineSite

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module KaehlerDifferential
open CycleQ2SmoothRelativeFrames CycleQ2FiniteExactAffineAtlas CycleQ2RelativeAffineOverlap
open CycleQ2AffineDeRhamComplex CycleQ2AffineDeRhamFunctorial

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

abbrev FramedOpen := {U : X.Opens // IsAffineOpen U ∧ HasFrame f 3 U}

def inclusion : FramedOpen f ⥤ X.Opens where
  obj U := U.1
  map g := homOfLE g.le

instance : (inclusion f).Full where
  map_surjective g := ⟨homOfLE g.le, Subsingleton.elim _ _⟩

instance : (inclusion f).Faithful where
  map_injective := fun _ => Subsingleton.elim _ _

theorem cover_dense [SmoothOfRelativeDimension 3 f] :
    (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).mpr
  have h : Set.range (inclusion f).obj = {U : X.Opens | IsAffineOpen U ∧ HasFrame f 3 U} := by
    ext U
    constructor
    · rintro ⟨⟨W,hW⟩,rfl⟩
      exact hW
    · intro hU
      exact ⟨⟨U,hU⟩,rfl⟩
  rw [h]
  exact CycleQ2FiniteExactAffineAtlas.isBasis f 3

def functions (U : FramedOpen f) : Fin 3 → Γ(X, U.1) := U.2.2.choose

def frame (U : FramedOpen f) :
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    Basis (Fin 3) Γ(X, U.1) Ω[Γ(X,U.1)⁄K] :=
  U.2.2.choose_spec.choose

theorem frame_apply (U : FramedOpen f) :
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    ∀ i, frame f U i = KaehlerDifferential.D K Γ(X, U.1) (functions f U i) :=
  U.2.2.choose_spec.choose_spec

abbrev chartComplex (U : FramedOpen f) : CochainComplex AddCommGrpCat.{0} ℕ :=
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  complex (frame f U) (functions f U) (frame_apply f U)

def restriction {U V : FramedOpen f} (h : V ⟶ U) : chartComplex f U ⟶ chartComplex f V :=
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  pullComplex (frame f U) (functions f U) (frame_apply f U) (restrict f (show V.1 ≤ U.1 from h.le))
    (frame f V) (functions f V) (frame_apply f V)

theorem restrict_id (U : X.Opens) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    restrict f (le_rfl : U ≤ U) = AlgHom.id K Γ(X, U) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  ext a
  change (X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op) a = a
  have h : (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id X.presheaf (op U)]
  rfl

theorem restrict_comp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
    letI : Algebra K Γ(X, W) := (sectionCoefficients f W).toAlgebra
    restrict f (k.trans h) = (restrict f k).comp (restrict f h) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
  letI : Algebra K Γ(X, W) := (sectionCoefficients f W).toAlgebra
  ext a
  change (X.presheaf.map (homOfLE (k.trans h)).op) a =
    ((X.presheaf.map (homOfLE h).op) ≫ (X.presheaf.map (homOfLE k).op)) a
  rw [← Functor.map_comp]
  exact congrArg (fun x => (X.presheaf.map x) a) (Subsingleton.elim _ _)

def deRham : (FramedOpen f)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj U := chartComplex f U.unop
  map h := restriction f h.unop
  map_id U := by
    letI : Algebra K Γ(X, U.unop.1) := (sectionCoefficients f U.unop.1).toAlgebra
    have h := restrict_id f U.unop.1
    exact (congrArg (fun φ => pullComplex (frame f U.unop) (functions f U.unop)
      (frame_apply f U.unop) φ (frame f U.unop) (functions f U.unop) (frame_apply f U.unop)) h).trans
      (pullComplex_id (frame f U.unop) (functions f U.unop) (frame_apply f U.unop))
  map_comp {U V W} h k := by
    letI : Algebra K Γ(X, U.unop.1) := (sectionCoefficients f U.unop.1).toAlgebra
    letI : Algebra K Γ(X, V.unop.1) := (sectionCoefficients f V.unop.1).toAlgebra
    letI : Algebra K Γ(X, W.unop.1) := (sectionCoefficients f W.unop.1).toAlgebra
    have e := restrict_comp f (show V.unop.1 ≤ U.unop.1 from h.unop.le)
      (show W.unop.1 ≤ V.unop.1 from k.unop.le)
    exact (congrArg (fun φ => pullComplex (frame f U.unop) (functions f U.unop)
      (frame_apply f U.unop) φ (frame f W.unop) (functions f W.unop) (frame_apply f W.unop)) e).trans
      (pullComplex_comp (frame f U.unop) (functions f U.unop) (frame_apply f U.unop)
        (frame f V.unop) (functions f V.unop) (frame_apply f V.unop)
        (frame f W.unop) (functions f W.unop) (frame_apply f W.unop) _ _)

def forms (p : ℕ) : (FramedOpen f)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  deRham f ⋙ HomologicalComplex.eval _ _ p

def exterior (p : ℕ) : forms f p ⟶ forms f (p+1) where
  app U := ((deRham f).obj U).d p (p+1)
  naturality U V h := by
    exact ((deRham f).map h).comm p (p+1)

theorem exterior_square (p : ℕ) :
    exterior f p ≫ exterior f (p+1) = 0 := by
  apply NatTrans.ext
  funext U
  exact ((deRham f).obj U).d_comp_d _ _ _

end CycleQ2FramedAffineSite

#print axioms CycleQ2FramedAffineSite.cover_dense
#print axioms CycleQ2FramedAffineSite.exterior_square

end

section

/-!
# Natural coordinates below a framed affine open

Every affine subopen uses the restriction of the original exact frame.
Kähler pullback sends its basis vectors to the same restricted
coordinates, as it does for all exterior powers. The coefficients
of a form thus restrict as ordinary functions on the same opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2FramedAffineCoordinates

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2FiniteExactAffineAtlas CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap
open CycleQ2FramedAffineSite CycleQ2ExactFrameThreeDeRham CycleQ2WeightedCoordinateExterior

section Algebra

variable {A B I M N : Type} [CommRing A] [CommRing B] [Fintype I]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]

theorem coefficients_natural (φ : A →+* B) (r : M →ₛₗ[φ] N)
    (b : Basis I A M) (c : Basis I B N) (hr : ∀ i, r (b i) = c i) (ω : M) (i : I) :
    c.repr (r ω) i = φ (b.repr ω i) := by
  classical
  have h := congrArg r (b.sum_repr ω)
  rw [← h]
  simp only [map_sum, map_smulₛₗ, hr]
  simp [Finsupp.single_apply]

theorem exteriorBasis_natural (φ : A →+* B) (r : M →ₛₗ[φ] N)
    (b : Basis (Fin 3) A M) (c : Basis (Fin 3) B N)
    (hr : ∀ i, r (b i) = c i) (p : ℕ) (i : Set.powersetCard (Fin 3) p) :
    CycleQ2GeometricExteriorSheaf.exteriorMap φ r p (b.exteriorPower p i) =
      c.exteriorPower p i := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
  congr 1
  funext j
  exact hr _

end Algebra

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
variable {U V W : FramedOpen f}

def transported (a : V ⟶ U) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    Basis (Fin 3) Γ(X, V.1) Ω[Γ(X,V.1)⁄K] :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 (functions f U) (frame f U) (frame_apply f U)).choose

theorem transported_apply (a : V ⟶ U) (i : Fin 3) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    transported f a i = KaehlerDifferential.D K Γ(X, V.1) (restrict f a.le (functions f U i)) :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 (functions f U) (frame f U) (frame_apply f U)).choose_spec i

theorem transported_natural (a : V ⟶ U) (g : W ⟶ V) (i : Fin 3) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    onePullback (restrict f g.le) (transported f a i) = transported f (g ≫ a) i := by
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  rw [transported_apply, onePullback_d, transported_apply]
  apply congrArg (KaehlerDifferential.D K Γ(X,W.1))
  exact (DFunLike.congr_fun (restrict_comp f a.le g.le) (functions f U i)).symm

theorem oneCoordinates_natural (a : V ⟶ U) (g : W ⟶ V) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    ∀ (ω : Ω[Γ(X,V.1)⁄K]) (i : Fin 3),
      ((transported f (g ≫ a)).equivFun (onePullback (restrict f g.le) ω)) i =
        restrict f g.le ((transported f a).equivFun ω i) := by
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  intro ω i
  exact coefficients_natural _ _ _ _ (transported_natural f a g) ω i

theorem exteriorCoordinates_natural (a : V ⟶ U) (g : W ⟶ V) (p : ℕ) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    ∀ (ω : Form K Γ(X,V.1) p) (i : Set.powersetCard (Fin 3) p),
      ((transported f (g ≫ a)).exteriorPower p).equivFun (exteriorPullback (restrict f g.le) p ω) i =
        restrict f g.le (((transported f a).exteriorPower p).equivFun ω i) := by
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  intro ω i
  classical
  exact coefficients_natural _ _ _ _ (exteriorBasis_natural _ _ _ _ (transported_natural f a g) p) ω i

end CycleQ2FramedAffineCoordinates

#print axioms CycleQ2FramedAffineCoordinates.oneCoordinates_natural
#print axioms CycleQ2FramedAffineCoordinates.exteriorCoordinates_natural

end

section

/-!
# Sheaf gluing in the coordinates of the target open

If the restrictions of a presheaf over a fixed object admit compatible
coordinates in a sheaf, glue each coordinate and return through the
coordinate equivalence on that object. The coordinate choice can
depend on the target open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2SheafForLocalCoordinates

open CategoryTheory Opposite Presieve

variable {C : Type} [Category C] {U : C} {P Q : Cᵒᵖ ⥤ Type}
  {I : Type} {S : Presieve U}
  (e : ∀ {V : C}, (V ⟶ U) → P.obj (op V) ≃ (I → Q.obj (op V)))
  (he : ∀ {V W : C} (a : V ⟶ U) (g : W ⟶ V) (x : P.obj (op V)) (i : I),
    e (g ≫ a) (P.map g.op x) i = Q.map g.op (e a x i))

include he in
theorem isSheafFor (hQ : IsSheafFor Q S) : IsSheafFor P S := by
  intro s hs
  let a (i : I) : FamilyOfElements Q S := fun V f hf => e f (s f hf) i
  have ha (i : I) : (a i).Compatible := by
    intro V W Y g h f f' hf hf' hh
    change Q.map g.op (e f (s f hf) i) = Q.map h.op (e f' (s f' hf') i)
    rw [← he, ← he, hs g h hf hf' hh, hh]
  let b : I → Q.obj (op U) := fun i => hQ.amalgamate (a i) (ha i)
  let z := (e (𝟙 U)).symm b
  have hz : s.IsAmalgamation z := by
    intro V f hf
    apply (e f).injective
    funext i
    have h := he (𝟙 U) f z i
    rw [Category.comp_id] at h
    change e f (P.map f.op z) i = e f (s f hf) i
    rw [h]
    change Q.map f.op (e (𝟙 U) ((e (𝟙 U)).symm b) i) = _
    rw [Equiv.apply_symm_apply]
    exact hQ.isAmalgamation (ha i) f hf
  refine ⟨z,hz,?_⟩
  intro y hy
  apply (e (𝟙 U)).injective
  funext i
  change e (𝟙 U) y i = e (𝟙 U) ((e (𝟙 U)).symm b) i
  rw [Equiv.apply_symm_apply]
  apply hQ.isSeparatedFor (a i) _ _ _ (hQ.isAmalgamation (ha i))
  intro V f hf
  have h := he (𝟙 U) f y i
  rw [Category.comp_id] at h
  exact h.symm.trans (congrArg (fun t => e f t i) (hy f hf))

end CycleQ2SheafForLocalCoordinates

#print axioms CycleQ2SheafForLocalCoordinates.isSheafFor

end

section

/-!
# The relative differential sheaves from the native affine basis

The ordinary Kähler and exterior sections satisfy the sheaf condition on
the dense exact affine basis. Glue their coefficients in the frame of the
target open and use their checked restriction formulas. The dense comparison
equivalence gives actual sheaves on the original scheme.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RelativeDeRhamSheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry Module
open CycleQ2FramedAffineSite CycleQ2FramedAffineCoordinates CycleQ2SmoothRelativeFrames
open CycleQ2RelativeAffineOverlap CycleQ2WeightedCoordinateExterior

variable {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

abbrev topology := (inclusion f).inducedTopology (Opens.grothendieckTopology X)

private abbrev ringPresheaf : (FramedOpen f)ᵒᵖ ⥤ Type :=
  (inclusion f).op ⋙ X.presheaf ⋙ forget CommRingCat

private abbrev formsType (p : ℕ) : (FramedOpen f)ᵒᵖ ⥤ Type :=
  forms f p ⋙ forget AddCommGrpCat

private theorem ring_isSheaf [SmoothOfRelativeDimension 3 f] :
    Presheaf.IsSheaf (topology f) (ringPresheaf f) := by
  have : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := cover_dense f
  have h : Presheaf.IsSheaf (topology f) ((inclusion f).op ⋙ X.presheaf) :=
    Functor.op_comp_isSheaf _ _ _ X.sheaf
  exact Presheaf.isSheaf_comp_of_isSheaf _ ((inclusion f).op ⋙ X.presheaf) (forget CommRingCat) h

private def functionCoordinates (V : FramedOpen f) :
    (formsType f 0).obj (op V) ≃ (Unit → (ringPresheaf f).obj (op V)) :=
  { toFun := fun x _ => x
    invFun := fun y => y ()
    left_inv := fun _ => rfl
    right_inv := fun _ => funext fun i => by cases i; rfl }

private def oneCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 1).obj (op V) ≃ (Fin 3 → (ringPresheaf f).obj (op V)) :=
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  (transported f a).equivFun.toEquiv

private def twoCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 2).obj (op V) ≃ (Set.powersetCard (Fin 3) 2 → (ringPresheaf f).obj (op V)) := by
  classical
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  exact ((transported f a).exteriorPower 2).equivFun.toEquiv

private def threeCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 3).obj (op V) ≃ (Set.powersetCard (Fin 3) 3 → (ringPresheaf f).obj (op V)) := by
  classical
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  exact ((transported f a).exteriorPower 3).equivFun.toEquiv

private def trivialCoordinates (V : FramedOpen f) (p : ℕ) :
    (formsType f (p+4)).obj (op V) ≃ (Empty → (ringPresheaf f).obj (op V)) :=
  { toFun := fun _ i => i.elim
    invFun := fun _ => PUnit.unit
    left_inv := fun x => by change PUnit.unit = (x : PUnit); cases x; rfl
    right_inv := fun _ => funext fun i => i.elim }

private theorem formsType_isSheaf [SmoothOfRelativeDimension 3 f] (p : ℕ) :
    Presheaf.IsSheaf (topology f) (formsType f p) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS
  have h := (ring_isSheaf f).isSheafFor S hS
  cases p with
  | zero =>
    exact CycleQ2SheafForLocalCoordinates.isSheafFor (fun {V} _ => functionCoordinates f V)
      (fun a g x i => rfl) h
  | succ p =>
    cases p with
    | zero =>
      exact CycleQ2SheafForLocalCoordinates.isSheafFor (oneCoordinates f)
        (fun a g x i => oneCoordinates_natural f a g x i) h
    | succ p =>
      cases p with
      | zero =>
        exact CycleQ2SheafForLocalCoordinates.isSheafFor (twoCoordinates f)
          (fun a g x i => exteriorCoordinates_natural f a g 2 x i) h
      | succ p =>
        cases p with
        | zero =>
          exact CycleQ2SheafForLocalCoordinates.isSheafFor (threeCoordinates f)
            (fun a g x i => exteriorCoordinates_natural f a g 3 x i) h
        | succ p =>
          exact CycleQ2SheafForLocalCoordinates.isSheafFor (fun {V} _ => trivialCoordinates f V p)
            (fun a g x i => i.elim) h

theorem forms_isSheaf [SmoothOfRelativeDimension 3 f] (p : ℕ) :
    Presheaf.IsSheaf (topology f) (forms f p) :=
  (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr (formsType_isSheaf f p)

def basisForms [SmoothOfRelativeDimension 3 f] (p : ℕ) : Sheaf (topology f) AddCommGrpCat :=
  ⟨forms f p, forms_isSheaf f p⟩

def basisDifferential [SmoothOfRelativeDimension 3 f] (p : ℕ) :
    basisForms f p ⟶ basisForms f (p+1) :=
  ⟨exterior f p⟩

def compare [SmoothOfRelativeDimension 3 f] :
    Sheaf (topology f) AddCommGrpCat.{0} ≌ TopCat.Sheaf AddCommGrpCat.{0} X := by
  have : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := cover_dense f
  exact (inclusion f).sheafInducedTopologyEquivOfIsCoverDense _ _

/-- The actual additive sheaves on the original Zariski opens. -/
abbrev sheafForms [SmoothOfRelativeDimension 3 f] (p : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (compare f).functor.obj (basisForms f p)

def differential [SmoothOfRelativeDimension 3 f] (p : ℕ) : sheafForms f p ⟶ sheafForms f (p+1) :=
  (compare f).functor.map (basisDifferential f p)

theorem differential_square [SmoothOfRelativeDimension 3 f] (p : ℕ) :
    differential f p ≫ differential f (p+1) = 0 := by
  unfold differential
  rw [← Functor.map_comp]
  have h : basisDifferential f p ≫ basisDifferential f (p+1) = 0 := by
    apply (sheafToPresheaf (topology f) AddCommGrpCat).map_injective
    exact exterior_square f p
  letI : (compare f).functor.Full := (compare f).fullyFaithfulFunctor.full
  rw [h, CategoryTheory.Functor.map_zero]

def relativeDeRham [SmoothOfRelativeDimension 3 f] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  CochainComplex.of (sheafForms f) (differential f) (differential_square f)

/-- The relative forms on every original basis open are the ordinary forms
over its actual function ring, compatibly with all restrictions. -/
def onBasisIso [SmoothOfRelativeDimension 3 f] (p : ℕ) :
    (inclusion f).op ⋙ (sheafForms f p).obj ≅ forms f p :=
  (sheafToPresheaf (topology f) AddCommGrpCat).mapIso
    (((compare f).unitIso.app (basisForms f p)).symm)

theorem onBasisIso_d [SmoothOfRelativeDimension 3 f] (p : ℕ) (U : FramedOpen f) :
    (differential f p).hom.app (op U.1) ≫ (onBasisIso f (p+1)).hom.app (op U) =
      (onBasisIso f p).hom.app (op U) ≫ (exterior f p).app (op U) :=
  congrArg (fun k => k.hom.app (op U)) ((compare f).unitIso.inv.naturality (basisDifferential f p))

/-- The same native relative complex in integer degrees for the derived category. -/
def relativeDeRhamInt [SmoothOfRelativeDimension 3 f] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ :=
  (relativeDeRham f).extend (ComplexShape.embeddingUpIntGE 0)

end CycleQ2RelativeDeRhamSheaves

#print axioms CycleQ2RelativeDeRhamSheaves.forms_isSheaf
#print axioms CycleQ2RelativeDeRhamSheaves.relativeDeRham
#print axioms CycleQ2RelativeDeRhamSheaves.onBasisIso_d

end

section

/-!
# The weighted source vertex in the full native relative complex

Use the glued relative de Rham complex on the actual generic ambient
threefold. The ordinary representative on the exact weighted patch
gives a section of its actual degree-three sheaf. Transporting it back
to the function field recovers precisely the original weighted form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeWeightedDeRham

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2NativeWeightedCover CycleQ2RelativeDeRhamSheaves CycleQ2FramedAffineSite
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2MonicGenericAmbientChart (K)
open CycleQ2NormalWeightedCotangent (A)
open CycleQ2NativeNormalResidue CycleQ2NativeResidueOffGraph
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham CycleQ2AffineDeRhamFunctorial
open CycleQ2WeightedRationalRestriction (evaluate)
open CycleQ2UniversalWeightedDeRham (sourceForm)
open CycleQ2IncidenceEtaleParameter (parameterScheme)

local instance : SmoothOfRelativeDimension 3 ambientToField :=
  CycleQ2NativeGenericSmooth.ambient_smooth

/-- The actual full sheaf complex over the universal monic function field. -/
def complex : CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} genericAmbient) ℤ :=
  relativeDeRhamInt ambientToField

def vertex (s : A) : FramedOpen ambientToField :=
  ⟨(patchInclusion s) ''ᵁ ⊤,
    by rw [(patchInclusion s).image_top_eq_opensRange]; exact isAffineOpen_opensRange _,
    native_patch_frame s⟩

def vertexRingIso (s : A) :
    letI : Algebra K Γ(genericAmbient, (vertex s).1) :=
      (CycleQ2SmoothRelativeFrames.sectionCoefficients ambientToField (vertex s).1).toAlgebra
    Γ(genericAmbient, (vertex s).1) ≃ₐ[K] Patch s :=
  CycleQ2AffineFrameBinding.sectionEquiv ambientToField (patchInclusion s) (patch_over s)

abbrev VertexSections (s : A) := ((sheafForms ambientToField 3).obj.obj (op (vertex s).1))

/-- Insert an ordinary form on the patch into the degree-three sheaf
of the full relative de Rham complex. -/
def asVertexSection (s : A) (ω : Form K (Patch s) 3) : VertexSections s :=
  letI : Algebra K Γ(genericAmbient, (vertex s).1) :=
    (CycleQ2SmoothRelativeFrames.sectionCoefficients ambientToField (vertex s).1).toAlgebra
  (onBasisIso ambientToField 3).inv.app (op (vertex s))
    (exteriorPullback (vertexRingIso s).symm.toAlgHom 3 ω)

def asOrdinaryForm (s : A) (ω : VertexSections s) : Form K (Patch s) 3 :=
  letI : Algebra K Γ(genericAmbient, (vertex s).1) :=
    (CycleQ2SmoothRelativeFrames.sectionCoefficients ambientToField (vertex s).1).toAlgebra
  exteriorPullback (vertexRingIso s).toAlgHom 3 ((onBasisIso ambientToField 3).hom.app (op (vertex s)) ω)

theorem roundTrip (s : A) (ω : Form K (Patch s) 3) :
    asOrdinaryForm s (asVertexSection s ω) = ω := by
  letI : Algebra K Γ(genericAmbient, (vertex s).1) :=
    (CycleQ2SmoothRelativeFrames.sectionCoefficients ambientToField (vertex s).1).toAlgebra
  let e := (onBasisIso ambientToField 3).app (op (vertex s))
  let a := vertexRingIso s
  change exteriorPullback a.toAlgHom 3 (e.hom (e.inv (exteriorPullback a.symm.toAlgHom 3 ω))) = ω
  let z := exteriorPullback a.symm.toAlgHom 3 ω
  have he : e.hom (e.inv z) = z := Iso.inv_hom_id_apply e z
  have ha : a.toAlgHom.comp a.symm.toAlgHom = AlgHom.id K (Patch s) := by
    apply AlgHom.ext
    exact a.apply_symm_apply
  exact (congrArg (fun x => exteriorPullback a.toAlgHom 3 x) he).trans <|
    (exteriorPullback_comp a.symm.toAlgHom a.toAlgHom 3 ω).symm.trans <| by
      rw [ha, exteriorPullback_id]

theorem exists_weighted_vertex {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    (hs : SmoothOfRelativeDimension 2 (CycleQ2GenericProperGraphOpen.surfaceStructure V t))
    (hp : IsProper (CycleQ2GenericProperGraphOpen.graphStructure V t)) :
    ∃ (s : A) (h₀ : s ≠ 0) (ω : VertexSections s),
      (vertex s).1 ≤ CycleQ2GenericProperGraphSupport.complement V t ∧
      evaluate (evaluatePatch s h₀) 3 (asOrdinaryForm s ω) = sourceForm := by
  obtain ⟨s,h₀,hc,ω,hω⟩ := exists_off_graph hs hp
  refine ⟨s,h₀,asVertexSection s ω,?_,?_⟩
  · rintro _ ⟨x,_,rfl⟩
    exact hc x
  · rw [roundTrip]
    exact hω

end CycleQ2NativeWeightedDeRham

#print axioms CycleQ2NativeWeightedDeRham.exists_weighted_vertex

end

section

/-!
# Evaluation of the actual relative forms at a field-valued point

Evaluation on an open through a field-valued point commutes with
restriction of the original section rings. Over an affine chart it
is the given ring map from the chart's coordinate ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RelativePointEvaluation

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap
open CycleQ2AffineFrameBinding

variable {K L : Type} [Field K] [Field L] [Algebra K L] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (q : Spec (CommRingCat.of L) ⟶ X)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)))

abbrev point := q (IsLocalRing.closedPoint L)

private theorem point_top {U : X.Opens} (h : point q ∈ U) :
    ⊤ ≤ q ⁻¹ᵁ U := fun y _ => by
  have e : y = IsLocalRing.closedPoint L := Subsingleton.elim _ _
  rw [e]
  exact h

private def ringValue (U : X.Opens) (h : point q ∈ U) : Γ(X, U) ⟶ CommRingCat.of L :=
  q.appLE U ⊤ (point_top q h) ≫ (Scheme.ΓSpecIso (CommRingCat.of L)).hom

include hq in
theorem ringValue_coefficients (U : X.Opens) (h : point q ∈ U) (a : K) :
    ringValue q U h (sectionCoefficients f U a) = algebraMap K L a := by
  let m := CommRingCat.ofHom (algebraMap K L)
  have e : (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appLE ⊤ U
      (by rw [Scheme.Hom.preimage_top]; exact le_top) ≫ ringValue q U h = m := by
    rw [ringValue, ← Category.assoc (f.appLE _ _ _) (q.appLE _ _ _) _,
      Scheme.Hom.appLE_comp_appLE]
    have ha : (q ≫ f).appLE ⊤ ⊤ le_rfl = (q ≫ f).appTop :=
      Scheme.Hom.appLE_eq_app (q ≫ f)
    erw [ha, hq]
    change (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec.map m).appTop ≫ _ = m
    rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality m,
      Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => g a) e

def value (U : X.Opens) (h : point q ∈ U) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    Γ(X, U) →ₐ[K] L :=
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  { (ringValue q U h).hom with commutes' := ringValue_coefficients f q hq U h }

theorem value_restrict {U V : X.Opens} (k : V ≤ U) (h : point q ∈ V) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
    (value f q hq V h).comp (restrict f k) = value f q hq U (k h) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
  have e : X.presheaf.map (homOfLE k).op ≫ ringValue q V h = ringValue q U (k h) := by
    unfold ringValue
    rw [← Category.assoc, Scheme.Hom.map_appLE]
  apply AlgHom.ext
  intro a
  exact congrArg (fun m => m a) e

variable {A : Type} [CommRing A] [Algebra K A]
  (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
  (hj : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K A))) (φ : A →ₐ[K] L)

abbrev ofChart := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ j

include hj in
theorem chart_over : ofChart j φ ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
  rw [ofChart, Category.assoc, hj, ← Spec.map_comp]
  congr 1
  ext a
  exact φ.commutes a

theorem point_mem_chart : point (ofChart j φ) ∈ j ''ᵁ ⊤ := by
  exact ⟨Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint L), trivial, rfl⟩

theorem value_chart :
    letI : Algebra K Γ(X, j ''ᵁ ⊤) := (sectionCoefficients f (j ''ᵁ ⊤)).toAlgebra
    value f (ofChart j φ) (chart_over f j hj φ) (j ''ᵁ ⊤) (point_mem_chart j φ) =
      φ.comp (sectionEquiv f j hj).toAlgHom := by
  letI : Algebra K Γ(X, j ''ᵁ ⊤) := (sectionCoefficients f (j ''ᵁ ⊤)).toAlgebra
  let m := CommRingCat.ofHom φ.toRingHom
  have e : ringValue (ofChart j φ) (j ''ᵁ ⊤) (point_mem_chart j φ) =
      (j.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ m := by
    unfold ringValue ofChart
    rw [Scheme.Hom.appIso_hom', ← Scheme.ΓSpecIso_naturality m, ← Category.assoc]
    congr 1
  apply AlgHom.ext
  intro a
  exact congrArg (fun n => n a) e

end CycleQ2RelativePointEvaluation

#print axioms CycleQ2RelativePointEvaluation.value_restrict
#print axioms CycleQ2RelativePointEvaluation.value_chart

end

section

/-!
# Local top-degree boundaries in the native relative de Rham complex

At a field-valued point, a zero top cokernel germ has a primitive on an
actual affine neighborhood of that point. Evaluation of the ordinary
form on the neighborhood commutes with restriction and exterior
differentiation, including when the neighborhood lies inside the
original weighted chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2ActualTopGerm

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap CycleQ2FramedAffineSite
open CycleQ2RelativeDeRhamSheaves CycleQ2ExactFrameThreeDeRham
open CycleQ2WeightedCoordinateExterior CycleQ2AffineDeRhamFunctorial
open CycleQ2RelativePointEvaluation

section LocalPreimage

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X} (d : F ⟶ G)
  {U : Opens X} (ω : G.obj.obj (op U)) (x : X) (hx : x ∈ U)

/-- An actual local boundary on the original topological space. -/
theorem exists_local_primitive
    (h : TopCat.Presheaf.germ (X := X) (cokernel d).obj U x hx ((cokernel.π d).hom.app (op U) ω) = 0) :
    ∃ (V : Opens X) (i : V ⟶ U), x ∈ V ∧
      ∃ η : F.obj.obj (op V), d.hom.app (op V) η = G.obj.map i.op ω := by
  let A : X.Presheaf AddCommGrpCat.{0} := F.obj
  let B : X.Presheaf AddCommGrpCat.{0} := G.obj
  let q := cokernel.π d
  let St := TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x
  letI : St.Additive := by dsimp [St]; infer_instance
  letI : PreservesFiniteLimits St := by dsimp [St]; infer_instance
  letI : PreservesFiniteColimits St := by dsimp [St]; infer_instance
  let S := ShortComplex.mk d q (cokernel.condition d)
  have hS : S.Exact := ShortComplex.exact_cokernel d
  have hE : (S.map St).Exact := hS.map St
  have hq : St.map q (B.germ U x hx ω) = 0 :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx q.hom ω).trans h
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff (S.map St)).mp hE (B.germ U x hx ω) hq
  obtain ⟨V, hxV, η, hη⟩ := A.exists_germ_eq b
  have he : B.germ V x hxV (d.hom.app (op V) η) = B.germ U x hx ω :=
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV d.hom η).symm.trans
      ((congrArg (St.map d) hη).trans hb)
  obtain ⟨W, hxW, k, i, hi⟩ := B.germ_eq x hxV hx _ _ he
  refine ⟨W, i, hxW, A.map k.op η, ?_⟩
  exact (NatTrans.naturality_apply d.hom k.op η).trans hi

end LocalPreimage

section FieldValue

variable {K L : Type} [Field K] [Field L] [Algebra K L] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 3 f]
  (q : Spec (CommRingCat.of L) ⟶ X)
  (hq : q ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L)))

abbrev Sections (p : ℕ) (U : FramedOpen f) := (sheafForms f p).obj.obj (op U.1)

def evalForm (U : FramedOpen f) (hU : point q ∈ U.1) (ω : Sections f 3 U) :
    Form K L 3 :=
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  exteriorPullback (value f q hq U.1 hU) 3 ((onBasisIso f 3).hom.app (op U) ω)

theorem evalForm_restrict {U V : FramedOpen f} (k : V ⟶ U)
    (hV : point q ∈ V.1) (ω : Sections f 3 U) :
    evalForm f q hq V hV ((sheafForms f 3).obj.map (homOfLE k.le).op ω) =
      evalForm f q hq U (k.le hV) ω := by
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  unfold evalForm
  have hE := NatTrans.naturality_apply (onBasisIso f 3).hom k.op ω
  change (onBasisIso f 3).hom.app (op V) ((sheafForms f 3).obj.map (homOfLE k.le).op ω) =
    exteriorPullback (restrict f k.le) 3 ((onBasisIso f 3).hom.app (op U) ω) at hE
  exact (congrArg (exteriorPullback (value f q hq V.1 hV) 3) hE).trans
    ((exteriorPullback_comp (restrict f k.le) (value f q hq V.1 hV) 3
      ((onBasisIso f 3).hom.app (op U) ω)).symm.trans <| by
        rw [value_restrict])

/-- The actual top differential is the ordinary exact-frame formula at
an affine member of the basis. -/
theorem onBasis_top (U : FramedOpen f) (η : Sections f 2 U) :
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    (onBasisIso f 3).hom.app (op U) ((differential f 2).hom.app (op U.1) η) =
      exteriorD2 (frame f U) (exactFrameDirection (frame f U))
        ((onBasisIso f 2).hom.app (op U) η) := by
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  exact congrArg (fun m => m η) (onBasisIso_d f 2 U)

end FieldValue

end CycleQ2ActualTopGerm

#print axioms CycleQ2ActualTopGerm.exists_local_primitive
#print axioms CycleQ2ActualTopGerm.evalForm_restrict
#print axioms CycleQ2ActualTopGerm.onBasis_top

end

section

/-!
# The original weighted form in the top cokernel of the full native complex

A zero germ of the top cokernel class of the actual weighted vertex
produces a local ordinary two-form primitive on the generic threefold.
Evaluating at the original function field gives the protected exactness.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeWeightedTopGerm

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2RelativePointEvaluation CycleQ2ActualTopGerm CycleQ2NativeWeightedDeRham
open CycleQ2NativeWeightedCover CycleQ2NativeResidueOffGraph
open CycleQ2NativeNormalResidue
open CycleQ2NormalWeightedCotangent (A)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2MonicGenericAmbientChart (K)
open CycleQ2FramedAffineSite CycleQ2RelativeDeRhamSheaves CycleQ2SmoothRelativeFrames
open CycleQ2ExactFrameThreeDeRham CycleQ2WeightedRationalRestriction
open CycleQ2WeightedCoordinateExterior
open CycleQ2UniversalWeightedDeRham (W sourceForm)
open CycleQ2AffineDeRhamFunctorial
open CycleQ2IncidenceEtaleParameter (parameterScheme)

local instance : SmoothOfRelativeDimension 3 ambientToField :=
  CycleQ2NativeGenericSmooth.ambient_smooth

abbrev functionPoint (s : A) (hs : s ≠ 0) : Spec (CommRingCat.of W) ⟶ genericAmbient :=
  ofChart (patchInclusion s) (evaluatePatch s hs)

theorem functionPoint_over (s : A) (hs : s ≠ 0) :
    functionPoint s hs ≫ ambientToField = Spec.map (CommRingCat.ofHom (algebraMap K W)) :=
  chart_over ambientToField (patchInclusion s) (patch_over s) (evaluatePatch s hs)

abbrev x (s : A) (hs : s ≠ 0) : genericAmbient := point (functionPoint s hs)

theorem x_mem_vertex (s : A) (hs : s ≠ 0) : x s hs ∈ (vertex s).1 :=
  point_mem_chart (patchInclusion s) (evaluatePatch s hs)

theorem eval_vertex (s : A) (hs : s ≠ 0) (ω : VertexSections s) :
    evalForm ambientToField (functionPoint s hs) (functionPoint_over s hs)
      (vertex s) (x_mem_vertex s hs) ω = evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) := by
  letI : Algebra K Γ(genericAmbient, (vertex s).1) :=
    (sectionCoefficients ambientToField (vertex s).1).toAlgebra
  unfold evalForm asOrdinaryForm
  have hv : value ambientToField (functionPoint s hs) (functionPoint_over s hs) _ (x_mem_vertex s hs) =
      (evaluatePatch s hs).comp (vertexRingIso s).toAlgHom :=
    value_chart ambientToField (patchInclusion s) (patch_over s) (evaluatePatch s hs)
  rw [hv]
  exact exteriorPullback_comp (vertexRingIso s).toAlgHom (evaluatePatch s hs) 3
    ((onBasisIso ambientToField 3).hom.app (op (vertex s)) ω)

abbrev topMap := differential ambientToField 2

def topGerm (s : A) (hs : s ≠ 0) (ω : VertexSections s) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{0}) (X := (show TopCat from genericAmbient)) (cokernel topMap).obj (x s hs) :=
  TopCat.Presheaf.germ (X := (show TopCat from genericAmbient)) (cokernel topMap).obj
    (vertex s).1 (x s hs) (x_mem_vertex s hs)
    ((cokernel.π topMap).hom.app (op (vertex s).1) ω)

theorem protected_of_zero_topGerm (s : A) (hs : s ≠ 0) (ω : VertexSections s)
    (hω : evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) = sourceForm)
    (h : topGerm s hs ω = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  obtain ⟨U, k, hx, η, hη⟩ := exists_local_primitive topMap ω (x s hs) (x_mem_vertex s hs) h
  obtain ⟨V, hV, hxV, hle⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis ambientToField 3)) hx
  let v : FramedOpen ambientToField := ⟨V, hV⟩
  let j : v ⟶ vertex s := homOfLE (hle.trans (leOfHom k))
  let i : V ⟶ U := homOfLE hle
  let ζ : Sections ambientToField 2 v := (sheafForms ambientToField 2).obj.map i.op η
  have hζ : topMap.hom.app (op v.1) ζ =
      (sheafForms ambientToField 3).obj.map (homOfLE j.le).op ω := by
    have hn := NatTrans.naturality_apply topMap.hom i.op η
    rw [hη] at hn
    exact hn.trans ((sheafForms ambientToField 3).obj.map_comp_apply k.op i.op ω).symm
  letI : Algebra K Γ(genericAmbient, v.1) := (sectionCoefficients ambientToField v.1).toAlgebra
  let b := frame ambientToField v
  let D := (exteriorD2 b (exactFrameDirection b)).toAddMonoidHom
  let φ := value ambientToField (functionPoint s hs) (functionPoint_over s hs) v.1 hxV
  let θ := (onBasisIso ambientToField 2).hom.app (op v) ζ
  have hD : ExactWedgeRule D :=
    exteriorD2_exactFrame b (functions ambientToField v) (frame_apply ambientToField v)
  let α := (sheafForms ambientToField 3).obj.map (homOfLE j.le).op ω
  have he : D θ = (onBasisIso ambientToField 3).hom.app (op v) α :=
    (onBasis_top ambientToField v ζ).symm.trans
      (congrArg ((onBasisIso ambientToField 3).hom.app (op v)) hζ)
  have hv : evalForm ambientToField (functionPoint s hs) (functionPoint_over s hs) v hxV α = sourceForm :=
    (evalForm_restrict ambientToField (functionPoint s hs) (functionPoint_over s hs)
      j hxV ω).trans ((eval_vertex s hs ω).trans hω)
  exact protected_exact_of_affine_boundary φ D hD _ hv θ he

end CycleQ2NativeWeightedTopGerm

#print axioms CycleQ2NativeWeightedTopGerm.protected_of_zero_topGerm

end

section

/-!
# Sections with support in the complement of an actual open subset

On sections, restriction followed by direct image evaluates the
original sheaf on the intersection with the chosen open. The unit
on an injective additive sheaf is an epimorphism, and its kernel
has zero stalks on the open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2OpenRestrictionSupport

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf injective_restriction_surjective)
open CycleQ2ClosedEmbeddingSheafExact (push)

variable {X : TopCat.{0}} (U : Opens X)

abbrev inclusion : TopCat.of U ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

abbrev imageOpen : Opens U ⥤ Opens X := U.isOpenEmbedding.isOpenMap.functor

abbrev onIntersection : AbSheaf X ⥤ AbSheaf X :=
  U.sheafRestrict (C := AddCommGrpCat.{0}) ⋙ push (inclusion U)

instance : (onIntersection U).Additive where
  map_add := rfl

abbrev intersection (V : Opens X) : Opens X := (imageOpen U).obj ((Opens.map (inclusion U)).obj V)

theorem intersection_eq (V : Opens X) : intersection U V = V ⊓ U := by
  ext x
  change (∃ y : U, (y : X) ∈ V ∧ (y : X) = x) ↔ x ∈ V ∧ x ∈ U
  exact ⟨fun ⟨y,hy,hx⟩ => ⟨hx ▸ hy,hx ▸ y.property⟩,
    fun ⟨hx,hU⟩ => ⟨⟨x,hU⟩,hx,rfl⟩⟩

theorem intersection_le (V : Opens X) : intersection U V ≤ V := by
  rw [intersection_eq]
  exact inf_le_left

/-- The unit for restriction to the open and direct image back to the ambient space. -/
def unit : 𝟭 (AbSheaf X) ⟶ onIntersection U where
  app F := ⟨{
    app := fun V => F.obj.map (homOfLE (intersection_le U V.unop)).op
    naturality := by
      intro V W i
      change F.obj.map i ≫ F.obj.map (homOfLE (intersection_le U W.unop)).op =
        F.obj.map (homOfLE (intersection_le U V.unop)).op ≫
          F.obj.map (((imageOpen U).map ((Opens.map (inclusion U)).map i.unop)).op)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg F.obj.map (Subsingleton.elim _ _)
    }⟩
  naturality F G f := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    exact (f.hom.naturality (homOfLE (intersection_le U V.unop)).op).symm

@[simp]
theorem unit_app_section (F : AbSheaf X) (V : Opens X) (x : F.obj.obj (op V)) :
    ((unit U).app F).hom.app (op V) x =
      F.obj.map (homOfLE (intersection_le U V)).op x := rfl

theorem epi_unit_of_injective (F : AbSheaf X) [Injective F] : Epi ((unit U).app F) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro V t x hx
  obtain ⟨s, hs⟩ := injective_restriction_surjective F (intersection_le U V) t
  refine ⟨V, le_rfl, ⟨s, ?_⟩, hx⟩
  refine (unit_app_section U F V s).trans (hs.trans ?_)
  change t = ((onIntersection U).obj F).obj.map (homOfLE (le_rfl : V ≤ V)).op t
  have h : (homOfLE (le_rfl : V ≤ V)).op = 𝟙 (op V) := Subsingleton.elim _ _
  rw [h]
  exact (ConcreteCategory.congr_hom (((onIntersection U).obj F).obj.map_id (op V)) t).symm

theorem unit_app_iso_of_le (F : AbSheaf X) (V : Opens X) (h : V ≤ U) :
    IsIso (((unit U).app F).hom.app (op V)) := by
  let e : intersection U V = V := (intersection_eq U V).trans (inf_eq_left.mpr h)
  change IsIso (F.obj.map (homOfLE (intersection_le U V)).op)
  have he : (homOfLE (intersection_le U V)).op = eqToHom (congrArg op e.symm) := Subsingleton.elim _ _
  rw [he]
  infer_instance

theorem kernel_sections_zero (F : AbSheaf X) (V : Opens X) (h : V ≤ U) :
    Subsingleton ((kernel ((unit U).app F)).obj.obj (op V)) := by
  let p := (unit U).app F
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
    (evaluation _ _).obj (op V)
  have he : Mono (E.map (kernel.ι p)) := inferInstance
  have hi : IsIso (E.map p) := unit_app_iso_of_le U F V h
  have hzero : E.map (kernel.ι p) = 0 := by
    apply (cancel_mono (E.map p)).mp
    rw [← E.map_comp, kernel.condition, E.map_zero, zero_comp]
  have hI : IsZero (E.obj (kernel p)) := (IsZero.iff_id_eq_zero _).mpr (by
    apply (cancel_mono (E.map (kernel.ι p))).mp
    rw [Category.id_comp, hzero, zero_comp])
  exact AddCommGrpCat.isZero_iff_subsingleton.mp hI

end CycleQ2OpenRestrictionSupport

#print axioms CycleQ2OpenRestrictionSupport.epi_unit_of_injective
#print axioms CycleQ2OpenRestrictionSupport.kernel_sections_zero

end

section

/-!
# The actual localization triangle for an injective complex of sheaves

Degreewise sections with support in the closed complement form the
kernel of restriction followed by direct image. Injectivity gives a
short exact sequence of complexes. Its derived triangle lifts every
class killed by the restriction map to the support complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2DerivedOpenSupport

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2OpenRestrictionSupport

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{0}} (U : Opens X)

abbrev Complex := CochainComplex (AbSheaf X) ℤ
abbrev D := DerivedCategory (AbSheaf X)

/-- The ordinary derived restriction target on an injective resolution. -/
def openComplex (I : Complex (X := X)) : Complex (X := X) :=
  ((onIntersection U).mapHomologicalComplex (ComplexShape.up ℤ)).obj I

/-- The degreewise restriction map to the actual open. -/
def restriction (I : Complex (X := X)) : I ⟶ openComplex U I where
  f n := (unit U).app (I.X n)
  comm' i j _ := ((unit U).naturality (I.d i j)).symm

private abbrev degreeKernel (I : Complex (X := X)) (n : ℤ) : AbSheaf X :=
  kernel ((unit U).app (I.X n))

private abbrev degreeInclusion (I : Complex (X := X)) (n : ℤ) : degreeKernel U I n ⟶ I.X n :=
  kernel.ι ((unit U).app (I.X n))

private theorem termSquare (I : Complex (X := X)) (i j : ℤ) :
    (degreeInclusion U I i ≫ I.d i j) ≫ (unit U).app (I.X j) = 0 := by
  have h := (unit U).naturality (I.d i j)
  change I.d i j ≫ (unit U).app (I.X j) =
    (unit U).app (I.X i) ≫ (onIntersection U).map (I.d i j) at h
  rw [Category.assoc, h, ← Category.assoc, kernel.condition, zero_comp]

private def kernelDifferential (I : Complex (X := X)) (i j : ℤ) :
    degreeKernel U I i ⟶ degreeKernel U I j :=
  kernel.lift _ (degreeInclusion U I i ≫ I.d i j) (termSquare U I i j)

@[reassoc]
private theorem kernelDifferential_comm (I : Complex (X := X)) (i j : ℤ) :
    kernelDifferential U I i j ≫ degreeInclusion U I j = degreeInclusion U I i ≫ I.d i j :=
  kernel.lift_ι _ _ _

/-- The degreewise kernel complex whose terms are sections with support. -/
def supported (I : Complex (X := X)) : Complex (X := X) where
  X := degreeKernel U I
  d := kernelDifferential U I
  shape i j h := by
    apply (cancel_mono (degreeInclusion U I j)).mp
    rw [kernelDifferential_comm, I.shape i j h, comp_zero, zero_comp]
  d_comp_d' i j k _ _ := by
    apply (cancel_mono (degreeInclusion U I k)).mp
    rw [Category.assoc, kernelDifferential_comm, kernelDifferential_comm_assoc, I.d_comp_d,
      comp_zero, zero_comp]

def inclusionToComplex (I : Complex (X := X)) : supported U I ⟶ I where
  f := degreeInclusion U I
  comm' i j _ := (kernelDifferential_comm U I i j).symm

private theorem in_support_of_restriction (I : Complex (X := X)) :
    inclusionToComplex U I ≫ restriction U I = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact kernel.condition ((unit U).app (I.X n))

def supportSequence (I : Complex (X := X)) : ShortComplex (Complex (X := X)) :=
  ShortComplex.mk (inclusionToComplex U I) (restriction U I) (in_support_of_restriction U I)

theorem supportSequence_exact (I : Complex (X := X)) (hi : ∀ n, Injective (I.X n)) :
    (supportSequence U I).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  have := hi n
  change (ShortComplex.mk (degreeInclusion U I n) ((unit U).app (I.X n))
    (kernel.condition ((unit U).app (I.X n)))).ShortExact
  refine ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel ((unit U).app (I.X n))) ?_ ?_
  · exact inferInstanceAs (Mono (degreeInclusion U I n))
  · exact epi_unit_of_injective U (I.X n)

def localizationTriangle (I : Complex (X := X)) (hi : ∀ n, Injective (I.X n)) : Triangle (D (X := X)) :=
  DerivedCategory.triangleOfSES (supportSequence_exact U I hi)

theorem localization_distinguished (I : Complex (X := X)) (hi : ∀ n, Injective (I.X n)) :
    localizationTriangle U I hi ∈ distTriang (D (X := X)) :=
  DerivedCategory.triangleOfSES_distinguished (supportSequence_exact U I hi)

/-- A derived class killed on the open factors through the literal support kernel. -/
theorem factor_of_restriction_zero (I : Complex (X := X)) (hi : ∀ n, Injective (I.X n))
    {A : D (X := X)} (a : A ⟶ DerivedCategory.Q.obj I)
    (ha : a ≫ DerivedCategory.Q.map (restriction U I) = 0) :
    ∃ b : A ⟶ DerivedCategory.Q.obj (supported U I),
      b ≫ DerivedCategory.Q.map (inclusionToComplex U I) = a := by
  obtain ⟨b, hb⟩ := (localizationTriangle U I hi).coyoneda_exact₂
    (localization_distinguished U I hi) a ha
  exact ⟨b, hb.symm⟩

/-- Every term of the support kernel has zero sections on a subopen of
its defining complement. -/
theorem support_sections_zero (I : Complex (X := X)) (n : ℤ)
    (V : Opens X) (hV : V ≤ U) :
    Subsingleton (((supported U I).X n).obj.obj (op V)) := by
  exact kernel_sections_zero U (I.X n) V hV

end CycleQ2DerivedOpenSupport

#print axioms CycleQ2DerivedOpenSupport.factor_of_restriction_zero
#print axioms CycleQ2DerivedOpenSupport.support_sections_zero

end

section

/-!
# Derived stalks of the localization support complex

Every term of the explicit localization kernel is zero on the chosen
open. Exactness of the ordinary stalk functor makes this a vanishing
statement in the derived category, at each actual point of the open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2DerivedSupportStalk

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CycleQ2DerivedOpenSupport
open CycleQ2InjectiveCech (AbSheaf)

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{0}} (U : Opens X)

abbrev stalkAt (x : X) : AbSheaf X ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x

local instance (x : X) : (stalkAt x).Additive :=
  Functor.instAdditiveComp (TopCat.Sheaf.forget AddCommGrpCat.{0} X)
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)

local instance (x : X) : PreservesFiniteLimits (stalkAt x) :=
  TopCat.Sheaf.instPreservesFiniteLimitsCompPresheafForgetStalkFunctor x

local instance (x : X) : PreservesFiniteColimits (stalkAt x) :=
  PreservesColimits.preservesFiniteColimits
    (TopCat.Sheaf.forget AddCommGrpCat.{0} X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{0} x)

theorem support_term_stalk_zero (I : Complex (X := X)) (n : ℤ) {x : X} (hx : x ∈ U) :
    IsZero ((stalkAt x).obj ((supported U I).X n)) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  let F := (supported U I).X n
  have hzero (a : TopCat.Presheaf.stalk (C := AddCommGrpCat) F.obj x) : a = 0 := by
    obtain ⟨V, hxV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.obj a
    let W := V ⊓ U
    have hWV : W ≤ V := inf_le_left
    have hres := (support_sections_zero U I n W inf_le_right).elim
      (F.obj.map (homOfLE hWV).op s) 0
    rw [← TopCat.Presheaf.germ_res_apply F.obj (homOfLE hWV) x (show x ∈ W from ⟨hxV, hx⟩),
      hres, map_zero]
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

theorem support_complex_stalk_zero (I : Complex (X := X)) {x : X} (hx : x ∈ U) :
    IsZero (((stalkAt x).mapHomologicalComplex (ComplexShape.up ℤ)).obj (supported U I)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro n
  exact (support_term_stalk_zero U I n hx).eq_of_src _ _

theorem support_derived_stalk_zero (I : Complex (X := X)) {x : X} (hx : x ∈ U) :
    IsZero ((stalkAt x).mapDerivedCategory.obj (DerivedCategory.Q.obj (supported U I))) :=
  ((stalkAt x).mapDerivedCategoryFactors.app (supported U I)).isZero_iff.mpr
    (DerivedCategory.Q.map_isZero (support_complex_stalk_zero U I hx))

/-- For a class on any complex, vanishing after the actual open restriction
on an injective resolution implies vanishing in every derived stalk in that open. -/
theorem germ_zero_of_restriction_zero {K I : Complex (X := X)}
    (q : K ⟶ I) [QuasiIso q] (hi : ∀ n, Injective (I.X n))
    {A : D (X := X)} (a : A ⟶ DerivedCategory.Q.obj K)
    (ha : a ≫ DerivedCategory.Q.map q ≫ DerivedCategory.Q.map (restriction U I) = 0)
    {x : X} (hx : x ∈ U) :
    (stalkAt x).mapDerivedCategory.map a = 0 := by
  let Q := DerivedCategory.Q (C := AbSheaf X)
  let F := (stalkAt x).mapDerivedCategory
  have hzero := support_derived_stalk_zero U I hx
  obtain ⟨b, hb⟩ := factor_of_restriction_zero U I hi (a ≫ Q.map q) (by
    rw [Category.assoc]
    exact ha)
  have h := congrArg F.map hb
  rw [Functor.map_comp, Functor.map_comp, hzero.eq_of_tgt (F.map b) 0, zero_comp] at h
  apply (cancel_mono (F.map (Q.map q))).mp
  simpa only [zero_comp] using h.symm

end CycleQ2DerivedSupportStalk

#print axioms CycleQ2DerivedSupportStalk.germ_zero_of_restriction_zero

end

section

/-!
# Injective resolutions for the localization support triangle

Every strictly bounded below complex of ordinary additive sheaves
admits an injective replacement starting at the same lower degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2BoundedInjectiveSupport

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CycleQ2DerivedOpenSupport
open CycleQ2InjectiveCech (AbSheaf)

variable {X : TopCat.{0}}

theorem exists_resolution (K : Complex (X := X)) (n : ℤ) [K.IsStrictlyGE n] :
    ∃ (I : Complex (X := X)) (q : K ⟶ I),
      QuasiIso q ∧ (∀ j, Injective (I.X j)) ∧ I.IsStrictlyGE n := by
  haveI : EnoughInjectives (AbSheaf X) := by
    change EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{0} X)
    infer_instance
  let K' : CochainComplex.Plus (AbSheaf X) := ⟨K, n, inferInstance⟩
  obtain ⟨L,hL,i,hi⟩ := CochainComplex.Plus.exists_quasiIso_injective K' n
  let I := ((InjectiveObject.ι (AbSheaf X)).mapHomologicalComplex (.up ℤ)).obj L.obj
  refine ⟨I, i.hom, ?_, fun j => inferInstanceAs (Injective ((InjectiveObject.ι (AbSheaf X)).obj (L.obj.X j))), ?_⟩
  · exact hi
  · rwa [CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff]

end CycleQ2BoundedInjectiveSupport

#print axioms CycleQ2BoundedInjectiveSupport.exists_resolution

end

section

/-!
# The canonical top projection of the native relative de Rham complex

The full integer-graded complex maps canonically to its top cokernel
placed in degree three. A class factoring through the strict swept
support has zero function-point stalk. If its top value is the class
of the original weighted vertex, it gives the protected primitive.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeDerivedTop

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open CycleQ2NativeWeightedDeRham CycleQ2NativeWeightedTopGerm CycleQ2NativeWeightedCover
open CycleQ2RelativeDeRhamSheaves CycleQ2WeightedRationalRestriction
open CycleQ2NativeNormalResidue CycleQ2GenericProperGraphSupport CycleQ2GenericGraphFunctionStalk
open CycleQ2NormalWeightedCotangent (A)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2UniversalWeightedDeRham (sourceForm)
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (app app_comp freeOpenSections_postcomp)
open CycleQ2IncidenceEtaleParameter (parameterScheme)

attribute [local instance] HasDerivedCategory.standard

local instance : SmoothOfRelativeDimension 3 ambientToField :=
  CycleQ2NativeGenericSmooth.ambient_smooth

private abbrev C := sheaves genericAmbient
private abbrev embedding := ComplexShape.embeddingUpIntGE 0
private abbrev Q := DerivedCategory.Q (C := C)
private abbrev S := DerivedCategory.singleFunctor C 3

private def termIso (n : ℕ) : complex.X (n : ℤ) ≅ sheafForms ambientToField n :=
  (relativeDeRham ambientToField).extendXIso embedding
    (show embedding.f n = (n : ℤ) from Int.zero_add _)

private theorem topDifferential_eq : complex.d 2 3 =
    (termIso 2).hom ≫ topMap ≫ (termIso 3).inv := by
  exact (relativeDeRham ambientToField).extend_d_eq embedding
    (Int.zero_add 2) (Int.zero_add 3)

/-- The genuine map of complexes from the native de Rham complex to
its top cokernel placed in degree three. -/
def topProjectionComplex : complex ⟶ (CochainComplex.singleFunctor C 3).obj (cokernel topMap) :=
  HomologicalComplex.mkHomToSingle (j := (3 : ℤ)) ((termIso 3).hom ≫ cokernel.π topMap) (by
    intro n hn
    have h : n + 1 = 3 := hn
    have hn' : n = 2 := by omega
    subst n
    change complex.d 2 3 ≫ (termIso 3).hom ≫ cokernel.π topMap = 0
    simp only [topDifferential_eq, Category.assoc, Iso.inv_hom_id_assoc, cokernel.condition, comp_zero])

def topProjection : Q.obj complex ⟶ S.obj (cokernel topMap) :=
  Q.map topProjectionComplex

private abbrev U (s : A) : Opens (show TopCat from genericAmbient) := (vertex s).1
private abbrev topSheaf : AbSheaf (show TopCat from genericAmbient) := sheafForms ambientToField 3

def vertexMap (s : A) (ω : VertexSections s) : freeOpen (U s) ⟶ topSheaf :=
  (freeOpenSections topSheaf (U s)).symm ω

private theorem vertexMap_app (s : A) (ω : VertexSections s) :
    app (vertexMap s ω) (U s) (freeOpenSections (freeOpen (U s)) (U s) (𝟙 _)) = ω := by
  refine (freeOpenSections_postcomp (U s) (𝟙 _) (vertexMap s ω)).trans ?_
  let E := freeOpenSections topSheaf (U s)
  exact (congrArg E (Category.id_comp (vertexMap s ω))).trans (E.apply_symm_apply ω)

private theorem topGerm_zero_of_map_zero (s : A) (hs : s ≠ 0) (ω : VertexSections s)
    (h : (stalkAt (x s hs)).map (vertexMap s ω ≫ cokernel.π topMap) = 0) : topGerm s hs ω = 0 := by
  let U := U s
  let P := freeOpen U
  let g := vertexMap s ω ≫ cokernel.π topMap
  let u := freeOpenSections P U (𝟙 P)
  let P₀ : TopCat.Presheaf AddCommGrpCat.{0} (show TopCat from genericAmbient) := P.obj
  let a := P₀.germ U (x s hs) (x_mem_vertex s hs) u
  have hzero : (stalkAt (x s hs)).map g a = 0 := ConcreteCategory.congr_hom h a
  have he := TopCat.Presheaf.stalkFunctor_map_germ_apply U (x s hs) (x_mem_vertex s hs) g.hom u
  have ha : app g U u = app (cokernel.π topMap) U ω :=
    (app_comp (vertexMap s ω) (cokernel.π topMap) U u).symm.trans
      (congrArg (app (cokernel.π topMap) U) (vertexMap_app s ω))
  unfold topGerm
  exact (congrArg (TopCat.Presheaf.germ (cokernel topMap).obj U (x s hs) (x_mem_vertex s hs)) ha).symm.trans
    (he.symm.trans hzero)

private theorem stalkMap_zero (s : A) (hs : s ≠ 0) {P T : C} (g : P ⟶ T)
    (h : (stalkAt (x s hs)).mapDerivedCategory.map (S.map g) = 0) :
    (stalkAt (x s hs)).map g = 0 := by
  let F := stalkAt (x s hs)
  let J := F.mapDerivedCategorySingleFunctor 3
  let B := DerivedCategory.singleFunctor AddCommGrpCat.{0} 3
  have hn : F.mapDerivedCategory.map (S.map g) ≫ J.hom.app T =
      J.hom.app P ≫ B.map (F.map g) := J.hom.naturality g
  apply B.map_injective
  rw [Functor.map_zero]
  apply (cancel_epi (J.hom.app P)).mp
  rw [← hn, h, zero_comp, comp_zero]

/-- The native complex has an injective resolution in nonnegative degrees. -/
theorem exists_injective_resolution :
    ∃ (I : CochainComplex C ℤ) (q : complex ⟶ I),
      QuasiIso q ∧ (∀ j, Injective (I.X j)) ∧ I.IsStrictlyGE 0 := by
  have h : complex.IsStrictlyGE 0 := ⟨fun n hn =>
    (relativeDeRham ambientToField).isZero_extend_X embedding n hn⟩
  exact @CycleQ2BoundedInjectiveSupport.exists_resolution
    (show TopCat from genericAmbient) complex 0 h

/-- Vanishing of the specified ambient class on the actual swept
complement implies the protected rational primitive. The restriction
in the hypothesis is computed on any injective replacement. -/
theorem protected_of_restricted_source {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    (s : A) (hs : s ≠ 0) (ω : VertexSections s)
    (hoff : (vertex s).1 ≤ complement V t)
    (hω : evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) = sourceForm)
    (I : CochainComplex C ℤ) (q : complex ⟶ I) [QuasiIso q]
    (hi : ∀ n, Injective (I.X n))
    (a : S.obj (freeOpen (U s)) ⟶ Q.obj complex)
    (hr : a ≫ Q.map q ≫ Q.map (CycleQ2DerivedOpenSupport.restriction (complement V t) I) = 0)
    (hc : a ≫ topProjection = S.map (vertexMap s ω ≫ cokernel.π topMap)) :
    (∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA) := by
  let F := (stalkAt (x s hs)).mapDerivedCategory
  have hzero : F.map a = 0 :=
    @CycleQ2DerivedSupportStalk.germ_zero_of_restriction_zero
      (show TopCat from genericAmbient) (complement V t) complex I q
      (inferInstanceAs (QuasiIso q)) hi _ a hr (x s hs) (hoff (x_mem_vertex s hs))
  have he : F.map (S.map (vertexMap s ω ≫ cokernel.π topMap)) = 0 := by
    rw [← hc, Functor.map_comp, hzero, zero_comp]
  exact protected_of_zero_topGerm s hs ω hω
    (topGerm_zero_of_map_zero s hs ω (stalkMap_zero s hs _ he))

/-- The remaining geometric input can now be stated for the actual
full complex, the actual support, and its canonical top projection. -/
theorem protected_of_supported_source {V : parameterScheme.Opens} {t : Fin 3 → ℂ}
    (s : A) (hs : s ≠ 0) (ω : VertexSections s)
    (hoff : (vertex s).1 ≤ complement V t)
    (hω : evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) = sourceForm)
    (G : CochainComplex (sheaves (support V t)) ℤ)
    (a : S.obj (freeOpen (U s)) ⟶ Q.obj (supportedComplex G))
    (b : Q.obj (supportedComplex G) ⟶ Q.obj complex)
    (hc : a ≫ b ≫ topProjection = S.map (vertexMap s ω ≫ cokernel.π topMap)) :
    (∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA) := by
  let F := (stalkAt (x s hs)).mapDerivedCategory
  have hz := derivedStalk_off (hoff (x_mem_vertex s hs)) G
  have he : F.map (S.map (vertexMap s ω ≫ cokernel.π topMap)) = 0 := by
    rw [← hc, Functor.map_comp, hz.eq_of_tgt (F.map a) 0, zero_comp]
  exact protected_of_zero_topGerm s hs ω hω
    (topGerm_zero_of_map_zero s hs ω (stalkMap_zero s hs _ he))

end CycleQ2NativeDerivedTop

#print axioms CycleQ2NativeDerivedTop.protected_of_supported_source
#print axioms CycleQ2NativeDerivedTop.protected_of_restricted_source

end

section

/-!
# Coefficient lifts on the actual framed affine site

On every framed affine open of a smooth scheme over a field the
section algebra is smooth. A lift fixing the selected coordinates
therefore exists. The actual section-ring restriction extends the
lift uniquely to every framed affine subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2NativeAffineCoefficientLifts

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap CycleQ2FramedAffineSite
open CycleQ2RelativeDerivationLift CycleQ2EtaleCoefficientTransport

variable {k K : Type} [CommRing k] [Field K] [Algebra k K] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K))

def groundAlgebra (U : X.Opens) : Algebra k Γ(X, U) :=
  ((sectionCoefficients f U).comp (algebraMap k K)).toAlgebra

/-- The coefficient map is smooth for the actual sections, using the
canonical identification of functions on the base field's spectrum. -/
theorem section_smooth [Smooth f] (U : X.Opens) (hU : IsAffineOpen U) :
    (sectionCoefficients f U).FormallySmooth := by
  let hle : U ≤ f ⁻¹ᵁ ⊤ := by rw [Scheme.Hom.preimage_top]; exact le_top
  have h := f.smooth_appLE (isAffineOpen_top _) hU hle
  have hr : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv).hom.FormallySmooth :=
    RingHom.FormallySmooth.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).inv)
  exact hr.comp h.formallySmooth

/-- On each chosen native framed affine chart, the unique horizontal
lift for that exact coordinate frame exists. -/
theorem chartLift [Smooth f] (U : FramedOpen f) (δ : Derivation k K K) :
    letI : Algebra k Γ(X, U.1) := groundAlgebra f U.1
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    ∃! d : Derivation k Γ(X, U.1) Γ(X, U.1),
      (∀ a, d (algebraMap K Γ(X, U.1) a) = algebraMap K Γ(X, U.1) (δ a)) ∧
      ∀ i, d (functions f U i) = 0 := by
  letI : Algebra k Γ(X, U.1) := groundAlgebra f U.1
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : IsScalarTower k K Γ(X, U.1) := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.FormallySmooth K Γ(X, U.1) := (section_smooth f U.1 U.2.1).toAlgebra
  exact exact_lift δ (frame f U) (functions f U) (frame_apply f U)

/-- At any native affine subopen, the actual ring restriction determines
the unique extension of a lift. Its coefficient values are unchanged. -/
theorem overlapLift {U V : FramedOpen f} (j : V ⟶ U) (δ : Derivation k K K) :
    letI : Algebra k Γ(X, U.1) := groundAlgebra f U.1
    letI : Algebra k Γ(X, V.1) := groundAlgebra f V.1
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    ∀ (d : Derivation k Γ(X, U.1) Γ(X, U.1)),
      (∀ a, d (algebraMap K Γ(X, U.1) a) = algebraMap K Γ(X, U.1) (δ a)) →
      ∃! e : Derivation k Γ(X, V.1) Γ(X, V.1),
        (∀ a, e (restrict f j.le a) = restrict f j.le (d a)) ∧
        (∀ a, e (algebraMap K Γ(X, V.1) a) = algebraMap K Γ(X, V.1) (δ a)) := by
  letI : Algebra k Γ(X, U.1) := groundAlgebra f U.1
  letI : Algebra k Γ(X, V.1) := groundAlgebra f V.1
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  let φ := restrict f j.le
  letI : Algebra Γ(X, U.1) Γ(X, V.1) := φ.toRingHom.toAlgebra
  letI : IsScalarTower K Γ(X, U.1) Γ(X, V.1) := IsScalarTower.of_algHom φ
  letI : IsScalarTower k K Γ(X, U.1) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k K Γ(X, V.1) := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower k Γ(X, U.1) Γ(X, V.1) := IsScalarTower.of_algebraMap_eq (fun x =>
    (φ.commutes (algebraMap k K x)).symm)
  letI : Algebra.Etale Γ(X, U.1) Γ(X, V.1) := (restrict_etale j.le U.2.1 V.2.1).toAlgebra
  intro d hd
  refine ⟨extend d, ⟨extend_apply d, extend_coefficients δ d hd⟩, ?_⟩
  intro e h
  exact (extend_unique d e h.1).symm

end CycleQ2NativeAffineCoefficientLifts

#print axioms CycleQ2NativeAffineCoefficientLifts.chartLift
#print axioms CycleQ2NativeAffineCoefficientLifts.overlapLift

end

section

/-!
# Pullback to a smooth surface on ordinary affine charts

The one-form derivative uses the checked formula for an exact frame
of arbitrary rank. A surface has no relative three-forms, so the
ordinary pullback from a threefold commutes with all differentials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2SurfaceDeRhamChart

open CategoryTheory CategoryTheory.Limits Module KaehlerDifferential
open CycleQ2WeightedCoordinateExterior CycleQ2AffineDeRhamComplex CycleQ2AffineDeRhamFunctorial
open CycleQ2ExactFrameFirstDifferential

variable {K A B C : Type} [Field K] [CharZero K] [CommRing A] [CommRing B] [CommRing C]
  [Algebra K A] [Algebra K B] [Algebra K C]

theorem exterior_subsingleton {p : ℕ} {n : ℕ} (b : Basis (Fin n) A Ω[A⁄K]) (h : n < p) :
    Subsingleton (Form K A p) := by
  classical
  haveI : IsEmpty (Set.powersetCard (Fin n) p) := ⟨fun i => by
    have hi := Finset.card_le_univ i.val
    rw [i.property, Fintype.card_fin] at hi
    exact (Nat.not_le_of_lt h) hi⟩
  exact b.exteriorPower p |>.equivFun.injective.subsingleton

variable (b : Basis (Fin 2) A Ω[A⁄K]) (u : Fin 2 → A) (hu : ∀ i, b i = D K A (u i))

def next : ∀ p, degree K A p ⟶ degree K A (p + 1)
  | 0 => AddCommGrpCat.ofHom (D K A).toLinearMap.toAddMonoidHom
  | 1 => AddCommGrpCat.ofHom (onOne b)
  | _ + 2 => 0

include hu in
private theorem square : ∀ p, next b p ≫ next b (p + 1) = 0
  | 0 => by
    ext a
    exact onOne_D b u hu a
  | 1 => comp_zero
  | _ + 2 => zero_comp

def complex : CochainComplex AddCommGrpCat.{0} ℕ :=
  CochainComplex.of (degree K A) (next b) (square b u hu)

variable (c : Basis (Fin 2) B Ω[B⁄K]) (v : Fin 2 → B) (hv : ∀ i, c i = D K B (v i))
  (φ : A →ₐ[K] B)

include hu hv in
theorem pull_comm : ∀ p, pullDegree φ p ≫ next c p = next b p ≫ pullDegree φ (p + 1)
  | 0 => by
    ext a
    exact (CycleQ2ExactFrameThreeDeRham.onePullback_d φ a).symm
  | 1 => by
    ext ω
    exact (onOne_natural b u hu φ c v hv ω).symm
  | _ + 2 => by simp only [next, comp_zero, zero_comp]

def pull : complex b u hu ⟶ complex c v hv :=
  CochainComplex.ofHom (pullDegree φ) (by
    intro p
    simp only [complex, CochainComplex.of_d]
    exact pull_comm b u hu c v hv φ p)

variable (a : Basis (Fin 3) A Ω[A⁄K]) (x : Fin 3 → A) (hx : ∀ i, a i = D K A (x i))

include hx hv in
theorem pull_from_three_comm :
    ∀ p, pullDegree φ p ≫ next c p = CycleQ2AffineDeRhamComplex.next a p ≫ pullDegree φ (p + 1)
  | 0 => by
    ext f
    exact (CycleQ2ExactFrameThreeDeRham.onePullback_d φ f).symm
  | 1 => by
    ext ω
    exact (onOne_natural a x hx φ c v hv ω).symm
  | 2 => by
    ext ω
    exact (exterior_subsingleton c (by decide : 2 < 3)).elim _ _
  | _ + 3 => by simp only [next, CycleQ2AffineDeRhamComplex.next, comp_zero, zero_comp]

/-- The pullback from the actual rank-three formula to the rank-two formula. -/
def pullFromThree : CycleQ2AffineDeRhamComplex.complex a x hx ⟶ complex c v hv :=
  CochainComplex.ofHom (pullDegree φ) (by
    intro p
    simp only [CycleQ2AffineDeRhamComplex.complex, complex, CochainComplex.of_d]
    exact pull_from_three_comm c v hv φ a x hx p)

end CycleQ2SurfaceDeRhamChart

#print axioms CycleQ2SurfaceDeRhamChart.pull
#print axioms CycleQ2SurfaceDeRhamChart.pullFromThree

end

section

/-!
# Pullback of the original section rings over the coefficient field

A scheme morphism over a field gives the ordinary algebra map on
sections for every open in the target and subopen of its preimage.
These are the maps on functions used to pull the native differential
forms back to the generic surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RelativeSectionPullback

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap

variable {K : Type} [Field K] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  (q : Y ⟶ X) (hq : q ≫ f = g)

def sectionPull (U : X.Opens) (V : Y.Opens) (h : V ≤ q ⁻¹ᵁ U) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
    Γ(X, U) →ₐ[K] Γ(Y, V) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  refine { toRingHom := (q.appLE U V h).hom, commutes' := ?_ }
  intro a
  unfold sectionCoefficients
  change (((Scheme.ΓSpecIso _).inv ≫ f.appLE ⊤ U _) ≫ q.appLE U V h) a =
    ((Scheme.ΓSpecIso _).inv ≫ g.appLE ⊤ V _) a
  rw [Category.assoc, Scheme.Hom.appLE_comp_appLE, hq]

theorem sectionPull_restrict_source {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ q ⁻¹ᵁ U) (j : W ≤ V) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
    letI : Algebra K Γ(Y, W) := (sectionCoefficients g W).toAlgebra
    (restrict g j).comp (sectionPull f g q hq U V h) =
      sectionPull f g q hq U W (j.trans h) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  letI : Algebra K Γ(Y, W) := (sectionCoefficients g W).toAlgebra
  apply AlgHom.ext
  intro a
  exact congrArg (fun z : Γ(X,U) ⟶ Γ(Y,W) => z a) (q.appLE_map h (homOfLE j).op)

theorem sectionPull_restrict_target {U U' : X.Opens} {V : Y.Opens}
    (h : V ≤ q ⁻¹ᵁ U') (j : U' ≤ U) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(X, U') := (sectionCoefficients f U').toAlgebra
    letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
    (sectionPull f g q hq U' V h).comp (restrict f j) =
      sectionPull f g q hq U V (h.trans ((Opens.map q.base).map (homOfLE j)).le) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(X, U') := (sectionCoefficients f U').toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  apply AlgHom.ext
  intro a
  exact congrArg (fun z : Γ(X,U) ⟶ Γ(Y,V) => z a) (q.map_appLE h (homOfLE j).op)

end CycleQ2RelativeSectionPullback

#print axioms CycleQ2RelativeSectionPullback.sectionPull_restrict_source
#print axioms CycleQ2RelativeSectionPullback.sectionPull_restrict_target

end

section

/-!
# The actual de Rham complex on a smooth generic surface

The rank-two framed affine site has ordinary functions and Kähler
forms with their original restriction maps. Coordinates in the frame
of a target open glue as ordinary functions. The dense-site comparison
extends this complex to the actual surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2SurfaceFramedAffineSite

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Module KaehlerDifferential
open CycleQ2SmoothRelativeFrames CycleQ2FiniteExactAffineAtlas CycleQ2RelativeAffineOverlap
open CycleQ2AffineDeRhamFunctorial
open CycleQ2FramedAffineSite (restrict_id restrict_comp)

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

abbrev FramedOpen := {U : X.Opens // IsAffineOpen U ∧ HasFrame f 2 U}

def inclusion : FramedOpen f ⥤ X.Opens where
  obj U := U.1
  map g := homOfLE g.le

instance : (inclusion f).Full where
  map_surjective g := ⟨homOfLE g.le, Subsingleton.elim _ _⟩

instance : (inclusion f).Faithful where
  map_injective := fun _ => Subsingleton.elim _ _

theorem cover_dense [SmoothOfRelativeDimension 2 f] :
    (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).mpr
  have h : Set.range (inclusion f).obj = {U : X.Opens | IsAffineOpen U ∧ HasFrame f 2 U} := by
    ext U
    constructor
    · rintro ⟨⟨W,hW⟩,rfl⟩
      exact hW
    · intro hU
      exact ⟨⟨U,hU⟩,rfl⟩
  rw [h]
  exact CycleQ2FiniteExactAffineAtlas.isBasis f 2

def functions (U : FramedOpen f) : Fin 2 → Γ(X, U.1) := U.2.2.choose

def frame (U : FramedOpen f) :
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    Basis (Fin 2) Γ(X, U.1) Ω[Γ(X,U.1)⁄K] :=
  U.2.2.choose_spec.choose

theorem frame_apply (U : FramedOpen f) :
    letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
    ∀ i, frame f U i = KaehlerDifferential.D K Γ(X, U.1) (functions f U i) :=
  U.2.2.choose_spec.choose_spec

abbrev chartComplex (U : FramedOpen f) : CochainComplex AddCommGrpCat.{0} ℕ :=
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  CycleQ2SurfaceDeRhamChart.complex (frame f U) (functions f U) (frame_apply f U)

def restriction {U V : FramedOpen f} (h : V ⟶ U) : chartComplex f U ⟶ chartComplex f V :=
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  CycleQ2SurfaceDeRhamChart.pull (frame f U) (functions f U) (frame_apply f U)
    (frame f V) (functions f V) (frame_apply f V) (restrict f (show V.1 ≤ U.1 from h.le))

theorem restrict_id (U : X.Opens) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    restrict f (le_rfl : U ≤ U) = AlgHom.id K Γ(X, U) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  ext a
  change (X.presheaf.map (homOfLE (le_rfl : U ≤ U)).op) a = a
  have h : (homOfLE (le_rfl : U ≤ U)).op = 𝟙 (op U) := Subsingleton.elim _ _
  rw [h, CategoryTheory.Functor.map_id X.presheaf (op U)]
  rfl

theorem restrict_comp {U V W : X.Opens} (h : V ≤ U) (k : W ≤ V) :
    letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
    letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
    letI : Algebra K Γ(X, W) := (sectionCoefficients f W).toAlgebra
    restrict f (k.trans h) = (restrict f k).comp (restrict f h) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(X, V) := (sectionCoefficients f V).toAlgebra
  letI : Algebra K Γ(X, W) := (sectionCoefficients f W).toAlgebra
  ext a
  change (X.presheaf.map (homOfLE (k.trans h)).op) a =
    ((X.presheaf.map (homOfLE h).op) ≫ (X.presheaf.map (homOfLE k).op)) a
  rw [← Functor.map_comp]
  exact congrArg (fun x => (X.presheaf.map x) a) (Subsingleton.elim _ _)

def deRham : (FramedOpen f)ᵒᵖ ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj U := chartComplex f U.unop
  map h := restriction f h.unop
  map_id U := by
    letI : Algebra K Γ(X, U.unop.1) := (sectionCoefficients f U.unop.1).toAlgebra
    have h := restrict_id f U.unop.1
    apply HomologicalComplex.hom_ext
    intro p
    change CycleQ2AffineDeRhamComplex.pullDegree (restrict f (show U.unop.1 ≤ U.unop.1 from le_rfl)) p = _
    rw [h]
    exact pullDegree_id p
  map_comp {U V W} h k := by
    letI : Algebra K Γ(X, U.unop.1) := (sectionCoefficients f U.unop.1).toAlgebra
    letI : Algebra K Γ(X, V.unop.1) := (sectionCoefficients f V.unop.1).toAlgebra
    letI : Algebra K Γ(X, W.unop.1) := (sectionCoefficients f W.unop.1).toAlgebra
    have e := restrict_comp f (show V.unop.1 ≤ U.unop.1 from h.unop.le)
      (show W.unop.1 ≤ V.unop.1 from k.unop.le)
    apply HomologicalComplex.hom_ext
    intro p
    change CycleQ2AffineDeRhamComplex.pullDegree (restrict f (k.unop.le.trans h.unop.le)) p =
      CycleQ2AffineDeRhamComplex.pullDegree (restrict f h.unop.le) p ≫
        CycleQ2AffineDeRhamComplex.pullDegree (restrict f k.unop.le) p
    rw [e]
    exact pullDegree_comp _ _ p

def forms (p : ℕ) : (FramedOpen f)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  deRham f ⋙ HomologicalComplex.eval _ _ p

def exterior (p : ℕ) : forms f p ⟶ forms f (p+1) where
  app U := ((deRham f).obj U).d p (p+1)
  naturality U V h := by
    exact ((deRham f).map h).comm p (p+1)

theorem exterior_square (p : ℕ) :
    exterior f p ≫ exterior f (p+1) = 0 := by
  apply NatTrans.ext
  funext U
  exact ((deRham f).obj U).d_comp_d _ _ _

end CycleQ2SurfaceFramedAffineSite

namespace CycleQ2SurfaceFramedAffineCoordinates

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module
open CycleQ2FiniteExactAffineAtlas CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap
open CycleQ2SurfaceFramedAffineSite CycleQ2ExactFrameThreeDeRham CycleQ2WeightedCoordinateExterior
open CycleQ2FramedAffineCoordinates (coefficients_natural)

section Algebra

variable {A B I M N : Type} [CommRing A] [CommRing B] [Fintype I]
  [AddCommGroup M] [AddCommGroup N] [Module A M] [Module B N]

theorem exteriorBasis_natural (φ : A →+* B) (r : M →ₛₗ[φ] N)
    (b : Basis (Fin 2) A M) (c : Basis (Fin 2) B N)
    (hr : ∀ i, r (b i) = c i) (p : ℕ) (i : Set.powersetCard (Fin 2) p) :
    CycleQ2GeometricExteriorSheaf.exteriorMap φ r p (b.exteriorPower p i) =
      c.exteriorPower p i := by
  rw [exteriorPower.basis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [CycleQ2GeometricExteriorSheaf.exteriorMap_wedge]
  congr 1
  funext j
  exact hr _

end Algebra

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))
variable {U V W : FramedOpen f}

def transported (a : V ⟶ U) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    Basis (Fin 2) Γ(X, V.1) Ω[Γ(X,V.1)⁄K] :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 (functions f U) (frame f U) (frame_apply f U)).choose

theorem transported_apply (a : V ⟶ U) (i : Fin 2) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    transported f a i = KaehlerDifferential.D K Γ(X, V.1) (restrict f a.le (functions f U i)) :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 (functions f U) (frame f U) (frame_apply f U)).choose_spec i

theorem transported_natural (a : V ⟶ U) (g : W ⟶ V) (i : Fin 2) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    onePullback (restrict f g.le) (transported f a i) = transported f (g ≫ a) i := by
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  rw [transported_apply, onePullback_d, transported_apply]
  apply congrArg (KaehlerDifferential.D K Γ(X,W.1))
  exact (DFunLike.congr_fun (CycleQ2FramedAffineSite.restrict_comp f a.le g.le) (functions f U i)).symm

theorem oneCoordinates_natural (a : V ⟶ U) (g : W ⟶ V) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    ∀ (ω : Ω[Γ(X,V.1)⁄K]) (i : Fin 2),
      ((transported f (g ≫ a)).equivFun (onePullback (restrict f g.le) ω)) i =
        restrict f g.le ((transported f a).equivFun ω i) := by
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  intro ω i
  exact coefficients_natural _ _ _ _ (transported_natural f a g) ω i

theorem exteriorCoordinates_natural (a : V ⟶ U) (g : W ⟶ V) (p : ℕ) :
    letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    ∀ (ω : Form K Γ(X,V.1) p) (i : Set.powersetCard (Fin 2) p),
      ((transported f (g ≫ a)).exteriorPower p).equivFun (exteriorPullback (restrict f g.le) p ω) i =
        restrict f g.le (((transported f a).exteriorPower p).equivFun ω i) := by
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra K Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  intro ω i
  classical
  exact coefficients_natural _ _ _ _ (exteriorBasis_natural _ _ _ _ (transported_natural f a g) p) ω i

end CycleQ2SurfaceFramedAffineCoordinates

namespace CycleQ2SurfaceDeRhamSheaves

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry Module
open CycleQ2SurfaceFramedAffineSite CycleQ2SurfaceFramedAffineCoordinates CycleQ2SmoothRelativeFrames
open CycleQ2RelativeAffineOverlap CycleQ2WeightedCoordinateExterior

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K))

abbrev topology := (inclusion f).inducedTopology (Opens.grothendieckTopology X)

private abbrev ringPresheaf : (FramedOpen f)ᵒᵖ ⥤ Type :=
  (inclusion f).op ⋙ X.presheaf ⋙ forget CommRingCat

private abbrev formsType (p : ℕ) : (FramedOpen f)ᵒᵖ ⥤ Type :=
  forms f p ⋙ forget AddCommGrpCat

private theorem ring_isSheaf [SmoothOfRelativeDimension 2 f] :
    Presheaf.IsSheaf (topology f) (ringPresheaf f) := by
  have : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := cover_dense f
  have h : Presheaf.IsSheaf (topology f) ((inclusion f).op ⋙ X.presheaf) :=
    Functor.op_comp_isSheaf _ _ _ X.sheaf
  exact Presheaf.isSheaf_comp_of_isSheaf _ ((inclusion f).op ⋙ X.presheaf) (forget CommRingCat) h

private def functionCoordinates (V : FramedOpen f) :
    (formsType f 0).obj (op V) ≃ (Unit → (ringPresheaf f).obj (op V)) :=
  { toFun := fun x _ => x
    invFun := fun y => y ()
    left_inv := fun _ => rfl
    right_inv := fun _ => funext fun i => by cases i; rfl }

private def oneCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 1).obj (op V) ≃ (Fin 2 → (ringPresheaf f).obj (op V)) :=
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  (transported f a).equivFun.toEquiv

private def twoCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 2).obj (op V) ≃ (Set.powersetCard (Fin 2) 2 → (ringPresheaf f).obj (op V)) := by
  classical
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  exact ((transported f a).exteriorPower 2).equivFun.toEquiv

private def threeCoordinates {U V : FramedOpen f} (a : V ⟶ U) :
    (formsType f 3).obj (op V) ≃ (Set.powersetCard (Fin 2) 3 → (ringPresheaf f).obj (op V)) := by
  classical
  letI : Algebra K Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  exact ((transported f a).exteriorPower 3).equivFun.toEquiv

private def trivialCoordinates (V : FramedOpen f) (p : ℕ) :
    (formsType f (p+4)).obj (op V) ≃ (Empty → (ringPresheaf f).obj (op V)) :=
  { toFun := fun _ i => i.elim
    invFun := fun _ => PUnit.unit
    left_inv := fun x => by change PUnit.unit = (x : PUnit); cases x; rfl
    right_inv := fun _ => funext fun i => i.elim }

private theorem formsType_isSheaf [SmoothOfRelativeDimension 2 f] (p : ℕ) :
    Presheaf.IsSheaf (topology f) (formsType f p) := by
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS
  have h := (ring_isSheaf f).isSheafFor S hS
  cases p with
  | zero =>
    exact CycleQ2SheafForLocalCoordinates.isSheafFor (fun {V} _ => functionCoordinates f V)
      (fun a g x i => rfl) h
  | succ p =>
    cases p with
    | zero =>
      exact CycleQ2SheafForLocalCoordinates.isSheafFor (oneCoordinates f)
        (fun a g x i => oneCoordinates_natural f a g x i) h
    | succ p =>
      cases p with
      | zero =>
        exact CycleQ2SheafForLocalCoordinates.isSheafFor (twoCoordinates f)
          (fun a g x i => exteriorCoordinates_natural f a g 2 x i) h
      | succ p =>
        cases p with
        | zero =>
          exact CycleQ2SheafForLocalCoordinates.isSheafFor (threeCoordinates f)
            (fun a g x i => exteriorCoordinates_natural f a g 3 x i) h
        | succ p =>
          exact CycleQ2SheafForLocalCoordinates.isSheafFor (fun {V} _ => trivialCoordinates f V p)
            (fun a g x i => i.elim) h

theorem forms_isSheaf [SmoothOfRelativeDimension 2 f] (p : ℕ) :
    Presheaf.IsSheaf (topology f) (forms f p) :=
  (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr (formsType_isSheaf f p)

def basisForms [SmoothOfRelativeDimension 2 f] (p : ℕ) : Sheaf (topology f) AddCommGrpCat :=
  ⟨forms f p, forms_isSheaf f p⟩

def basisDifferential [SmoothOfRelativeDimension 2 f] (p : ℕ) :
    basisForms f p ⟶ basisForms f (p+1) :=
  ⟨exterior f p⟩

def compare [SmoothOfRelativeDimension 2 f] :
    Sheaf (topology f) AddCommGrpCat.{0} ≌ TopCat.Sheaf AddCommGrpCat.{0} X := by
  have : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := cover_dense f
  exact (inclusion f).sheafInducedTopologyEquivOfIsCoverDense _ _

/-- The actual additive sheaves on the original Zariski opens. -/
abbrev sheafForms [SmoothOfRelativeDimension 2 f] (p : ℕ) : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (compare f).functor.obj (basisForms f p)

def differential [SmoothOfRelativeDimension 2 f] (p : ℕ) : sheafForms f p ⟶ sheafForms f (p+1) :=
  (compare f).functor.map (basisDifferential f p)

theorem differential_square [SmoothOfRelativeDimension 2 f] (p : ℕ) :
    differential f p ≫ differential f (p+1) = 0 := by
  unfold differential
  rw [← Functor.map_comp]
  have h : basisDifferential f p ≫ basisDifferential f (p+1) = 0 := by
    apply (sheafToPresheaf (topology f) AddCommGrpCat).map_injective
    exact exterior_square f p
  letI : (compare f).functor.Full := (compare f).fullyFaithfulFunctor.full
  rw [h, CategoryTheory.Functor.map_zero]

def relativeDeRham [SmoothOfRelativeDimension 2 f] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℕ :=
  CochainComplex.of (sheafForms f) (differential f) (differential_square f)

/-- The relative forms on every original basis open are the ordinary forms
over its actual function ring, compatibly with all restrictions. -/
def onBasisIso [SmoothOfRelativeDimension 2 f] (p : ℕ) :
    (inclusion f).op ⋙ (sheafForms f p).obj ≅ forms f p :=
  (sheafToPresheaf (topology f) AddCommGrpCat).mapIso
    (((compare f).unitIso.app (basisForms f p)).symm)

theorem onBasisIso_d [SmoothOfRelativeDimension 2 f] (p : ℕ) (U : FramedOpen f) :
    (differential f p).hom.app (op U.1) ≫ (onBasisIso f (p+1)).hom.app (op U) =
      (onBasisIso f p).hom.app (op U) ≫ (exterior f p).app (op U) :=
  congrArg (fun k => k.hom.app (op U)) ((compare f).unitIso.inv.naturality (basisDifferential f p))

/-- The same native relative complex in integer degrees for the derived category. -/
def relativeDeRhamInt [SmoothOfRelativeDimension 2 f] :
    CochainComplex (TopCat.Sheaf AddCommGrpCat.{0} X) ℤ :=
  (relativeDeRham f).extend (ComplexShape.embeddingUpIntGE 0)

end CycleQ2SurfaceDeRhamSheaves

#print axioms CycleQ2SurfaceDeRhamSheaves.forms_isSheaf
#print axioms CycleQ2SurfaceDeRhamSheaves.relativeDeRham

end

section

/-!
# Presheaves of ordinary forms and pullback on every open

The relative functions and exterior forms on the original section
rings give additive presheaves. Every map over the coefficient field
gives a natural pullback into the direct image of these presheaves.
Their restrictions to the exact affine bases are the ordinary terms
used in the actual relative de Rham complexes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RawRelativeForms

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap
open CycleQ2AffineDeRhamComplex CycleQ2AffineDeRhamFunctorial
open CycleQ2FramedAffineSite (restrict_id restrict_comp)
open CycleQ2RelativeSectionPullback

variable {K : Type} [Field K] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))

def forms (p : ℕ) : X.Opensᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj W :=
    letI : Algebra K Γ(X, W.unop) := (sectionCoefficients f W.unop).toAlgebra
    degree K Γ(X, W.unop) p
  map {U V} h :=
    letI : Algebra K Γ(X, U.unop) := (sectionCoefficients f U.unop).toAlgebra
    letI : Algebra K Γ(X, V.unop) := (sectionCoefficients f V.unop).toAlgebra
    pullDegree (restrict f h.unop.le) p
  map_id U := by
    letI : Algebra K Γ(X, U.unop) := (sectionCoefficients f U.unop).toAlgebra
    change pullDegree (restrict f (le_rfl : U.unop ≤ U.unop)) p = _
    rw [restrict_id]
    exact pullDegree_id p
  map_comp {U V W} h k := by
    letI : Algebra K Γ(X, U.unop) := (sectionCoefficients f U.unop).toAlgebra
    letI : Algebra K Γ(X, V.unop) := (sectionCoefficients f V.unop).toAlgebra
    letI : Algebra K Γ(X, W.unop) := (sectionCoefficients f W.unop).toAlgebra
    change pullDegree (restrict f (k.unop.le.trans h.unop.le)) p =
      pullDegree (restrict f h.unop.le) p ≫ pullDegree (restrict f k.unop.le) p
    rw [restrict_comp]
    exact pullDegree_comp _ _ p

variable (q : Y ⟶ X) (hq : q ≫ f = g)

abbrev directImage (P : Y.Opensᵒᵖ ⥤ AddCommGrpCat.{0}) : X.Opensᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Opens.map q.base).op ⋙ P

def pullToSubopen (p : ℕ) (U : X.Opens) (V : Y.Opens) (h : V ≤ q ⁻¹ᵁ U) :
    (forms f p).obj (op U) ⟶ (forms g p).obj (op V) :=
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  pullDegree (sectionPull f g q hq U V h) p

@[reassoc]
theorem pullToSubopen_restrict_source (p : ℕ) {U : X.Opens} {V W : Y.Opens}
    (h : V ≤ q ⁻¹ᵁ U) (j : W ≤ V) :
    pullToSubopen f g q hq p U V h ≫ (forms g p).map (homOfLE j).op =
      pullToSubopen f g q hq p U W (j.trans h) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  letI : Algebra K Γ(Y, W) := (sectionCoefficients g W).toAlgebra
  change pullDegree (sectionPull f g q hq U V h) p ≫ pullDegree (restrict g j) p =
    pullDegree (sectionPull f g q hq U W (j.trans h)) p
  rw [← pullDegree_comp, sectionPull_restrict_source]

@[reassoc]
theorem pullToSubopen_restrict_target (p : ℕ) {U U' : X.Opens} {V : Y.Opens}
    (h : V ≤ q ⁻¹ᵁ U') (j : U' ≤ U) :
    (forms f p).map (homOfLE j).op ≫ pullToSubopen f g q hq p U' V h =
      pullToSubopen f g q hq p U V (h.trans ((Opens.map q.base).map (homOfLE j)).le) := by
  letI : Algebra K Γ(X, U) := (sectionCoefficients f U).toAlgebra
  letI : Algebra K Γ(X, U') := (sectionCoefficients f U').toAlgebra
  letI : Algebra K Γ(Y, V) := (sectionCoefficients g V).toAlgebra
  change pullDegree (restrict f j) p ≫ pullDegree (sectionPull f g q hq U' V h) p =
    pullDegree (sectionPull f g q hq U V (h.trans ((Opens.map q.base).map (homOfLE j)).le)) p
  rw [← pullDegree_comp, sectionPull_restrict_target]

def pull (p : ℕ) : forms f p ⟶ directImage q (forms g p) where
  app U := pullToSubopen f g q hq p U.unop (q ⁻¹ᵁ U.unop) le_rfl
  naturality U V i := by
    have h₁ : i = (homOfLE i.unop.le).op := Subsingleton.elim _ _
    have h₂ : ((Opens.map q.base).op.map i) =
        (homOfLE (((Opens.map q.base).map (homOfLE i.unop.le)).le)).op := Subsingleton.elim _ _
    change (forms f p).map i ≫ pullToSubopen f g q hq p V.unop (q ⁻¹ᵁ V.unop) le_rfl =
      pullToSubopen f g q hq p U.unop (q ⁻¹ᵁ U.unop) le_rfl ≫
        (forms g p).map ((Opens.map q.base).op.map i)
    rw [h₂, pullToSubopen_restrict_source]
    rw [h₁]
    exact pullToSubopen_restrict_target f g q hq p le_rfl i.unop.le

end CycleQ2RawRelativeForms

#print axioms CycleQ2RawRelativeForms.pull

end

section

/-!
# Pullback of the actual de Rham sheaves to a smooth surface

The ordinary maps of forms on pairs of affine charts determine a map
into the actual direct image. Dense comparison is used twice, first
to attach regular forms on the preimage open to the surface sheaf,
then to extend the result across the ambient scheme.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2SurfacePullbackSheaves

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Functor (whiskerLeft)
open CycleQ2RawRelativeForms
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2RelativeDeRhamSheaves (sheafForms onBasisIso)
open CycleQ2FramedAffineSite (FramedOpen inclusion)

variable {K : Type} [Field K] [CharZero K] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  [SmoothOfRelativeDimension 3 f] [SmoothOfRelativeDimension 2 g]

local instance sourceDense :
    (CycleQ2SurfaceFramedAffineSite.inclusion g).IsCoverDense (Opens.grothendieckTopology Y) :=
  CycleQ2SurfaceFramedAffineSite.cover_dense g

local instance targetDense : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) :=
  CycleQ2FramedAffineSite.cover_dense f

/-- Map the ordinary presheaf into the actual surface differential sheaf. -/
def toSurface (p : ℕ) : forms g p ⟶ (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj :=
  Functor.IsCoverDense.sheafHom (G := CycleQ2SurfaceFramedAffineSite.inclusion g)
    (K := Opens.grothendieckTopology Y) (ℱ := forms g p) (ℱ' := CycleQ2SurfaceDeRhamSheaves.sheafForms g p)
    (CycleQ2SurfaceDeRhamSheaves.onBasisIso g p).inv

theorem toSurface_on_basis (p : ℕ) (V : CycleQ2SurfaceFramedAffineSite.FramedOpen g) :
    (toSurface g p).app (op V.1) = (CycleQ2SurfaceDeRhamSheaves.onBasisIso g p).inv.app (op V) := by
  have e := Functor.IsCoverDense.sheafHom_restrict_eq
    (G := CycleQ2SurfaceFramedAffineSite.inclusion g) (K := Opens.grothendieckTopology Y) (ℱ := forms g p)
    (ℱ' := CycleQ2SurfaceDeRhamSheaves.sheafForms g p)
    (CycleQ2SurfaceDeRhamSheaves.onBasisIso g p).inv
  exact NatTrans.congr_app e (op V)

variable (q : Y ⟶ X) (hq : q ≫ f = g)

abbrev target (p : ℕ) := (push q.base).obj (CycleQ2SurfaceDeRhamSheaves.sheafForms g p)

def onAmbientBasis (p : ℕ) :
    (inclusion f).op ⋙ (sheafForms f p).obj ⟶ (inclusion f).op ⋙ (target g q p).obj :=
  (onBasisIso f p).hom ≫ whiskerLeft (inclusion f).op
    (CycleQ2RawRelativeForms.pull f g q hq p ≫ whiskerLeft (Opens.map q.base).op (toSurface g p))

def pullbackSheaf (p : ℕ) : sheafForms f p ⟶ target g q p :=
  ⟨Functor.IsCoverDense.sheafHom (G := inclusion f) (K := Opens.grothendieckTopology X)
    (ℱ' := target g q p) (onAmbientBasis f g q hq p)⟩

theorem pullbackSheaf_on_ambient_basis (p : ℕ) (U : FramedOpen f) :
    (pullbackSheaf f g q hq p).hom.app (op U.1) = (onAmbientBasis f g q hq p).app (op U) := by
  have e := Functor.IsCoverDense.sheafHom_restrict_eq
    (G := inclusion f) (K := Opens.grothendieckTopology X) (ℱ' := target g q p)
    (onAmbientBasis f g q hq p)
  exact NatTrans.congr_app e (op U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
theorem pullbackSheaf_on_charts (p : ℕ) (U : FramedOpen f)
    (V : CycleQ2SurfaceFramedAffineSite.FramedOpen g) (h : V.1 ≤ q ⁻¹ᵁ U.1) :
    (pullbackSheaf f g q hq p).hom.app (op U.1) ≫
      (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj.map (homOfLE h).op ≫
      (CycleQ2SurfaceDeRhamSheaves.onBasisIso g p).hom.app (op V) =
    (onBasisIso f p).hom.app (op U) ≫ pullToSubopen f g q hq p U.1 V.1 h := by
  rw [pullbackSheaf_on_ambient_basis]
  change ((onBasisIso f p).hom.app (op U) ≫
       (pullToSubopen f g q hq p U.1 (q ⁻¹ᵁ U.1) le_rfl ≫
         (toSurface g p).app (op (q ⁻¹ᵁ U.1)))) ≫ _ ≫ _ = _
  simp only [Category.assoc]
  have e := (toSurface g p).naturality (homOfLE h).op
  change (forms g p).map (homOfLE h).op ≫ (toSurface g p).app (op V.1) =
    (toSurface g p).app (op (q ⁻¹ᵁ U.1)) ≫
      (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj.map (homOfLE h).op at e
  rw [← Category.assoc ((toSurface g p).app _), ← e, Category.assoc, pullToSubopen_restrict_source_assoc, toSurface_on_basis,
    Iso.inv_hom_id_app]
  let a := (onBasisIso f p).hom.app (op U)
  let b := pullToSubopen f g q hq p U.1 V.1 h
  exact congrArg (fun c => a ≫ c) (Category.comp_id b)

end CycleQ2SurfacePullbackSheaves

#print axioms CycleQ2SurfacePullbackSheaves.pullbackSheaf_on_charts

end

section

/-!
# The actual de Rham pullback as a morphism of complexes

Commutation with every differential is checked on the two dense
affine bases. The termwise maps therefore give one cochain morphism
on the original schemes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfacePullbackComplex

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CategoryTheory.Functor (whiskerLeft)
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2SurfacePullbackSheaves (pullbackSheaf pullbackSheaf_on_charts)
open CycleQ2RelativeDeRhamSheaves (sheafForms onBasisIso onBasisIso_d differential relativeDeRham)
open CycleQ2FramedAffineSite (FramedOpen inclusion exterior)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeSectionPullback (sectionPull)
open CycleQ2RawRelativeForms (pullToSubopen)

variable {K : Type} [Field K] [CharZero K] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  [SmoothOfRelativeDimension 3 f] [SmoothOfRelativeDimension 2 g]
  (q : Y ⟶ X) (hq : q ≫ f = g)

local instance sourceDense :
    (CycleQ2SurfaceFramedAffineSite.inclusion g).IsCoverDense (Opens.grothendieckTopology Y) :=
  CycleQ2SurfaceFramedAffineSite.cover_dense g

local instance targetDense : (inclusion f).IsCoverDense (Opens.grothendieckTopology X) :=
  CycleQ2FramedAffineSite.cover_dense f

private theorem chart_square (p : ℕ) (U : FramedOpen f)
    (V : CycleQ2SurfaceFramedAffineSite.FramedOpen g) (h : V.1 ≤ q ⁻¹ᵁ U.1) :
    pullToSubopen f g q hq p U.1 V.1 h ≫ (CycleQ2SurfaceFramedAffineSite.exterior g p).app (op V) =
      (exterior f p).app (op U) ≫ pullToSubopen f g q hq (p+1) U.1 V.1 h := by
  letI : Algebra K Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra K Γ(Y, V.1) := (sectionCoefficients g V.1).toAlgebra
  let φ := sectionPull f g q hq U.1 V.1 h
  let P := CycleQ2SurfaceDeRhamChart.pullFromThree (CycleQ2SurfaceFramedAffineSite.frame g V)
    (CycleQ2SurfaceFramedAffineSite.functions g V) (CycleQ2SurfaceFramedAffineSite.frame_apply g V)
    φ (CycleQ2FramedAffineSite.frame f U) (CycleQ2FramedAffineSite.functions f U)
    (CycleQ2FramedAffineSite.frame_apply f U)
  exact P.comm p (p+1)

private theorem morphism_on_chart_ext (p : ℕ) (W : Y.Opens) {A : AddCommGrpCat.{0}}
    {m n : A ⟶ (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj.obj (op W)}
    (h : ∀ (V : CycleQ2SurfaceFramedAffineSite.FramedOpen g) (hV : V.1 ≤ W),
      m ≫ (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj.map (homOfLE hV).op =
        n ≫ (CycleQ2SurfaceDeRhamSheaves.sheafForms g p).obj.map (homOfLE hV).op) :
    m = n := by
  let F := CycleQ2SurfaceDeRhamSheaves.sheafForms g p
  let E : Sheaf (Opens.grothendieckTopology Y) (Type) :=
    ⟨F.obj ⋙ forget AddCommGrpCat, Presheaf.isSheaf_comp_of_isSheaf _ F.obj _ F.property⟩
  ext x
  change (m x : E.obj.obj (op W)) = n x
  apply Functor.IsCoverDense.ext (CycleQ2SurfaceFramedAffineSite.inclusion g) E W
  intro V i
  exact ConcreteCategory.congr_hom (h V i.le) x

private theorem differential_on_ambient_basis (p : ℕ) (U : FramedOpen f) :
    (pullbackSheaf f g q hq p).hom.app (op U.1) ≫
        (CycleQ2SurfaceDeRhamSheaves.differential g p).hom.app (op (q ⁻¹ᵁ U.1)) =
      (differential f p).hom.app (op U.1) ≫ (pullbackSheaf f g q hq (p+1)).hom.app (op U.1) := by
  apply morphism_on_chart_ext g (p+1) (q ⁻¹ᵁ U.1)
  intro V h
  apply (cancel_mono ((CycleQ2SurfaceDeRhamSheaves.onBasisIso g (p+1)).hom.app (op V))).mp
  simp only [Category.assoc]
  rw [← (CycleQ2SurfaceDeRhamSheaves.differential g p).hom.naturality_assoc (homOfLE h).op,
    CycleQ2SurfaceDeRhamSheaves.onBasisIso_d g p V]
  simp only [← Category.assoc]
  rw [Category.assoc ((pullbackSheaf f g q hq p).hom.app _),
    pullbackSheaf_on_charts, Category.assoc,
    chart_square f g q hq p U V h,
    ← Category.assoc, ← onBasisIso_d f p U]
  simp only [Category.assoc, pullbackSheaf_on_charts]

theorem differential_comm (p : ℕ) :
    pullbackSheaf f g q hq p ≫ (push q.base).map (CycleQ2SurfaceDeRhamSheaves.differential g p) =
      differential f p ≫ pullbackSheaf f g q hq (p+1) := by
  apply Sheaf.hom_ext
  let E := Functor.IsCoverDense.restrictHomEquivHom
    (G := inclusion f) (K := Opens.grothendieckTopology X) (ℱ := (sheafForms f p).obj)
    (ℱ' := (push q.base).obj (CycleQ2SurfaceDeRhamSheaves.sheafForms g (p+1)))
  apply E.symm.injective
  apply NatTrans.ext
  funext U
  exact differential_on_ambient_basis f g q hq p U.unop

/-- The literal cochain pullback to the direct image of the surface complex. -/
def pullbackComplex :
    relativeDeRham f ⟶ ((push q.base).mapHomologicalComplex (.up ℕ)).obj
      (CycleQ2SurfaceDeRhamSheaves.relativeDeRham g) :=
  CochainComplex.ofHom (pullbackSheaf f g q hq) (by
    intro p
    change pullbackSheaf f g q hq p ≫
        (push q.base).map ((CycleQ2SurfaceDeRhamSheaves.relativeDeRham g).d p (p+1)) =
      (relativeDeRham f).d p (p+1) ≫ pullbackSheaf f g q hq (p+1)
    simp only [relativeDeRham, CycleQ2SurfaceDeRhamSheaves.relativeDeRham, CochainComplex.of_d]
    exact differential_comm f g q hq p)

end CycleQ2SurfacePullbackComplex

#print axioms CycleQ2SurfacePullbackComplex.pullbackComplex

end

section

/-!
# Actual derived pullback to the smooth graph open

Pullback of additive sheaves is exact. The adjoint of the relative
de Rham cochain map gives an actual morphism of integer-graded
complexes, hence a map on degree-three hypercohomology classes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SurfacePullbackDerived

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2ClosedEmbeddingSheafExact (push)
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (app)

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] reflectsLimits_of_reflectsIsomorphisms
  preservesBinaryBiproducts_of_preservesBinaryCoproducts

section Inverse

variable {X Y : TopCat.{0}} (j : Y ⟶ X)

abbrev inverse := TopCat.Sheaf.pullback AddCommGrpCat.{0} j

abbrev adjunction : inverse j ⊣ push j := TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{0} j

local instance : PreservesFiniteLimits (inverse j) := by
  unfold inverse TopCat.Sheaf.pullback
  exact Functor.sheafPullbackConstruction.preservesFiniteLimits _ _ _ _

local instance : (inverse j).IsLeftAdjoint := (adjunction j).isLeftAdjoint

local instance : (inverse j).Additive := Functor.additive_of_preservesBinaryBiproducts _

variable {ι : Type} {c : ComplexShape ι}

/-- Adjunction on sheaves commutes with the differential equation of a cochain map. -/
def adjointOnComplex {K : HomologicalComplex (AbSheaf X) c}
    {L : HomologicalComplex (AbSheaf Y) c}
    (ψ : K ⟶ ((push j).mapHomologicalComplex c).obj L) :
    ((inverse j).mapHomologicalComplex c).obj K ⟶ L where
  f n := ((adjunction j).homEquiv _ _).symm (ψ.f n)
  comm' i k _ := ((adjunction j).homEquiv_naturality_right_square
    (K.d i k) (ψ.f k) (ψ.f i) (L.d i k) (ψ.comm i k).symm).symm

private abbrev e := ComplexShape.embeddingUpIntGE 0

private def restrictionIso (K : CochainComplex (AbSheaf X) ℕ) :
    (K.extend e).restriction e ≅ K :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => K.extendXIso e rfl) (by
    intro p r h
    change (K.extendXIso e rfl).hom ≫ K.d p r =
      (K.extend e).d (e.f p) (e.f r) ≫ (K.extendXIso e rfl).hom
    simp only [K.extend_d_eq e rfl rfl, Category.assoc, Iso.inv_hom_id, Category.comp_id])

def adjointOnComplexInt {K : CochainComplex (AbSheaf X) ℕ}
    {L : CochainComplex (AbSheaf Y) ℕ}
    (ψ : K ⟶ ((push j).mapHomologicalComplex (.up ℕ)).obj L) :
    ((inverse j).mapHomologicalComplex (.up ℤ)).obj (K.extend e) ⟶ L.extend e := by
  let F := inverse j
  let M := (F.mapHomologicalComplex (.up ℤ)).obj (K.extend e)
  let φ : M.restriction e ⟶ L :=
    (F.mapHomologicalComplex (.up ℕ)).map (restrictionIso K).hom ≫ adjointOnComplex j ψ
  refine e.liftExtend φ ?_
  intro n hn i hi
  have hz : IsZero (M.X i) :=
    F.map_isZero (K.isZero_extend_X e i (fun l hl => hn.notMem hi l hl))
  exact hz.eq_of_src _ _

/-- The actual derived morphism induced by a pullback cochain map. -/
def derivedPull {K : CochainComplex (AbSheaf X) ℕ} {L : CochainComplex (AbSheaf Y) ℕ}
    (ψ : K ⟶ ((push j).mapHomologicalComplex (.up ℕ)).obj L) :
    (inverse j).mapDerivedCategory.obj (DerivedCategory.Q.obj (K.extend e)) ⟶
      DerivedCategory.Q.obj (L.extend e) :=
  (inverse j).mapDerivedCategoryFactors.hom.app (K.extend e) ≫
    DerivedCategory.Q.map (adjointOnComplexInt j ψ)

/-- The inverse image of the global-section generator receives the
canonical global-section generator on the source. -/
def globalSectionsSource :
    freeOpen (⊤ : Opens Y) ⟶ (inverse j).obj (freeOpen (⊤ : Opens X)) :=
  (freeOpenSections _ ⊤).symm (app ((adjunction j).unit.app (freeOpen (⊤ : Opens X))) ⊤
    (freeOpenSections _ ⊤ (𝟙 (freeOpen (⊤ : Opens X)))))

def derivedGlobalPull {K : CochainComplex (AbSheaf X) ℕ} {L : CochainComplex (AbSheaf Y) ℕ}
    (ψ : K ⟶ ((push j).mapHomologicalComplex (.up ℕ)).obj L) (n : ℤ)
    (a : (DerivedCategory.singleFunctor (AbSheaf X) n).obj (freeOpen (⊤ : Opens X)) ⟶
      DerivedCategory.Q.obj (K.extend e)) :
    (DerivedCategory.singleFunctor (AbSheaf Y) n).obj (freeOpen (⊤ : Opens Y)) ⟶
      DerivedCategory.Q.obj (L.extend e) :=
  (DerivedCategory.singleFunctor (AbSheaf Y) n).map (globalSectionsSource j) ≫
    ((inverse j).mapDerivedCategorySingleFunctor n).inv.app _ ≫
      (inverse j).mapDerivedCategory.map a ≫ derivedPull j ψ

end Inverse

section Surface

variable {K : Type} [Field K] [CharZero K] {X Y : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of K)) (g : Y ⟶ Spec (CommRingCat.of K))
  [SmoothOfRelativeDimension 3 f] [SmoothOfRelativeDimension 2 g]
  (q : Y ⟶ X) (hq : q ≫ f = g)

/-- Pullback on degree-three derived de Rham classes for the actual map of schemes. -/
def pullH3
    (a : (DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 3).obj (freeOpen (⊤ : X.Opens)) ⟶
      DerivedCategory.Q.obj (CycleQ2RelativeDeRhamSheaves.relativeDeRhamInt f)) :
    (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 3).obj (freeOpen (⊤ : Y.Opens)) ⟶
      DerivedCategory.Q.obj (CycleQ2SurfaceDeRhamSheaves.relativeDeRhamInt g) :=
  derivedGlobalPull q.base (CycleQ2SurfacePullbackComplex.pullbackComplex f g q hq) 3 a

end Surface

end CycleQ2SurfacePullbackDerived

#print axioms CycleQ2SurfacePullbackDerived.pullH3

end

section

/-!
# Pullback along the original generic surface projection

The smooth generic surface is the actual pullback of the original
time-family open. The projection to the monic weighted threefold is
over the same coefficient field, so the constructed derived map
applies to the original relative complexes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2GenericSurfaceDerivedPull

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite
open CycleQ2GenericProperGraphOpen
open CycleQ2LiteralIncidenceGenericCorrespondence
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2InjectiveCech (AbSheaf freeOpen)

attribute [local instance] HasDerivedCategory.standard

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

abbrev projection : GenericSurface V t ⟶ genericAmbient :=
  graphOpen V t ≫ genericAmbientProjection V t

theorem projection_over : projection V t ≫ ambientToField = genericSurfaceStructure V t := by
  unfold projection
  rw [Category.assoc]
  have h₁ : genericAmbientProjection V t ≫ ambientToField = toGenericField V t := by
    unfold genericAmbientProjection
    exact CycleQ2CoefficientBaseChange.changeMap_snd _ _ _
  rw [h₁]
  unfold graphOpen
  exact CycleQ2CoefficientBaseChange.changeMap_snd _ _ _

local instance : SmoothOfRelativeDimension 3 ambientToField :=
  CycleQ2NativeGenericSmooth.ambient_smooth

/-- The actual pullback from the generic threefold to the smooth graph
open, defined on the native relative de Rham cochain complexes. -/
def nativePull (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t)) :
    letI : SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) := graphOpen_smooth V t hs
    CycleQ2RelativeDeRhamSheaves.relativeDeRham ambientToField ⟶
      ((CycleQ2ClosedEmbeddingSheafExact.push (projection V t).base).mapHomologicalComplex
        (.up ℕ)).obj (CycleQ2SurfaceDeRhamSheaves.relativeDeRham (genericSurfaceStructure V t)) := by
  exact @CycleQ2SurfacePullbackComplex.pullbackComplex
    _ _ _ _ _ ambientToField (genericSurfaceStructure V t)
    CycleQ2NativeGenericSmooth.ambient_smooth (graphOpen_smooth V t hs)
    (projection V t) (projection_over V t)

/-- The induced pullback of arbitrary actual degree-three classes on the generic fibre. -/
def nativePullH3 (hs : SmoothOfRelativeDimension 2 (surfaceStructure V t))
    (a : (DerivedCategory.singleFunctor (AbSheaf (show TopCat from genericAmbient)) 3).obj
      (freeOpen (⊤ : genericAmbient.Opens)) ⟶ DerivedCategory.Q.obj CycleQ2NativeWeightedDeRham.complex) :
    letI : SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) := graphOpen_smooth V t hs
    (DerivedCategory.singleFunctor (AbSheaf (show TopCat from GenericSurface V t)) 3).obj
      (freeOpen (⊤ : (GenericSurface V t).Opens)) ⟶
      DerivedCategory.Q.obj (CycleQ2SurfaceDeRhamSheaves.relativeDeRhamInt (genericSurfaceStructure V t)) := by
  letI : SmoothOfRelativeDimension 2 (genericSurfaceStructure V t) := graphOpen_smooth V t hs
  exact CycleQ2SurfacePullbackDerived.pullH3 ambientToField (genericSurfaceStructure V t)
    (projection V t) (projection_over V t) a

end CycleQ2GenericSurfaceDerivedPull

#print axioms CycleQ2GenericSurfaceDerivedPull.nativePull
#print axioms CycleQ2GenericSurfaceDerivedPull.nativePullH3

end

section

/-!
# The actual two-chart projective line

Glue two affine polynomial spectra along the Laurent spectrum using
the inverse coordinate on the second chart. The two chart images
cover the scheme, and their intersection is precisely the shared
Laurent spectrum.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LaurentProjectiveLine

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Polynomial LaurentPolynomial

variable (k : Type) [Field k]

abbrev affineLine := Spec (CommRingCat.of k[X])

abbrev torus := Spec (CommRingCat.of (LaurentPolynomial k))

def zeroMap : torus k ⟶ affineLine k :=
  Spec.map (CommRingCat.ofHom Polynomial.toLaurent)

def inversion : torus k ⟶ torus k :=
  Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.toRingHom)

instance : IsOpenImmersion (zeroMap k) :=
  IsOpenImmersion.of_isLocalization (Polynomial.X : k[X])

instance : IsIso (inversion k) := by
  let a := (LaurentPolynomial.invert (R := k)).toRingEquiv.toCommRingCatIso
  change IsIso (Scheme.Spec.map a.hom.op)
  infer_instance

def infinityMap : torus k ⟶ affineLine k := inversion k ≫ zeroMap k

instance : IsOpenImmersion (infinityMap k) := by unfold infinityMap; infer_instance

abbrev diagram := span (zeroMap k) (infinityMap k)

abbrev line := colimit (diagram k)

abbrev chartZero : affineLine k ⟶ line k := colimit.ι (diagram k) WalkingSpan.left
abbrev chartInfinity : affineLine k ⟶ line k := colimit.ι (diagram k) WalkingSpan.right
abbrev chartTorus : torus k ⟶ line k := colimit.ι (diagram k) WalkingSpan.zero

instance : IsOpenImmersion (chartZero k) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (diagram k) WalkingSpan.left))

instance : IsOpenImmersion (chartInfinity k) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (diagram k) WalkingSpan.right))

instance : IsOpenImmersion (chartTorus k) := inferInstanceAs
  (IsOpenImmersion (colimit.ι (diagram k) WalkingSpan.zero))

theorem torus_zero : zeroMap k ≫ chartZero k = chartTorus k :=
  colimit.w (diagram k) WalkingSpan.Hom.fst

theorem torus_infinity : infinityMap k ≫ chartInfinity k = chartTorus k :=
  colimit.w (diagram k) WalkingSpan.Hom.snd

abbrev openZero := (chartZero k).opensRange
abbrev openInfinity := (chartInfinity k).opensRange

theorem cover : openZero k ⊔ openInfinity k = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (diagram k) x
  rcases i with (_ | (_ | _))
  · exact Or.inl ⟨zeroMap k y, congrArg (fun f : torus k ⟶ line k => f y) (torus_zero k)⟩
  · exact Or.inl ⟨y,rfl⟩
  · exact Or.inr ⟨y,rfl⟩

theorem overlap : openZero k ⊓ openInfinity k = (chartTorus k).opensRange := by
  ext x
  constructor
  · rintro ⟨⟨y,rfl⟩,⟨z,hz⟩⟩
    obtain ⟨i, il, ir, u, h₁,h₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram k)).mp hz.symm
    rcases i with (_ | (_ | _))
    · have e : il = WalkingSpan.Hom.fst := Subsingleton.elim _ _
      subst il
      exact ⟨u, (congrArg (fun f : torus k ⟶ line k => f u) (torus_zero k)).symm.trans
        (congrArg (chartZero k) h₁)⟩
    · cases ir
    · cases il
  · rintro ⟨z,rfl⟩
    exact ⟨⟨zeroMap k z, congrArg (fun f : torus k ⟶ line k => f z) (torus_zero k)⟩,
      ⟨infinityMap k z, congrArg (fun f : torus k ⟶ line k => f z) (torus_infinity k)⟩⟩

end CycleQ2LaurentProjectiveLine

#print axioms CycleQ2LaurentProjectiveLine.cover
#print axioms CycleQ2LaurentProjectiveLine.overlap

end

section

/-!
# The coefficient map and ordinary affine charts of the glued line

The zero and infinity polynomial charts induce the same map to the
coefficient field on the Laurent overlap. Their common structure
map is smooth of relative dimension one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineStructure

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine
open Polynomial

variable (k : Type) [Field k]

abbrev base := Spec (CommRingCat.of k)

def affineStructure : affineLine k ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k k[X]))

def torusStructure : torus k ⟶ base k :=
  Spec.map (CommRingCat.ofHom (algebraMap k (LaurentPolynomial k)))

theorem zeroMap_over : zeroMap k ≫ affineStructure k = torusStructure k := by
  rw [zeroMap, affineStructure, torusStructure, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (Polynomial.toLaurentAlg (R := k)).commutes

theorem inversion_over : inversion k ≫ torusStructure k = torusStructure k := by
  rw [inversion, torusStructure, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (LaurentPolynomial.invert (R := k)).commutes

theorem infinityMap_over : infinityMap k ≫ affineStructure k = torusStructure k := by
  rw [infinityMap, Category.assoc, zeroMap_over, inversion_over]

/-- The actual induced morphism from the glued line to its coefficient field. -/
def structureMap : line k ⟶ base k :=
  pushout.desc (affineStructure k) (affineStructure k) ((zeroMap_over k).trans (infinityMap_over k).symm)

theorem chartZero_over : chartZero k ≫ structureMap k = affineStructure k := by
  unfold structureMap
  exact pushout.inl_desc _ _ _

theorem chartInfinity_over : chartInfinity k ≫ structureMap k = affineStructure k := by
  unfold structureMap
  exact pushout.inr_desc _ _ _

theorem chartTorus_over : chartTorus k ≫ structureMap k = torusStructure k := by
  rw [← torus_zero k, Category.assoc, chartZero_over, zeroMap_over]

private theorem affine_smooth : SmoothOfRelativeDimension 1 (affineStructure k) := by
  let P : Algebra.SubmersivePresentation k (MvPolynomial PUnit k) PUnit Empty :=
    { toPreSubmersivePresentation :=
        { toGenerators := Algebra.Generators.mvPolynomial k PUnit
          relation := Empty.elim
          span_range_relation_eq_ker := by rw [Algebra.Generators.ker_mvPolynomial]; simp
          map := Empty.elim
          map_inj := fun a => a.elim }
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hP : Algebra.IsStandardSmoothOfRelativeDimension 1 k (MvPolynomial PUnit k) :=
    P.isStandardSmoothOfRelativeDimension (by
      change Nat.card PUnit - Nat.card Empty = 1
      simp [Nat.card_eq_fintype_card])
  have h : SmoothOfRelativeDimension 1
      (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial PUnit k)))) := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
      ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap 1).mpr hP)
  let e := (MvPolynomial.uniqueAlgEquiv k PUnit).toRingEquiv.toCommRingCatIso
  let q := Spec.map e.hom
  have hq : IsIso q := inferInstanceAs (IsIso (Scheme.Spec.map e.hom.op))
  have ee : affineStructure k = q ≫ Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial PUnit k))) := by
    rw [affineStructure, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    exact fun r => ((MvPolynomial.uniqueAlgEquiv k PUnit).commutes r).symm
  rw [ee]
  exact smoothOfRelativeDimension_comp 0 1 q _

theorem smooth : SmoothOfRelativeDimension 1 (structureMap k) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @SmoothOfRelativeDimension 1)
    (Scheme.IsLocallyDirected.openCover (diagram k))).mpr
  intro i
  rcases i with (_ | (_ | _))
  · change SmoothOfRelativeDimension 1 (chartTorus k ≫ structureMap k)
    rw [← torus_zero k, Category.assoc, chartZero_over]
    have := affine_smooth k
    exact smoothOfRelativeDimension_comp 0 1 (zeroMap k) (affineStructure k)
  · change SmoothOfRelativeDimension 1 (chartZero k ≫ structureMap k)
    rw [chartZero_over]
    exact affine_smooth k
  · change SmoothOfRelativeDimension 1 (chartInfinity k ≫ structureMap k)
    rw [chartInfinity_over]
    exact affine_smooth k

end CycleQ2ProjectiveLineStructure

#print axioms CycleQ2ProjectiveLineStructure.smooth

end

section

/-!
# The actual ordinary one-form sheaf on a smooth relative curve

Regular Kähler one-forms glue in the inherited exact affine frame.
The resulting sheaf has the ordinary derivation from the structure
sheaf, with its actual restrictions on the original affine opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RankOneDifferentialSheaf

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2FiniteExactAffineAtlas CycleQ2SmoothRelativeFrames CycleQ2RelativeAffineOverlap
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2FramedAffineCoordinates (coefficients_natural)
open CycleQ2ExactFrameThreeDeRham (onePullback onePullback_d)

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))

abbrev Framed := {U : X.Opens // IsAffineOpen U ∧ HasFrame f 1 U}

def inclusion : Framed f ⥤ X.Opens where
  obj U := U.1
  map h := homOfLE h.le

instance : (inclusion f).Full where
  map_surjective g := ⟨homOfLE g.le, Subsingleton.elim _ _⟩

instance : (inclusion f).Faithful where
  map_injective _ := Subsingleton.elim _ _

local instance dense [SmoothOfRelativeDimension 1 f] :
    (inclusion f).IsCoverDense (Opens.grothendieckTopology X) := by
  apply (TopCat.Opens.coverDense_iff_isBasis _).mpr
  have h : Set.range (inclusion f).obj = {U : X.Opens | IsAffineOpen U ∧ HasFrame f 1 U} := by
    ext U
    constructor
    · rintro ⟨⟨W,hW⟩,rfl⟩
      exact hW
    · intro hU
      exact ⟨⟨U,hU⟩,rfl⟩
  rw [h]
  exact CycleQ2FiniteExactAffineAtlas.isBasis f 1

abbrev site := (inclusion f).inducedTopology (Opens.grothendieckTopology X)

abbrev functions : TopCat.Sheaf AddCommGrpCat.{0} X :=
  CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf X

private abbrev raw := CycleQ2RawRelativeForms.forms f 1

private def coordinates {U V : Framed f} (a : V ⟶ U) :
    letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    Basis (Fin 1) Γ(X, V.1) Ω[Γ(X,V.1)⁄k] :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 U.2.2.choose
    U.2.2.choose_spec.choose U.2.2.choose_spec.choose_spec).choose

private theorem coordinates_apply {U V : Framed f} (a : V ⟶ U) (i : Fin 1) :
    letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    coordinates f a i = D k Γ(X,V.1) (restrict f a.le (U.2.2.choose i)) :=
  (exact_on_affine_subopen f a.le U.2.1 V.2.1 U.2.2.choose
    U.2.2.choose_spec.choose U.2.2.choose_spec.choose_spec).choose_spec i

private theorem transported_natural {U V W : Framed f} (a : V ⟶ U) (b : W ⟶ V) (i : Fin 1) :
    letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
    letI : Algebra k Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
    onePullback (restrict f b.le) (coordinates f a i) = coordinates f (b ≫ a) i := by
  letI : Algebra k Γ(X, U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra k Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  rw [coordinates_apply, onePullback_d, coordinates_apply]
  apply congrArg (D k Γ(X,W.1))
  exact (DFunLike.congr_fun (restrict_comp f a.le b.le) (U.2.2.choose i)).symm

private abbrev basisForms := (inclusion f).op ⋙ raw f

private abbrev formsType := basisForms f ⋙ forget AddCommGrpCat

private abbrev ringType := (inclusion f).op ⋙ X.presheaf ⋙ forget CommRingCat

private def frameCoordinates {U V : Framed f} (a : V ⟶ U) :
    (formsType f).obj (op V) ≃ (Fin 1 → (ringType f).obj (op V)) :=
  letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  (coordinates f a).equivFun.toEquiv

private theorem frameCoordinates_natural {U V W : Framed f} (a : V ⟶ U) (b : W ⟶ V)
    (ω : (formsType f).obj (op V)) (i : Fin 1) :
    frameCoordinates f (b ≫ a) ((formsType f).map b.op ω) i =
      (ringType f).map b.op (frameCoordinates f a ω i) := by
  letI : Algebra k Γ(X, V.1) := (sectionCoefficients f V.1).toAlgebra
  letI : Algebra k Γ(X, W.1) := (sectionCoefficients f W.1).toAlgebra
  exact coefficients_natural _ _ _ _ (transported_natural f a b) ω i

private theorem isSheaf [SmoothOfRelativeDimension 1 f] : Presheaf.IsSheaf (site f) (basisForms f) := by
  apply (Presheaf.isSheaf_iff_isSheaf_forget _ _ (forget AddCommGrpCat)).mpr
  apply (isSheaf_iff_isSheaf_of_type _ _).mpr
  intro U S hS
  have h : Presheaf.IsSheaf (site f) ((inclusion f).op ⋙ X.presheaf) :=
    Functor.op_comp_isSheaf _ _ _ X.sheaf
  have h' : Presheaf.IsSheaf (site f) (ringType f) :=
    Presheaf.isSheaf_comp_of_isSheaf _ ((inclusion f).op ⋙ X.presheaf) (forget CommRingCat) h
  exact CycleQ2SheafForLocalCoordinates.isSheafFor (frameCoordinates f)
    (frameCoordinates_natural f) (h'.isSheafFor S hS)

def basisSheaf [SmoothOfRelativeDimension 1 f] : Sheaf (site f) AddCommGrpCat :=
  ⟨basisForms f, isSheaf f⟩

def compare [SmoothOfRelativeDimension 1 f] :
    Sheaf (site f) AddCommGrpCat.{0} ≌ TopCat.Sheaf AddCommGrpCat.{0} X :=
  (inclusion f).sheafInducedTopologyEquivOfIsCoverDense _ _

abbrev oneForms [SmoothOfRelativeDimension 1 f] : TopCat.Sheaf AddCommGrpCat.{0} X :=
  (compare f).functor.obj (basisSheaf f)

def onBasisIso [SmoothOfRelativeDimension 1 f] : (inclusion f).op ⋙ (oneForms f).obj ≅ basisForms f :=
  (sheafToPresheaf (site f) AddCommGrpCat).mapIso (((compare f).unitIso.app (basisSheaf f)).symm)

private def rawDeriv : (functions (X := X)).obj ⟶ raw f where
  app W := letI : Algebra k Γ(X,W.unop) := (sectionCoefficients f W.unop).toAlgebra
    AddCommGrpCat.ofHom (D k Γ(X,W.unop)).toLinearMap.toAddMonoidHom
  naturality U V j := by
    letI : Algebra k Γ(X,U.unop) := (sectionCoefficients f U.unop).toAlgebra
    letI : Algebra k Γ(X,V.unop) := (sectionCoefficients f V.unop).toAlgebra
    ext a
    change Γ(X,U.unop) at a
    exact (onePullback_d (restrict f j.unop.le) a).symm

/-- The universal ordinary derivation into the actual one-form sheaf. -/
def derivative [SmoothOfRelativeDimension 1 f] : functions (X := X) ⟶ oneForms f :=
  ⟨Functor.IsCoverDense.sheafHom (G := inclusion f) (K := Opens.grothendieckTopology X)
    (ℱ' := oneForms f) (Functor.whiskerLeft (inclusion f).op (rawDeriv f) ≫ (onBasisIso f).inv)⟩

theorem derivative_on_basis [SmoothOfRelativeDimension 1 f] (U : Framed f) :
    (derivative f).hom.app (op U.1) ≫ (onBasisIso f).hom.app (op U) =
      (rawDeriv f).app (op U.1) := by
  have h := Functor.IsCoverDense.sheafHom_restrict_eq
    (G := inclusion f) (K := Opens.grothendieckTopology X) (ℱ' := oneForms f)
    (Functor.whiskerLeft (inclusion f).op (rawDeriv f) ≫ (onBasisIso f).inv)
  have e := NatTrans.congr_app h (op U)
  change (derivative f).hom.app (op U.1) =
    (rawDeriv f).app (op U.1) ≫ (onBasisIso f).inv.app (op U) at e
  rw [e, Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id ((rawDeriv f).app (op U.1))

end CycleQ2RankOneDifferentialSheaf

#print axioms CycleQ2RankOneDifferentialSheaf.derivative_on_basis

end

section

/-!
# The original restriction between two explicit affine schemes

When one affine chart factors through another, the restriction on
their actual section rings is the original algebra map between
their coordinate rings. The identification also holds for ordinary
Kähler one-forms by functoriality.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2NativeChartRestriction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2AffineFrameBinding (sectionEquiv)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)

variable {k A B : Type} [Field k] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of k))
  (a : Spec (CommRingCat.of A) ⟶ X) (b : Spec (CommRingCat.of B) ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b]
  (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  (hb : b ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (φ : A →ₐ[k] B) (h : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ a = b)
  (hle : b ''ᵁ ⊤ ≤ a ''ᵁ ⊤)

include h in
theorem sections_restrict :
    letI : Algebra k Γ(X, a ''ᵁ ⊤) := (sectionCoefficients f (a ''ᵁ ⊤)).toAlgebra
    letI : Algebra k Γ(X, b ''ᵁ ⊤) := (sectionCoefficients f (b ''ᵁ ⊤)).toAlgebra
    (sectionEquiv f b hb).toAlgHom.comp (restrict f hle) =
      φ.comp (sectionEquiv f a ha).toAlgHom := by
  letI : Algebra k Γ(X, a ''ᵁ ⊤) := (sectionCoefficients f (a ''ᵁ ⊤)).toAlgebra
  letI : Algebra k Γ(X, b ''ᵁ ⊤) := (sectionCoefficients f (b ''ᵁ ⊤)).toAlgebra
  let q := Spec.map (CommRingCat.ofHom φ.toRingHom)
  let U := a ''ᵁ (⊤ : (Spec (CommRingCat.of A)).Opens)
  let V := b ''ᵁ (⊤ : (Spec (CommRingCat.of B)).Opens)
  have e₁ : ⊤ ≤ a ⁻¹ᵁ U := (Scheme.Hom.preimage_image_eq a ⊤).ge
  have e₂ : ⊤ ≤ q ⁻¹ᵁ ⊤ := le_rfl
  have e₃ : ⊤ ≤ b ⁻¹ᵁ V := (Scheme.Hom.preimage_image_eq b ⊤).ge
  have e₄ : q.appLE ⊤ ⊤ e₂ = q.appTop := Scheme.Hom.appLE_eq_app q
  have eq : X.presheaf.map (homOfLE hle).op ≫ (b.appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom =
      (a.appIso ⊤).hom ≫ (Scheme.ΓSpecIso _).hom ≫ CommRingCat.ofHom φ.toRingHom := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc (a.appIso ⊤).hom,
      ← Category.assoc (X.presheaf.map (homOfLE hle).op)]
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, ← e₄,
      Scheme.Hom.appLE_comp_appLE]
    change q ≫ a = b at h
    cases h
    rfl
  apply AlgHom.ext
  intro x
  exact congrArg (fun g : Γ(X,U) ⟶ CommRingCat.of B => g x) eq

end CycleQ2NativeChartRestriction

#print axioms CycleQ2NativeChartRestriction.sections_restrict

end

section

/-!
# Exact cotangent frames on the original projective-line charts

The ordinary polynomial frame is dX. On the actual Laurent overlap,
dT is a frame because T is a unit and dT/T is the logarithmic frame.
The three frames are transported through the original chart rings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineExactCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open Polynomial LaurentPolynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2LaurentLogDerivative (L logCoordinates logDerivative_T)
open CycleQ2LaurentKahlerResidue (logCoordinates_D)
open CycleQ2RankOneDifferentialSheaf
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2AffineFrameBinding (frame_of_chart sectionEquiv)
open CycleQ2ExactFrameThreeDeRham (onePullback onePullback_d)
open CycleQ2AffineDeRhamFunctorial (onePullback_comp onePullback_id)

variable (k : Type) [Field k]

local instance : SmoothOfRelativeDimension 1 (structureMap k) := smooth k

def polynomialFrame : Basis (Fin 1) k[X] Ω[k[X]⁄k] :=
  (Basis.singleton (Fin 1) k[X]).map (polynomialEquiv k).symm

theorem polynomialFrame_apply (i : Fin 1) :
    polynomialFrame k i = D k k[X] X := by
  rw [polynomialFrame, Basis.map_apply, Basis.singleton_apply, polynomialEquiv_symm, one_smul]

private def torusUnit : (L k)ˣ := (isUnit_T (R := k) 1).unit

def torusFrame : Basis (Fin 1) (L k) Ω[L k⁄k] :=
  (Basis.singleton (Fin 1) (L k)).map
    ((LinearEquiv.smulOfUnit (M := L k) (torusUnit k)).trans (logCoordinates k).symm)

theorem torusFrame_apply (i : Fin 1) :
    torusFrame k i = D k (L k) (T 1) := by
  apply (logCoordinates k).injective
  rw [torusFrame, Basis.map_apply, Basis.singleton_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, logCoordinates_D, logDerivative_T, Int.cast_one]
  change (torusUnit k : L k) * 1 = LaurentPolynomial.C (1 : k) * T 1
  rw [mul_one, (LaurentPolynomial.C : k →+* L k).map_one, one_mul, torusUnit, IsUnit.unit_spec]

private theorem affine_openRange {A : Type} [CommRing A]
    (j : Spec (CommRingCat.of A) ⟶ line k) [IsOpenImmersion j] : IsAffineOpen (j ''ᵁ ⊤) := by
  rw [j.image_top_eq_opensRange]
  exact isAffineOpen_opensRange j

def zeroFramed : Framed (structureMap k) :=
  ⟨(chartZero k) ''ᵁ ⊤, affine_openRange k (chartZero k),
    frame_of_chart (structureMap k) (chartZero k) (chartZero_over k)
      (fun _ => X) (polynomialFrame k) (polynomialFrame_apply k)⟩

def infinityFramed : Framed (structureMap k) :=
  ⟨(chartInfinity k) ''ᵁ ⊤, affine_openRange k (chartInfinity k),
    frame_of_chart (structureMap k) (chartInfinity k) (chartInfinity_over k)
      (fun _ => X) (polynomialFrame k) (polynomialFrame_apply k)⟩

def torusFramed : Framed (structureMap k) :=
  ⟨(chartTorus k) ''ᵁ ⊤, affine_openRange k (chartTorus k),
    frame_of_chart (structureMap k) (chartTorus k) (chartTorus_over k)
      (fun _ => T 1) (torusFrame k) (torusFrame_apply k)⟩

theorem cover_framed : (zeroFramed k).1 ⊔ (infinityFramed k).1 = ⊤ := by
  change (chartZero k) ''ᵁ ⊤ ⊔ (chartInfinity k) ''ᵁ ⊤ = ⊤
  rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.image_top_eq_opensRange]
  exact cover k

theorem overlap_framed : (torusFramed k).1 = (zeroFramed k).1 ⊓ (infinityFramed k).1 := by
  change (chartTorus k) ''ᵁ ⊤ = ((chartZero k) ''ᵁ ⊤) ⊓ ((chartInfinity k) ''ᵁ ⊤)
  simp only [Scheme.Hom.image_top_eq_opensRange]
  exact (overlap k).symm

private def pullEquiv {A B : Type} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) : Ω[A⁄k] ≃+ Ω[B⁄k] where
  toFun := onePullback e.toAlgHom
  invFun := onePullback e.symm.toAlgHom
  left_inv ω := by
    rw [← onePullback_comp, show e.symm.toAlgHom.comp e.toAlgHom = AlgHom.id k A from
      AlgHom.ext e.symm_apply_apply, onePullback_id]
  right_inv ω := by
    rw [← onePullback_comp, show e.toAlgHom.comp e.symm.toAlgHom = AlgHom.id k B from
      AlgHom.ext e.apply_symm_apply, onePullback_id]
  map_add' := (onePullback e.toAlgHom).map_add

/-- Ordinary Kähler one-forms on the actual framed chart. -/
def chartForms {A : Type} [CommRing A] [Algebra k A]
    (j : Spec (CommRingCat.of A) ⟶ line k) [IsOpenImmersion j]
    (hj : j ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (U : Framed (structureMap k)) (hU : U.1 = j ''ᵁ ⊤) :
    (oneForms (structureMap k)).obj.obj (op U.1) ≃+ Ω[A⁄k] := by
  rcases U with ⟨O,hO⟩
  change O = j ''ᵁ ⊤ at hU
  subst O
  let V : Framed (structureMap k) := ⟨j ''ᵁ ⊤,hO⟩
  let X := line k
  letI : Algebra k Γ(X, j ''ᵁ ⊤) := (sectionCoefficients (structureMap k) (j ''ᵁ ⊤)).toAlgebra
  let φ := sectionEquiv (structureMap k) j hj
  let u : (oneForms (structureMap k)).obj.obj (op (j ''ᵁ ⊤)) ≃+ Ω[Γ(X,j ''ᵁ ⊤)⁄k] :=
    ((onBasisIso (structureMap k)).app (op V)).addCommGroupIsoToAddEquiv
  exact u.trans (pullEquiv k φ)

theorem chartForms_apply {A : Type} [CommRing A] [Algebra k A]
    (j : Spec (CommRingCat.of A) ⟶ line k) [IsOpenImmersion j]
    (hj : j ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hF : IsAffineOpen (j ''ᵁ ⊤) ∧ CycleQ2FiniteExactAffineAtlas.HasFrame (structureMap k) 1 (j ''ᵁ ⊤))
    (ω : (oneForms (structureMap k)).obj.obj (op (j ''ᵁ ⊤))) :
    letI : Algebra k Γ(line k, j ''ᵁ ⊤) := (sectionCoefficients (structureMap k) (j ''ᵁ ⊤)).toAlgebra
    chartForms k j hj ⟨j ''ᵁ ⊤,hF⟩ rfl ω =
      onePullback (sectionEquiv (structureMap k) j hj).toAlgHom
        ((onBasisIso (structureMap k)).hom.app (op ⟨j ''ᵁ ⊤,hF⟩) ω) :=
  rfl

end CycleQ2ProjectiveLineExactCharts

#print axioms CycleQ2ProjectiveLineExactCharts.overlap_framed
#print axioms CycleQ2ProjectiveLineExactCharts.chartForms

end

section

/-!
# The two original restriction maps of projective-line one-forms

The actual section-ring restrictions on the glued curve conjugate to
the two polynomial-to-Laurent maps. Their Kähler maps therefore
give the original maps on regular differential sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineFormRestrictions

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open Polynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure CycleQ2ProjectiveLineExactCharts
open CycleQ2LaurentKahlerResidue (zeroRingMap infinityRingMap)
open CycleQ2LaurentLogDerivative (L)
open CycleQ2RankOneDifferentialSheaf
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2AffineFrameBinding (sectionEquiv)
open CycleQ2ExactFrameThreeDeRham (onePullback)
open CycleQ2AffineDeRhamFunctorial (onePullback_comp)
open CycleQ2FiniteExactAffineAtlas (HasFrame)

variable (k : Type) [Field k]

local instance : SmoothOfRelativeDimension 1 (structureMap k) := smooth k

private abbrev F := oneForms (structureMap k)

private theorem chart_natural {A B : Type} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (a : Spec (CommRingCat.of A) ⟶ line k) (b : Spec (CommRingCat.of B) ⟶ line k)
    [IsOpenImmersion a] [IsOpenImmersion b]
    (ha : a ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k A)))
    (hb : b ≫ structureMap k = Spec.map (CommRingCat.ofHom (algebraMap k B)))
    (hA : IsAffineOpen (a ''ᵁ ⊤) ∧ HasFrame (structureMap k) 1 (a ''ᵁ ⊤))
    (hB : IsAffineOpen (b ''ᵁ ⊤) ∧ HasFrame (structureMap k) 1 (b ''ᵁ ⊤))
    (φ : A →ₐ[k] B) (hφ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ a = b)
    (h : b ''ᵁ ⊤ ≤ a ''ᵁ ⊤)
    (ω : (F k).obj.obj (op (a ''ᵁ ⊤))) :
    chartForms k b hb ⟨b ''ᵁ ⊤,hB⟩ rfl ((F k).obj.map (homOfLE h).op ω) =
      onePullback φ (chartForms k a ha ⟨a ''ᵁ ⊤,hA⟩ rfl ω) := by
  let P : Framed (structureMap k) := ⟨a ''ᵁ ⊤,hA⟩
  let Q : Framed (structureMap k) := ⟨b ''ᵁ ⊤,hB⟩
  let e := (onBasisIso (structureMap k)).hom
  let I : Q ⟶ P := homOfLE h
  letI : Algebra k Γ(line k,a ''ᵁ ⊤) := (sectionCoefficients (structureMap k) (a ''ᵁ ⊤)).toAlgebra
  letI : Algebra k Γ(line k,b ''ᵁ ⊤) := (sectionCoefficients (structureMap k) (b ''ᵁ ⊤)).toAlgebra
  rw [chartForms_apply, chartForms_apply]
  have eRes := NatTrans.naturality_apply e I.op ω
  change e.app (op Q) ((F k).obj.map (homOfLE h).op ω) =
    onePullback (restrict (structureMap k) h) (e.app (op P) ω) at eRes
  rw [eRes, ← onePullback_comp, CycleQ2NativeChartRestriction.sections_restrict
    (structureMap k) a b ha hb φ hφ h, onePullback_comp]

abbrev atZero :=
  chartForms k (chartZero k) (chartZero_over k) (zeroFramed k) rfl

abbrev atInfinity :=
  chartForms k (chartInfinity k) (chartInfinity_over k) (infinityFramed k) rfl

abbrev atTorus :=
  chartForms k (chartTorus k) (chartTorus_over k) (torusFramed k) rfl

abbrev torusInZero : (torusFramed k).1 ≤ (zeroFramed k).1 :=
  (overlap_framed k).le.trans inf_le_left

abbrev torusInInfinity : (torusFramed k).1 ≤ (infinityFramed k).1 :=
  (overlap_framed k).le.trans inf_le_right

theorem restriction_zero (a : (F k).obj.obj (op (zeroFramed k).1)) :
    atTorus k ((F k).obj.map (homOfLE (torusInZero k)).op a) =
      onePullback (zeroRingMap k) (atZero k a) :=
  chart_natural k (chartZero k) (chartTorus k) (chartZero_over k) (chartTorus_over k)
    (zeroFramed k).2 (torusFramed k).2 (zeroRingMap k) (torus_zero k) (torusInZero k) a

private theorem infinity_spec :
    Spec.map (CommRingCat.ofHom (infinityRingMap k).toRingHom) = infinityMap k := by
  rw [infinityMap, inversion, zeroMap, ← Spec.map_comp]
  rfl

theorem restriction_infinity (a : (F k).obj.obj (op (infinityFramed k).1)) :
    atTorus k ((F k).obj.map (homOfLE (torusInInfinity k)).op a) =
      onePullback (infinityRingMap k) (atInfinity k a) :=
  chart_natural k (chartInfinity k) (chartTorus k) (chartInfinity_over k) (chartTorus_over k)
    (infinityFramed k).2 (torusFramed k).2 (infinityRingMap k)
    (by rw [infinity_spec, torus_infinity]) (torusInInfinity k) a

end CycleQ2ProjectiveLineFormRestrictions

#print axioms CycleQ2ProjectiveLineFormRestrictions.restriction_zero
#print axioms CycleQ2ProjectiveLineFormRestrictions.restriction_infinity

end

section

/-!
# The residue class in actual H¹ of projective-line differentials

The connecting map from the Laurent overlap has exactly the kernel
of constant Laurent coefficient. In particular the normalized class
of dT/T is nonzero in derived sheaf cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineCohomologyResidue

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Module KaehlerDifferential LaurentPolynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2ProjectiveLineExactCharts CycleQ2ProjectiveLineFormRestrictions
open CycleQ2LaurentLogDerivative CycleQ2LaurentCurveResidue CycleQ2LaurentKahlerResidue
open CycleQ2RankOneDifferentialSheaf
open CycleQ2ClosedSupportCohomology

variable (k : Type) [Field k]

local instance : SmoothOfRelativeDimension 1 (structureMap k) := smooth k

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology (line k)) AddCommGrpCat.{0}) :=
  HasExt.standard _

private abbrev F := oneForms (structureMap k)

def square := coverSquare (zeroFramed k).1 (infinityFramed k).1 (torusFramed k).1
  (overlap_framed k) (cover_framed k)

/-- The actual connecting map from Kähler forms on the overlap. -/
def boundary : Ω[L k⁄k] →+ (F k).H' 1 ⊤ :=
  (sectionBoundary (F k) (square k)).comp (atTorus k).symm.toAddMonoidHom

theorem boundary_zero_iff (ω : Ω[L k⁄k]) :
    boundary k ω = 0 ↔ differentialResidue k ω = 0 := by
  change sectionBoundary (F k) (square k) ((atTorus k).symm ω) = 0 ↔ _
  rw [sectionBoundary_zero_iff]
  change (∃ (a : (F k).obj.obj (op (zeroFramed k).1))
      (b : (F k).obj.obj (op (infinityFramed k).1)),
    (F k).obj.map (homOfLE (torusInZero k)).op a -
    (F k).obj.map (homOfLE (torusInInfinity k)).op b = (atTorus k).symm ω) ↔ _
  constructor
  · rintro ⟨a,b,h⟩
    have h' := congrArg (atTorus k) h
    rw [map_sub, restriction_zero, restriction_infinity, AddEquiv.apply_symm_apply] at h'
    rw [← h',map_sub,differentialResidue_zero_chart,differentialResidue_infinity_chart,sub_zero]
  · intro h
    change residue k (logCoordinates k ω) = 0 at h
    obtain ⟨a,b,hab⟩ := (residue_zero_iff_boundary k _).mp h
    refine ⟨(atZero k).symm ((polynomialEquiv k).symm a),
      -(atInfinity k).symm ((polynomialEquiv k).symm b), ?_⟩
    apply (atTorus k).injective
    apply (logCoordinates k).injective
    rw [map_sub, restriction_zero, restriction_infinity, map_neg, AddEquiv.apply_symm_apply,
      AddEquiv.apply_symm_apply, map_neg, sub_neg_eq_add, map_add, chartZero_value,
      chartInfinity_value, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
    simpa only [AddEquiv.apply_symm_apply] using hab.symm

theorem logForm_residue : differentialResidue k (logForm k) = 1 := by
  have hc : logCoordinates k (logForm k) = 1 := by
    rw [logForm, map_smul, logCoordinates_D, logDerivative_T,
      Int.cast_one, map_one, one_mul, smul_eq_mul, ← T_add]
    rfl
  change residue k (logCoordinates k (logForm k)) = 1
  rw [hc]
  have e : (1 : L k) = AddMonoidAlgebra.single (0 : ℤ) (1 : k) := rfl
  rw [e]
  change (Finsupp.single (0 : ℤ) (1 : k)) 0 = 1
  exact Finsupp.single_eq_same

theorem boundary_logForm_ne_zero : boundary k (logForm k) ≠ 0 := by
  rw [ne_eq,boundary_zero_iff,logForm_residue]
  exact one_ne_zero

theorem boundary_exact (x : L k) : boundary k (D k (L k) x) = 0 :=
  (boundary_zero_iff k _).2 (differentialResidue_exact k x)

end CycleQ2ProjectiveLineCohomologyResidue

#print axioms CycleQ2ProjectiveLineCohomologyResidue.boundary_zero_iff
#print axioms CycleQ2ProjectiveLineCohomologyResidue.boundary_logForm_ne_zero
#print axioms CycleQ2ProjectiveLineCohomologyResidue.boundary_exact

end

section

/-!
# The actual one-form sheaf is acyclic on an exact affine curve chart

Every affine subopen inherits the exact one-coordinate frame. The
coefficient isomorphisms on that dense subsite therefore extend to an
isomorphism with the structure sheaf on all subopens of the chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RankOneDenseOver

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2RankOneDifferentialSheaf
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2FramedAffineCoordinates (coefficients_natural)
open CycleQ2ExactFrameThreeDeRham (onePullback onePullback_d)
open CycleQ2GeometricProjectiveHOne
open CycleQ2GeometricAffineChartSections (chartOpensEquiv)

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
variable [SmoothOfRelativeDimension 1 f]

private abbrev J := Opens.grothendieckTopology X

def target (U : X.Opens) (W : {V : Framed f // V.1 ≤ U}) : Over U :=
  Over.mk (homOfLE W.2)

abbrev Dense (U : X.Opens) := InducedCategory (Over U) (target f U)

abbrev inc (U : X.Opens) : Dense f U ⥤ Over U := inducedFunctor (target f U)

instance (U : X.Opens) : (inc f U).IsCoverDense (J.over U) := by
  constructor
  intro V
  rw [GrothendieckTopology.mem_over_iff]
  intro x hx
  obtain ⟨W,hW,hxW,hWV⟩ := Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis f 1) hx
  let P : Dense f U := ⟨⟨W,hW⟩, hWV.trans V.hom.le⟩
  let i : (inc f U).obj P ⟶ V := Over.homMk (homOfLE hWV)
  refine ⟨W,homOfLE hWV, ?_, hxW⟩
  rw [Sieve.overEquiv_iff]
  exact Presieve.in_coverByImage (inc f U) (Y := P) i


end CycleQ2RankOneDenseOver

end

section

/-!
# The actual one-form sheaf is acyclic on an exact affine curve chart

Every affine subopen inherits the exact one-coordinate frame. The
coefficient isomorphisms on that dense subsite therefore extend to an
isomorphism with the structure sheaf on all subopens of the chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RankOneFrameAcyclic

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module KaehlerDifferential
open CycleQ2RankOneDifferentialSheaf CycleQ2RankOneDenseOver
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict exact_on_affine_subopen)
open CycleQ2FramedAffineSite (restrict_comp)
open CycleQ2FramedAffineCoordinates (coefficients_natural)
open CycleQ2ExactFrameThreeDeRham (onePullback onePullback_d)
open CycleQ2GeometricProjectiveHOne

variable {k : Type} [Field k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
variable [SmoothOfRelativeDimension 1 f]

private abbrev J := Opens.grothendieckTopology X

private def basisAt (U : Framed f) (W : Dense f U.1) :
    letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
    Basis (Fin 1) Γ(X,W.1.1) Ω[Γ(X,W.1.1)⁄k] :=
  (exact_on_affine_subopen f W.2 U.2.1 W.1.2.1 U.2.2.choose
    U.2.2.choose_spec.choose U.2.2.choose_spec.choose_spec).choose

private theorem basisAt_apply (U : Framed f) (W : Dense f U.1) (i : Fin 1) :
    letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
    basisAt f U W i = D k Γ(X,W.1.1) (restrict f W.2 (U.2.2.choose i)) :=
  (exact_on_affine_subopen f W.2 U.2.1 W.1.2.1 U.2.2.choose
    U.2.2.choose_spec.choose U.2.2.choose_spec.choose_spec).choose_spec i

private theorem basisAt_naturality (U : Framed f) {W V : Dense f U.1} (a : V ⟶ W) (i : Fin 1) :
    letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
    letI : Algebra k Γ(X,V.1.1) := (sectionCoefficients f V.1.1).toAlgebra
    onePullback (restrict f (show V.1.1 ≤ W.1.1 from a.hom.left.le)) (basisAt f U W i) = basisAt f U V i := by
  letI : Algebra k Γ(X,U.1) := (sectionCoefficients f U.1).toAlgebra
  letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
  letI : Algebra k Γ(X,V.1.1) := (sectionCoefficients f V.1.1).toAlgebra
  rw [basisAt_apply, basisAt_apply, onePullback_d]
  exact congrArg (D k Γ(X,V.1.1))
    ((DFunLike.congr_fun (restrict_comp f W.2 (show V.1.1 ≤ W.1.1 from a.hom.left.le)) (U.2.2.choose i)).symm)

private def coordinates (U : Framed f) (W : Dense f U.1) :
    (oneForms f).obj.obj (op W.1.1) ≃+ Γ(X,W.1.1) :=
  letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
  (((onBasisIso f).app (op W.1)).addCommGroupIsoToAddEquiv.trans
    (basisAt f U W).equivFun.toAddEquiv).trans (AddEquiv.funUnique (Fin 1) Γ(X,W.1.1))

private theorem coordinates_naturality (U : Framed f) {W V : Dense f U.1} (a : V ⟶ W)
    (ω : (oneForms f).obj.obj (op W.1.1)) :
    coordinates f U V ((oneForms f).obj.map (homOfLE (show V.1.1 ≤ W.1.1 from a.hom.left.le)).op ω) =
      (restrict f (show V.1.1 ≤ W.1.1 from a.hom.left.le)) (coordinates f U W ω) := by
  letI : Algebra k Γ(X,W.1.1) := (sectionCoefficients f W.1.1).toAlgebra
  letI : Algebra k Γ(X,V.1.1) := (sectionCoefficients f V.1.1).toAlgebra
  let j : V.1 ⟶ W.1 := homOfLE (show V.1.1 ≤ W.1.1 from a.hom.left.le)
  let e := (onBasisIso f).hom
  change (basisAt f U V).equivFun (e.app (op V.1)
      ((oneForms f).obj.map (homOfLE (show V.1.1 ≤ W.1.1 from a.hom.left.le)).op ω)) 0 =
    (restrict f (show V.1.1 ≤ W.1.1 from a.hom.left.le)) ((basisAt f U W).equivFun (e.app (op W.1) ω) 0)
  have hr := NatTrans.naturality_apply e j.op ω
  change e.app (op V.1) ((oneForms f).obj.map (homOfLE (show V.1.1 ≤ W.1.1 from a.hom.left.le)).op ω) =
    onePullback (restrict f (show V.1.1 ≤ W.1.1 from a.hom.left.le)) (e.app (op W.1) ω) at hr
  rw [hr]
  exact coefficients_natural _ _ _ _ (basisAt_naturality f U a) _ _

/-- On the whole chart, the actual differential sheaf is the free
rank-one additive structure sheaf. -/
def frameOver (U : Framed f) : (oneForms f).over U.1 ≅ (functions (X := X)).over U.1 := by
  apply Functor.IsCoverDense.sheafIso (G := inc f U.1) (K := J.over U.1)
  refine NatIso.ofComponents (fun W => (coordinates f U W.unop).toAddCommGrpIso) ?_
  intro W V j
  ext ω
  exact coordinates_naturality f U j.unop ω

local instance : HasExt.{1} (Sheaf (J (X := X)) AddCommGrpCat.{0}) := HasExt.standard _

theorem affine_HOne_subsingleton (U : Framed f) :
    Subsingleton ((oneForms f).H' 1 U.1) :=
  affineFrameHOne_subsingleton U.2.1.isoSpec (oneForms f) (frameOver f U)

end CycleQ2RankOneFrameAcyclic

#print axioms CycleQ2RankOneFrameAcyclic.frameOver
#print axioms CycleQ2RankOneFrameAcyclic.affine_HOne_subsingleton

end

section

/-!
# The structure sheaf of the actual projective line is acyclic

In the native two-chart cover, a Laurent function is the sum of an
ordinary polynomial and a polynomial in the inverse coordinate.
This kills the genuine Mayer–Vietoris boundary. Higher cohomology
vanishes by affine structure-sheaf acyclicity on the same opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineFunctions

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open scoped Polynomial
open LaurentPolynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2ProjectiveLineExactCharts CycleQ2ProjectiveLineFormRestrictions
open CycleQ2LaurentLogDerivative (L)
open CycleQ2LaurentKahlerResidue (zeroRingMap infinityRingMap)
open CycleQ2RankOneDifferentialSheaf (functions)
open CycleQ2ClosedSupportCohomology
open CycleQ2GeometricConeCech.HZero (sectionsEquiv)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf affineFrameHOne_subsingleton affineFrameHTwo_subsingleton)
open CycleQ2AffineFrameBinding (sectionEquiv)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ProjectiveLineCohomologyResidue (square)

variable (k : Type) [Field k]

local instance : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology (line k)) AddCommGrpCat.{0}) := HasExt.standard _

abbrev O := functions (X := line k)

private theorem polynomial_X (a : k) (n : ℕ) :
    zeroRingMap k (Polynomial.monomial n a) = C a * T (n : ℤ) :=
  Polynomial.toLaurent_C_mul_T n a

private theorem inverse_polynomial_X (a : k) (n : ℕ) :
    infinityRingMap k (Polynomial.monomial n a) = C a * T (-(n : ℤ)) := by
  change invert (Polynomial.toLaurent (Polynomial.monomial n a)) = _
  rw [Polynomial.toLaurent_C_mul_T, map_mul, invert_C, invert_T]

theorem laurent_decompose (z : L k) :
    ∃ a b : k[X], z = zeroRingMap k a - infinityRingMap k b := by
  induction z using LaurentPolynomial.induction_on' with
  | add z w hz hw =>
    obtain ⟨a,b,hab⟩ := hz
    obtain ⟨c,d,hcd⟩ := hw
    exact ⟨a+c,b+d, by rw [hab,hcd,map_add,map_add]; abel⟩
  | C_mul_T n a =>
    by_cases hn : 0 ≤ n
    · refine ⟨Polynomial.monomial n.toNat a,0,?_⟩
      rw [map_zero,sub_zero,polynomial_X,Int.toNat_of_nonneg hn]
    · refine ⟨0,-Polynomial.monomial (-n).toNat a,?_⟩
      rw [map_zero,map_neg,sub_neg_eq_add,zero_add,inverse_polynomial_X,
        Int.toNat_of_nonneg (by omega), neg_neg]

def zeroSections : Γ(line k,(zeroFramed k).1) ≃+* k[X] :=
  letI : Algebra k Γ(line k, (chartZero k) ''ᵁ ⊤) :=
    (sectionCoefficients (structureMap k) ((chartZero k) ''ᵁ ⊤)).toAlgebra
  (sectionEquiv (structureMap k) (chartZero k) (chartZero_over k)).toRingEquiv

def infinitySections : Γ(line k,(infinityFramed k).1) ≃+* k[X] :=
  letI : Algebra k Γ(line k, (chartInfinity k) ''ᵁ ⊤) :=
    (sectionCoefficients (structureMap k) ((chartInfinity k) ''ᵁ ⊤)).toAlgebra
  (sectionEquiv (structureMap k) (chartInfinity k) (chartInfinity_over k)).toRingEquiv

def torusSections : Γ(line k,(torusFramed k).1) ≃+* L k :=
  letI : Algebra k Γ(line k, (chartTorus k) ''ᵁ ⊤) :=
    (sectionCoefficients (structureMap k) ((chartTorus k) ''ᵁ ⊤)).toAlgebra
  (sectionEquiv (structureMap k) (chartTorus k) (chartTorus_over k)).toRingEquiv

private theorem ring_zero (a : Γ(line k,(zeroFramed k).1)) :
    torusSections k ((O k).obj.map (homOfLE (torusInZero k)).op a) =
      zeroRingMap k (zeroSections k a) :=
  DFunLike.congr_fun (CycleQ2NativeChartRestriction.sections_restrict (structureMap k)
    (chartZero k) (chartTorus k) (chartZero_over k) (chartTorus_over k)
    (zeroRingMap k) (torus_zero k) (torusInZero k)) a

private theorem ring_infinity (a : Γ(line k,(infinityFramed k).1)) :
    torusSections k ((O k).obj.map (homOfLE (torusInInfinity k)).op a) =
      infinityRingMap k (infinitySections k a) := by
  have h : Spec.map (CommRingCat.ofHom (infinityRingMap k).toRingHom) ≫ chartInfinity k =
      chartTorus k := by
    rw [← torus_infinity]
    congr 1
    rw [infinityMap,inversion,zeroMap,← Spec.map_comp]
    rfl
  exact DFunLike.congr_fun (CycleQ2NativeChartRestriction.sections_restrict (structureMap k)
    (chartInfinity k) (chartTorus k) (chartInfinity_over k) (chartTorus_over k)
    (infinityRingMap k) h (torusInInfinity k)) a

theorem sectionBoundary_eq_zero (z : (O k).obj.obj (op (torusFramed k).1)) :
    sectionBoundary (O k) (square k) z = 0 := by
  obtain ⟨a,b,hab⟩ := laurent_decompose k (torusSections k z)
  apply (sectionBoundary_zero_iff (O k) (square k) z).2
  refine ⟨(zeroSections k).symm a,(infinitySections k).symm b,?_⟩
  apply (torusSections k).injective
  change torusSections k (((O k).obj.map (homOfLE (torusInZero k)).op ((zeroSections k).symm a)) -
    ((O k).obj.map (homOfLE (torusInInfinity k)).op ((infinitySections k).symm b))) = torusSections k z
  rw [map_sub,ring_zero,ring_infinity,RingEquiv.apply_symm_apply,RingEquiv.apply_symm_apply]
  exact hab.symm

/-- If degree-one cohomology vanishes on the two patches, every
degree-one global class is the connecting class of a section. -/
theorem boundary_surjective {Y : TopCat.{0}}
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})]
    (F : Y.Sheaf AddCommGrpCat.{0}) (S : (Opens.grothendieckTopology Y).MayerVietorisSquare)
    [Subsingleton (F.H' 1 S.X₂)] [Subsingleton (F.H' 1 S.X₃)] :
    Function.Surjective (sectionBoundary F S) := by
  intro x
  have hz : S.toBiprod F 1 x = 0 := by
    apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    exact Subsingleton.elim _ _
  obtain ⟨z,hz⟩ := (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F 0 1 rfl).exact 2) x hz
  refine ⟨sectionsEquiv F S.X₁ z,?_⟩
  change S.δ F 0 1 rfl ((sectionsEquiv F S.X₁).symm (sectionsEquiv F S.X₁ z)) = x
  rw [AddEquiv.symm_apply_apply]
  exact hz

private theorem affine_HOne {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})] :
    Subsingleton ((structureAdditiveSheaf Y).H' 1 U) :=
  affineFrameHOne_subsingleton hU.isoSpec (structureAdditiveSheaf Y) (Iso.refl _)

private theorem affine_HTwo {Y : Scheme.{0}} {U : Y.Opens} (hU : IsAffineOpen U)
    [HasExt.{1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0})] :
    Subsingleton ((structureAdditiveSheaf Y).H' 2 U) :=
  affineFrameHTwo_subsingleton hU.isoSpec (structureAdditiveSheaf Y) (Iso.refl _)
    (CycleQ2GeometricAffineHTwo.affine_H_two_subsingleton Γ(Y,U))

theorem functions_HOne : Subsingleton ((O k).H' 1 ⊤) := by
  let S := square k
  letI : Subsingleton ((O k).H' 1 S.X₂) := affine_HOne (zeroFramed k).2.1
  letI : Subsingleton ((O k).H' 1 S.X₃) := affine_HOne (infinityFramed k).2.1
  have hb := boundary_surjective (O k) S
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z,rfl⟩ := hb x
  exact sectionBoundary_eq_zero k z

theorem functions_HTwo : Subsingleton ((O k).H' 2 ⊤) := by
  let S := square k
  let F := O k
  letI : Subsingleton (F.H' 1 S.X₁) := affine_HOne (torusFramed k).2.1
  letI : Subsingleton (F.H' 2 S.X₂) := affine_HTwo (zeroFramed k).2.1
  letI : Subsingleton (F.H' 2 S.X₃) := affine_HTwo (infinityFramed k).2.1
  apply subsingleton_of_forall_eq 0
  intro x
  have hz : S.toBiprod F 2 x = 0 := by
    apply (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective
    exact Subsingleton.elim _ _
  obtain ⟨y,hy⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F 1 2 rfl).exact 2) x hz
  change F.H' 1 S.X₁ at y
  have e : y = 0 := Subsingleton.elim _ _
  rw [e,map_zero] at hy
  exact hy.symm

end CycleQ2ProjectiveLineFunctions

#print axioms CycleQ2ProjectiveLineFunctions.functions_HOne
#print axioms CycleQ2ProjectiveLineFunctions.functions_HTwo

end

section

/-!
# Degree-two hypercohomology of an actual two-term complex

If first and second cohomology of the function term vanish, then first
cohomology of the one-form term is precisely degree-two cohomology of
the two-term complex. This is the actual map of the shifted mapping
cone, with the standard triangle signs.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2TwoTermTopComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Abelian C] [HasExt.{1} C] [HasDerivedCategory.{1} C]

variable {A B : C} (d : A ⟶ B)

private abbrev C₀ := CochainComplex.singleFunctor C 0

private abbrev baseTriangle :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle ((C₀ (C := C)).map d))

abbrev shiftedTriangle :=
  (Triangle.shiftFunctor (DerivedCategory C) (1 : ℤ)).obj (baseTriangle d)

variable (X : C)

private abbrev E := DerivedCategory.singleFunctor C 0

abbrev topGroup := (E.obj X ⟶ (shiftedTriangle d).obj₃)

private theorem distinguished : shiftedTriangle d ∈ distTriang (DerivedCategory C) :=
  Triangle.shift_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _

/-- The actual map from first cohomology of the second term into the shifted cone. -/
def topMap : Ext X B 1 →+ topGroup d X where
  toFun x := x.hom ≫ (shiftedTriangle d).mor₂
  map_zero' := by simp
  map_add' x y := by rw [Ext.add_hom, Preadditive.add_comp]

variable (h₁ : Subsingleton (Ext.{1} X A 1)) (h₂ : Subsingleton (Ext.{1} X A 2))

include h₁ in
theorem topMap_injective : Function.Injective (topMap d X) := by
  apply (injective_iff_map_eq_zero _).2
  intro x hx
  change x.hom ≫ (shiftedTriangle d).mor₂ = 0 at hx
  obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₂ _ (distinguished d) x.hom hx
  haveI : Subsingleton (E.obj X ⟶ (shiftedTriangle d).obj₁) :=
    Function.Injective.subsingleton
      (Ext.homEquiv (X := X) (Y := A) (n := 1)).symm.injective
  have hz : g = 0 := Subsingleton.elim _ _
  apply Ext.homEquiv.injective
  change x.hom = (0 : Ext X B 1).hom
  rw [hg,hz,zero_comp]
  exact (Ext.zero_hom (X := X) (Y := B) (n := 1)).symm

include h₂ in
theorem topMap_surjective : Function.Surjective (topMap d X) := by
  intro x
  let T := shiftedTriangle d
  let e := ((shiftFunctorAdd' (DerivedCategory C) (1 : ℤ) 1 2 (by decide)).app (E.obj A))
  haveI : Subsingleton (E.obj X ⟶ (E.obj A)⟦(2 : ℤ)⟧) :=
    Function.Injective.subsingleton
      (Ext.homEquiv (X := X) (Y := A) (n := 2)).symm.injective
  have hz : x ≫ T.mor₃ = 0 := by
    apply (cancel_mono e.inv).mp
    exact Subsingleton.elim _ _
  obtain ⟨y,hy⟩ := Triangle.coyoneda_exact₃ T (distinguished d) x hz
  refine ⟨Ext.homEquiv.symm y,?_⟩
  change Ext.homEquiv (Ext.homEquiv.symm y) ≫ T.mor₂ = x
  rw [Equiv.apply_symm_apply]
  exact hy.symm

/-- Under the two vanishings this is the canonical upper-term comparison. -/
def topEquiv : Ext X B 1 ≃+ topGroup d X :=
  AddEquiv.ofBijective (topMap d X) ⟨topMap_injective d X h₁, topMap_surjective d X h₂⟩

end CycleQ2TwoTermTopComparison

#print axioms CycleQ2TwoTermTopComparison.topMap_injective
#print axioms CycleQ2TwoTermTopComparison.topMap_surjective

end

section

/-!
# The normalized Laurent class in actual degree-two de Rham cohomology

The ordinary two-term complex of native functions and Kähler forms
has no contribution from the first and second structure-sheaf
cohomology groups. The Laurent connecting map therefore retains its
exact residue kernel in degree-two derived de Rham cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineDeRhamTrace

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Module KaehlerDifferential LaurentPolynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2LaurentLogDerivative CycleQ2LaurentKahlerResidue
open CycleQ2RankOneDifferentialSheaf
open CycleQ2ProjectiveLineCohomologyResidue (boundary boundary_zero_iff logForm_residue square)
open CycleQ2ProjectiveLineFunctions (functions_HOne functions_HTwo boundary_surjective)
open CycleQ2ProjectiveLineExactCharts (zeroFramed infinityFramed torusFramed)
open CycleQ2ProjectiveLineFormRestrictions (atTorus)
open CycleQ2ClosedSupportCohomology (sectionBoundary)
open CycleQ2RankOneFrameAcyclic (affine_HOne_subsingleton)
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2TwoTermTopComparison (topGroup topEquiv)

variable (k : Type) [Field k]

private abbrev Sheaves := AbSheaf (show TopCat from line k)
local instance : HasExt.{1} (Sheaves k) := HasExt.standard _
local instance : HasDerivedCategory.{1} (Sheaves k) := HasDerivedCategory.standard _
local instance : SmoothOfRelativeDimension 1 (structureMap k) := smooth k

abbrev TopDeRham := topGroup (C := Sheaves k)
  (derivative (structureMap k)) (freeOpen (⊤ : (line k).Opens))

/-- The genuine upper-term inclusion, which is an isomorphism here. -/
def coherentComparison : (oneForms (structureMap k)).H' 1 ⊤ ≃+ TopDeRham k :=
  topEquiv (C := Sheaves k) (derivative (structureMap k)) (freeOpen (⊤ : (line k).Opens))
    (functions_HOne k) (functions_HTwo k)

/-- The actual derived class of a regular Laurent differential on the overlap. -/
def derivedBoundary : Ω[L k⁄k] →+ TopDeRham k :=
  (coherentComparison k).toAddMonoidHom.comp (boundary k)

theorem derivedBoundary_zero_iff (ω : Ω[L k⁄k]) :
    derivedBoundary k ω = 0 ↔ differentialResidue k ω = 0 := by
  change coherentComparison k (boundary k ω) = 0 ↔ _
  rw [← map_zero (coherentComparison k), (coherentComparison k).injective.eq_iff,
    boundary_zero_iff]

theorem derivedLogForm_ne_zero : derivedBoundary k (logForm k) ≠ 0 := by
  rw [ne_eq,derivedBoundary_zero_iff,logForm_residue]
  exact one_ne_zero

/-- A normalized multiple of the original logarithmic differential. -/
def constantLog : k →+ Ω[L k⁄k] where
  toFun c := c • logForm k
  map_zero' := zero_smul k _
  map_add' a b := add_smul a b _

theorem constantLog_residue (c : k) : differentialResidue k (constantLog k c) = c := by
  change differentialResidue k (c • logForm k) = c
  rw [map_smul,logForm_residue,smul_eq_mul,mul_one]

/-- The normalized scalar class in actual H² of the de Rham complex. -/
def fromScalar : k →+ TopDeRham k := (derivedBoundary k).comp (constantLog k)

theorem fromScalar_injective : Function.Injective (fromScalar k) :=
  (injective_iff_map_eq_zero _).2 (fun c h => by
    change derivedBoundary k (constantLog k c) = 0 at h
    rw [derivedBoundary_zero_iff,constantLog_residue] at h
    exact h)

theorem derivedBoundary_eq_scalar (ω : Ω[L k⁄k]) :
    derivedBoundary k ω = fromScalar k (differentialResidue k ω) := by
  change derivedBoundary k ω = derivedBoundary k (constantLog k (differentialResidue k ω))
  rw [← sub_eq_zero,← map_sub,derivedBoundary_zero_iff,map_sub,constantLog_residue,sub_self]

theorem derivedBoundary_surjective : Function.Surjective (derivedBoundary k) := by
  let F := oneForms (structureMap k)
  let I := square k
  letI : Subsingleton (F.H' 1 I.X₂) := affine_HOne_subsingleton (structureMap k) (zeroFramed k)
  letI : Subsingleton (F.H' 1 I.X₃) := affine_HOne_subsingleton (structureMap k) (infinityFramed k)
  intro x
  obtain ⟨h,rfl⟩ := (coherentComparison k).surjective x
  obtain ⟨z,rfl⟩ := boundary_surjective F I h
  refine ⟨atTorus k z,?_⟩
  change coherentComparison k (sectionBoundary F I ((atTorus k).symm (atTorus k z))) = _
  rw [AddEquiv.symm_apply_apply]

theorem fromScalar_surjective : Function.Surjective (fromScalar k) := by
  intro x
  obtain ⟨ω,rfl⟩ := derivedBoundary_surjective k x
  exact ⟨differentialResidue k ω,(derivedBoundary_eq_scalar k ω).symm⟩

/-- The normalized trace on the full actual degree-two de Rham group. -/
def trace : TopDeRham k ≃+ k :=
  (AddEquiv.ofBijective (fromScalar k) ⟨fromScalar_injective k,fromScalar_surjective k⟩).symm

theorem trace_derivedBoundary (ω : Ω[L k⁄k]) :
    trace k (derivedBoundary k ω) = differentialResidue k ω := by
  rw [derivedBoundary_eq_scalar]
  exact (trace k).apply_symm_apply (differentialResidue k ω)

theorem trace_logForm : trace k (derivedBoundary k (logForm k)) = 1 := by
  rw [trace_derivedBoundary,logForm_residue]

end CycleQ2ProjectiveLineDeRhamTrace

#print axioms CycleQ2ProjectiveLineDeRhamTrace.coherentComparison
#print axioms CycleQ2ProjectiveLineDeRhamTrace.derivedLogForm_ne_zero
#print axioms CycleQ2ProjectiveLineDeRhamTrace.derivedBoundary_eq_scalar

#print axioms CycleQ2ProjectiveLineDeRhamTrace.trace_derivedBoundary

end

section

/-!
# Ordinary cotangent frames at the points of a normal affine curve

A normal finite-type curve over a characteristic-zero field is smooth.
The actual Kähler module at a closed point is free over its local
ring and has the same rank as the cotangent module of its fraction
field. Its residue field is finite separable over the original field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2NormalCurveLocalFrames

open Algebra KaehlerDifferential IsLocalRing

variable {k A K : Type} [Field k] [CharZero k] [CommRing A] [IsDedekindDomain A]
  [Algebra k A] [Algebra.FiniteType k A] [Field K]
  [Algebra k K] [Algebra A K] [IsScalarTower k A K] [IsFractionRing A K]

variable (q : Ideal A) [q.IsMaximal]

local instance : q.IsPrime := Ideal.IsMaximal.isPrime inferInstance

abbrev R := Localization.AtPrime q

/-- It suffices to normalize the rank once, at the generic function field. -/
def localFrame [Algebra (R q) K] [IsScalarTower A (R q) K] [IsScalarTower k (R q) K]
    (hrank : Module.finrank K Ω[K⁄k] = 1) : Ω[R q⁄k] ≃ₗ[R q] R q := by
  letI : Algebra.Smooth k A := CycleQ2NormalCurveSmooth.smooth_of_isDedekindDomain
  letI : Algebra.FormallySmooth A (R q) :=
    Algebra.FormallySmooth.of_isLocalization (Rₘ := R q) q.primeCompl
  letI : Algebra.FormallySmooth k (R q) := Algebra.FormallySmooth.comp k A (R q)
  letI : Algebra.EssFiniteType A (R q) := Algebra.EssFiniteType.of_isLocalization _ q.primeCompl
  letI : Algebra.EssFiniteType k (R q) := Algebra.EssFiniteType.comp _ A _
  letI : Module.Free (R q) Ω[R q⁄k] := Module.free_of_flat_of_isLocalRing
  letI : IsFractionRing (R q) K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl (R q) K
  letI : IsLocalizedModule (nonZeroDivisors (R q)) (KaehlerDifferential.map k k (R q) K) :=
    KaehlerDifferential.isLocalizedModule_map _ _ _ (nonZeroDivisors (R q))
  have he := Module.finrank_of_isLocalizedModule_of_free K
    (nonZeroDivisors (R q)) (KaehlerDifferential.map k k (R q) K)
  exact (Module.nonempty_linearEquiv_of_finrank_eq_one (he.symm.trans hrank)).some.symm

theorem residue_finite : Module.Finite k (ResidueField (R q)) := by
  letI := Ideal.Quotient.field q
  letI : Module.Finite k (A ⧸ q) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ q)
  letI : Module.Finite (A ⧸ q) q.ResidueField := Module.Finite.of_surjective
    (Algebra.linearMap (A ⧸ q) q.ResidueField) q.bijective_algebraMap_quotient_residueField.2
  exact Module.Finite.trans (R := k) (A ⧸ q) q.ResidueField

theorem residue_separable : Algebra.IsSeparable k (ResidueField (R q)) := by
  letI : Module.Finite k (ResidueField (R q)) := residue_finite q
  infer_instance

end CycleQ2NormalCurveLocalFrames

#print axioms CycleQ2NormalCurveLocalFrames.localFrame
#print axioms CycleQ2NormalCurveLocalFrames.residue_separable

end

section

/-!
# The finite trace sends regular affine curve differentials to regular forms

For a finite separable extension, use any finite Galois overfield
and its integral closure over the original affine ring. At a
closed point choose a point above it. All conjugate differentials
are regular there, so tame descent gives regularity of the original
finite trace at every closed point of the original chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2AffineFiniteCurveTrace

open Algebra IsLocalRing KaehlerDifferential Module
open CycleQ2AffineCurveRegularity CycleQ2ClosedValuationSquare
open CycleQ2FractionOneForms (fractionCoordinates mapRegular)
open CycleQ2NormalCurveLocalFrames (localFrame residue_separable)
open CycleQ2IntegralClosureConjugates (conjugateRing conjugate_regular)
open CycleQ2GaloisTraceRegularity (trace_subfield_regular)
open CycleQ2FiniteFieldOneFormTrace (traceOne)
open CycleQ2ExactFrameThreeDeRham (onePullback)

variable {k A B K L E : Type} [Field k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Field E] [Algebra k A] [Algebra.FiniteType k A]
  [Algebra k B] [Algebra k K] [Algebra k L] [Algebra k E]
  [Algebra A B] [Algebra A K] [Algebra A L] [Algebra A E]
  [Algebra B L] [Algebra K L] [Algebra K E] [Algebra L E]
  [IsScalarTower k A B] [IsScalarTower k A K] [IsScalarTower k A E] [IsScalarTower k B L]
  [IsScalarTower k K L] [IsScalarTower k K E] [IsScalarTower k L E]
  [IsScalarTower A B L] [IsScalarTower A L E] [IsScalarTower A K E] [IsScalarTower K L E]
  [Algebra.IsIntegral A B] [IsFractionRing A K] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [FiniteDimensional K E] [IsGalois K E]

private abbrev C := integralClosure A E
local instance : Algebra k (C (A := A) (E := E)) :=
  ((algebraMap A (C (A := A) (E := E))).comp (algebraMap k A)).toAlgebra
local instance : IsScalarTower k A (C (A := A) (E := E)) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance : IsScalarTower k (C (A := A) (E := E)) E :=
  IsScalarTower.of_algebraMap_eq (fun x => IsScalarTower.algebraMap_apply k A E x)

variable (c : Ω[A⁄k] ≃ₗ[A] A)

include c in
private theorem source_rank : Module.finrank K Ω[K⁄k] = 1 := by
  simpa only [Module.finrank_self] using (fractionCoordinates (K := K) c).finrank_eq

include c K in
private theorem closure_rank : Module.finrank E Ω[E⁄k] = 1 := by
  letI : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_isSeparable K E
  let b := (Basis.singleton (Fin 1) K).map (fractionCoordinates (K := K) c).symm
  let e := (b.baseChange E).map (tensorKaehlerEquivOfFormallyEtale k K E)
  rw [Module.finrank_eq_card_basis e,Fintype.card_fin]

include c E in
theorem trace_regular_of_normalExtension (hA : ¬IsField A) (ω : Ω[B⁄k]) :
    ∃ η : Ω[A⁄k], traceOne (K := K) (KaehlerDifferential.map k k B L ω) = mapRegular η := by
  let D := C (A := A) (E := E)
  letI : IsDedekindDomain D := integralClosure.isDedekindDomain A K E
  letI : Module.Finite A D := IsIntegralClosure.finite A K E D
  letI : Algebra.FiniteType k D := Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k A) inferInstance
  letI : IsFractionRing D E := IsIntegralClosure.isFractionRing_of_finite_extension A K E D
  letI : FiniteDimensional L E := FiniteDimensional.right K L E
  letI : Algebra.IsSeparable L E := Algebra.isSeparable_tower_top_of_isSeparable K L E
  apply (regular_at_closedPoints_iff c _).1
  intro p
  have hp : p.asIdeal ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField p.isMaximal hA
  have hinj : Function.Injective (algebraMap A D) := by
    intro a b h
    apply (IsFractionRing.injective A K)
    apply (algebraMap K E).injective
    have he := congrArg (algebraMap D E) h
    simpa only [← IsScalarTower.algebraMap_apply A D E,IsScalarTower.algebraMap_apply A K E]
      using he
  obtain ⟨q,hq,hpq⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := D) p.asIdeal
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  letI : q.IsMaximal := hq
  have hq₀ : q ≠ ⊥ := by
    intro h
    apply hp
    rw [← hpq,h,Ideal.comap_bot_of_injective _ hinj]
  let R := Localization.AtPrime p.asIdeal
  let S := Localization.AtPrime q
  letI : IsDiscreteValuationRing R :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hp R
  letI : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain D hq₀ S
  letI : Algebra R K := localFractionAlgebra K p.asIdeal
  letI : Algebra S E := localFractionAlgebra E q
  letI : IsFractionRing R K := localFractionField p.asIdeal
  letI : IsFractionRing S E := localFractionField q
  letI : IsScalarTower A R K := localFractionTower p.asIdeal
  letI : IsScalarTower D S E := localFractionTower q
  letI : IsScalarTower k R K := localFractionBaseTower p.asIdeal
  letI : IsScalarTower k S E := localFractionBaseTower q
  letI : Algebra.IsSeparable k (ResidueField R) := residue_separable p.asIdeal
  letI : Algebra.IsSeparable k (ResidueField S) := residue_separable q
  let r := localFrame p.asIdeal (source_rank (K := K) c)
  let s := localFrame q (closure_rank (K := K) (E := E) c)
  obtain ⟨π,hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨σ,hσ⟩ := IsDiscreteValuationRing.exists_irreducible S
  let i := IsScalarTower.toAlgHom k A D
  let j := IsScalarTower.toAlgHom k K E
  let f := localizationMap i p.asIdeal q hpq.symm
  letI : IsLocalHom f.toRingHom :=
    Localization.isLocalHom_localRingHom p.asIdeal q i.toRingHom hpq.symm
  have hsq (a : R) : algebraMap K E (algebraMap R K a) = algebraMap S E (f a) :=
    localization_square i p.asIdeal q hpq.symm j
      (fun t => (IsScalarTower.algebraMap_apply A K E t).symm.trans
        (IsScalarTower.algebraMap_apply A D E t)) a
  change ∃ a : Ω[R⁄k], _ = mapRegular a
  refine trace_subfield_regular f hsq r s hπ hσ _ ?_
  intro γ
  let β : Ω[D⁄k] := onePullback ((conjugateRing (A := A) (L := L) γ).restrictScalars k) ω
  refine ⟨KaehlerDifferential.map k k D S β,?_⟩
  have hγ := conjugate_regular (A := A) (L := L) γ ω
  change onePullback (γ.toAlgHom.restrictScalars k)
    (KaehlerDifferential.map k k L E (KaehlerDifferential.map k k B L ω)) =
    KaehlerDifferential.map k k D E β at hγ
  exact hγ.trans (localToRational_map q β).symm

end CycleQ2AffineFiniteCurveTrace

#print axioms CycleQ2AffineFiniteCurveTrace.trace_regular_of_normalExtension

end

section

/-!
# Regularity of trace for an arbitrary finite separable curve extension

The finite Galois comparison field is the actual normal closure in
an algebraic closure of the source field. No presentation or
unramified hypothesis is imposed on the affine finite map.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2TraceRegularFiniteExtension

open Algebra KaehlerDifferential IntermediateField
open CycleQ2AffineFiniteCurveTrace (trace_regular_of_normalExtension)
open CycleQ2FiniteFieldOneFormTrace (traceOne)
open CycleQ2FractionOneForms (mapRegular)

variable {k A B K L : Type} [Field k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Algebra k A] [Algebra.FiniteType k A]
  [Algebra k B] [Algebra k K] [Algebra k L]
  [Algebra A B] [Algebra A K] [Algebra A L]
  [Algebra B L] [Algebra K L]
  [IsScalarTower k A B] [IsScalarTower k A K] [IsScalarTower k B L]
  [IsScalarTower k K L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] [IsFractionRing A K] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

theorem trace_regular (c : Ω[A⁄k] ≃ₗ[A] A) (hA : ¬ IsField A) (ω : Ω[B⁄k]) :
    ∃ η : Ω[A⁄k], traceOne (K := K) (KaehlerDifferential.map k k B L ω) = mapRegular η := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  let F := AlgebraicClosure L
  letI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.trans K L F
  let E := normalClosure K L F
  letI : FiniteDimensional K E := normalClosure.is_finiteDimensional K L F
  letI : IsGalois K E := inferInstanceAs (IsGalois K (normalClosure K L F))
  letI : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq' (R := A) (S := K) (A := E) rfl
  letI : IsScalarTower A L E := IsScalarTower.to₁₃₄ A K L E
  letI : Algebra k E := ((algebraMap K E).comp (algebraMap k K)).toAlgebra
  letI : IsScalarTower k K E := IsScalarTower.of_algebraMap_eq' (R := k) (S := K) (A := E) rfl
  letI : IsScalarTower k L E := IsScalarTower.to₁₃₄ k K L E
  letI : IsScalarTower k A E := IsScalarTower.to₁₂₄ k A K E
  exact trace_regular_of_normalExtension (E := E) c hA ω

end CycleQ2TraceRegularFiniteExtension

#print axioms CycleQ2TraceRegularFiniteExtension.trace_regular

end

section

/-!
# The regular finite cochain trace on affine curve charts

Both terms of the trace are uniquely determined by their actual
function-field images. They commute with the ordinary derivative
and the composite of pullback and trace is the degree on forms.
These comparison identities are independent of affine presentations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/


noncomputable section

namespace CycleQ2RegularCurveCochainTrace

open Algebra KaehlerDifferential
open CycleQ2FiniteFieldOneFormTrace (traceOne)
open CycleQ2DifferentialTraceEmbeddings (traceOne_D traceOne_pullback_degree)
open CycleQ2CotangentLocalizationTower (map_tower)
open CycleQ2FractionOneForms (fractionCoordinates regular_coordinates mapRegular)

variable {k A B K L : Type} [Field k] [CharZero k]
  [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B]
  [Field K] [Field L] [Algebra k A] [Algebra.FiniteType k A]
  [Algebra k B] [Algebra k K] [Algebra k L]
  [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
  [IsScalarTower k A B] [IsScalarTower k A K] [IsScalarTower k B L]
  [IsScalarTower k K L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] [IsFractionRing A K] [IsFractionRing B L]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

variable (c : Ω[A⁄k] ≃ₗ[A] A) (hA : ¬IsField A)

include c in
theorem regularMap_injective : Function.Injective (mapRegular (k := k) (A := A) (K := K)) := by
  intro a b h
  have he := congrArg (fractionCoordinates c) h
  rw [regular_coordinates,regular_coordinates] at he
  exact c.injective ((IsFractionRing.injective A K) he)

private def rationalTrace : Ω[B⁄k] →ₗ[A] Ω[K⁄k] :=
  ((traceOne (K := K) (L := L)).restrictScalars A).comp
    ((KaehlerDifferential.map k k B L).restrictScalars A)

private def traceToRange : Ω[B⁄k] →ₗ[A] LinearMap.range (mapRegular (k := k) (A := A) (K := K)) :=
  (rationalTrace (K := K) (L := L)).codRestrict _ fun ω => by
    obtain ⟨η,hη⟩ := CycleQ2TraceRegularFiniteExtension.trace_regular (K := K) (L := L) c hA ω
    exact ⟨η,hη.symm⟩

def traceForm : Ω[B⁄k] →ₗ[A] Ω[A⁄k] :=
  (LinearEquiv.ofInjective mapRegular (regularMap_injective (K := K) c)).symm.toLinearMap.comp
    (traceToRange (L := L) c hA)

theorem traceForm_spec (ω : Ω[B⁄k]) :
    mapRegular (traceForm (K := K) (L := L) c hA ω) =
      traceOne (K := K) (KaehlerDifferential.map k k B L ω) := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective mapRegular (regularMap_injective (K := K) c)).apply_symm_apply
      (traceToRange (K := K) (L := L) c hA ω))

theorem traceForm_pullback (ω : Ω[A⁄k]) :
    traceForm (K := K) (L := L) c hA (KaehlerDifferential.map k k A B ω) =
      Module.finrank K L • ω := by
  apply regularMap_injective (K := K) c
  letI : IsScalarTower k A L := IsScalarTower.to₁₂₄ k A K L
  rw [traceForm_spec,map_tower (B := B),← map_tower (B := K) ω,
    traceOne_pullback_degree,map_nsmul]

private def rationalFunctionTrace : B →ₗ[A] K :=
  ((Algebra.trace K L).restrictScalars A).comp
    (((IsScalarTower.toAlgHom A B L).toLinearMap))

private theorem rationalFunctionTrace_mem (b : B) :
    rationalFunctionTrace (A := A) (K := K) (L := L) b ∈ LinearMap.range (Algebra.linearMap A K) := by
  have hb : IsIntegral A (algebraMap B L b) :=
    (Algebra.IsIntegral.isIntegral b).map (IsScalarTower.toAlgHom A B L)
  have ht : IsIntegral A (Algebra.trace K L (algebraMap B L b)) := Algebra.isIntegral_trace (R := A) (L := K) (F := L) hb
  obtain ⟨a,ha⟩ := (isIntegrallyClosed_iff K).mp (inferInstance : IsIntegrallyClosed A) ht
  exact ⟨a,ha⟩

/-- The genuine ordinary trace restricted to regular functions. -/
def traceFunction : B →ₗ[A] A :=
  (LinearEquiv.ofInjective (Algebra.linearMap A K) (IsFractionRing.injective A K)).symm.toLinearMap.comp
    ((rationalFunctionTrace (A := A) (K := K) (L := L)).codRestrict _
      (rationalFunctionTrace_mem (K := K) (L := L)))

theorem traceFunction_spec (b : B) :
    algebraMap A K (traceFunction (K := K) (L := L) b) =
      Algebra.trace K L (algebraMap B L b) := by
  exact congrArg Subtype.val
    ((LinearEquiv.ofInjective (Algebra.linearMap A K) (IsFractionRing.injective A K)).apply_symm_apply
      ⟨rationalFunctionTrace (A := A) (K := K) (L := L) b,rationalFunctionTrace_mem (K := K) (L := L) b⟩)

/-- The ordinary differential commutes with the trace of regular functions. -/
theorem traceForm_derivative (b : B) :
    traceForm (K := K) (L := L) c hA (D k B b) = D k A (traceFunction (K := K) (L := L) b) := by
  letI : CharZero K := charZero_of_injective_algebraMap (algebraMap k K).injective
  apply regularMap_injective (K := K) c
  rw [traceForm_spec,KaehlerDifferential.map_D,traceOne_D]
  change D k K (Algebra.trace K L (algebraMap B L b)) =
    KaehlerDifferential.map k k A K (D k A (traceFunction (K := K) (L := L) b))
  rw [KaehlerDifferential.map_D,traceFunction_spec]

end CycleQ2RegularCurveCochainTrace

#print axioms CycleQ2RegularCurveCochainTrace.traceForm_spec
#print axioms CycleQ2RegularCurveCochainTrace.traceForm_pullback
#print axioms CycleQ2RegularCurveCochainTrace.traceForm_derivative

end

section

/-!
# A surjective ring map checks one affine piece of a diagonal

The overlap and both charts here are the actual schemes. The two
coordinate restrictions determine the actual map into the product
of the affine charts over the coefficient field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2AffineDiagonalCriterion

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Algebra.TensorProduct
open scoped TensorProduct

private theorem congr_fst {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.fst f₂ g₂ = pullback.fst f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom]

private theorem congr_snd {X Y Z : Scheme} {f₁ f₂ : X ⟶ Z} {g₁ g₂ : Y ⟶ Z}
    (h₁ : f₁ = f₂) (h₂ : g₁ = g₂) :
    (pullback.congrHom h₁ h₂).hom ≫ pullback.snd f₂ g₂ = pullback.snd f₁ g₁ := by
  subst f₂
  subst g₂
  simp [pullback.congrHom]

variable {k A B R : Type} [Field k] [CommRing A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R] {Y : Scheme.{0}}
  (f : Y ⟶ Spec (CommRingCat.of k))
  (a : Spec (CommRingCat.of A) ⟶ Y) (b : Spec (CommRingCat.of B) ⟶ Y)
  (ha : a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k A)))
  (hb : b ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k B)))
  (φ : A →ₐ[k] R) (ψ : B →ₐ[k] R)
  (e : Spec (CommRingCat.of R) ≅ pullback a b)
  (he₁ : e.hom ≫ pullback.fst a b = Spec.map (CommRingCat.ofHom φ.toRingHom))
  (he₂ : e.hom ≫ pullback.snd a b = Spec.map (CommRingCat.ofHom ψ.toRingHom))

abbrev jointMap : A ⊗[k] B →ₐ[k] R := Algebra.TensorProduct.lift φ ψ (fun x y => Commute.all _ _)

include ha hb he₁ he₂ in
theorem closed_piece (h : Function.Surjective (jointMap φ ψ)) :
    IsClosedImmersion (pullback.mapDesc a b f) := by
  let d := pullback.mapDesc a b f
  let q := pullback.congrHom ha hb
  let t := pullbackSpecIso k A B
  let g := Spec.map (CommRingCat.ofHom (jointMap φ ψ).toRingHom)
  have e₁ : g ≫ t.inv ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    rw [pullbackSpecIso_inv_fst,← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x =>
      DFunLike.congr_fun (lift_comp_includeLeft φ ψ (fun x y => Commute.all _ _)) x)
  have e₂ : g ≫ t.inv ≫ pullback.snd _ _ = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    rw [pullbackSpecIso_inv_snd,← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun x =>
      DFunLike.congr_fun (lift_comp_includeRight φ ψ (fun x y => Commute.all _ _)) x)
  have hcomp : e.hom ≫ d ≫ q.hom = g ≫ t.inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, e₁, q, congr_fst, d, pullback.lift_fst, Category.comp_id]
      exact he₁
    · simp only [Category.assoc, e₂, q, congr_snd, d, pullback.lift_snd, Category.comp_id]
      exact he₂
  have hg : IsClosedImmersion g := IsClosedImmersion.spec_of_surjective _ h
  have ht : IsClosedImmersion (g ≫ t.inv) := by infer_instance
  have hh : IsClosedImmersion (e.hom ≫ d ≫ q.hom) := hcomp ▸ ht
  have hh' := (MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion e.hom (d ≫ q.hom)).mp hh
  exact (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion d q.hom).mp hh'

end CycleQ2AffineDiagonalCriterion

#print axioms CycleQ2AffineDiagonalCriterion.closed_piece

end

section

/-!
# Separatedness of the actual glued projective line

Both diagonal pieces from a single chart are ordinary affine
diagonals. On the two mixed pieces, the overlap is the genuine
Laurent scheme. The images of the polynomial charts generate
its whole coordinate ring, so the mixed diagonals are closed.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveLineSeparated

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Polynomial
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2LaurentLogDerivative (L)
open CycleQ2LaurentKahlerResidue (zeroRingMap infinityRingMap)
open CycleQ2ProjectiveLineFunctions (laurent_decompose)
open CycleQ2AffineDiagonalCriterion (jointMap closed_piece)
open scoped TensorProduct

variable (k : Type) [Field k]

private def chart (i : Bool) : affineLine k ⟶ line k := if i then chartInfinity k else chartZero k

private instance chart_open (i : Bool) : IsOpenImmersion (chart k i) := by
  cases i
  · exact inferInstanceAs (IsOpenImmersion (chartZero k))
  · exact inferInstanceAs (IsOpenImmersion (chartInfinity k))

def twoCharts : (line k).OpenCover where
  I₀ := Bool
  X _ := affineLine k
  f := chart k
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_,fun _ => inferInstance⟩
    intro x
    have h : x ∈ openZero k ⊔ openInfinity k := by rw [cover]; trivial
    rcases h with ⟨y,hy⟩ | ⟨y,hy⟩
    · exact ⟨false,y,hy⟩
    · exact ⟨true,y,hy⟩

private theorem chart_over (i : Bool) : chart k i ≫ structureMap k = affineStructure k := by
  cases i
  · exact chartZero_over k
  · exact chartInfinity_over k

private theorem self_piece (i : Bool) :
    IsClosedImmersion (pullback.mapDesc (chart k i) (chart k i) (structureMap k)) := by
  let a := chart k i
  let e : affineLine k ≅ pullback a a := asIso (pullback.diagonal a)
  let φ : k[X] →ₐ[k] k[X] := AlgHom.id k k[X]
  have h : Function.Surjective (jointMap φ φ) := by
    intro x
    refine ⟨x ⊗ₜ[k] (1 : k[X]),?_⟩
    simp [jointMap,φ]
  exact closed_piece (structureMap k) a a (chart_over k i) (chart_over k i)
    φ φ e (by simp [e,φ]) (by simp [e,φ]) h

private theorem mixed_piece (i j : Bool) (φ ψ : k[X] →ₐ[k] L k)
    (h₁ : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ chart k i = chartTorus k)
    (h₂ : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ chart k j = chartTorus k)
    (hr : Set.range (chartTorus k) = Set.range (chart k i) ∩ Set.range (chart k j))
    (hs : ∀ z : L k, ∃ x y, z = φ x - ψ y) :
    IsClosedImmersion (pullback.mapDesc (chart k i) (chart k j) (structureMap k)) := by
  let a := chart k i
  let b := chart k j
  let v := pullback.fst a b ≫ a
  letI : IsOpenImmersion v := by dsimp [v]; infer_instance
  have he : Set.range (chartTorus k) = Set.range v := hr.trans
    (IsOpenImmersion.range_pullback_to_base_of_left a b).symm
  let e := IsOpenImmersion.isoOfRangeEq (chartTorus k) v he
  have ea : e.hom ≫ pullback.fst a b = Spec.map (CommRingCat.ofHom φ.toRingHom) := by
    apply (cancel_mono a).mp
    rw [Category.assoc,h₁]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac (chartTorus k) v he
  have eb : e.hom ≫ pullback.snd a b = Spec.map (CommRingCat.ofHom ψ.toRingHom) := by
    apply (cancel_mono b).mp
    rw [Category.assoc,h₂,← pullback.condition]
    exact IsOpenImmersion.isoOfRangeEq_hom_fac (chartTorus k) v he
  refine closed_piece (structureMap k) a b (chart_over k i) (chart_over k j) φ ψ e ea eb ?_
  intro z
  obtain ⟨x,y,hxy⟩ := hs z
  refine ⟨x ⊗ₜ[k] (1 : k[X]) - (1 : k[X]) ⊗ₜ[k] y,?_⟩
  rw [map_sub,jointMap,Algebra.TensorProduct.lift_tmul,Algebra.TensorProduct.lift_tmul,map_one,
    map_one,mul_one,one_mul]
  exact hxy.symm

private theorem spec_infinity : Spec.map (CommRingCat.ofHom (infinityRingMap k).toRingHom) =
    infinityMap k := by
  rw [infinityMap,inversion,zeroMap,← Spec.map_comp]
  rfl

private theorem mixed_range : Set.range (chartTorus k) =
    Set.range (chartZero k) ∩ Set.range (chartInfinity k) := by
  exact congrArg (fun U : (line k).Opens => (U : Set (line k))) (overlap k).symm

private theorem mixed_zero_infinity :
    IsClosedImmersion (pullback.mapDesc (chartZero k) (chartInfinity k) (structureMap k)) := by
  apply mixed_piece k false true (zeroRingMap k) (infinityRingMap k)
  · exact torus_zero k
  · rw [spec_infinity]
    exact torus_infinity k
  · exact mixed_range k
  · exact laurent_decompose k

private theorem mixed_infinity_zero :
    IsClosedImmersion (pullback.mapDesc (chartInfinity k) (chartZero k) (structureMap k)) := by
  apply mixed_piece k true false (infinityRingMap k) (zeroRingMap k)
  · rw [spec_infinity]
    exact torus_infinity k
  · exact torus_zero k
  · rw [Set.inter_comm]
    exact mixed_range k
  · intro z
    obtain ⟨a,b,hab⟩ := laurent_decompose k z
    exact ⟨-b,-a,by rw [hab,map_neg,map_neg]; abel⟩

private abbrev Q : AffineTargetMorphismProperty :=
  fun X _ f => IsAffine X ∧ Function.Surjective (f.appTop)

/-- The actual structure morphism of the Laurent gluing is separated. -/
theorem separated : IsSeparated (structureMap k) := by
  letI : HasAffineProperty @IsClosedImmersion Q := IsClosedImmersion.hasAffineProperty
  letI : Q.IsLocal := HasAffineProperty.isLocal_affineProperty @IsClosedImmersion
  letI : ∀ i, IsAffine ((twoCharts k).X i) := fun _ => inferInstanceAs (IsAffine (affineLine k))
  have h : Q.diagonal (structureMap k) := by
    apply AffineTargetMorphismProperty.diagonal_of_openCover_source (Q := Q) (structureMap k) (twoCharts k)
    intro i j
    have he : IsClosedImmersion (pullback.mapDesc (chart k i) (chart k j) (structureMap k)) := by
      cases i <;> cases j
      · exact self_piece k false
      · exact mixed_zero_infinity k
      · exact mixed_infinity_zero k
      · exact self_piece k true
    letI : IsClosedImmersion (pullback.mapDesc ((twoCharts k).f i) ((twoCharts k).f j)
        (structureMap k)) := he
    exact IsClosedImmersion.isAffine_surjective_of_isAffine _
  exact ⟨(HasAffineProperty.diagonal_iff @IsClosedImmersion).mp h⟩

end CycleQ2ProjectiveLineSeparated

#print axioms CycleQ2ProjectiveLineSeparated.separated

end

section

/-!
# The actual regular locus of a rational function

The nonempty opens on which a rational function is represented
form its maximal regular open. The representatives agree on
overlaps by injectivity into the function field and therefore
glue to a unique regular section on that open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionRegularLocus

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open TopCat.Presheaf

variable (X : Scheme.{0}) [IsIntegral X]

structure Representative (z : X.functionField) where
  openSet : X.Opens
  nonempty : Nonempty openSet
  value : Γ(X,openSet)
  germ_eq : letI : Nonempty openSet := nonempty
    X.germToFunctionField openSet value = z

def regularOpen (z : X.functionField) : X.Opens :=
  ⨆ i : Representative X z, i.openSet

private theorem generic_mem {U : X.Opens} [Nonempty U] : genericPoint X ∈ U :=
  ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance : Nonempty U))

private theorem representative_exists (z : X.functionField) : Nonempty (Representative X z) := by
  obtain ⟨U,hU,s,hs⟩ := X.presheaf.exists_germ_eq z
  let h : Nonempty U := ⟨genericPoint X,hU⟩
  exact ⟨⟨U,h,s,hs⟩⟩

instance (z : X.functionField) : Nonempty (regularOpen X z) := by
  obtain ⟨i⟩ := representative_exists X z
  letI : Nonempty i.openSet := i.nonempty
  exact ⟨genericPoint X,(le_iSup (fun j : Representative X z => j.openSet) i) (generic_mem X)⟩

theorem germ_restrict {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U) (s : Γ(X,U)) :
    X.germToFunctionField V (X.presheaf.map (homOfLE h).op s) = X.germToFunctionField U s :=
  germ_res_apply X.presheaf (homOfLE h) (genericPoint X) (generic_mem X) s

private theorem sections_compatible (z : X.functionField) :
    IsCompatible X.presheaf (fun i : Representative X z => i.openSet) (fun i => i.value) := by
  intro i j
  letI : Nonempty i.openSet := i.nonempty
  letI : Nonempty j.openSet := j.nonempty
  let O : X.Opens := i.openSet ⊓ j.openSet
  letI : Nonempty O := ⟨⟨genericPoint X,⟨generic_mem X,generic_mem X⟩⟩⟩
  apply (X.germToFunctionField_injective O)
  let l : O ≤ i.openSet := inf_le_left
  let r : O ≤ j.openSet := inf_le_right
  change X.germToFunctionField O (X.presheaf.map (homOfLE l).op i.value) =
    X.germToFunctionField O (X.presheaf.map (homOfLE r).op j.value)
  calc
    _ = X.germToFunctionField i.openSet i.value := germ_restrict X l i.value
    _ = X.germToFunctionField j.openSet j.value := i.germ_eq.trans j.germ_eq.symm
    _ = _ := (germ_restrict X r j.value).symm

theorem section_exists (z : X.functionField) :
    ∃ s : Γ(X,regularOpen X z), X.germToFunctionField (regularOpen X z) s = z := by
  let U := regularOpen X z
  let W := fun i : Representative X z => i.openSet
  let leU (i : Representative X z) : i.openSet ≤ U := le_iSup W i
  obtain ⟨s,hs,_⟩ := X.sheaf.existsUnique_gluing' W U (fun i => homOfLE (leU i))
    le_rfl (fun i => i.value) (sections_compatible X z)
  obtain ⟨i⟩ := representative_exists X z
  letI : Nonempty i.openSet := i.nonempty
  refine ⟨s,?_⟩
  change X.germToFunctionField U s = z
  have hsi : X.presheaf.map (homOfLE (leU i)).op s = i.value := hs i
  rw [← germ_restrict X (leU i), hsi, i.germ_eq]

/-- The original rational function as a regular section on its maximal domain. -/
def sectionValue (z : X.functionField) : Γ(X,regularOpen X z) :=
  (section_exists X z).choose

theorem sectionValue_germ (z : X.functionField) :
    X.germToFunctionField (regularOpen X z) (sectionValue X z) = z :=
  (section_exists X z).choose_spec

/-- Membership in the literal regular open is tested by the actual local ring. -/
theorem mem_regularOpen_iff (z : X.functionField) (x : X) :
    x ∈ regularOpen X z ↔ ∃ a : X.presheaf.stalk x,
      algebraMap (X.presheaf.stalk x) X.functionField a = z := by
  constructor
  · intro hx
    refine ⟨X.presheaf.germ (regularOpen X z) x hx (sectionValue X z),?_⟩
    rw [Scheme.algebraMap_germ_eq_germToFunctionField,sectionValue_germ]
  · rintro ⟨a,ha⟩
    obtain ⟨W,hW,b,hb⟩ := X.presheaf.exists_germ_eq a
    letI : Nonempty W := ⟨x,hW⟩
    let i : Representative X z := ⟨W,inferInstance,b,?_⟩
    · exact (le_iSup (fun j : Representative X z => j.openSet) i) hW
    · rw [← Scheme.algebraMap_germ_eq_germToFunctionField X hW,hb,ha]

end CycleQ2RationalFunctionRegularLocus

#print axioms CycleQ2RationalFunctionRegularLocus.section_exists
#print axioms CycleQ2RationalFunctionRegularLocus.mem_regularOpen_iff

end

section

/-!
# The inverse-coordinate cover on a curve with valuation local rings

A rational function or its inverse is regular at every valuation
point. On the actual overlap both regular sections multiply to
one, since their images in the function field are inverse.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionInverseCover

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2RationalFunctionRegularLocus

variable (X : Scheme.{0}) [IsIntegral X]

variable (z : X.functionField)

abbrev reciprocalOpen := regularOpen X z⁻¹
abbrev overlap := regularOpen X z ⊓ reciprocalOpen X z

theorem inverse_cover (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) :
    regularOpen X z ⊔ reciprocalOpen X z = ⊤ := by
  apply top_unique
  intro x _
  letI : ValuationRing (X.presheaf.stalk x) := hv x
  rcases ValuationRing.isInteger_or_isInteger (↑(X.presheaf.stalk x)) z with h | h
  · exact Or.inl ((mem_regularOpen_iff X z x).2 h)
  · exact Or.inr ((mem_regularOpen_iff X z⁻¹ x).2 h)

instance : Nonempty (overlap X z : X.Opens) := by
  let U := regularOpen X z
  let V := reciprocalOpen X z
  have hU : genericPoint X ∈ U := ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
    (by simpa using (inferInstance : Nonempty U))
  have hV : genericPoint X ∈ V := ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr
    (by simpa using (inferInstance : Nonempty V))
  exact ⟨⟨genericPoint X,hU,hV⟩⟩

def onOverlap : Γ(X,overlap X z) :=
  X.presheaf.map (homOfLE (show overlap X z ≤ regularOpen X z from inf_le_left)).op
    (sectionValue X z)

def inverseOnOverlap : Γ(X,overlap X z) :=
  X.presheaf.map (homOfLE (show overlap X z ≤ reciprocalOpen X z from inf_le_right)).op
    (sectionValue X z⁻¹)

theorem onOverlap_germ :
    X.germToFunctionField (overlap X z) (onOverlap X z) = z :=
  (germ_restrict X inf_le_left (sectionValue X z)).trans (sectionValue_germ X z)

theorem inverseOnOverlap_germ :
    X.germToFunctionField (overlap X z) (inverseOnOverlap X z) = z⁻¹ :=
  (germ_restrict X inf_le_right (sectionValue X z⁻¹)).trans (sectionValue_germ X z⁻¹)

theorem inverse_mul (hz : z ≠ 0) : onOverlap X z * inverseOnOverlap X z = 1 := by
  apply X.germToFunctionField_injective (overlap X z)
  rw [map_mul, onOverlap_germ, inverseOnOverlap_germ, map_one, mul_inv_cancel₀ hz]

/-- The actual overlap coordinate as a unit, with the actual inverse section. -/
def overlapUnit (hz : z ≠ 0) : Γ(X,overlap X z)ˣ where
  val := onOverlap X z
  inv := inverseOnOverlap X z
  val_inv := inverse_mul X z hz
  inv_val := (mul_comm _ _).trans (inverse_mul X z hz)

end CycleQ2RationalFunctionInverseCover

#print axioms CycleQ2RationalFunctionInverseCover.inverse_cover
#print axioms CycleQ2RationalFunctionInverseCover.overlapUnit

end

section

/-!
# The reciprocal chart maps of a rational function on a curve

The two maps to the affine line are induced by the actual
regular representatives. On their overlap the chosen unit maps
to the Laurent torus and both restrictions are the corresponding
polynomial maps, with inverse coordinate on the second chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionLineCharts

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2RationalFunctionRegularLocus (regularOpen sectionValue)
open CycleQ2RationalFunctionInverseCover (reciprocalOpen overlap overlapUnit)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open scoped Polynomial

variable (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) (z : X.functionField)

private abbrev A := regularOpen X z
private abbrev B := reciprocalOpen X z
private abbrev W := overlap X z

def affineMap : (A z).toScheme ⟶ affineLine k :=
  (A z).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Polynomial.eval₂RingHom (sectionCoefficients p (A z)) (sectionValue X z)))

def torusMap (hz : z ≠ 0) : (W z).toScheme ⟶ torus k :=
  (W z).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (LaurentPolynomial.eval₂ (sectionCoefficients p (W z)) (overlapUnit X z hz)))

private theorem polynomial_eval_restrict {U V : X.Opens} (h : V ≤ U) (a : Γ(X,U)) :
    (X.presheaf.map (homOfLE h).op).hom.comp (Polynomial.eval₂RingHom (sectionCoefficients p U) a) =
      Polynomial.eval₂RingHom (sectionCoefficients p V) (X.presheaf.map (homOfLE h).op a) := by
  letI : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  letI : Algebra k Γ(X,V) := (sectionCoefficients p V).toAlgebra
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    exact (restrict p h).commutes r
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]

theorem zero_factor (hz : z ≠ 0) :
    X.homOfLE (show W z ≤ A z from inf_le_left) ≫ affineMap k p z =
      torusMap k p z hz ≫ zeroMap k := by
  unfold affineMap torusMap zeroMap
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f => (W z).toSpecΓ ≫ Spec.map f)
  apply CommRingCat.hom_ext
  let h : W z ≤ A z := inf_le_left
  change (X.presheaf.map (homOfLE h).op).hom.comp
    (Polynomial.eval₂RingHom (sectionCoefficients p (A z)) (sectionValue X z)) =
    (LaurentPolynomial.eval₂ (sectionCoefficients p (W z)) (overlapUnit X z hz)).comp
      Polynomial.toLaurent
  rw [polynomial_eval_restrict k p h (sectionValue X z)]
  apply RingHom.ext
  intro q
  exact (LaurentPolynomial.eval₂_toLaurent (sectionCoefficients p (W z)) (overlapUnit X z hz) q).symm

private theorem eval_inverted (V : X.Opens) (u : Γ(X,V)ˣ) :
    (LaurentPolynomial.eval₂ (sectionCoefficients p V) u).comp
      ((LaurentPolynomial.invert : LaurentPolynomial k ≃ₐ[k] LaurentPolynomial k).toRingHom.comp
        (Polynomial.toLaurentAlg : k[X] →ₐ[k] LaurentPolynomial k).toRingHom) =
      Polynomial.eval₂RingHom (sectionCoefficients p V) (↑u⁻¹ : Γ(X,V)) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    change LaurentPolynomial.eval₂ (sectionCoefficients p V) u
      (LaurentPolynomial.invert (Polynomial.toLaurent (Polynomial.C r))) = _
    rw [Polynomial.toLaurent_C,LaurentPolynomial.invert_C,LaurentPolynomial.eval₂_C]
  · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
    change LaurentPolynomial.eval₂ (sectionCoefficients p V) u
      (LaurentPolynomial.invert (Polynomial.toLaurent Polynomial.X)) = _
    rw [Polynomial.toLaurent_X,LaurentPolynomial.invert_T,LaurentPolynomial.eval₂_T]
    simp

theorem infinity_factor (hz : z ≠ 0) :
    X.homOfLE (show W z ≤ B z from inf_le_right) ≫ affineMap k p z⁻¹ =
      torusMap k p z hz ≫ infinityMap k := by
  unfold affineMap torusMap infinityMap inversion zeroMap
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
  apply congrArg (fun f => (W z).toSpecΓ ≫ Spec.map f)
  apply CommRingCat.hom_ext
  let h : W z ≤ B z := inf_le_right
  change (X.presheaf.map (homOfLE h).op).hom.comp
    (Polynomial.eval₂RingHom (sectionCoefficients p (B z)) (sectionValue X z⁻¹)) = _
  rw [polynomial_eval_restrict k p h (sectionValue X z⁻¹)]
  change Polynomial.eval₂RingHom (sectionCoefficients p (W z))
      (↑(overlapUnit X z hz)⁻¹ : Γ(X,W z)) = _
  exact (eval_inverted k p (W z) (overlapUnit X z hz)).symm

end CycleQ2RationalFunctionLineCharts

#print axioms CycleQ2RationalFunctionLineCharts.zero_factor
#print axioms CycleQ2RationalFunctionLineCharts.infinity_factor

end

section

/-!
# A rational function gives an actual projective-line morphism

On an integral scheme with valuation local rings the regular
loci of the function and its reciprocal cover the scheme. The
two actual affine chart morphisms glue along the verified
Laurent overlap by the scheme open-cover gluing theorem.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionToLine

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine
open CycleQ2RationalFunctionRegularLocus (regularOpen)
open CycleQ2RationalFunctionInverseCover (reciprocalOpen overlap inverse_cover)
open CycleQ2RationalFunctionLineCharts (affineMap torusMap zero_factor infinity_factor)

variable {X : Scheme.{0}}

private theorem intersectionRange (U V : X.Opens) :
    Set.range (U ⊓ V : X.Opens).ι = Set.range (pullback.fst U.ι V.ι ≫ U.ι) := by
  rw [IsOpenImmersion.range_pullback_to_base_of_left,Scheme.Opens.range_ι,Scheme.Opens.range_ι,Scheme.Opens.range_ι]
  rfl

private def intersectionIso (U V : X.Opens) :
    (U ⊓ V : X.Opens).toScheme ≅ pullback U.ι V.ι :=
  IsOpenImmersion.isoOfRangeEq (U ⊓ V : X.Opens).ι (pullback.fst U.ι V.ι ≫ U.ι)
    (intersectionRange U V)

private theorem intersection_fst (U V : X.Opens) :
    (intersectionIso U V).hom ≫ pullback.fst U.ι V.ι =
      X.homOfLE (show U ⊓ V ≤ U from inf_le_left) := by
  apply (cancel_mono U.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac (U ⊓ V : X.Opens).ι (pullback.fst U.ι V.ι ≫ U.ι) (intersectionRange U V)

private theorem intersection_snd (U V : X.Opens) :
    (intersectionIso U V).hom ≫ pullback.snd U.ι V.ι =
      X.homOfLE (show U ⊓ V ≤ V from inf_le_right) := by
  apply (cancel_mono V.ι).mp
  rw [Category.assoc, Scheme.homOfLE_ι, ← pullback.condition]
  exact IsOpenImmersion.isoOfRangeEq_hom_fac (U ⊓ V : X.Opens).ι (pullback.fst U.ι V.ι ≫ U.ι) (intersectionRange U V)

variable [IsIntegral X] (z : X.functionField)

private def domain : Bool → X.Opens
  | false => regularOpen X z
  | true => reciprocalOpen X z

def inverseCover (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) : X.OpenCover where
  I₀ := Bool
  X i := (domain z i).toScheme
  f i := (domain z i).ι
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    refine ⟨?_,fun _ => inferInstance⟩
    intro x
    have hx : x ∈ regularOpen X z ⊔ reciprocalOpen X z := by rw [inverse_cover X z hv]; trivial
    rcases hx with hx | hx
    · exact ⟨false,⟨x,hx⟩,rfl⟩
    · exact ⟨true,⟨x,hx⟩,rfl⟩

variable (k : Type) [Field k] (p : X ⟶ Spec (CommRingCat.of k))

private def piece (i : Bool) : (domain z i).toScheme ⟶ line k := by
  cases i
  · exact affineMap k p z ≫ chartZero k
  · exact affineMap k p z⁻¹ ≫ chartInfinity k

private theorem mixed (hz : z ≠ 0) :
    pullback.fst (regularOpen X z).ι (reciprocalOpen X z).ι ≫ piece z k p false =
      pullback.snd (regularOpen X z).ι (reciprocalOpen X z).ι ≫ piece z k p true := by
  let U := regularOpen X z
  let V := reciprocalOpen X z
  apply (cancel_epi (intersectionIso U V).hom).mp
  simp only [← Category.assoc]
  rw [intersection_fst (regularOpen X z) (reciprocalOpen X z),
    intersection_snd (regularOpen X z) (reciprocalOpen X z)]
  change (X.homOfLE (show overlap X z ≤ U from inf_le_left) ≫ affineMap k p z) ≫ chartZero k =
    (X.homOfLE (show overlap X z ≤ V from inf_le_right) ≫ affineMap k p z⁻¹) ≫ chartInfinity k
  rw [zero_factor k p z hz, infinity_factor k p z hz,Category.assoc,Category.assoc,
    torus_zero,torus_infinity]

private theorem pieces_compatible (hz : z ≠ 0) (i j : Bool) :
    pullback.fst (domain z i).ι (domain z j).ι ≫ piece z k p i =
      pullback.snd (domain z i).ι (domain z j).ι ≫ piece z k p j := by
  cases i <;> cases j
  · rw [show pullback.fst (domain z false).ι (domain z false).ι = pullback.snd _ _ from
      (cancel_mono (domain z false).ι).mp pullback.condition]
  · exact mixed z k p hz
  · change pullback.fst (reciprocalOpen X z).ι (regularOpen X z).ι ≫ piece z k p true =
      pullback.snd (reciprocalOpen X z).ι (regularOpen X z).ι ≫ piece z k p false
    apply (cancel_epi (pullbackSymmetry (regularOpen X z).ι (reciprocalOpen X z).ι).hom).mp
    simpa only [← Category.assoc,pullbackSymmetry_hom_comp_fst,pullbackSymmetry_hom_comp_snd] using
      (mixed z k p hz).symm
  · rw [show pullback.fst (domain z true).ι (domain z true).ι = pullback.snd _ _ from
      (cancel_mono (domain z true).ι).mp pullback.condition]

def toLine (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    X ⟶ line k :=
  (inverseCover z hv).glueMorphisms (piece z k p) (pieces_compatible z k p hz)

theorem zero_chart (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    (regularOpen X z).ι ≫ toLine z k p hv hz = affineMap k p z ≫ chartZero k :=
  (inverseCover z hv).ι_glueMorphisms (piece z k p) (pieces_compatible z k p hz) false

theorem infinity_chart (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    (reciprocalOpen X z).ι ≫ toLine z k p hv hz = affineMap k p z⁻¹ ≫ chartInfinity k :=
  (inverseCover z hv).ι_glueMorphisms (piece z k p) (pieces_compatible z k p hz) true

end CycleQ2RationalFunctionToLine

#print axioms CycleQ2RationalFunctionToLine.zero_chart
#print axioms CycleQ2RationalFunctionToLine.infinity_chart

end

section

/-!
# The rational-function map is over the original coefficient field

The cohomological projections later use this literal scheme
morphism over the given field. The affine factor is checked
through the adjunction with global sections, including its
induced coefficient ring homomorphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionRelativeMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure
open CycleQ2RationalFunctionRegularLocus (regularOpen sectionValue)
open CycleQ2RationalFunctionInverseCover (reciprocalOpen)
open CycleQ2RationalFunctionLineCharts (affineMap)
open CycleQ2RationalFunctionToLine (toLine inverseCover zero_chart infinity_chart)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open scoped Polynomial

variable (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k))

theorem sectionCoefficients_Spec (U : X.Opens) :
    U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (sectionCoefficients p U)) = U.ι ≫ p := by
  let γ := Scheme.ΓSpecIso (CommRingCat.of k)
  let r := X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op
  change U.toSpecΓ ≫ Spec.map (γ.inv ≫ p.appTop ≫ r) = _
  rw [Spec.map_comp,Spec.map_comp]
  simp only [← Category.assoc]
  rw [U.toSpecΓ_SpecMap_presheaf_map_top,Category.assoc U.ι,
    ← Scheme.toSpecΓ_naturality, ← Category.assoc, Category.assoc (U.ι ≫ p),
    toSpecΓ_SpecMap_ΓSpecIso_inv,Category.comp_id]

variable [IsIntegral X] (z : X.functionField)

theorem affineMap_over : affineMap k p z ≫ affineStructure k = (regularOpen X z).ι ≫ p := by
  unfold affineMap affineStructure
  rw [Category.assoc,← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap k k[X]) ≫ CommRingCat.ofHom
      (Polynomial.eval₂RingHom (sectionCoefficients p (regularOpen X z)) (sectionValue X z)) =
      CommRingCat.ofHom (sectionCoefficients p (regularOpen X z)) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact Polynomial.eval₂_C _ _
  rw [h,sectionCoefficients_Spec]

theorem toLine_over (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    toLine z k p hv hz ≫ structureMap k = p := by
  apply (inverseCover z hv).hom_ext
  intro b
  cases b
  · change (regularOpen X z).ι ≫ toLine z k p hv hz ≫ structureMap k = _
    rw [← Category.assoc,zero_chart,Category.assoc,chartZero_over,affineMap_over]
    rfl
  · change (reciprocalOpen X z).ι ≫ toLine z k p hv hz ≫ structureMap k = _
    rw [← Category.assoc,infinity_chart,Category.assoc,chartInfinity_over,affineMap_over]
    rfl

theorem toLine_proper [IsProper p] (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    IsProper (toLine z k p hv hz) := by
  letI : IsSeparated (structureMap k) := CycleQ2ProjectiveLineSeparated.separated k
  letI : IsProper (toLine z k p hv hz ≫ structureMap k) := (toLine_over k p z hv hz).symm ▸ inferInstance
  exact IsProper.of_comp _ (structureMap k)

end CycleQ2RationalFunctionRelativeMap

#print axioms CycleQ2RationalFunctionRelativeMap.toLine_over
#print axioms CycleQ2RationalFunctionRelativeMap.toLine_proper

end

section

/-!
# A nonconstant proper integral curve map is finite

Every nongeneric point of an integral one-dimensional scheme is
closed. A proper closed subset of a Noetherian integral curve is
a finite union of such points. A proper morphism that sends the
generic point to a nonclosed point therefore has finite fibers.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProperCurveFiniteFibres

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Order Set

section Spaces

variable {X : Type} [TopologicalSpace X] [T0Space X] [QuasiSober X] [IrreducibleSpace X]

private def closureOf (x : X) : IrreducibleCloseds X :=
  ⟨closure ({x} : Set X),isIrreducible_singleton.closure,isClosed_closure⟩

theorem closed_nongeneric (hX : topologicalKrullDim X ≤ 1) {x : X}
    (hx : x ≠ genericPoint X) : IsClosed ({x} : Set X) := by
  by_contra h
  have hn : ¬ closure ({x} : Set X) ⊆ {x} := fun hsub =>
    h ((Set.Subset.antisymm hsub subset_closure) ▸ isClosed_closure)
  obtain ⟨y,hy,hy'⟩ := Set.not_subset.mp hn
  have h₁ : closureOf x < closureOf (genericPoint X) := by
    refine lt_of_le_of_ne ?_ ?_
    · change closure ({x} : Set X) ⊆ closure {genericPoint X}
      rw [genericPoint_closure]
      exact Set.subset_univ _
    · intro hxy
      apply hx
      apply IsGenericPoint.eq (S := closure ({x} : Set X))
      · rfl
      · exact congrArg (fun s : IrreducibleCloseds X => (s : Set X)) hxy.symm
  have h₂ : closureOf y < closureOf x := by
    refine lt_of_le_of_ne (closure_minimal (Set.singleton_subset_iff.mpr hy) isClosed_closure) ?_
    intro hxy
    apply hy'
    rw [Set.mem_singleton_iff]
    apply IsGenericPoint.eq (S := closure ({y} : Set X))
    · rfl
    · exact congrArg (fun s : IrreducibleCloseds X => (s : Set X)) hxy.symm
  let p : LTSeries (IrreducibleCloseds X) :=
    (RelSeries.singleton _ (closureOf (genericPoint X))).cons (closureOf x) h₁
  let q : LTSeries (IrreducibleCloseds X) := p.cons (closureOf y) (by
    change closureOf y < p.head
    simpa only [p,RelSeries.head_cons] using h₂)
  have hd := LTSeries.length_le_krullDim q
  change (2 : WithBot ℕ∞) ≤ topologicalKrullDim X at hd
  exact (by decide : ¬(2 : WithBot ℕ∞) ≤ 1) (hd.trans hX)

theorem finite_closed_proper [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1)
    {S : Set X} (hS : IsClosed S) (hproper : S ≠ univ) : S.Finite := by
  obtain ⟨T,hT,hcl,hirr,hcover⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hS
  rw [hcover]
  apply hT.sUnion
  intro W hW
  have hgen := (hirr W hW).closure_genericPoint (hcl W hW)
  have hng : (hirr W hW).genericPoint ≠ genericPoint X := by
    intro h
    rw [h,genericPoint_closure] at hgen
    apply hproper
    apply Set.eq_univ_of_univ_subset
    rw [hgen,hcover]
    exact Set.subset_sUnion_of_mem hW
  rw [← hgen,(closed_nongeneric hX hng).closure_eq]
  exact Set.finite_singleton _

end Spaces

variable {X Y : Scheme.{0}} [IsIntegral X] [NoetherianSpace X]
  (f : X ⟶ Y) [IsProper f]

theorem finite_fibers (hX : topologicalKrullDim X ≤ 1)
    (hf : ¬ IsClosed ({f (genericPoint X)} : Set Y)) :
    ∀ y : Y, (f ⁻¹' {y}).Finite := by
  intro y
  by_cases hy : IsClosed ({y} : Set Y)
  · refine finite_closed_proper hX (hy.preimage f.continuous) ?_
    intro h
    have hz : genericPoint X ∈ f ⁻¹' ({y} : Set Y) := by rw [h]; trivial
    change f (genericPoint X) = y at hz
    exact hf (hz.symm ▸ hy)
  · have hgen : ∀ x ∈ f ⁻¹' ({y} : Set Y), x = genericPoint X := by
      intro x hx
      by_contra hn
      have h := f.isClosedMap _ (closed_nongeneric hX hn)
      rw [Set.image_singleton] at h
      change f x = y at hx
      exact hy (hx ▸ h)
    exact (Set.finite_singleton (genericPoint X)).subset (fun x hx => hgen x hx)

theorem finite_map (hX : topologicalKrullDim X ≤ 1)
    (hf : ¬ IsClosed ({f (genericPoint X)} : Set Y)) : IsFinite f := by
  letI : LocallyQuasiFinite f := LocallyQuasiFinite.of_finite_preimage_singleton f (finite_fibers f hX hf)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end CycleQ2ProperCurveFiniteFibres

#print axioms CycleQ2ProperCurveFiniteFibres.finite_map

end

section

/-!
# A transcendental rational function gives a finite proper curve projection

The actual glued morphism sends the generic point to the generic point
of the polynomial chart. Properness and the dimension bound make its
fibers finite.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2RationalFunctionFiniteMap

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2LaurentProjectiveLine
open CycleQ2RationalFunctionRegularLocus (regularOpen sectionValue sectionValue_germ germ_restrict)
open CycleQ2RationalFunctionLineCharts (affineMap)
open CycleQ2RationalFunctionToLine (toLine zero_chart)
open CycleQ2RationalFunctionRelativeMap (toLine_proper)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open scoped Polynomial

variable (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X]
  (p : X ⟶ Spec (CommRingCat.of k)) (z : X.functionField)

abbrev fieldCoefficients : k →+* X.functionField :=
  (X.germToFunctionField (regularOpen X z)).hom.comp (sectionCoefficients p (regularOpen X z))

private def evalChart {V : X.Opens} (h : V ≤ regularOpen X z) : k[X] →+* Γ(X,V) :=
  Polynomial.eval₂RingHom (sectionCoefficients p V)
    (X.presheaf.map (homOfLE h).op (sectionValue X z))

private theorem evalChart_restrict {V : X.Opens} (h : V ≤ regularOpen X z) :
    (X.presheaf.map (homOfLE h).op).hom.comp
      (Polynomial.eval₂RingHom (sectionCoefficients p (regularOpen X z)) (sectionValue X z)) =
    evalChart k p z h := by
  letI : Algebra k Γ(X,regularOpen X z) := (sectionCoefficients p (regularOpen X z)).toAlgebra
  letI : Algebra k Γ(X,V) := (sectionCoefficients p V).toAlgebra
  apply Polynomial.ringHom_ext
  · intro c
    simp only [evalChart,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
    exact (restrict p h).commutes c
  · simp only [evalChart,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]

private theorem evalChart_injective {V : X.Opens} [Nonempty V] (h : V ≤ regularOpen X z)
    (he : Function.Injective (Polynomial.eval₂RingHom (fieldCoefficients k p z) z)) :
    Function.Injective (evalChart k p z h) := by
  have e : (X.germToFunctionField V).hom.comp (evalChart k p z h) =
      Polynomial.eval₂RingHom (fieldCoefficients k p z) z := by
    rw [← evalChart_restrict,← RingHom.comp_assoc]
    apply Polynomial.ringHom_ext
    · intro c
      simp only [fieldCoefficients,RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C]
      exact germ_restrict X h _
    · simp only [RingHom.comp_apply,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_X]
      exact (germ_restrict X h _).trans (sectionValue_germ X z)
  intro a b hab
  apply he
  rw [← e]
  exact congrArg (X.germToFunctionField V) hab

private theorem affine_factor {V : X.Opens} (hV : IsAffineOpen V) (h : V ≤ regularOpen X z)
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0) :
    hV.fromSpec ≫ toLine z k p hv hz =
      Spec.map (CommRingCat.ofHom (evalChart k p z h)) ≫ chartZero k := by
  unfold IsAffineOpen.fromSpec
  rw [Category.assoc, ← Scheme.homOfLE_ι X h,Category.assoc (X.homOfLE h),zero_chart]
  unfold affineMap
  simp only [Category.assoc]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc]
  have e : CommRingCat.ofHom (Polynomial.eval₂RingHom (sectionCoefficients p (regularOpen X z))
        (sectionValue X z)) ≫ X.presheaf.map (homOfLE h).op =
      CommRingCat.ofHom (evalChart k p z h) := CommRingCat.hom_ext (evalChart_restrict k p z h)
  rw [e,← Category.assoc, hV.isoSpec_inv_toSpecΓ,Category.id_comp]

private theorem generic_image (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0)
    (he : Function.Injective (Polynomial.eval₂RingHom (fieldCoefficients k p z) z)) :
    toLine z k p hv hz (genericPoint X) = chartZero k (genericPoint (affineLine k)) := by
  have hm : genericPoint X ∈ regularOpen X z :=
    ((genericPoint_spec X).mem_open_set_iff (regularOpen X z).isOpen).mpr
      (by simpa using (inferInstance : Nonempty (regularOpen X z)))
  obtain ⟨_,⟨V,hV,rfl⟩,hg,h⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hm
    (regularOpen X z).isOpen
  letI : Nonempty V := ⟨genericPoint X,hg⟩
  have h₁ : hV.fromSpec (genericPoint (Spec Γ(X,V))) = genericPoint X :=
    genericPoint_eq_of_isOpenImmersion hV.fromSpec
  have h₂ : Spec.map (CommRingCat.ofHom (evalChart k p z h)) (genericPoint (Spec Γ(X,V))) =
      genericPoint (affineLine k) := by
    change _ = genericPoint (Spec (CommRingCat.of k[X]))
    rw [genericPoint_eq_bot_of_affine,genericPoint_eq_bot_of_affine]
    apply PrimeSpectrum.ext
    exact Ideal.comap_bot_of_injective (evalChart k p z h) (evalChart_injective k p z h he)
  have e := congrArg (fun f : Spec Γ(X,V) ⟶ line k => f (genericPoint (Spec Γ(X,V))))
    (affine_factor k p z hV h hv hz)
  change toLine z k p hv hz (hV.fromSpec (genericPoint (Spec Γ(X,V)))) =
    chartZero k (Spec.map (CommRingCat.ofHom (evalChart k p z h)) (genericPoint (Spec Γ(X,V)))) at e
  rwa [h₁,h₂] at e

private theorem affine_generic_not_closed :
    ¬ IsClosed ({genericPoint (affineLine k)} : Set (affineLine k)) := by
  intro h
  change IsClosed ({genericPoint (Spec (CommRingCat.of k[X]))} : Set (PrimeSpectrum k[X])) at h
  rw [genericPoint_eq_bot_of_affine] at h
  have hm : (⊥ : Ideal k[X]).IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp h
  exact Polynomial.not_isField k (Ring.isField_iff_maximal_bot.mpr hm)

theorem finite_projection [IsProper p] [NoetherianSpace X] (hX : topologicalKrullDim X ≤ 1)
    (hv : ∀ x : X, ValuationRing (X.presheaf.stalk x)) (hz : z ≠ 0)
    (he : Function.Injective (Polynomial.eval₂RingHom (fieldCoefficients k p z) z)) :
    IsFinite (toLine z k p hv hz) := by
  letI := toLine_proper k p z hv hz
  refine CycleQ2ProperCurveFiniteFibres.finite_map _ hX ?_
  rw [generic_image k p z hv hz he]
  intro h
  apply affine_generic_not_closed k
  have e : (chartZero k) ⁻¹' ({chartZero k (genericPoint (affineLine k))} : Set (line k)) =
      {genericPoint (affineLine k)} := by
    ext x
    simpa only [Set.mem_preimage,Set.mem_singleton_iff] using
      ((chartZero k).isOpenEmbedding.injective.eq_iff :
        chartZero k x = chartZero k (genericPoint (affineLine k)) ↔ _)
  exact e ▸ h.preimage (chartZero k).continuous

end CycleQ2RationalFunctionFiniteMap

#print axioms CycleQ2RationalFunctionFiniteMap.finite_projection

end

section

/-!
# The upper hypercohomology of a two-term complex as a quotient

The upper edge of the derived triangle is surjective once degree two
of the function term vanishes. Its kernel is the image of degree-one
cohomology under the original differential. This describes the upper
group even when degree one of the function term is nonzero.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2TwoTermTopQuotient

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CategoryTheory.Pretriangulated
open CycleQ2TwoTermTopComparison (shiftedTriangle topGroup topMap topMap_surjective)

variable {C : Type*} [Category C] [Abelian C] [HasExt.{1} C] [HasDerivedCategory.{1} C]
  {A B : C} (d : A ⟶ B) (X : C)

private abbrev E := DerivedCategory.singleFunctor C 0

def upperDerivative : Ext X A 1 →+ Ext X B 1 where
  toFun x := Ext.homEquiv.symm (x.hom ≫ (shiftedTriangle d).mor₁)
  map_zero' := by
    apply Ext.homEquiv.injective
    simp only [Equiv.apply_symm_apply,Ext.zero_hom,zero_comp]
  map_add' x y := by
    apply Ext.homEquiv.injective
    simp only [Equiv.apply_symm_apply,Ext.add_hom,Preadditive.add_comp]

theorem upperDerivative_hom (x : Ext X A 1) :
    (upperDerivative d X x).hom = x.hom ≫ (shiftedTriangle d).mor₁ :=
  Equiv.apply_symm_apply Ext.homEquiv _

theorem topMap_zero_iff (b : Ext X B 1) :
    topMap d X b = 0 ↔ ∃ a : Ext X A 1, upperDerivative d X a = b := by
  have hT : shiftedTriangle d ∈ distTriang (DerivedCategory C) :=
    Triangle.shift_distinguished _ (DerivedCategory.mappingCone_triangle_distinguished _) _
  constructor
  · intro hb
    obtain ⟨g,hg⟩ := Triangle.coyoneda_exact₂ _ hT b.hom hb
    refine ⟨Ext.homEquiv.symm g,Ext.homEquiv.injective ?_⟩
    change (upperDerivative d X (Ext.homEquiv.symm g)).hom = b.hom
    rw [upperDerivative_hom]
    change Ext.homEquiv (Ext.homEquiv.symm g) ≫ (shiftedTriangle d).mor₁ = b.hom
    rw [Equiv.apply_symm_apply,hg]
  · rintro ⟨a,rfl⟩
    change (upperDerivative d X a).hom ≫ (shiftedTriangle d).mor₂ = 0
    rw [upperDerivative_hom,Category.assoc,comp_distTriang_mor_zero₁₂ _ hT,comp_zero]

/-- An additive functional that kills the derived upper differential
descends uniquely to actual degree-two hypercohomology. -/
def descend {M : Type*} [AddCommGroup M] (h₂ : Subsingleton (Ext X A 2))
    (f : Ext X B 1 →+ M) (hf : ∀ a : Ext X A 1, f (upperDerivative d X a) = 0) :
    topGroup d X →+ M :=
  AddMonoidHom.liftOfSurjective (topMap d X) (topMap_surjective d X h₂)
    ⟨f,fun b hb => by
      obtain ⟨a,rfl⟩ := (topMap_zero_iff d X b).mp hb
      exact hf a⟩

theorem descend_topMap {M : Type*} [AddCommGroup M] (h₂ : Subsingleton (Ext X A 2))
    (f : Ext X B 1 →+ M) (hf : ∀ a : Ext X A 1, f (upperDerivative d X a) = 0)
    (b : Ext X B 1) :
    descend d X h₂ f hf (topMap d X b) = f b := by
  simp [descend]

end CycleQ2TwoTermTopQuotient

#print axioms CycleQ2TwoTermTopQuotient.topMap_zero_iff
#print axioms CycleQ2TwoTermTopQuotient.descend_topMap

end
