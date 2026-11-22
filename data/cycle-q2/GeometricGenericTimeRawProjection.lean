import Proposal.GeometricGenericTimeAffineCharts
import Proposal.GeometricHodgeThreefoldIncidence
import Proposal.GeometricMarkedPivotEquations

/-!
# Raw homogeneous coordinates of the generic time product charts

On each weight-one affine chart over an affine time test, project the actual
curve–threefold product to the original universal sextic. Its map on the raw
degree-zero homogeneous functions is coefficient base change after ordinary
dehomogenization. Both steps of coefficient base change come from the chart
isomorphisms of the original scheme pullbacks.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 1000000

noncomputable section


namespace CycleQ2GenericTimeRawProjection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2GenericTimeProductChart (atTime inProduct)
open CycleQ2GenericTimeCoefficients (ground)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient genericPoint genericField)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw)
open CycleQ2LiteralIncidenceRelativeCorrespondence (ambientStructure)
open CycleQ2LiteralIncidenceCylinderMap (universalPoint universalAmbientToBase)
open CycleQ2NativeSexticChartComparison (toAffine toAffine_fraction toAffine_inclusion)
open CycleQ2LiteralAbelJacobiQChartSource (sexticInclusion)
open CycleQ2LiteralAbelJacobiQCoordinates (SexticChart sexticFraction)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2NativeGenericSmooth (Fibre chartIn nativeComparison)
open CycleQ2MonicGenericAmbientChart (genericCoeff rawPoint Raw)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2MarkedPivotSource (congr_snd tensor_second)
open CycleQ2MonicGenericAmbientChartBaseChange (tensorInclusion tensorChartEquiv)
open CycleQ2GeometricHodgeThreefold (toBase threefold coordinateOpen)
open CycleQ2HodgeEulerChartBinding (affineChart)
open CycleQ2HodgeEuler (chart dehom chartMap)
open CycleQ2GeometricHodgeThreefoldIncidence (nativeIso)
open CycleQ2GenericSexticGradient (CoeffRing)
open scoped TensorProduct

def changeChart {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
    (φ : CoeffRing →+* k) (i : Fin 4) :
    chart φ i →+* chart ((algebraMap k S).comp φ) i :=
  (tensorChartEquiv (S := S) φ i).toRingHom.comp
    (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := chart φ i)).toRingHom

theorem changeChart_polynomial {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
    (φ : CoeffRing →+* k) (i : Fin 4) (p : MvPolynomial (Fin 4) k) :
    changeChart (S := S) φ i (CycleQ2HodgeEuler.chartMap φ i p) =
      CycleQ2HodgeEuler.chartMap ((algebraMap k S).comp φ) i (MvPolynomial.map (algebraMap k S) p) := by
  change CycleQ2HodgeEuler.chartMap ((algebraMap k S).comp φ) i
    (MvPolynomial.algebraTensorAlgEquiv k S ((1 : S) ⊗ₜ[k] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul,one_smul]

private abbrev rawOpen (i : Fin 4) : Spec (CommRingCat.of (chart rawPoint i)) ⟶ threefold rawPoint :=
  (affineChart rawPoint i).inv ≫ (coordinateOpen rawPoint i).ι

private local instance : Algebra Raw genericField := genericCoeff.toAlgebra

private abbrev rawBase := Spec.map (CommRingCat.ofHom genericCoeff)
private abbrev rawAmbient := toBase rawPoint

theorem chartIn_raw (i : Fin 4) :
    chartIn i ≫ pullback.snd rawBase rawAmbient =
      Spec.map (CommRingCat.ofHom (changeChart (S := genericField) rawPoint i)) ≫ rawOpen i := by
  change Spec.map (CommRingCat.ofHom (tensorChartEquiv (S := genericField) rawPoint i).toRingHom) ≫
    tensorInclusion (S := genericField) rawAmbient (rawOpen i)
      (CycleQ2HodgeEulerChartBinding.affineChart_overBase rawPoint i) ≫ pullback.snd rawBase rawAmbient = _
  erw [tensor_second,← Spec.map_comp_assoc]
  rfl

abbrev toRawAmbient : genericAmbient ⟶ CycleQ2IncidenceFamilyContainment.weightedThreefold universalPoint :=
  pullback.fst ambientStructure genericPoint ≫ pullback.snd toRaw universalAmbientToBase

private theorem nested_raw {A Z S K Y : Scheme} {f : S ⟶ Z} {g : Y ⟶ Z} {x : K ⟶ S}
    {p : A ⟶ K} {q : A ⟶ Y} (h : IsPullback p q (x ≫ f) g) :
    (h.isoPullback ≪≫ (pullbackRightPullbackFstIso f g x).symm ≪≫
      pullbackSymmetry x (pullback.fst f g)).hom ≫
      pullback.fst (pullback.fst f g) x ≫ pullback.snd f g = q := by
  simp only [Iso.trans_hom,Iso.symm_hom,Category.assoc,pullbackSymmetry_hom_comp_fst_assoc,
    pullbackRightPullbackFstIso_inv_snd_snd,IsPullback.isoPullback_hom_snd]

theorem comparison_raw :
    nativeComparison.hom ≫ toRawAmbient =
      pullback.snd rawBase rawAmbient ≫ (nativeIso universalPoint).hom := by
  unfold nativeComparison toRawAmbient
  exact nested_raw _

variable {C D : Scheme.{0}} {R : Type} [CommRing R]
  (c : C ⟶ Spec (CommRingCat.of genericField)) (j : D ⟶ C) (u : Spec (CommRingCat.of R) ⟶ D)

theorem inProduct_snd (i : Fin 4) :
    inProduct c j u i ≫ pullback.snd c ambientToField =
      atTime c j u i ≫ pullback.snd (u ≫ j ≫ c) ambientToField := by
  simp only [inProduct,Category.assoc,pullbackRightPullbackFstIso_inv_snd_snd,congr_snd]

theorem atTime_snd (i : Fin 4) :
    letI : Algebra genericField R := (ground c j u).toAlgebra
    atTime c j u i ≫ pullback.snd (u ≫ j ≫ c) ambientToField =
      Spec.map (CommRingCat.ofHom (changeChart (S := R) coeff i)) ≫ chartIn i ≫ nativeComparison.hom := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  change (Spec.map (CommRingCat.ofHom (tensorChartEquiv (S := R) coeff i).toRingHom) ≫
    tensorInclusion (S := R) ambientToField (chartIn i ≫ nativeComparison.hom) _ ≫
    (pullback.congrHom (Spec.map_preimage _) (rfl : ambientToField = ambientToField)).hom) ≫ _ = _
  erw [Category.assoc,Category.assoc,congr_snd,tensor_second,← Spec.map_comp_assoc]
  rfl

theorem product_raw (i : Fin 4) :
    letI : Algebra genericField R := (ground c j u).toAlgebra
    inProduct c j u i ≫ pullback.snd c ambientToField ≫ toRawAmbient =
      Spec.map (CommRingCat.ofHom ((changeChart (S := R) coeff i).comp
        (changeChart (S := genericField) rawPoint i))) ≫ rawOpen i ≫ (nativeIso universalPoint).hom := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  rw [← Category.assoc,inProduct_snd,atTime_snd,Category.assoc,Category.assoc,comparison_raw,
    ← Category.assoc (chartIn i),chartIn_raw,Category.assoc,← Spec.map_comp_assoc]
  rfl

def rawFunctions (i : Fin 4) :
    SexticChart universalPoint i →+* chart ((ground c j u).comp coeff) i :=
  letI : Algebra genericField R := (ground c j u).toAlgebra
  ((changeChart (S := R) coeff i).comp (changeChart (S := genericField) rawPoint i)).comp
    (toAffine universalPoint i)

theorem rawFunctions_fraction (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) Raw)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    rawFunctions c j u i (sexticFraction universalPoint i n p hp) =
      chartMap ((ground c j u).comp coeff) i
        (MvPolynomial.map ((ground c j u).comp genericCoeff) (dehom i p)) := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  change changeChart (S := R) coeff i (changeChart (S := genericField) rawPoint i
    (toAffine universalPoint i (sexticFraction universalPoint i n p hp))) = _
  rw [toAffine_fraction,changeChart_polynomial]
  change changeChart (S := R) coeff i (chartMap coeff i _) = _
  rw [changeChart_polynomial,MvPolynomial.map_map]
  rfl

theorem inProduct_raw_projection (i : Fin 4) :
    inProduct c j u i ≫ pullback.snd c ambientToField ≫ toRawAmbient =
      Spec.map (CommRingCat.ofHom (rawFunctions c j u i)) ≫ sexticInclusion universalPoint i := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  rw [product_raw]
  change Spec.map _ ≫ ((affineChart rawPoint i).inv ≫ (coordinateOpen rawPoint i).ι) ≫
    (nativeIso universalPoint).hom = _
  rw [Category.assoc (affineChart rawPoint i).inv,toAffine_inclusion,← Spec.map_comp_assoc]
  rfl

end CycleQ2GenericTimeRawProjection

#print axioms CycleQ2GenericTimeRawProjection.inProduct_raw_projection
#print axioms CycleQ2GenericTimeRawProjection.rawFunctions_fraction
