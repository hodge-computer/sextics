import Proposal.GeometricGenericTimeAffineCharts
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

namespace CycleQ2NativeSexticChartComparison

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceUniversalChart CycleQ2IncidenceFamilyContainment
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2HodgeEuler (chart chartMap dehom dehom_X_self chartMap_F)
open CycleQ2HodgeEulerChartBinding (chartEquiv fraction affineChart)
open CycleQ2LiteralAbelJacobiQChartSource (sexticInclusion)
open CycleQ2LiteralAbelJacobiQCoordinates (SexticChart sexticFraction sexticX)
open CycleQ2GeometricProjectiveCurve.HomogeneousQuotient
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R : Type} [CommRing R]

private abbrev HI (R : Type) [CommRing R] :=
  { I : Ideal (MvPolynomial (Fin 5) R) // I.IsHomogeneous (PolynomialGrade R) }
private abbrev grades (I : HI R) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade (PolynomialGrade R) I.val
private instance modelGradedRing (I : HI R) : GradedRing (grades I) := gradedRing _ _ I.property
private abbrev model (I : HI R) : Scheme := Proj (grades I)
private abbrev xi (I : HI R) (i : Fin 4) := Ideal.Quotient.mk I.val (X i.castSucc)

private theorem xi_grade (I : HI R) (i : Fin 4) : xi I i ∈ grades I 1 := by
  exact ⟨X i.castSucc,by
    change (X i.castSucc : MvPolynomial (Fin 5) R).IsWeightedHomogeneous geometricWeight 1
    simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc] using
      isWeightedHomogeneous_X R geometricWeight i.castSucc,rfl⟩

private abbrev affineRing (I : HI R) (i : Fin 4) := Away (grades I) (xi I i)
private def away (I : HI R) (i : Fin 4) : Spec (CommRingCat.of (affineRing I i)) ⟶ model I :=
  Proj.awayι (grades I) (xi I i) (xi_grade I i) (by decide)

section Evaluation

variable {U : Type} [CommRing U] (f : MvPolynomial (Fin 5) R →+* U)
    (I : Ideal (MvPolynomial (Fin 5) R)) (hf : I ≤ RingHom.ker f)

private def onCone : MvPolynomial (Fin 5) R ⧸ I →+* U :=
  Ideal.Quotient.lift I f hf

private theorem onCone_X (i : Fin 4) (hx : f (X i.castSucc) = 1) :
    onCone f I hf (Ideal.Quotient.mk I (X i.castSucc)) = 1 := hx

private def localEval (i : Fin 4) (hx : f (X i.castSucc) = 1) :
    Localization.Away (Ideal.Quotient.mk I (X i.castSucc)) →+* U :=
  Localization.awayLift (onCone f I hf) (Ideal.Quotient.mk I (X i.castSucc))
    (isUnit_iff_exists_inv.mpr ⟨1,by rw [onCone_X f I hf i hx,mul_one]⟩)

private theorem localEval_mk (i : Fin 4) (hx : f (X i.castSucc) = 1)
    (n : ℕ) (p : MvPolynomial (Fin 5) R) :
    localEval f I hf i hx (Localization.mk (Ideal.Quotient.mk I p)
      ⟨(Ideal.Quotient.mk I (X i.castSucc)) ^ n,n,rfl⟩) = f p := by
  unfold localEval
  trans onCone f I hf (Ideal.Quotient.mk I p)
  · simpa only [one_pow,mul_one] using Localization.awayLift_mk
      (onCone f I hf) (Ideal.Quotient.mk I (X i.castSucc)) (Ideal.Quotient.mk I p)
      1 (by rw [onCone_X f I hf i hx,mul_one]) n
  · rfl

private abbrev Allowed := {I : HI R // I.val ≤ RingHom.ker f}

private structure ChartMorphism (U : Type) [CommRing U] where
  target : Scheme.{0}
  map : Spec (CommRingCat.of U) ⟶ target

private def fromIdeal (i : Fin 4) (hx : f (X i.castSucc) = 1) (J : Allowed f) :
    ChartMorphism U :=
  let g := (localEval f J.val.val J.property i hx).comp
    (algebraMap (affineRing J.val i) (Localization.Away (xi J.val i)))
  ⟨model J.val,Spec.map (CommRingCat.ofHom g) ≫ away J.val i⟩

private theorem transport {A B : ChartMorphism U} (h : A = B) (e : A.target ≅ B.target)
    (he : e = eqToIso (congrArg (fun M : ChartMorphism U => M.target) h)) :
    A.map ≫ e.hom = B.map := by
  subst B
  subst e
  simp

end Evaluation

attribute [-instance] modelGradedRing

variable [Algebra ℂ R] (y : ParameterIndex → R)

private def moving : HI R :=
  ⟨Ideal.span {equation (sexticEval y)},Ideal.homogeneous_span _ _ (by
    rintro p (rfl : p = equation (sexticEval y))
    exact ⟨6,equation_homogeneous _⟩)⟩
private def point : HI R := ⟨sexticIdeal y,sexticIdeal_homogeneous y⟩
private theorem same : moving y = point y := Subtype.ext
  (congrArg (fun q : MvPolynomial (Fin 5) R => Ideal.span {q}) (equation_eq y))

private def evaluate (i : Fin 4) :
    MvPolynomial (Fin 5) R →+* chart (sexticEval y) i :=
  ((chartMap (sexticEval y) i).comp (dehom i)).toRingHom

private theorem evaluate_X (i : Fin 4) : evaluate y i (X i.castSucc) = 1 := by
  change chartMap (sexticEval y) i (dehom i (X i.castSucc)) = 1
  rw [dehom_X_self,map_one]

private theorem movingKer (i : Fin 4) : (moving y).val ≤ RingHom.ker (evaluate y i) := by
  change Ideal.span {equation (sexticEval y)} ≤ RingHom.ker (evaluate y i)
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  exact chartMap_F (sexticEval y) i

private theorem nativeKer (i : Fin 4) : sexticIdeal y ≤ RingHom.ker (evaluate y i) := by
  change (point y).val ≤ _
  rw [← same y]
  exact movingKer y i

private def familyIdeal (i : Fin 4) : Allowed (evaluate y i) := ⟨moving y,movingKer y i⟩
private def nativeIdeal (i : Fin 4) : Allowed (evaluate y i) := ⟨point y,nativeKer y i⟩

private theorem allowed_eq (i : Fin 4) : familyIdeal y i = nativeIdeal y i := Subtype.ext (same y)

/-- The degree-zero localization maps directly to the ordinary dehomogenized ring
by sending the inverted homogeneous chart coordinate to one. -/
def toAffine (i : Fin 4) : SexticChart y i →+* chart (sexticEval y) i :=
  (localEval (evaluate y i) (sexticIdeal y) (nativeKer y i) i (evaluate_X y i)).comp
    (algebraMap (SexticChart y i) (Localization.Away (sexticX y i)))

theorem toAffine_fraction (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    toAffine y i (sexticFraction y i n p hp) = chartMap (sexticEval y) i (dehom i p) := by
  change localEval (evaluate y i) (sexticIdeal y) (nativeKer y i) i (evaluate_X y i)
    (Localization.mk (Ideal.Quotient.mk (sexticIdeal y) p) ⟨sexticX y i ^ n,n,rfl⟩) = _
  exact localEval_mk (evaluate y i) (sexticIdeal y) (nativeKer y i) i (evaluate_X y i) n p

private def familyAway (i : Fin 4) :
    Spec (CommRingCat.of (ChartRing (sexticEval y) i)) ⟶ threefold (sexticEval y) :=
  Proj.awayι (CycleQ2GeometricHodgeThreefold.grade (sexticEval y)) (coord (sexticEval y) i.castSucc)
    (weightOne_mem_grade (sexticEval y) i) (by decide)

private def familyData (i : Fin 4) : ChartMorphism (chart (sexticEval y) i) :=
  ⟨threefold (sexticEval y),Spec.map (CommRingCat.ofHom (chartEquiv (sexticEval y) i).toRingHom) ≫
    familyAway y i⟩

private def pointData (i : Fin 4) : ChartMorphism (chart (sexticEval y) i) :=
  ⟨weightedThreefold y,Spec.map (CommRingCat.ofHom (toAffine y i)) ≫ sexticInclusion y i⟩

private theorem data_eq (i : Fin 4) : familyData y i = pointData y i := by
  change fromIdeal (evaluate y i) i (evaluate_X y i) (familyIdeal y i) =
    fromIdeal (evaluate y i) i (evaluate_X y i) (nativeIdeal y i)
  exact congrArg (fromIdeal (evaluate y i) i (evaluate_X y i)) (allowed_eq y i)

private theorem affineChart_toAway (i : Fin 4) :
    (affineChart (sexticEval y) i).inv ≫ (coordinateOpen (sexticEval y) i).ι =
      Spec.map (CommRingCat.ofHom (chartEquiv (sexticEval y) i).toRingHom) ≫ familyAway y i := by
  change (Spec.map (CommRingCat.ofHom (chartEquiv (sexticEval y) i).toRingHom) ≫
    (Proj.basicOpenIsoSpec (CycleQ2GeometricHodgeThreefold.grade (sexticEval y))
    (coord (sexticEval y) i.castSucc) (weightOne_mem_grade (sexticEval y) i) (by decide)).inv) ≫
    (Proj.basicOpen (CycleQ2GeometricHodgeThreefold.grade (sexticEval y))
      (coord (sexticEval y) i.castSucc)).ι = _
  rw [Category.assoc,Proj.basicOpenIsoSpec_inv_ι]
  rfl

private theorem nativeIso_eqToIso (h : threefold (sexticEval y) = weightedThreefold y) :
    nativeIso y = eqToIso h := rfl

theorem toAffine_inclusion (i : Fin 4) :
    (affineChart (sexticEval y) i).inv ≫ (coordinateOpen (sexticEval y) i).ι ≫ (nativeIso y).hom =
      Spec.map (CommRingCat.ofHom (toAffine y i)) ≫ sexticInclusion y i := by
  rw [← Category.assoc,affineChart_toAway]
  exact @transport _ _ (familyData y i) (pointData y i) (data_eq y i) (nativeIso y)
    (nativeIso_eqToIso y (congrArg ChartMorphism.target (data_eq y i)))

end CycleQ2NativeSexticChartComparison

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
