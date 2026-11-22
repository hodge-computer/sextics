import Proposal.GeometricHodgeThreefold
import Proposal.GeometricHodgeEulerChartBinding
import Proposal.GeometricLiteralAbelJacobiQChartSource

/-!
# Binding the full sextic to the original incidence family

For an incidence parameter point, evaluating the independent sextic
coefficients returns its actual defining polynomial. Equality of the
homogeneous ideals identifies the two projective schemes, their structure
morphisms and all four weight-one coordinate opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefoldIncidence

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
  CycleQ2IncidenceGenericPointSemantics CycleQ2IncidenceImageLine
  CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold CycleQ2IncidenceFamilyContainment
open CycleQ2GenericSexticGradient (CoeffRing universalF)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {R : Type} [CommRing R] [Algebra ℂ R] (y : ParameterIndex → R)

def sexticEval : CoeffRing →+* R := (aeval (pointSextic y)).toRingHom

theorem equation_eq : equation (sexticEval y) = pointEquationF y := by
  rw [equation, universalF, map_fullInvariantPolynomial, pointEquationF, pointMap_familyF]
  congr 1
  funext j
  simp [sexticEval]

def nativeOpen (i : Fin 4) : (weightedThreefold y).Opens :=
  Proj.basicOpen (sexticGrade y) (Ideal.Quotient.mk (sexticIdeal y) (X i.castSucc))

private structure Model (R : Type) [CommRing R] where
  space : Scheme
  structureMap : space ⟶ Spec (CommRingCat.of R)
  opens : Fin 4 → space.Opens

private def model (I : {I : Ideal (MvPolynomial (Fin 5) R) // I.IsHomogeneous (PolynomialGrade R)}) :
    Model R := by
  let g := CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade (PolynomialGrade R) I.val
  letI : GradedRing g := CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing _ _ I.property
  exact ⟨Proj g, Proj.toSpecZero g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (g 0))),
    fun i => Proj.basicOpen g (Ideal.Quotient.mk I.val (X i.castSucc))⟩

private def fromFamily : Model R :=
  ⟨threefold (sexticEval y), toBase (sexticEval y), coordinateOpen (sexticEval y)⟩

private def fromPoint : Model R :=
  ⟨weightedThreefold y, weightedThreefoldToBase y, nativeOpen y⟩

private theorem model_eq : fromFamily y = fromPoint y := by
  let I := Ideal.span ({equation (sexticEval y)} : Set (MvPolynomial (Fin 5) R))
  have hi : I.IsHomogeneous (PolynomialGrade R) :=
    Ideal.homogeneous_span _ _ (by
      rintro p (rfl : p = equation (sexticEval y))
      exact ⟨6, equation_homogeneous _⟩)
  change model ⟨I, hi⟩ = model ⟨sexticIdeal y, sexticIdeal_homogeneous y⟩
  apply congrArg model
  apply Subtype.ext
  exact congrArg (fun p : MvPolynomial (Fin 5) R => Ideal.span {p}) (equation_eq y)

private def modelIso {a b : Model R} (h : a = b) : a.space ≅ b.space :=
  eqToIso (congrArg Model.space h)

def nativeIso : threefold (sexticEval y) ≅ weightedThreefold y := modelIso (model_eq y)

theorem nativeIso_overBase : (nativeIso y).hom ≫ weightedThreefoldToBase y = toBase (sexticEval y) := by
  have e {a b : Model R} (h : a = b) : (modelIso h).hom ≫ b.structureMap = a.structureMap := by
    subst b
    simp [modelIso]
  exact e (model_eq y)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 4500 in
theorem nativeIso_preimage (i : Fin 4) :
    (nativeIso y).hom ⁻¹ᵁ nativeOpen y i = coordinateOpen (sexticEval y) i := by
  have e {a b : Model R} (h : a = b) : (modelIso h).hom ⁻¹ᵁ b.opens i = a.opens i := by
    subst b
    simp [modelIso]
  exact @e (fromFamily y) (fromPoint y) (model_eq y)

end CycleQ2GeometricHodgeThreefoldIncidence
end

#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_overBase
#print axioms CycleQ2GeometricHodgeThreefoldIncidence.nativeIso_preimage

/-! Native homogeneous chart maps, placed before the fixed-fiber trace
comparison so that the original Proj morphism can be reused there. -/

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
end

#print axioms CycleQ2NativeSexticChartComparison.toAffine_inclusion
