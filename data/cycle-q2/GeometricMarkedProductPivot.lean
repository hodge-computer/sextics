import Proposal.GeometricMarkedPivotEquations
import Proposal.GeometricGenericTimeRawProjection
import Proposal.GeometricIncidenceLogarithmicSpecialization
import Mathlib.RingTheory.Localization.BaseChange

/-! The literal two-equation affine chart inside the same marked projective graph.
The ambient chart is open in the product with the proper parameter curve. Its
cubic and row are the pullbacks of the generic logarithmic representative.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2MarkedPivotRing

open MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CycleQ2IncidenceDensePivot CycleQ2IncidenceDehomogenizedChart
open CycleQ2ShiftedChartCoordinates (unshift unshift_dehomogenize)
open CycleQ2HodgeEuler (chart chartMap dehom)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericField)
open CycleQ2IncidenceEtaleParameter (incidencePoint ParameterAlgebra)
open CycleQ2GeometricIncidenceProj
open CycleQ2MonicGenericSmooth (coeff)
open scoped TensorProduct

variable {R : Type} [CommRing R] [Algebra ℂ R] (i : Fin 4)
private def inverseShift : MvPolynomial (Fin 4) R →ₐ[R] ChartPolynomial R :=
  aeval fun j => dehomogenize i (X (i.castSucc.succAbove j))

private theorem inverse_dehom (w : MvPolynomial (Fin 5) R) :
    inverseShift i (dehom i w) = dehomogenize i w := by
  have h : (inverseShift (R := R) i).comp (dehom i) = dehomogenize i := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i.castSucc ?_ (fun m => ?_) j
    · simp only [AlgHom.comp_apply,CycleQ2HodgeEuler.dehom_X_self,map_one,dehomogenize_self]
    · rw [AlgHom.comp_apply,CycleQ2HodgeEuler.dehom_X_succAbove,inverseShift,aeval_X]
  exact DFunLike.congr_fun h w

private def unshiftEquiv : ChartPolynomial R ≃ₐ[R] MvPolynomial (Fin 4) R :=
  AlgEquiv.ofAlgHom (unshift i) (inverseShift i) (by
    apply MvPolynomial.algHom_ext
    intro x
    rw [AlgHom.comp_apply,inverseShift,aeval_X,unshift_dehomogenize,CycleQ2HodgeEuler.dehom_X_succAbove]
    rfl) (by
    apply MvPolynomial.algHom_ext
    intro x
    change inverseShift i (unshift i (X x)) = X x
    cases x with
    | none => rw [← dehomogenize_normal i,unshift_dehomogenize,inverse_dehom]
    | some j => rw [← dehomogenize_succAbove i j,unshift_dehomogenize,inverse_dehom])

variable [Algebra genericField R] [Algebra P R]

private abbrev φ := (algebraMap genericField R).comp coeff
private abbrev A := ambient i
private abbrev target := chart (φ (R := R)) i
private abbrev polynomialEquiv : R ⊗[P] ChartPolynomial P ≃ₐ[R] MvPolynomial (Fin 4) R :=
  (MvPolynomial.algebraTensorAlgEquiv P R).trans (unshiftEquiv i)

omit [Algebra genericField R] in
private theorem polynomialEquiv_tmul (w : ChartPolynomial P) :
    polynomialEquiv i (1 ⊗ₜ[P] w) = unshift i (MvPolynomial.map (algebraMap P R) w) := by
  change unshift i ((MvPolynomial.algebraTensorAlgEquiv P R) (1 ⊗ₜ[P] w)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul,one_smul]

open CycleQ2IncidenceTimeCurve CycleQ2LiteralIncidenceCylinderMap CycleQ2MonicGenericAmbientChart
  CycleQ2GeometricHodgeThreefold
variable (hα : (algebraMap P R).comp sexticToParameter =
    (algebraMap genericField R).comp genericCoeff)

include hα in
private theorem polynomialEquiv_equation : polynomialEquiv (R := R) i (1 ⊗ₜ[P] F i) =
    CycleQ2HodgeEuler.F (φ (R := R)) i := by
  let F₀ := pointEquationF incidencePoint
  change polynomialEquiv i (1 ⊗ₜ[P] dehomogenize i F₀) = _
  rw [polynomialEquiv_tmul,CycleQ2IncidenceChartSeedFiber.map_dehomogenize,unshift_dehomogenize]
  dsimp only [F₀]
  rw [← universal_to_incidence,MvPolynomial.map_map,hα,← CycleQ2GeometricHodgeThreefoldIncidence.equation_eq,
    equation,MvPolynomial.map_map]
  rfl

/-- Before the matrix pivot, the base-changed incidence affine hypersurface
is the native chart of the original generic ambient threefold. -/
def chartEquiv : R ⊗[P] A i ≃ₐ[R] target (R := R) i := by
  let I := (Ideal.span {F i} : Ideal (ChartPolynomial P))
  let J := (Ideal.span {CycleQ2HodgeEuler.F (φ (R := R)) i} : Ideal (MvPolynomial (Fin 4) R))
  let q := Algebra.TensorProduct.includeRight (R := P) (A := R) (B := ChartPolynomial P)
  let e := polynomialEquiv (R := R) i
  have hI : (I.map q.toRingHom).map e.toRingHom = J := by
    simp only [I,J,Ideal.map_span,Set.image_singleton]
    exact congrArg (fun w => Ideal.span {w}) (polynomialEquiv_equation i hα)
  exact (Algebra.TensorProduct.tensorQuotientEquiv (R := P) R (ChartPolynomial P) R I).trans
    (Ideal.quotientEquivAlg _ J e hI.symm)

theorem chartEquiv_tmul (w : ChartPolynomial P) :
    chartEquiv i hα (1 ⊗ₜ[P] mk i w) =
      chartMap (φ (R := R)) i (unshift i (MvPolynomial.map (algebraMap P R) w)) := by
  change _ = Ideal.Quotient.mk _ _
  simp only [chartEquiv,AlgEquiv.trans_apply,Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul]
  exact congrArg (Ideal.Quotient.mk _) (polynomialEquiv_tmul (R := R) i w)


section Localize
variable {P S A B : Type} [CommRing P] [CommRing S] [CommRing A] [CommRing B]
  [Algebra P S] [Algebra P A] [Algebra S B] (v : A) (e : S ⊗[P] A ≃ₐ[S] B)

private def localizedMap : B →ₐ[S] S ⊗[P] Localization.Away v :=
  let L := IsLocalization.Away.tensorProductEquivTMulRight P S v (Localization.Away v)
  let g := IsScalarTower.toAlgHom S (S ⊗[P] A) (Localization.Away ((1:S) ⊗ₜ[P] v))
  L.symm.toAlgHom.comp (g.comp e.symm.toAlgHom)

private theorem localizedMap_open : IsOpenImmersion (Spec.map (CommRingCat.ofHom (localizedMap v e).toRingHom)) := by
  let L := IsLocalization.Away.tensorProductEquivTMulRight P S v (Localization.Away v)
  let g := Spec.map (CommRingCat.ofHom (algebraMap (S ⊗[P] A) (Localization.Away ((1:S) ⊗ₜ[P] v))))
  let : IsOpenImmersion g := IsOpenImmersion.of_isLocalization ((1:S) ⊗ₜ[P] v)
  have h : Spec.map (CommRingCat.ofHom (localizedMap v e).toRingHom) =
      (Scheme.Spec.mapIso L.toRingEquiv.toCommRingCatIso.op).inv ≫ g ≫
        (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).inv := by
    change _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp_assoc,← Spec.map_comp]
    rfl
  rw [h]
  infer_instance

private theorem localizedMap_mk (b : A) :
    localizedMap v e (e ((1 : S) ⊗ₜ[P] b)) = (1 : S) ⊗ₜ[P] algebraMap A (Localization.Away v) b := by
  let L := IsLocalization.Away.tensorProductEquivTMulRight P S v (Localization.Away v)
  change L.symm (algebraMap _ _ (e.symm (e _))) = _
  rw [e.symm_apply_apply]
  apply L.injective
  rw [L.apply_symm_apply]
  exact (IsLocalization.Away.tensorProductEquivTMulRight_tmul (R := P) (S := S) (A := A) (g := v) (B := Localization.Away v) (x := 1) (a := b)).symm

end Localize

section Actual
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2LiteralIncidenceRelativeSpread (Time)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw)
open CycleQ2LiteralIncidenceRelativeCompletion (Completion structureMap inclusion)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericPoint)
open CycleQ2GenericTimeCoefficients (parameter ground)
open CycleQ2GenericTimeProductChart (inProduct)
open CycleQ2LiteralAbelJacobiQCoordinates (sexticFraction SexticChart)
open CycleQ2LiteralAbelJacobiQChartSource (sexticInclusion)

variable {V : parameterScheme.Opens} {C D : Scheme.{0}} {S : CommRingCat.{0}}
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ inclusion V) (u : Spec S ⟶ D)

abbrev tensorAmbient (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  S ⊗[P] Ambient i p

private abbrev native (i : Fin 4) := chart ((ground c j u).comp coeff) i

def nativeToTensor (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    native c j u i →+* tensorAmbient a u i p :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  letI : Algebra genericField S := (ground c j u).toAlgebra
  letI : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  let e : (S ⊗[P] A i) ≃ₐ[S] native c j u i := chartEquiv (R := S) i (CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u)
  (localizedMap (pivot i p) e).toRingHom

private theorem nativeToTensor_open (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (nativeToTensor r c hc j a ha u i p))) := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  let : Algebra genericField S := (ground c j u).toAlgebra
  let : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  let e : (S ⊗[P] A i) ≃ₐ[S] native c j u i := chartEquiv (R := S) i (CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u)
  exact localizedMap_open (pivot i p) e

/-- The tensor-product ambient ring of the actual two-equation kernel is an affine
open of the very same product with the full parameter curve. -/
def inActualProduct (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  Spec.map (CommRingCat.ofHom (nativeToTensor r c hc j a ha u i p)) ≫ inProduct c j u i

instance [IsOpenImmersion u] [IsOpenImmersion j] (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    IsOpenImmersion (inActualProduct r c hc j a ha u i p) := by
  let := nativeToTensor_open r c hc j a ha u i p
  unfold inActualProduct
  infer_instance


open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2MarkedPivotSource (chartToTest testOriginal)
open CycleQ2GenericSmoothCurveGraph (TestSurface fromTest test_square test_to_original_ambient)
open CycleQ2LiteralIncidenceRelativeSpread (curveMap)
open CycleQ2GenericSmoothCurveGraph (embeddingGeneric)
open CycleQ2LiteralIncidenceRelativeCylinder (toOriginal)

abbrev tensorCurve (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  S ⊗[P] Curve t i p

def restriction (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    tensorAmbient a u i p →+* tensorCurve a u t i p :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  (Algebra.TensorProduct.map (AlgHom.id P S) (inclusionMap t i p)).toRingHom

theorem restriction_surjective (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    Function.Surjective (restriction a u t i p) := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  exact LinearMap.lTensor_surjective S (g := (inclusionMap t i p).toLinearMap) (inclusion_surjective t i p)

private theorem inProduct_parameter (i : Fin 4) :
    inProduct c j u i ≫ pullback.fst c ambientToField =
      Spec.map (CommRingCat.ofHom (algebraMap S (native c j u i))) ≫ u ≫ j := by
  simp only [inProduct,Category.assoc,pullbackRightPullbackFstIso_inv_snd_fst]
  simp only [pullback.congrHom_hom,pullback.lift_fst_assoc,Category.comp_id]
  rw [← Category.assoc (CycleQ2GenericTimeProductChart.atTime c j u i),CycleQ2GenericTimeProductChart.atTime_over]

private abbrev nativeScalar (i : Fin 4) := algebraMap S (native c j u i)
private abbrev targetScalar (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    S →+* tensorAmbient a u i p :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  algebraMap S _
private abbrev sourceScalar (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    S →+* tensorCurve a u t i p :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  algebraMap S _
private theorem scalar_compat (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    (nativeToTensor r c hc j a ha u i p).comp (nativeScalar c j u i) = targetScalar a u i p := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  let : Algebra genericField S := (ground c j u).toAlgebra
  let : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  apply RingHom.ext
  intro z
  let e : (S ⊗[P] A i) ≃ₐ[S] native c j u i := chartEquiv (R := S) i
    (CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u)
  exact (localizedMap (pivot i p) e).commutes z

private theorem restriction_scalar (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    (restriction a u t i p).comp (targetScalar a u i p) = sourceScalar a u t i p := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  apply RingHom.ext
  intro z
  change z ⊗ₜ[P] ((inclusionMap t i p) 1) = z ⊗ₜ[P] 1
  rw [map_one]

private theorem source_parameter (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    chartToTest t i p a u ≫ pullback.fst a (curveMap toRaw V t) =
      Spec.map (CommRingCat.ofHom (sourceScalar a u t i p)) ≫ u := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  simp only [chartToTest,Category.assoc]
  rw [← pullback.condition (f := u) (g := pullback.fst a (curveMap toRaw V t)),
    IsPullback.isoPullback_inv_fst_assoc,← Category.assoc]
  apply congrArg (fun k => k ≫ u)
  exact CycleQ2MonicGenericAmbientChartBaseChange.tensorInclusion_overBase (R := P) (S := S) _ _ _

private theorem graph_parameter (t : Fin 3 → ℂ) :
    (fromTest V t r j a ha ≫ embeddingGeneric V t r c hc) ≫ pullback.fst c ambientToField =
      pullback.fst a (curveMap toRaw V t) ≫ j := by
  rw [Category.assoc,CycleQ2GenericSmoothCurveGraph.embeddingGeneric_toCurve]
  exact (test_square V t r j a ha).w.symm

set_option maxHeartbeats 800000 in
private theorem actual_over (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    (Spec.map (CommRingCat.ofHom (restriction a u t i p)) ≫ inActualProduct r c hc j a ha u i p) ≫
      pullback.fst c ambientToField =
    (chartToTest t i p a u ≫ fromTest V t r j a ha ≫ embeddingGeneric V t r c hc) ≫
      pullback.fst c ambientToField := by
  have hg := graph_parameter r c hc j a ha t
  simp only [Category.assoc] at hg
  simp only [Category.assoc,inActualProduct,inProduct_parameter,hg]
  rw [← Category.assoc (chartToTest t i p a u),source_parameter,Category.assoc]
  rw [← Spec.map_comp_assoc,← Spec.map_comp_assoc,← CommRingCat.ofHom_comp,← CommRingCat.ofHom_comp]
  change Spec.map (CommRingCat.ofHom (((restriction a u t i p).comp
    (nativeToTensor r c hc j a ha u i p)).comp (nativeScalar c j u i))) ≫ u ≫ j = _
  rw [RingHom.comp_assoc,scalar_compat,restriction_scalar]



private theorem map_dehom {A B : Type} [CommRing A] [CommRing B] (i : Fin 4) (h : A →+* B)
    (w : MvPolynomial (Fin 5) A) :
    MvPolynomial.map h (dehom i w) = dehom i (MvPolynomial.map h w) := by
  induction w using MvPolynomial.induction_on with
  | C c => simp only [dehom,aeval_C,MvPolynomial.algebraMap_eq,MvPolynomial.map_C]
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p x hp =>
    by_cases h' : x = i.castSucc
    · subst x
      simp only [map_mul,CycleQ2HodgeEuler.dehom_X_self,map_one,map_X,hp]
    · obtain ⟨x,rfl⟩ := Fin.exists_succAbove_eq h'
      simp only [map_mul,CycleQ2HodgeEuler.dehom_X_succAbove,map_X,hp]

abbrev ambientRight (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    Ambient i p →+* tensorAmbient a u i p :=
  letI : Algebra P S := (actualParameters a u).toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

private theorem nativeToTensor_shifted (i : Fin 4) (p : CycleQ2SegreCech.Chart) (w : ChartPolynomial P) :
    nativeToTensor r c hc j a ha u i p (chartMap ((ground c j u).comp coeff) i
      (unshift i (MvPolynomial.map (actualParameters a u) w))) =
      ambientRight a u i p (algebraMap (ambient i) (Ambient i p) (mk i w)) := by
  let : Algebra P S := (actualParameters a u).toAlgebra
  let : Algebra genericField S := (ground c j u).toAlgebra
  let : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  let hα : (algebraMap P S).comp sexticToParameter = (algebraMap genericField S).comp genericCoeff :=
    CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u
  let e := chartEquiv (R := S) i hα
  exact (congrArg (localizedMap (pivot i p) e) (chartEquiv_tmul i hα w).symm).trans
    (localizedMap_mk (pivot i p) e (mk i w))

/-- Pulling any polynomial in the incidence parameters to the true product pivot
returns its original shifted dehomogenization. This applies simultaneously to
the cubic equation and the selected row giving the projective graph ideal. -/
theorem nativeToTensor_homogeneous (i : Fin 4) (p : CycleQ2SegreCech.Chart)
    (w : MvPolynomial (Fin 5) P) :
    nativeToTensor r c hc j a ha u i p (chartMap ((ground c j u).comp coeff) i
      (dehom i (MvPolynomial.map (actualParameters a u) w))) =
      ambientRight a u i p (algebraMap (ambient i) (Ambient i p) (mk i (dehomogenize i w))) := by
  let : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  have h := nativeToTensor_shifted r c hc j a ha u i p (dehomogenize i w)
  rwa [CycleQ2IncidenceChartSeedFiber.map_dehomogenize,unshift_dehomogenize] at h

private theorem nativeToTensor_polynomial (i : Fin 4) (p : CycleQ2SegreCech.Chart)
    (w : MvPolynomial (Fin 5) CycleQ2IncidenceTimeCurve.SexticRing) :
    nativeToTensor r c hc j a ha u i p (chartMap ((ground c j u).comp coeff) i
      (MvPolynomial.map ((ground c j u).comp genericCoeff) (dehom i w))) =
      ambientRight a u i p (algebraMap (ambient i) (Ambient i p)
        (mk i (dehomogenize i (MvPolynomial.map sexticToParameter w)))) := by
  have hα : (actualParameters a u).comp sexticToParameter = (ground c j u).comp genericCoeff :=
    CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u
  have h := nativeToTensor_homogeneous r c hc j a ha u i p (MvPolynomial.map sexticToParameter w)
  rw [MvPolynomial.map_map,hα,← map_dehom] at h
  exact h

/-- The actual generic-time logarithmic representative pulls back to the
two generators of the projective curve restriction, in their original order. -/
theorem logarithmic_equations (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    letI : Algebra genericField S := (ground c j u).toAlgebra
    letI : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
    letI : IsScalarTower ℂ genericField S := IsScalarTower.of_algebraMap_eq' rfl
    let τ := CycleQ2IncidenceSymbolDomain.toGeneric V r c hc j a ha u rfl i
    let E := nativeToTensor r c hc j a ha u i p
    E (τ (CycleQ2IncidenceSymbolDomain.eqn i (CycleQ2IncidenceSymbolFiber.H i))) =
        ambientRight a u i p (cubic i p) ∧
      E (τ (CycleQ2IncidenceSymbolDomain.eqn i (CycleQ2IncidenceSymbolFiber.G t i p))) =
        ambientRight a u i p (row t i p) := by
  let : Algebra genericField S := (ground c j u).toAlgebra
  let : Algebra ℂ S := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  let : IsScalarTower ℂ genericField S := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨_,hH,hG⟩ := CycleQ2IncidenceSymbolDomain.actual_chart_equations V r c hc j a ha u t i p
  exact ⟨(congrArg (nativeToTensor r c hc j a ha u i p) hH).trans
    (nativeToTensor_homogeneous r c hc j a ha u i p (pointEquationH incidencePoint)),
    (congrArg (nativeToTensor r c hc j a ha u i p) hG).trans
      (nativeToTensor_homogeneous r c hc j a ha u i p
        (CycleQ2RelativeConstantSection.relativeSectionPolynomial incidencePoint t p.1))⟩

private abbrev rawProjection := CycleQ2GenericTimeRawProjection.toRawAmbient

private theorem graph_raw (t : Fin 3 → ℂ) :
    (fromTest V t r j a ha ≫ embeddingGeneric V t r c hc) ≫
      pullback.snd c ambientToField ≫ rawProjection =
    testOriginal t a ≫ originalToAmbient t := by
  let d := CycleQ2MarkedDenseTestIdeal.denseEmbedding t c r hc j a ha
  let J := CycleQ2MarkedDenseTestIdeal.toProduct c j
  have h : d ≫ J = fromTest V t r j a ha ≫ embeddingGeneric V t r c hc := IsPullback.lift_snd _ _ _ _
  rw [← h,Category.assoc]
  let H := CycleQ2MarkedDenseTestIdeal.dense_relative_square t c r hc j a ha
  have hh := congrArg (fun k => k ≫ pullback.snd _ _ ≫ pullback.snd toRaw universalAmbientToBase) H.w
  simpa only [d,J,CycleQ2MarkedDenseTestIdeal.relativeProductMap,CycleQ2MarkedDenseTestIdeal.toProduct,
    rawProjection,Category.assoc,CycleQ2RelativeGraphClosure.productMap_snd_assoc,
    pullback.lift_snd_assoc,CycleQ2LiteralIncidenceRelativeEmbedding.joint_toAmbient_assoc,
    CycleQ2LiteralIncidenceRelativeCylinder.relativeQ_snd,testOriginal] using hh


open CycleQ2RelativeCurveChart (curveCoordinateChartEquiv AffineCurveChart)
attribute [local instance] CycleQ2RelativeCurveChartScheme.affineCurveChartCommRing
  CycleQ2RelativeCurveChartScheme.curveCoordinateCommRing
open CycleQ2LiteralAbelJacobiQCoordinates (SexticChart)
set_option maxHeartbeats 900000 in
/-- The actual two-equation projective pivot square commutes with the
closed inclusion of the marked closure in the product with the entire curve. -/
theorem commutes (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    Spec.map (CommRingCat.ofHom (restriction a u t i p)) ≫ inActualProduct r c hc j a ha u i p =
      (chartToTest t i p a u ≫ (fromTest V t r j a ha).toImage) ≫
        ((fromTest V t r j a ha).imageι ≫ embeddingGeneric V t r c hc) := by
  rw [Category.assoc,Scheme.Hom.toImage_imageι_assoc]
  let σ := CycleQ2GenericTimeRawProjection.rawFunctions c j u i
  have hσ := CycleQ2GenericTimeRawProjection.rawFunctions_fraction c j u i
  have hρ : inProduct c j u i ≫ pullback.snd c ambientToField ≫ rawProjection =
      Spec.map (CommRingCat.ofHom σ) ≫ sexticInclusion universalPoint i :=
    CycleQ2GenericTimeRawProjection.inProduct_raw_projection c j u i
  let F := pullback.fst c ambientToField
  let Q := pullback.snd c ambientToField ≫ rawProjection
  have H : IsPullback F Q (c ≫ genericPoint ≫ toRaw) universalAmbientToBase := by
    have h := ((IsPullback.of_hasPullback c ambientToField).paste_vert
      (IsPullback.of_hasPullback CycleQ2LiteralIncidenceRelativeCorrespondence.ambientStructure genericPoint).flip).paste_vert
      (IsPullback.of_hasPullback toRaw universalAmbientToBase)
    simpa only [Category.assoc,F,Q,rawProjection] using h
  apply H.hom_ext (actual_over r c hc j a ha u t i p)
  let H0 := (curveCoordinateChartEquiv incidencePoint t i).toRingHom.comp
      (CycleQ2LiteralAbelJacobiQCoordinates.universalToOriginal t i)
  let v : AffineCurveChart incidencePoint t i := CycleQ2LiteralAbelJacobiSeedLiftChart.toCurve incidencePoint t i p
    (CycleQ2LiteralAbelJacobiSeedLiftChart.rowPivot incidencePoint t i p)
  let l : AffineCurveChart incidencePoint t i →+* Curve t i p := algebraMap (AffineCurveChart incidencePoint t i) (Localization.Away v)
  let : Algebra P S := (actualParameters a u).toAlgebra
  let k := Algebra.TensorProduct.includeRight (R := P) (A := S) (B := Curve t i p)
  have hring :
      ((restriction a u t i p).comp (nativeToTensor r c hc j a ha u i p)).comp σ =
        k.toRingHom.comp (l.comp H0) := by
    ext z
    obtain ⟨n,w,hw,rfl⟩ := CycleQ2LiteralAbelJacobiQCoordinates.sexticFraction_surjective universalPoint i z
    change restriction a u t i p (nativeToTensor r c hc j a ha u i p (σ _)) = _
    dsimp only [σ]
    rw [hσ,nativeToTensor_polynomial]
    exact (CycleQ2MarkedPivotSource.raw_fraction t i p a u n w hw).symm
  have hg := graph_raw r c hc j a ha t
  have ht := CycleQ2MarkedPivotSource.chartToTest_raw t i p a u
  dsimp only [Q]
  rw [Category.assoc,Category.assoc,inActualProduct,Category.assoc,hρ]
  simp only [Category.assoc] at hg ht ⊢
  rw [hg,ht]
  simp only [← Spec.map_comp_assoc,← CommRingCat.ofHom_comp]
  exact congrArg (fun m => Spec.map (CommRingCat.ofHom m) ≫ sexticInclusion universalPoint i) hring


end Actual

end CycleQ2MarkedPivotRing
#print axioms CycleQ2MarkedPivotRing.commutes
#print axioms CycleQ2MarkedPivotRing.logarithmic_equations
