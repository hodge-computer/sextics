import Proposal.GeometricMonicGenericSupport

/-!
# Affine tests of the generic time and its ambient sextic

Pull the incidence parameters back along the normalized time and identify their
raw sextic with the one induced by the generic coefficient field. On each of
the four weight-one charts, translate the shifted fourth coordinate and exhibit
the resulting affine chart as an open in the actual base-changed sextic.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2GenericTimeCoefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
open CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeSpread
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceGenericCorrespondence
open CycleQ2LiteralIncidenceRelativeCylinder CycleQ2IncidenceFirstOrder

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing

variable (V : parameterScheme.Opens) {D C : Scheme.{0}} {R : Type} [CommRing R]

/-- The incidence parameter of a test time point, including its cubic and its matrix rows. -/
def incidence (a : D ⟶ Time toRaw V) : D ⟶ parameterScheme :=
  a ≫ pullback.snd toRaw (V.ι ≫ parameterToSextics) ≫ V.ι

def parameter (a : D ⟶ Time toRaw V) (u : Spec (CommRingCat.of R) ⟶ D) :
    ParameterAlgebra →+* R :=
  (Spec.preimage (u ≫ incidence V a)).hom

def ground (c : C ⟶ Spec (CommRingCat.of genericField)) (j : D ⟶ C)
    (u : Spec (CommRingCat.of R) ⟶ D) : genericField →+* R :=
  (Spec.preimage (u ≫ j ≫ c)).hom

variable (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V)
  (ha : j ≫ r = a ≫ inclusion V) (u : Spec (CommRingCat.of R) ⟶ D)

include hc ha in
theorem incidence_over :
    incidence V a ≫ parameterToSextics = j ≫ c ≫ genericPoint ≫ toRaw := by
  have pb := pullback.condition (f := toRaw) (g := V.ι ≫ parameterToSextics)
  have hp : incidence V a ≫ parameterToSextics = (a ≫ timeMap toRaw V) ≫ toRaw := by
    simpa only [incidence,timeMap,Category.assoc] using
      congrArg (fun (f : Time toRaw V ⟶ sexticBase) => a ≫ f) pb.symm
  have ht : a ≫ timeMap toRaw V = j ≫ c ≫ genericPoint := by
    calc
      a ≫ timeMap toRaw V = (a ≫ inclusion V) ≫ structureMap V := by rw [Category.assoc,inclusion_over]
      _ = j ≫ c ≫ genericPoint := by rw [← ha,Category.assoc,hc]
  rw [hp,ht]
  simp only [Category.assoc]

include hc ha in
/-- The coefficient field and the original incidence presentation induce the same raw sextic. -/
theorem parameter_comp_sextic :
    (parameter V a u).comp sexticToParameter =
      (ground c j u).comp CycleQ2MonicGenericAmbientChart.genericCoeff := by
  have hg : genericPoint ≫ toRaw = Spec.map (CommRingCat.ofHom CycleQ2MonicGenericAmbientChart.genericCoeff) := by
    change Spec.map (CommRingCat.ofHom (algebraMap MonicRing genericField)) ≫
      Spec.map (CommRingCat.ofHom rawToMonic) = _
    rw [← Spec.map_comp]
    rfl
  let x : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of ParameterAlgebra) := u ≫ incidence V a
  let y : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of genericField) := u ≫ j ≫ c
  have h : x ≫ Spec.map (CommRingCat.ofHom sexticToParameter) =
      y ≫ Spec.map (CommRingCat.ofHom CycleQ2MonicGenericAmbientChart.genericCoeff) := by
    calc
      _ = u ≫ incidence V a ≫ parameterToSextics := Category.assoc u (incidence V a) parameterToSextics
      _ = u ≫ j ≫ c ≫ genericPoint ≫ toRaw :=
        congrArg (fun (f : D ⟶ sexticBase) => u ≫ f) (incidence_over V r c hc j a ha)
      _ = y ≫ (genericPoint ≫ toRaw) := by simp only [y,Category.assoc]
      _ = _ := congrArg (fun (m : Spec (CommRingCat.of genericField) ⟶ sexticBase) => y ≫ m) hg
  have he := congrArg Spec.preimage h
  rw [Spec.preimage_comp x,Spec.preimage_comp y,Spec.preimage_map,Spec.preimage_map] at he
  exact congrArg CommRingCat.Hom.hom he

include hc ha in
theorem parameter_complex (z : ℂ) :
    parameter V a u (algebraMap ℂ ParameterAlgebra z) =
      ground c j u (algebraMap ℂ genericField z) := by
  have hK : CycleQ2MonicGenericAmbientChart.genericCoeff (MvPolynomial.C z) =
      algebraMap ℂ genericField z := by
    change algebraMap MonicRing genericField (rawToMonic (MvPolynomial.C z)) = _
    rw [rawToMonic_C]
    exact (IsScalarTower.algebraMap_apply ℂ MonicRing genericField z).symm
  exact (congrArg (parameter V a u) (CycleQ2GenericTimeDerivation.sexticToParameter_C z).symm).trans
    ((RingHom.congr_fun (parameter_comp_sextic V r c hc j a ha u) (MvPolynomial.C z)).trans
      (congrArg (ground c j u) hK))

variable (hV : CycleQ2IncidenceSeedFiberCover.seedBasePoint ∈ V)

theorem parameter_at_marked_tangent :
    parameter V (relativeTangent toRaw V seedPoint seedPoint_toRaw hV) (𝟙 _) =
      firstOrderMap.toRingHom := by
  have h : incidence V (relativeTangent toRaw V seedPoint seedPoint_toRaw hV) =
      firstOrderParameterPoint :=
    tangent_to_incidence toRaw V seedPoint seedPoint_toRaw hV
  have h' : (𝟙 _) ≫ incidence V (relativeTangent toRaw V seedPoint seedPoint_toRaw hV) =
      firstOrderParameterPoint := (Category.id_comp _).trans h
  have he := congrArg (fun (g : Spec (CommRingCat.of (DualNumber ℂ)) ⟶ parameterScheme) =>
    (Spec.preimage g).hom) h'
  exact he.trans (congrArg CommRingCat.Hom.hom (Spec.preimage_map (CommRingCat.ofHom firstOrderMap.toRingHom)))

end CycleQ2GenericTimeCoefficients

namespace CycleQ2ShiftedChartCoordinates

open MvPolynomial
open CycleQ2IncidenceDehomogenizedChart (ChartPolynomial linearCoordinate dehomogenize)
open CycleQ2HodgeEuler (dehom)

variable {R : Type} [CommRing R]

/-- The incidence coordinate named by `none` is (w + x₂²) / xᵢ². -/
def unshift (i : Fin 4) : ChartPolynomial R →ₐ[R] MvPolynomial (Fin 4) R :=
  aeval (fun j => match j with
    | none => dehom i (X (Fin.last 4)) + dehom i (X (2 : Fin 4).castSucc) ^ 2
    | some j => dehom i (X (i.succAbove j).castSucc))

variable [Algebra ℂ R]

theorem unshift_linear (i k : Fin 4) :
    unshift (R := R) i (linearCoordinate i k) = dehom i (X k.castSucc) := by
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · rw [CycleQ2IncidenceDehomogenizedChart.linearCoordinate_self,map_one,
      CycleQ2HodgeEuler.dehom_X_self]
  · rw [CycleQ2IncidenceDehomogenizedChart.linearCoordinate_succAbove,unshift,aeval_X]

/-- Every homogeneous polynomial, and indeed every polynomial, gives the same
function after translating the incidence chart's fourth coordinate. -/
theorem unshift_comp_dehomogenize (i : Fin 4) :
    (unshift (R := R) i).comp (dehomogenize i) = dehom i := by
  apply MvPolynomial.algHom_ext
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · simp only [AlgHom.comp_apply,CycleQ2IncidenceDehomogenizedChart.dehomogenize_last,
      map_sub,map_pow,unshift_linear]
    rw [unshift,aeval_X]
    exact add_sub_cancel_right _ _
  · rw [AlgHom.comp_apply,CycleQ2IncidenceDehomogenizedChart.dehomogenize_castSucc,unshift_linear]

theorem unshift_dehomogenize (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    unshift i (dehomogenize i p) = dehom i p :=
  DFunLike.congr_fun (unshift_comp_dehomogenize (R := R) i) p

end CycleQ2ShiftedChartCoordinates

namespace CycleQ2GenericTimeProductChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CycleQ2HodgeEuler (chart)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericField genericAmbient)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2NativeGenericSmooth (chartIn nativeComparison)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2MonicGenericAmbientChartBaseChange (tensorChartEquiv tensorInclusion tensorInclusion_overBase congr_fst)
open CycleQ2GenericTimeCoefficients (ground)

private abbrev nativeChart (i : Fin 4) :
    Spec (CommRingCat.of (chart coeff i)) ⟶ genericAmbient :=
  chartIn i ≫ nativeComparison.hom

private theorem nativeChart_over (i : Fin 4) :
    nativeChart i ≫ ambientToField =
      Spec.map (CommRingCat.ofHom (algebraMap genericField (chart coeff i))) := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => chartIn i ≫ f) CycleQ2NativeGenericSmooth.nativeComparison_over).trans
      (CycleQ2NativeGenericSmooth.chartIn_over i))

variable {R : Type} [CommRing R]

section BaseChange
variable [Algebra genericField R] (b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of genericField))
  (hb : Spec.map (CommRingCat.ofHom (algebraMap genericField R)) = b)

private def fromChart (i : Fin 4) :
    Spec (CommRingCat.of (chart ((algebraMap genericField R).comp coeff) i)) ⟶ pullback b ambientToField :=
  (Scheme.Spec.mapIso (tensorChartEquiv (S := R) coeff i).toRingEquiv.toCommRingCatIso.op).hom ≫
    tensorInclusion (S := R) ambientToField (nativeChart i) (nativeChart_over i) ≫
    (pullback.congrHom hb (rfl : ambientToField = ambientToField)).hom

private theorem fromChart_isOpenImmersion (i : Fin 4) : IsOpenImmersion (fromChart b hb i) := by
  unfold fromChart
  infer_instance

private theorem fromChart_over (i : Fin 4) :
    fromChart b hb i ≫ pullback.fst b ambientToField =
      Spec.map (CommRingCat.ofHom (algebraMap R (chart ((algebraMap genericField R).comp coeff) i))) := by
  change (Spec.map (CommRingCat.ofHom (tensorChartEquiv (S := R) coeff i).toRingHom) ≫
    tensorInclusion (S := R) ambientToField (nativeChart i) (nativeChart_over i) ≫
    (pullback.congrHom hb (rfl : ambientToField = ambientToField)).hom) ≫ _ = _
  erw [Category.assoc,Category.assoc,congr_fst,tensorInclusion_overBase,← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (tensorChartEquiv (S := R) coeff i).commutes

end BaseChange

variable {D C : Scheme.{0}}
  (c : C ⟶ Spec (CommRingCat.of genericField)) (j : D ⟶ C)
  (u : Spec (CommRingCat.of R) ⟶ D)

/-- A native weight-one affine coordinate chart inside the actual pullback of
the original generic threefold along the chosen time point. -/
def atTime (i : Fin 4) : Spec (CommRingCat.of (chart ((ground c j u).comp coeff) i)) ⟶
    pullback (u ≫ j ≫ c) ambientToField :=
  letI : Algebra genericField R := (ground c j u).toAlgebra
  fromChart (u ≫ j ≫ c) (Spec.map_preimage _) i

instance atTime_isOpenImmersion (i : Fin 4) : IsOpenImmersion (atTime c j u i) := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  exact fromChart_isOpenImmersion (u ≫ j ≫ c) (Spec.map_preimage _) i

theorem atTime_over (i : Fin 4) :
    atTime c j u i ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (algebraMap R (chart ((ground c j u).comp coeff) i))) := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  exact fromChart_over (u ≫ j ≫ c) (Spec.map_preimage _) i

/-- The same affine chart in the product with the full parameter curve. -/
def inProduct (i : Fin 4) : Spec (CommRingCat.of (chart ((ground c j u).comp coeff) i)) ⟶
    pullback c ambientToField :=
  atTime c j u i ≫
    (pullback.congrHom (Category.assoc u j c).symm (rfl : ambientToField = ambientToField)).hom ≫
    (pullbackRightPullbackFstIso c ambientToField (u ≫ j)).inv ≫
    pullback.snd (u ≫ j) (pullback.fst c ambientToField)

instance inProduct_isOpenImmersion [IsOpenImmersion u] [IsOpenImmersion j] (i : Fin 4) :
    IsOpenImmersion (inProduct c j u i) := by
  unfold inProduct
  infer_instance

end CycleQ2GenericTimeProductChart

#print axioms CycleQ2GenericTimeCoefficients.parameter_comp_sextic
#print axioms CycleQ2GenericTimeCoefficients.parameter_at_marked_tangent
#print axioms CycleQ2ShiftedChartCoordinates.unshift_comp_dehomogenize
#print axioms CycleQ2GenericTimeProductChart.atTime_over
#print axioms CycleQ2GenericTimeProductChart.inProduct_isOpenImmersion
