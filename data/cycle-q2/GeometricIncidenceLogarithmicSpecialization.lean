import Proposal.GeometricGenericTimeAffineCharts
import Proposal.GeometricMarkedLogarithmicVelocity

/-!
# The incidence logarithmic symbol at generic and marked time

The cubic and the moving section define a double-localization two-form on one
affine incidence sextic. Its pullbacks are computed on every affine test of the
normalized generic time, relative to the generic coefficient field, and at the
marked dual-number time, relative to ℂ. At the marked time these are exactly
the two jets used to compute the logarithmic velocity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2IncidenceLogSpread

open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2DoubleLogarithmicClass (twoLog)
open CycleQ2PrincipalGysinFunctions (logarithm)
open CycleQ2NativeDoubleLocalization (localizedF localizedG localizedF_val localizedG_val cochain)
open KaehlerDifferential

section ChangeBase

variable {k l A B : Type} [CommRing k] [CommRing l] [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k l] [Algebra l B] [Algebra k B] [IsScalarTower k l B]
  (φ : A →ₐ[k] B)

private def relativeOne : Ω[A⁄k] →ₛₗ[φ.toRingHom] Ω[B⁄l] := by
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : IsScalarTower k A B := IsScalarTower.of_algHom φ
  let m := KaehlerDifferential.map k l A B
  exact { toFun := m
          map_add' := m.map_add
          map_smul' := fun a x => (m.map_smul a x).trans (IsScalarTower.algebraMap_smul B a (m x)).symm }

private theorem relativeOne_D (a : A) :
    relativeOne (l := l) φ (D k A a) = D l B (φ a) := by
  let : Algebra A B := φ.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algHom φ
  exact KaehlerDifferential.map_D k l A B a

def relativeTwo : Form k A 2 →ₛₗ[φ.toRingHom] Form l B 2 :=
  exteriorMap φ.toRingHom (relativeOne (l := l) φ) 2

private theorem relative_log (u : Aˣ) :
    relativeOne (l := l) φ (logarithm (K := k) u) = logarithm (K := l) (Units.map φ.toRingHom u) := by
  unfold logarithm
  rw [map_smulₛₗ, relativeOne_D]
  rfl

theorem relative_twoLog (f g : Aˣ) :
    relativeTwo (l := l) φ (twoLog (K := k) f g) =
      twoLog (K := l) (Units.map φ.toRingHom f) (Units.map φ.toRingHom g) := by
  unfold relativeTwo twoLog CycleQ2ExactFrameThreeDeRham.wedge
  rw [exteriorMap_wedge]
  apply congrArg (exteriorPower.ιMulti B 2)
  funext i
  fin_cases i
  · exact relative_log φ f
  · exact relative_log φ g

open CycleQ2NativeDoubleLocalization (T)
private abbrev extend (f g : A) := (IsScalarTower.toAlgHom k B (T (φ f) (φ g))).comp φ

private theorem product_unit (f g : A) : IsUnit (extend φ f g (f*g)) := by
  rw [map_mul]
  change IsUnit (algebraMap B (T (φ f) (φ g)) (φ f) * algebraMap B (T (φ f) (φ g)) (φ g))
  exact (IsLocalization.Away.isUnit_of_dvd (φ f * φ g) (dvd_mul_right _ _)).mul
    (IsLocalization.Away.isUnit_of_dvd (φ f * φ g) (dvd_mul_left _ _))

def onOverlap (f g : A) : T f g →ₐ[k] T (φ f) (φ g) :=
  IsLocalization.Away.liftAlgHom (f := extend φ f g) (f*g) (product_unit φ f g)

private theorem onOverlap_base (f g a : A) :
    onOverlap φ f g (algebraMap A (T f g) a) = algebraMap B (T (φ f) (φ g)) (φ a) :=
  IsLocalization.Away.lift_eq (S := T f g) (g := (extend φ f g).toRingHom) _ (product_unit φ f g) a

/-- A coefficient and chart specialization takes the common double-localization
representative to the representative relative to the new ground ring. -/
theorem native_baseChange (f g : A) :
    letI : IsScalarTower k l (T (φ f) (φ g)) := IsScalarTower.to₁₂₄ k l B _
    relativeTwo (l := l) (onOverlap φ f g) (cochain (K := k) f g) =
      cochain (K := l) (φ f) (φ g) := by
  let : IsScalarTower k l (T (φ f) (φ g)) := IsScalarTower.to₁₂₄ k l B _
  unfold cochain
  rw [relative_twoLog]
  congr 1
  · apply Units.ext
    change onOverlap φ f g (localizedF (K := k) f g) = (localizedF (K := l) (φ f) (φ g) : _)
    rw [localizedF_val, localizedF_val, onOverlap_base]
  · apply Units.ext
    change onOverlap φ f g (localizedG (K := k) f g) = (localizedG (K := l) (φ f) (φ g) : _)
    rw [localizedG_val, localizedG_val, onOverlap_base]

end ChangeBase
end CycleQ2IncidenceLogSpread

namespace CycleQ2IncidenceSymbolFiber

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MvPolynomial
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
open CycleQ2IncidenceChartSeedFiber CycleQ2RelativeConstantSection
open CycleQ2LiteralIncidenceCylinderMap (universalPoint)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericField genericAmbient)
open CycleQ2MonicGenericAmbientChart (genericCoeff rawPoint)
open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2HodgeEuler (dehom chartMap chart)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2ShiftedChartCoordinates (unshift unshift_dehomogenize)
open CycleQ2MarkedLogarithmicVelocity (jet fixedChartMap)
open CycleQ2LiteralAbelJacobiContraction (T)
open scoped DualNumber TensorProduct

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
abbrev P := ChartPolynomial ParameterAlgebra

def H (i : Fin 4) : P := dehomogenizedEquations incidencePoint i 1
def G (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) : P :=
  dehomogenize i (relativeSectionPolynomial incidencePoint t p.1)

section Marked
local instance fixedRing (i : Fin 4) : CommRing (T i) := inferInstance

def markedMap (i : Fin 4) : P →ₐ[ℂ] DualNumber (T i) where
  toRingHom := (jet (fixedChartMap i)).comp (MvPolynomial.map firstOrderMap.toRingHom)
  commutes' z := by
    change jet _ (MvPolynomial.map firstOrderMap.toRingHom (C (algebraMap ℂ ParameterAlgebra z))) = _
    rw [map_C,show firstOrderMap.toRingHom (algebraMap ℂ ParameterAlgebra z) = _ from firstOrderMap.commutes z]
    rw [jet,eval₂Hom_C]
    apply TrivSqZeroExt.ext
    · rfl
    · exact map_zero _

end Marked

section Generic
variable {R : Type} [CommRing R] [Algebra genericField R] [Algebra ℂ R] [IsScalarTower ℂ genericField R]
  (α : ParameterAlgebra →ₐ[ℂ] R) (i : Fin 4)
abbrev ambientRing (R : Type) [CommRing R] [Algebra genericField R] (i : Fin 4) :=
  chart ((algebraMap genericField R).comp coeff) i

private def parameterPolynomial : P →ₐ[ℂ] ChartPolynomial R :=
  MvPolynomial.mapAlgHom α

def genericMap : P →ₐ[ℂ] ambientRing R i :=
  ((chartMap ((algebraMap genericField R).comp coeff) i).restrictScalars ℂ).comp
    (((unshift (R := R) i).restrictScalars ℂ).comp (parameterPolynomial α))

omit [IsScalarTower ℂ genericField R] in
theorem genericMap_homogeneous (w : MvPolynomial (Fin 5) ParameterAlgebra) :
    genericMap α i (dehomogenize i w) =
      chartMap ((algebraMap genericField R).comp coeff) i (dehom i (MvPolynomial.map α.toRingHom w)) := by
  change chartMap _ i (unshift i (MvPolynomial.map α.toRingHom (dehomogenize i w))) = _
  rw [map_dehomogenize,unshift_dehomogenize]

omit [IsScalarTower ℂ genericField R] in
theorem generic_sextic
    (hα : α.toRingHom.comp sexticToParameter = (algebraMap genericField R).comp genericCoeff) :
    genericMap α i (dehomogenizedEquations incidencePoint i 0) = 0 := by
  change genericMap α i (dehomogenize i (pointEquationF incidencePoint)) = _
  rw [genericMap_homogeneous,← CycleQ2LiteralIncidenceCylinderMap.universal_to_incidence,map_map,hα,
      ← CycleQ2GeometricHodgeThreefoldIncidence.equation_eq, equation, map_map]
  exact CycleQ2HodgeEuler.chartMap_F _ _

end Generic
end CycleQ2IncidenceSymbolFiber

namespace CycleQ2IncidenceSymbolDomain

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve CycleQ2IncidenceFirstOrder
open CycleQ2GeometricIncidenceProj CycleQ2IncidenceDehomogenizedChart
open CycleQ2IncidenceChartSeedFiber CycleQ2RelativeConstantSection
open CycleQ2IncidenceNormalForm CycleQ2IncidenceUniversalChart
open CycleQ2IncidencePolynomialJacobianBinding
open CycleQ2LiteralIncidenceCylinderMap (universalPoint)
open CycleQ2LiteralIncidenceNormalizedSlice (toRaw)
open CycleQ2LiteralIncidenceRelativeSpread (Time)
open CycleQ2LiteralIncidenceRelativeCompletion (Completion structureMap inclusion)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericField genericPoint genericAmbient)
open CycleQ2LiteralAbelJacobiEquations (seedF)
open CycleQ2GenericTimeCoefficients (parameter ground)
open CycleQ2IncidenceLogSpread (relativeTwo onOverlap native_baseChange)
open CycleQ2NativeDoubleLocalization (cochain)
open CycleQ2MarkedLogarithmicVelocity (jet fixedChartMap cubicJet rowJet)
open CycleQ2LiteralAbelJacobiContraction (T fixedIdeal)
open CycleQ2IncidenceSymbolFiber (P H G markedMap ambientRing genericMap)
open CycleQ2GeometricIncidenceProj
open scoped DualNumber

attribute [local instance] CycleQ2IncidenceTimeCurve.timeParameterCommRing
private abbrev F (i : Fin 4) : P := dehomogenizedEquations incidencePoint i 0
abbrev Chart (i : Fin 4) := P ⧸ (Ideal.span {F i} : Ideal P)
abbrev eqn (i : Fin 4) : P →ₐ[ℂ] Chart i := Ideal.Quotient.mkₐ ℂ _
abbrev universalSymbol (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :=
  cochain (K := ℂ) (eqn i (H i)) (eqn i (G t i p))

private def descend {B : Type} [CommRing B] [Algebra ℂ B] (i : Fin 4) (φ : P →ₐ[ℂ] B)
    (h : φ (F i) = 0) : Chart i →ₐ[ℂ] B := Ideal.Quotient.liftₐ _ φ
  (fun _ hx => (Ideal.span_singleton_le_iff_mem (RingHom.ker φ.toRingHom)).mpr h hx)

section Marked

local instance fixedRing (i : Fin 4) : CommRing (T i) := inferInstance
private abbrev seed := seedPoint (57 : ℂ) Complex.I
private theorem marked_sextic (i : Fin 4) : markedMap i (F i) = 0 := by
  have h : MvPolynomial.map firstOrderMap.toRingHom (pointEquationF incidencePoint) =
      MvPolynomial.map (algebraMap ℂ (DualNumber ℂ)) (pointEquationF seed) := by
    simp only [pointEquationF,CycleQ2IncidenceImageLine.pointMap_familyF,
      CycleQ2IncidenceNormalForm.map_fullInvariantPolynomial]
    exact congrArg (CycleQ2IncidenceNormalForm.fullInvariantPolynomial 6)
      (funext firstOrderIncidencePoint_sextic)
  change jet (fixedChartMap i) (MvPolynomial.map firstOrderMap.toRingHom
    (dehomogenize i (pointEquationF incidencePoint))) = 0
  rw [map_dehomogenize,h,← map_dehomogenize,CycleQ2MarkedLogarithmicVelocity.jet_constant]
  have hz : fixedChartMap i (seedF i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  change algebraMap (T i) (DualNumber (T i)) (fixedChartMap i (seedF i)) = 0
  rw [hz,map_zero]

def toMarked (i : Fin 4) := descend i (markedMap i) (marked_sextic i)

theorem marked (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    relativeTwo (l := ℂ) (onOverlap (toMarked i) (eqn i (H i)) (eqn i (G t i p)))
      (universalSymbol t i p) = cochain (K := ℂ) (cubicJet i) (rowJet t i p) :=
  native_baseChange (l := ℂ) (toMarked i) (eqn i (H i)) (eqn i (G t i p))

end Marked

section Generic

variable (V : parameterScheme.Opens) {D C : Scheme.{0}} {R : Type} [CommRing R]
  [Algebra genericField R] [Algebra ℂ R] [IsScalarTower ℂ genericField R]
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V) (ha : j ≫ r = a ≫ inclusion V)
  (u : Spec (CommRingCat.of R) ⟶ D) (hu : ground c j u = algebraMap genericField R)

def parameters : ParameterAlgebra →ₐ[ℂ] R where
  toRingHom := parameter V a u
  commutes' z := by
    change parameter V a u (algebraMap ℂ ParameterAlgebra z) = algebraMap ℂ R z
    rw [CycleQ2GenericTimeCoefficients.parameter_complex V r c hc j a ha u z,hu,
      ← IsScalarTower.algebraMap_apply]

private theorem ambient_zero (i : Fin 4) : genericMap (parameters V r c hc j a ha u hu) i (F i) = 0 := by
  apply CycleQ2IncidenceSymbolFiber.generic_sextic
  exact (CycleQ2GenericTimeCoefficients.parameter_comp_sextic V r c hc j a ha u).trans (by rw [hu])

def toGeneric (i : Fin 4) :=
  descend i (genericMap (parameters V r c hc j a ha u hu) i) (ambient_zero V r c hc j a ha u hu i)

/-- The native logarithmic representative on every affine test of the actual
generic time comes from the universal incidence sextic quotient. -/
theorem generic (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    let τ := toGeneric V r c hc j a ha u hu i
    relativeTwo (l := genericField) (onOverlap τ (eqn i (H i)) (eqn i (G t i p)))
      (universalSymbol t i p) =
      cochain (K := genericField) (τ (eqn i (H i))) (τ (eqn i (G t i p))) :=
  native_baseChange (l := genericField) (toGeneric V r c hc j a ha u hu i)
    (eqn i (H i)) (eqn i (G t i p))

end Generic

open CycleQ2MonicGenericSmooth (coeff)
open CycleQ2HodgeEuler (chartMap dehom)
open CycleQ2GenericTimeProductChart (atTime)
open CycleQ2IncidenceSymbolFiber (genericMap_homogeneous)

variable (V : parameterScheme.Opens) {D C : Scheme.{0}} {R : Type} [CommRing R]
  (r : C ⟶ Completion V) (c : C ⟶ Spec (CommRingCat.of genericField))
  (hc : r ≫ structureMap V = c ≫ genericPoint)
  (j : D ⟶ C) (a : D ⟶ Time toRaw V) (ha : j ≫ r = a ≫ inclusion V)
  (u : Spec (CommRingCat.of R) ⟶ D)

/-- In the affine chart ring of the chosen normalized generic time, these are
the ordinary homogeneous cubic and section-row functions on the actual ambient
sextic. The compatible field structure on an affine test is induced by u. -/
theorem actual_chart_equations (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart) :
    letI : Algebra genericField R := (ground c j u).toAlgebra
    letI : Algebra ℂ R := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
    letI : IsScalarTower ℂ genericField R := IsScalarTower.of_algebraMap_eq' rfl
    let τ := toGeneric V r c hc j a ha u rfl i
    let α := parameters V r c hc j a ha u rfl
    let q := (ground c j u).comp coeff
    IsOpenImmersion (atTime c j u i) ∧
    τ (eqn i (H i)) =
      chartMap q i (dehom i (MvPolynomial.map α.toRingHom (pointEquationH incidencePoint))) ∧
    τ (eqn i (G t i p)) =
      chartMap q i (dehom i (MvPolynomial.map α.toRingHom (relativeSectionPolynomial incidencePoint t p.1))) := by
  let : Algebra genericField R := (ground c j u).toAlgebra
  let : Algebra ℂ R := ((ground c j u).comp (algebraMap ℂ genericField)).toAlgebra
  let : IsScalarTower ℂ genericField R := IsScalarTower.of_algebraMap_eq' rfl
  let α := parameters V r c hc j a ha u rfl
  exact ⟨inferInstance, genericMap_homogeneous α i (pointEquationH incidencePoint),
    genericMap_homogeneous α i (relativeSectionPolynomial incidencePoint t p.1)⟩

end CycleQ2IncidenceSymbolDomain

#print axioms CycleQ2IncidenceSymbolDomain.marked
#print axioms CycleQ2IncidenceSymbolDomain.generic
#print axioms CycleQ2IncidenceSymbolDomain.actual_chart_equations
