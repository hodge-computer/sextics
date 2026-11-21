import Proposal.GeometricLocalGysinProjection
import Proposal.GeometricIncidenceLogarithmicSpecialization
import Proposal.GeometricMarkedFundamentalClass

/-! The regular numerator of the marked logarithmic cochain on the actual
dual-number chart specializes to the moving adjunction numerator on the seed curve.
On a projective overlap the common incidence symbol can also be multiplied by the
native ambient test edge. Contraction of the regular four-form along the actual
marked tangent retains both conormals. The remaining covectors on the curve
represent the signed moving cubic class on its twelve vertex opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section

namespace CycleQ2MarkedGysinNumerator

open Module KaehlerDifferential
open CycleQ2MarkedLogarithmicVelocity
open CycleQ2LiteralAbelJacobiContraction (T toCurve cubicOnT fixedIdeal)
open CycleQ2LiteralAbelJacobiMovingNormal (A B)
open CycleQ2LiteralCylinderEvaluation (toFamily)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2LocalGysinProjection (cup22 clears_poles)
open CycleQ2ArbitraryFrameDifferential (front front_wedge)
open CycleQ2WeightedCoordinateExterior (Form)
open scoped DualNumber

attribute [local instance] TrivSqZeroExt.algebraBase CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  CycleQ2LiteralCylinderEvaluation.familyRing CycleQ2LiteralCylinderEvaluation.reductionAlgebra
  CycleQ2CurveParameterTangent.chartComplexAlgebra
local instance fixedRing (i : Fin 4) : CommRing (T i) := inferInstance
local instance seedRing (t : Fin 3 → ℂ) (i : Fin 4) : CommRing (A t i) := inferInstance

local instance dualTower (A : Type) [CommRing A] [Algebra ℂ A] : IsScalarTower ℂ (DualNumber A) A :=
  ⟨fun c z x => smul_mul_assoc c z.fst x⟩

local instance dualComm (A : Type) [CommRing A] [Algebra ℂ A] : SMulCommClass ℂ (DualNumber A) A :=
  ⟨fun c z x => smul_comm c z.fst x⟩

variable (t : Fin 3 → ℂ) (i : Fin 4) (p : CycleQ2SegreCech.Chart)
abbrev P := DualNumber (T i)
abbrev ρ : P i →+* A t i := (toCurve t i).toRingHom.comp (TrivSqZeroExt.fstHom (T i) (T i) (T i)).toRingHom

open scoped TensorProduct
abbrev SeedMixed := A t i ⊗[T i] (T i × Ω[T i⁄ℂ])
def restrictMixed : (T i × Ω[T i⁄ℂ]) →ₗ[T i] SeedMixed t i :=
  TensorProduct.mk (T i) (A t i) (T i × Ω[T i⁄ℂ]) 1

/-- Read the time derivative and the vertical differential on the closed curve. -/
def mixedRestriction : Ω[P i⁄ℂ] →ₛₗ[ρ t i] SeedMixed t i where
  toFun x := restrictMixed t i ((dualVelocity (A := T i)).liftKaehlerDifferential x,
    KaehlerDifferential.map ℂ ℂ (P i) (T i) x)
  map_add' x y := by
    rw [← (restrictMixed t i).map_add]
    exact congrArg (restrictMixed t i) (Prod.ext (map_add _ x y) (map_add _ x y))
  map_smul' a x := by
    simp only [map_smul]
    change restrictMixed t i (a.fst • (_, _)) = _
    rw [map_smul]
    exact (IsScalarTower.algebraMap_smul (A t i) a.fst _).symm

private theorem mixed_D (a : P i) :
    mixedRestriction t i (D ℂ (P i) a) = restrictMixed t i (a.snd, D ℂ (T i) a.fst) := by
  change restrictMixed t i (_, _) = _
  rw [Derivation.liftKaehlerDifferential_comp_D, KaehlerDifferential.map_D]
  rfl

private abbrev F := cubicJet i
private abbrev G := rowJet t i p
abbrev overlap := CycleQ2NativeDoubleLocalization.T (F i) (G t i p)

private abbrev fixedH := algebraMap (T i) (P i) (cubicOnT i)
abbrev cubicConormalTest (β : Ω[P i⁄ℂ]) : Form ℂ (P i) 2 :=
  exteriorPower.ιMulti (P i) 2 ![D ℂ (P i) (fixedH i),β]


open CycleQ2IncidenceSymbolDomain (eqn toMarked universalSymbol)
open CycleQ2IncidenceSymbolFiber (H G) in
def markedSymbol : Form ℂ (overlap t i p) 2 :=
  CycleQ2IncidenceLogSpread.relativeTwo (l := ℂ)
    (CycleQ2IncidenceLogSpread.onOverlap (toMarked i) (eqn i (H i)) (eqn i (CycleQ2IncidenceSymbolFiber.G t i p)))
    (universalSymbol t i p)

open CycleQ2NativeDoubleLocalization (localizedF localizedG localizedF_val localizedG_val)

private theorem conormal_wedge {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (f g h b : M) :
    front 3 f (front 2 g (exteriorPower.ιMulti R 2 ![h,b])) =
      exteriorPower.ιMulti R 4 ![f,g,h,b] := by
  rw [front_wedge,front_wedge]

def dt := restrictMixed t i (1,0)
def vertical (a : T i) := restrictMixed t i (0,D ℂ (T i) a)

private theorem split_D (a : P i) : mixedRestriction t i (D ℂ (P i) a) =
    vertical t i a.fst + toCurve t i a.snd • dt t i := by
  have e : restrictMixed t i (a.snd • ((1,0) : T i × Ω[T i⁄ℂ])) =
      toCurve t i a.snd • dt t i := by
    rw [map_smul]
    exact (IsScalarTower.algebraMap_smul (A t i) a.snd _).symm
  rw [mixed_D, vertical, ← e, ← (restrictMixed t i).map_add]
  apply congrArg (restrictMixed t i)
  ext <;> simp

private theorem evaluate_wedge {R E : Type} [CommRing R] [AddCommGroup E] [Module R E]
    (dt h g b : E) (L M : R) :
    exteriorPower.ιMulti R 4 ![h + L • dt,g + M • dt,h,b] =
      (-L) • exteriorPower.ιMulti R 4 ![dt,h,g,b] := by
  let w := exteriorPower.ιMulti (M := E) R 4
  rw [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul]
  have hh : w ![h,g + M • dt,h,b] = 0 :=
    w.map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have htt : w ![dt,dt,h,b] = 0 :=
    w.map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  have hsum : w ![dt,g + M • dt,h,b] = w ![dt,g,h,b] + w ![dt,M • dt,h,b] :=
    (w.curryLeft dt).map_vecCons_add ![h,b] g (M • dt)
  have hmul : w ![dt,M • dt,h,b] = M • w ![dt,dt,h,b] :=
    (w.curryLeft dt).map_vecCons_smul ![h,b] M dt
  have sw : ![dt,g,h,b] = ![dt,h,g,b] ∘ Equiv.swap (1 : Fin 4) 2 := by
    funext j; fin_cases j <;> rfl
  change w _ + L • w _ = _
  rw [hh,zero_add,hsum,hmul,htt,smul_zero,add_zero,sw,AlternatingMap.map_swap _ _ (by decide),
    smul_neg]
  exact (neg_smul L _).symm

set_option maxHeartbeats 500000 in
/-- The same regular four-form clears the poles of the marked incidence symbol
and gives the velocity of the fixed cubic on the actual special curve. -/
theorem marked_seed_pairing (v : Derivation ℂ (B t i) (A t i))
    (hv : v (algebraMap ℂ[ε] (B t i) ε) = 1) (β : Ω[P i⁄ℂ]) :
    let l := IsScalarTower.toAlgHom ℂ (P i) (overlap t i p)
    ∃ ν : Form ℂ (P i) 4,
      exteriorPullback l 4 ν = l (cubicJet i * rowJet t i p) •
        cup22 (markedSymbol t i p) (exteriorPullback l 2 (cubicConormalTest i β)) ∧
      exteriorMap (ρ t i) (mixedRestriction t i) 4 ν =
        v (toFamily t i (cubicOnT i)) • exteriorPower.ιMulti (A t i) 4
          ![dt t i,vertical t i (cubicJet i).fst,vertical t i (rowJet t i p).fst,mixedRestriction t i β] := by
  dsimp only
  let l := IsScalarTower.toAlgHom ℂ (P i) (overlap t i p)
  let m := mixedRestriction t i
  let d := D ℂ (P i)
  let ν := front 3 (d (F i)) (front 2 (d (G t i p)) (cubicConormalTest i β))
  refine ⟨ν, ?_, ?_⟩
  · have hMarked : markedSymbol t i p =
        CycleQ2NativeDoubleLocalization.cochain (K := ℂ) (F i) (G t i p) :=
      CycleQ2IncidenceSymbolDomain.marked t i p
    have clear := clears_poles (F i) (G t i p) (localizedF (K := ℂ) (F i) (G t i p))
      (localizedG (K := ℂ) (F i) (G t i p)) (localizedF_val _ _) (localizedG_val _ _) (cubicConormalTest i β)
    have e : (localizedF (K := ℂ) (F i) (G t i p) : overlap t i p) *
        localizedG (K := ℂ) (F i) (G t i p) = l (F i * G t i p) := by
      rw [localizedF_val, localizedG_val, map_mul]; rfl
    exact clear.symm.trans (((congrArg (fun r : overlap t i p => r • cup22
      (CycleQ2NativeDoubleLocalization.cochain (K := ℂ) (F i) (G t i p))
      (exteriorPullback l 2 (cubicConormalTest i β))) e)).trans
      (congrArg (fun α : Form ℂ (overlap t i p) 2 => l (F i * G t i p) •
        cup22 α (exteriorPullback l 2 (cubicConormalTest i β))) hMarked.symm))
  · have hH : m (d (fixedH i)) = vertical t i (F i).fst := by
      rw [show m (d (fixedH i)) = _ from mixed_D t i _, F, cubicJet_parts]
      rfl
    have h := evaluate_wedge (dt t i) (vertical t i (F i).fst) (vertical t i (G t i p).fst)
      (m β) (toCurve t i (F i).snd) (toCurve t i (G t i p).snd)
    rw [← map_neg, marked_curve_velocity t i v hv] at h
    rw [show ν = exteriorPower.ιMulti (P i) 4 ![d (F i),d (G t i p),d (fixedH i),β] from
      conormal_wedge (d (F i)) (d (G t i p)) (d (fixedH i)) β]
    rw [exteriorMap_wedge]
    refine Eq.trans (congrArg (exteriorPower.ιMulti (A t i) 4) ?_) h
    funext j
    fin_cases j
    · exact split_D t i _
    · exact split_D t i _
    · exact hH
    · rfl

end CycleQ2MarkedGysinNumerator
#print axioms CycleQ2MarkedGysinNumerator.marked_seed_pairing

namespace CycleQ2MarkedGysinNumerator
namespace ProjectiveEdge
open Module KaehlerDifferential CycleQ2MarkedLogarithmicVelocity
open CycleQ2LocalGysinProjection (exteriorMap_front interior_front)
open CycleQ2ArbitraryFrameDifferential (front)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2LiteralAbelJacobiContraction (contractRestrict contractRestrict_wedge T toCurve cubicOnT)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback onePullback)
open scoped TensorProduct DualNumber

section Normal
variable {R C : Type} [CommRing R] [CommRing C] [Algebra ℂ R] [Algebra ℂ C]
    [Algebra R C] [IsScalarTower ℂ R C]

abbrev Ambient (R C : Type) [CommRing R] [CommRing C] [Algebra ℂ R] [Algebra R C] :=
  C ⊗[R] Ω[R⁄ℂ]

/-- Keep ambient covectors after restricting scalars to the curve. -/
def alongCurve : Ω[R⁄ℂ] →ₛₗ[algebraMap R C] Ambient R C where
  toFun x := 1 ⊗ₜ[R] x
  map_add' _ _ := TensorProduct.tmul_add _ _ _
  map_smul' r x := by
    change 1 ⊗ₜ[R] (r • x) = (algebraMap R C r) • (1 ⊗ₜ[R] x)
    rw [TensorProduct.tmul_smul]
    exact (IsScalarTower.algebraMap_smul C r _).symm

def ambientVelocity (v : Derivation ℂ R C) : Ambient R C →ₗ[C] C :=
  v.liftKaehlerDifferential.liftBaseChange C

def toCurveForm : Ambient R C →ₗ[C] Ω[C⁄ℂ] :=
  (KaehlerDifferential.map ℂ ℂ R C).liftBaseChange C

private theorem velocity_d (v : Derivation ℂ R C) (f : R) :
    ambientVelocity v (alongCurve (C := C) (D ℂ R f)) = v f := by
  change v.liftKaehlerDifferential.liftBaseChange C (1 ⊗ₜ[R] D ℂ R f) = _
  rw [LinearMap.liftBaseChange_one_tmul, Derivation.liftKaehlerDifferential_comp_D]

def curveCoefficient (v : Derivation ℂ R C) (ω : Form ℂ R 2) : Ambient R C :=
  exteriorPower.oneEquiv C _ (interior 1 (ambientVelocity v)
    (exteriorMap (algebraMap R C) alongCurve 2 ω))

private theorem coefficient_projects (v : Derivation ℂ R C) (ω : Form ℂ R 2) :
    toCurveForm (curveCoefficient v ω) = contractRestrict v ω := by
  have h : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction h using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [curveCoefficient,exteriorMap_wedge,interior_wedge,Fin.sum_univ_two]
    rw [show a = ![a 0, a 1] from (List.ofFn_inj.mp (by simp [List.ofFn_succ]))]
    rw [contractRestrict_wedge]
    simp [ambientVelocity,alongCurve,toCurveForm,exteriorPower.oneEquiv_ιMulti,
      Fin.removeNth_apply,Fin.tail,sub_eq_add_neg]
  | zero => simp [curveCoefficient]
  | add x y _ _ hx hy =>
    change toCurveForm _ = _ at hx hy ⊢
    simpa [curveCoefficient, map_add] using congrArg₂ (· + ·) hx hy
  | smul a x _ hx =>
    unfold curveCoefficient
    rw [map_smulₛₗ,map_smul,map_smul,map_smul,map_smul,IsScalarTower.algebraMap_smul]
    exact congrArg (a • ·) hx

private theorem factor_contraction (v : Derivation ℂ R C) (f g : R)
    (hf : v f = 0) (hg : v g = 0) (ω : Form ℂ R 2) :
    let A := alongCurve (R := R) (C := C)
    interior 3 (ambientVelocity v)
      (exteriorMap (algebraMap R C) A 4 (front 3 (D ℂ R f) (front 2 (D ℂ R g) ω))) =
      front 2 (A (D ℂ R f)) (front 1 (A (D ℂ R g))
        ((exteriorPower.oneEquiv C _).symm (curveCoefficient v ω))) := by
  dsimp only
  rw [exteriorMap_front,exteriorMap_front,interior_front,interior_front,velocity_d,velocity_d,hf,hg]
  simp [curveCoefficient]
end Normal

open CycleQ2LiteralAbelJacobiMovingNormal (A B)
open CycleQ2LiteralAbelJacobiQPairCharts (BPair APair pairMap movingMap pairMap_source)
open CycleQ2LiteralThreefoldLiftTransition (jetMap sourceMap)
open CycleQ2LiteralThreefoldChartLift
open CycleQ2LiteralThreefoldResidueChartMaps
open CycleQ2LiteralThreefoldResidueCoordinates
open CycleQ2LiteralThreefoldPairMotion
open CycleQ2LiteralCylinderEvaluation
open CycleQ2LiteralAbelJacobiEquations (relativeEval dualEval chartMap dualEval_parameter)
open CycleQ2IncidenceSymbolFiber (H G)
open MvPolynomial

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  familyRing closedRing threefoldRing CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower CycleQ2LiteralAbelJacobiContraction.fixedAlgebra
  CycleQ2LiteralAbelJacobiContraction.fixedTower reductionAlgebra fixedCurveTower familyReductionTower
  reductionPairAlgebra reductionPairTower baseAlgebra baseTower baseATower baseBTower
  ambientThickAlgebra ambientThickTower ambientClosedAlgebra ambientClosedTower ambientPairTower
attribute [local instance 2000] Algebra.toSMul Algebra.toModule

private def specializeDual {U E : Type} [CommRing U] [CommRing E] [Algebra ℂ U] [Algebra ℂ E]
    (f : U →ₐ[ℂ] E) (e : E) (he : e * e = 0) : DualNumber U →ₐ[ℂ] E :=
  DualNumber.lift ⟨(f,e),he,fun _ => Commute.all _ _⟩

variable (t : Fin 3 → ℂ) (i : Fin 4) (k : Fin 3) (p : CycleQ2SegreCech.Chart)

private abbrev eB := algebraMap ℂ[ε] (B t i) ε
private theorem eB_square : eB t i * eB t i = 0 := by
  rw [eB,← map_mul,DualNumber.eps_mul_eps,map_zero]
private abbrev seedEval := specializeDual (movingMap t i) (eB t i) (eB_square t i)

open CycleQ2IncidenceDehomogenizedChart (ChartPolynomial)
private theorem evaluates_jet (w : ChartPolynomial ℂ[ε]) :
    seedEval t i (jet (fixedChartMap i) w) = dualEval t i w := by
  apply RingHom.congr_fun (f := (seedEval t i).toRingHom.comp (jet (fixedChartMap i)))
  apply MvPolynomial.ringHom_ext
  · intro z
    simp only [RingHom.comp_apply,jet,dualEval,eval₂Hom_C]
    change seedEval t i ((fixedChartMap i (C z.fst),fixedChartMap i (C z.snd)) : DualNumber (T i)) =
      algebraMap ℂ[ε] (B t i) z
    change algebraMap ℂ (B t i) z.fst + algebraMap ℂ (B t i) z.snd * eB t i = _
    rw [chartMap_constant,chartMap_constant,eB,←map_mul,←map_add]
    apply congrArg (algebraMap ℂ[ε] (B t i))
    apply TrivSqZeroExt.ext
    · change z.fst + z.snd * 0 = z.fst
      ring
    · change 0 + (z.snd * 1 + 0 * 0) = z.snd
      ring
  · intro x
    simp only [RingHom.comp_apply,jet,dualEval,eval₂Hom_X']
    change seedEval t i (algebraMap (T i) (DualNumber (T i)) (fixedChartMap i (X x))) = relativeEval t i (X x)
    rw [seedEval,specializeDual,TrivSqZeroExt.algebraMap_eq_inl,DualNumber.lift_apply_inl]
    change chartMap t i (X x) = relativeEval t i (X x)
    simp [CycleQ2LiteralAbelJacobiEquations.chartMap]

private theorem moving_equations :
    seedEval t i (cubicJet i) = 0 ∧ seedEval t i (rowJet t i p) = 0 := by
  constructor
  · rw [cubicJet,evaluates_jet,dualEval_parameter]
    simp only [relativeEval,RingHom.comp_apply,CycleQ2IncidenceDehomogenizedChart.dehomogenizedMap_equation,map_zero]
  · rw [rowJet,evaluates_jet,dualEval_parameter]
    have h : Ideal.Quotient.mk (CycleQ2RelativeCurveChart.affineSectionIdeal
        CycleQ2IncidenceEtaleParameter.incidencePoint t i)
        (CycleQ2RelativeCurveChart.affineSectionEquation CycleQ2IncidenceEtaleParameter.incidencePoint t i p.1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨p.1, rfl⟩)
    change Algebra.TensorProduct.includeRight (R := CycleQ2IncidenceEtaleParameter.ParameterAlgebra) (A := ℂ[ε])
      (B := CycleQ2RelativeCurveChart.AffineCurveChart CycleQ2IncidenceEtaleParameter.incidencePoint t i)
      (Ideal.Quotient.mk _ (CycleQ2RelativeCurveChart.affineSectionEquation
        CycleQ2IncidenceEtaleParameter.incidencePoint t i p.1)) = 0
    rw [h,map_zero]

abbrev Pair := FixedOverlap i k
abbrev DualPair := DualNumber (Pair i k)
def toDualPair := jetMap (sourceMap i k)
private abbrev thickPoint := pairMap i k (movingMap t i)
private abbrev epsPair := algebraMap (B t i) (BPair t i k) (eB t i)
private theorem epsPair_square : epsPair t i k * epsPair t i k = 0 := by
  rw [epsPair,←map_mul,eB_square,map_zero]
def thickEvaluation := specializeDual (thickPoint t i k) (epsPair t i k) (epsPair_square t i k)

private theorem thickEvaluation_source (x : CycleQ2MarkedGysinNumerator.P i) :
    thickEvaluation t i k (toDualPair i k x) = algebraMap (B t i) (BPair t i k) (seedEval t i x) := by
  change thickPoint t i k (sourceMap i k x.fst) + thickPoint t i k (sourceMap i k x.snd) * _ =
    algebraMap (B t i) (BPair t i k) (movingMap t i x.fst + movingMap t i x.snd * _)
  simp only [thickPoint,pairMap_source,map_add,map_mul]
  rfl

abbrev cubic := toDualPair i k (cubicJet i)
abbrev row := toDualPair i k (rowJet t i p)
private theorem thick_pair_equations :
    thickEvaluation t i k (cubic i k) = 0 ∧ thickEvaluation t i k (row t i k p) = 0 := by
  rw [cubic,row,thickEvaluation_source,thickEvaluation_source,(moving_equations t i p).1,
    (moving_equations t i p).2,map_zero]
  exact ⟨rfl,rfl⟩

open CycleQ2LiteralAbelJacobiQPairReduction (reduce)
local instance thickAlgebra : Algebra (DualPair i k) (BPair t i k) :=
  (thickEvaluation t i k).toRingHom.toAlgebra
local instance thickTower : IsScalarTower ℂ (DualPair i k) (BPair t i k) :=
  IsScalarTower.of_algHom (thickEvaluation t i k)
local instance curveAlgebra : Algebra (DualPair i k) (APair t i k) :=
  ((reduce t i k).comp (thickEvaluation t i k)).toRingHom.toAlgebra
local instance curveTower : IsScalarTower ℂ (DualPair i k) (APair t i k) :=
  IsScalarTower.of_algHom ((reduce t i k).comp (thickEvaluation t i k))
local instance reductionTower : IsScalarTower (DualPair i k) (BPair t i k) (APair t i k) :=
  IsScalarTower.of_algebraMap_eq' rfl
local instance fixedThick : IsScalarTower (Pair i k) (DualPair i k) (BPair t i k) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    change thickPoint t i k x = thickEvaluation t i k (TrivSqZeroExt.inl x)
    rw [thickEvaluation,specializeDual,DualNumber.lift_apply_inl]
local instance fixedCurve : IsScalarTower (Pair i k) (DualPair i k) (APair t i k) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (Pair i k) (BPair t i k) (APair t i k),
      IsScalarTower.algebraMap_apply (DualPair i k) (BPair t i k) (APair t i k),
      ← IsScalarTower.algebraMap_apply (Pair i k) (DualPair i k) (BPair t i k)]

open CycleQ2LiteralThreefoldTestEdges (nativeEdge edgeAt)
open CycleQ2LiteralAbelJacobiQNativeSeedEvaluation (pairVelocity)
open CycleQ2CurveCylinderPullback (pullTwo contract_pullTwo)
open CycleQ2NativeDoubleLocalization (cochain localizedF localizedG localizedF_val localizedG_val)
open CycleQ2IncidenceLogSpread (relativeTwo onOverlap native_baseChange)
open CycleQ2LocalGysinProjection (cup22 clears_poles)

abbrev PoleRing := CycleQ2NativeDoubleLocalization.T (cubic i k) (row t i k p)
def poleSymbol : Form ℂ (PoleRing t i k p) 2 :=
  relativeTwo (l := ℂ) (onOverlap (toDualPair i k) (cubicJet i) (rowJet t i p))
    (markedSymbol t i p)
set_option maxRecDepth 4096 in
private theorem poleSymbol_eq : poleSymbol t i k p = cochain (K := ℂ) (cubic i k) (row t i k p) := by
  let φ := onOverlap (toDualPair i k) (cubicJet i) (rowJet t i p)
  have h : markedSymbol t i p = cochain (K := ℂ) (cubicJet i) (rowJet t i p) :=
    CycleQ2IncidenceSymbolDomain.marked t i p
  exact (congrArg (relativeTwo (l := ℂ) φ) h).trans
    (native_baseChange (l := ℂ) (toDualPair i k) (cubicJet i) (rowJet t i p))

abbrev testEdge := pullTwo (Pair i k) (DualPair i k) (nativeEdge i k)
abbrev velocity (ht : AlgebraicIndependent ℚ t) :=
  (pairVelocity t ht i k).compAlgebraMap (DualPair i k)

def nativeCoefficient (ht : AlgebraicIndependent ℚ t) := curveCoefficient (velocity t i k ht) (testEdge i k)

set_option maxRecDepth 4096 in
private theorem edge_coefficient (ht : AlgebraicIndependent ℚ t) :
    toCurveForm (nativeCoefficient t i k ht) =
      contractRestrict ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k)) (nativeEdge i k) := by
  refine (coefficient_projects _ _).trans ((contract_pullTwo _ _).trans ?_)
  apply congrArg (fun v => contractRestrict v (nativeEdge i k))
  ext x
  change pairVelocity t ht i k (algebraMap (DualPair i k) (BPair t i k) (algebraMap (Pair i k) (DualPair i k) x)) =
    pairVelocity t ht i k (algebraMap (Pair i k) (BPair t i k) x)
  rw [← IsScalarTower.algebraMap_apply]

set_option maxHeartbeats 600000 in
set_option maxRecDepth 4096 in
/-- On the projective overlap the time contraction of the common incidence numerator
factors through both conormals. Its remaining covector restricts on the closed seed
pair to the actual moving-family evaluation of the native test edge. -/
theorem native_edge_projection (ht : AlgebraicIndependent ℚ t) :
    let C := APair t i k
    let l := IsScalarTower.toAlgHom ℂ (DualPair i k) (PoleRing t i k p)
    let F := cubic i k
    let G := row t i k p
    let ω := testEdge i k
    let j := alongCurve (R := DualPair i k) (C := C)
    let w := velocity t i k ht
    let β := nativeCoefficient t i k ht
    ∃ ν : Form ℂ (DualPair i k) 4,
      exteriorPullback l 4 ν = l (F*G) • cup22 (poleSymbol t i k p) (exteriorPullback l 2 ω) ∧
      interior 3 (ambientVelocity w) (exteriorMap (algebraMap (DualPair i k) C) j 4 ν) =
        front 2 (j (D ℂ (DualPair i k) F)) (front 1 (j (D ℂ (DualPair i k) G))
          ((exteriorPower.oneEquiv C _).symm β)) ∧
      toCurveForm β = contractRestrict ((pairVelocity t ht i k).compAlgebraMap (FixedOverlap i k)) (nativeEdge i k) := by
  dsimp only
  let F := cubic i k
  let G := row t i k p
  let ω := testEdge i k
  let w := velocity t i k ht
  let l := IsScalarTower.toAlgHom ℂ (DualPair i k) (PoleRing t i k p)
  refine ⟨front 3 (D ℂ _ F) (front 2 (D ℂ _ G) ω),?_,?_,edge_coefficient t i k ht⟩
  · have clear := clears_poles F G (localizedF (K := ℂ) F G) (localizedG (K := ℂ) F G)
      (localizedF_val _ _) (localizedG_val _ _) ω
    have h : (localizedF (K := ℂ) F G : PoleRing t i k p) * localizedG (K := ℂ) F G = l (F*G) := by
      rw [localizedF_val,localizedG_val,map_mul]; rfl
    exact clear.symm.trans ((congrArg (fun r : PoleRing t i k p =>
      r • cup22 (cochain (K := ℂ) F G) (exteriorPullback l 2 ω)) h).trans
      (congrArg (fun a : Form ℂ (PoleRing t i k p) 2 => l (F*G) • cup22 a (exteriorPullback l 2 ω))
        (poleSymbol_eq t i k p).symm))
  · have hf : w F = 0 := by
      change pairVelocity t ht i k (thickEvaluation t i k (cubic i k)) = 0
      rw [(thick_pair_equations t i k p).1,map_zero]
    have hg : w G = 0 := by
      change pairVelocity t ht i k (thickEvaluation t i k (row t i k p)) = 0
      rw [(thick_pair_equations t i k p).2,map_zero]
    exact factor_contraction w F G hf hg ω

section Cech
open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralThreefoldCurveTestSections CycleQ2LiteralThreefoldVertexMotion
open CycleQ2LiteralThreefoldCurveEvaluationRefinement CycleQ2LiteralThreefoldSurfaceTestLifts
open CycleQ2LiteralAbelJacobiQNativeSeedEvaluation CycleQ2LiteralAbelJacobiQPairSeedSections
open CycleQ2LiteralAbelJacobiEvaluationChart CycleQ2LiteralAbelJacobiEvaluationFiber
open CycleQ2LiteralThreefoldHodgeCech CycleQ2LiteralAmbientCharts
open CycleQ2LiteralAbelJacobiEvaluationDerived CycleQ2LiteralAbelJacobiQPullback
open CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover
open CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueAdjunction.AffineFrame
open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
open CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne CycleQ2InjectiveCech
open CycleQ2LiteralMovingCurveDifferentialNonzero CycleQ2GeometricSheafLocalIso

local instance (Z : Scheme.{0}) : HasExt.{1} (AbSheaf Z) := HasExt.standard _
variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

private theorem over_chart (u v : Vertex) (W : (Curve t).Opens) (hu : W ≤ vertexOpen t u)
    (hv : W ≤ vertexOpen t v) :
    W ≤ (seedToTime t V hV ≫ toThreefold V t) ⁻¹ᵁ (fixedOpen (chartIndex u) ⊓ fixedOpen (chartIndex v)) := by
  rw [Scheme.Hom.preimage_inf]
  exact le_inf (hu.trans (vertex_le_test t V hV u)) (hv.trans (vertex_le_test t V hV v))

private theorem on_chart (u : Vertex) (W : (Curve t).Opens) (hu : W ≤ vertexOpen t u) :
    W ≤ (seedChart t (chartIndex u)).opensRange :=
  hu.trans ((vertexWithin t u).trans (seedChart_opensRange t (chartIndex u)).ge)

variable (ht : AlgebraicIndependent ℚ t)
def coefficientOn (u v : Vertex) (h : chartIndex u < chartIndex v) (W : (Curve t).Opens)
    (hu : W ≤ vertexOpen t u) (hv : W ≤ vertexOpen t v) :=
  let i := chartIndex u
  let j := chartIndex v
  let U := fixedOpen i ⊓ fixedOpen j
  let k := slot i j h
  seedOne t i k W (withinNativePair t i V hV j h U inf_le_right W
    (over_chart t V hV u v W hu hv) (on_chart t u W hu))
    (toCurveForm (nativeCoefficient t i k ht))

set_option maxRecDepth 4096 in
private theorem on_increasing_edge (u v : Vertex) (h : chartIndex u < chartIndex v) (W : (Curve t).Opens)
    (hu : W ≤ vertexOpen t u) (hv : W ≤ vertexOpen t v) :
    edgeValue (curveForms t) (vertexOpen t) (nativeTest t V hV ht) u v W hu hv =
      coefficientOn t V hV ht u v h W hu hv := by
  let i := chartIndex u
  let j := chartIndex v
  let k := slot i j h
  let U := fixedOpen i ⊓ fixedOpen j
  let hW := over_chart t V hV u v W hu hv
  let hY := on_chart t u W hu
  exact (nativeTest_edge t V hV ht u v W hu hv).trans
    ((evaluatedTest_native t ht i V hV j h U inf_le_left inf_le_right W hW hY).trans
      (congrArg (seedOne t i k W (withinNativePair t i V hV j h U inf_le_right W hW hY))
        (edge_coefficient t i k ht).symm))

/-- The ordinary curve coefficient of the marked numerators, with signs on
reversed pairs of the twelve projective vertex opens. -/
def numeratorCochain : One (curveForms t) (vertexOpen t) := fun u v =>
  let W := vertexOpen t u ⊓ vertexOpen t v
  if h : chartIndex u < chartIndex v then coefficientOn t V hV ht u v h W inf_le_left inf_le_right
  else if h : chartIndex v < chartIndex u then -coefficientOn t V hV ht v u h W inf_le_right inf_le_left
  else 0

set_option maxRecDepth 4096 in
theorem numerator_cochain_eq : numeratorCochain t V hV ht = nativeTest t V hV ht := by
  funext u v
  let W := vertexOpen t u ⊓ vertexOpen t v
  let F := curveForms t
  let U := vertexOpen t
  let c := nativeTest t V hV ht
  have hu : W ≤ U u := inf_le_left
  have hv : W ≤ U v := inf_le_right
  have he : edgeValue F U c u v W hu hv = c u v := res_self F W _
  change _ = c u v
  rw [← he]
  dsimp only [numeratorCochain]
  by_cases h : chartIndex u < chartIndex v
  · exact (dif_pos h).trans (on_increasing_edge t V hV ht u v h W hu hv).symm
  · refine (dif_neg h).trans ?_
    by_cases h' : chartIndex v < chartIndex u
    · refine (dif_pos h').trans ?_
      have hz := oneCocycle_diagonal c (nativeTest_closed t V hV ht) u W hu
      have hs := nativeTest_closed t V hV ht u v u W hu hv hu
      change edgeValue F U c u u W hu hu = edgeValue F U c u v W hu hv + edgeValue F U c v u W hv hu at hs
      change edgeValue F U c u u W hu hu = 0 at hz
      exact (congrArg Neg.neg (on_increasing_edge t V hV ht v u h' W hv hu).symm).trans
        (eq_neg_of_add_eq_zero_left (hs.symm.trans hz)).symm
    · refine (dif_neg h').trans (Eq.trans ?_ (nativeTest_edge t V hV ht u v W hu hv).symm)
      have diagonal (a b : Fin 4) (e : a = b) (ha : W ≤ testCover t V hV a) (hb : W ≤ testCover t V hV b) :
          0 = edgeValue F (testCover t V hV) (evaluatedTest t ht V hV) a b W ha hb := by
        subst b
        exact (oneCocycle_diagonal (evaluatedTest t ht V hV) (evaluatedTest_closed t ht V hV) a W ha).symm
      exact diagonal _ _ (le_antisymm (le_of_not_gt h') (le_of_not_gt h)) _ _


theorem numerator_closed : IsOneCocycle (curveForms t) (vertexOpen t) (numeratorCochain t V hV ht) :=
  (numerator_cochain_eq t V hV ht).symm ▸ nativeTest_closed t V hV ht

/-- The curve cohomology class of the actual marked numerator coefficients. -/
theorem numerator_class :
    cechOneClass (vertexOpen t) (vertexOpen_cover t) (numeratorCochain t V hV ht)
      (numerator_closed t V hV ht) = -curveClass t := by
  simpa only [numerator_cochain_eq] using (evaluated_class_native t V hV ht).symm.trans
    (CycleQ2LiteralThreefoldCurvePairing.signed_class t ht V hV)
/-- The signed class has nonzero scalar trace on every regular marked seed curve. -/
theorem numerator_trace_ne_zero (hreg : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i) :
    differentialTrace t hreg (cechOneClass (vertexOpen t) (vertexOpen_cover t) (numeratorCochain t V hV ht)
      (numerator_closed t V hV ht)) ≠ 0 := by
  rw [numerator_class,map_neg]
  exact neg_ne_zero.mpr (differentialTrace_curveClass_ne_zero t hreg)


open CategoryTheory.Limits CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceRelativeCompletion
  CycleQ2LiteralIncidenceRelativeCorrespondence CycleQ2LiteralIncidenceGenericCorrespondence
  CycleQ2GenericSmoothCurveGraph CycleQ2SurvivingProductGysin
open CycleQ2NativeWeightedCover (ambientToField)

/-- The class on the literal generic graph and the nonzero trace of the marked
numerator use the same parameter curve and the same section. -/
theorem exists_literal_graph_with_seed_trace :
    ∃ (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t) (V : parameterScheme.Opens)
      (hV : seedBasePoint ∈ V) (C : Scheme) (c : C ⟶ Spec (CommRingCat.of genericField))
      (r : C ⟶ Completion V) (hc : r ≫ structureMap V = c ≫ genericPoint)
      (D : Scheme) (j : D ⟶ C) (a : D ⟶ Time toRaw V)
      (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion V),
      let m := fromTest V t r j a ha
      let b := m.imageι ≫ embeddingGeneric V t r c hc
      IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c ∧
      CycleQ2MarkedGenericSurvives.SeedCompatible t V hV c r j a ∧
      ∃ (U : genericAmbient.Opens) (S : Scheme) (I : S ⟶ pullback c (U.ι ≫ ambientToField))
        (v : S ⟶ TestSurface V t a),
        IsOpenImmersion v ∧ IsPullback I (v ≫ m.toImage) (literalOpen c U) b ∧ LiteralClass c U I ∧
        ∃ hreg : ∀ i, CycleQ2SeedSectionAffineInjective.ChartRegular t i,
          let τ := differentialTrace t hreg (cechOneClass (vertexOpen t) (vertexOpen_cover t)
            (numeratorCochain t V hV ht) (numerator_closed t V hV ht))
          τ = -differentialTrace t hreg (curveClass t) ∧ τ ≠ 0 := by
  obtain ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hs,_,_,_,U,_,_,S,i,v,_,hvo,_,_,
    ⟨_,hseed⟩,_,⟨hpb,hLit⟩,_⟩ := exists_seed_compatible_literal_product
  obtain ⟨hreg,htrace⟩ := hseed.1
  refine ⟨t,ht,V,hV,C,c,r,hc,D,j,a,ha,hC,hp,hs,hseed,U,S,_,v,hvo,hpb,hLit,hreg,?_⟩
  dsimp only
  rw [numerator_class,map_neg]
  exact ⟨rfl,neg_ne_zero.mpr htrace⟩

end Cech

end ProjectiveEdge
end CycleQ2MarkedGysinNumerator
#print axioms CycleQ2MarkedGysinNumerator.ProjectiveEdge.native_edge_projection
#print axioms CycleQ2MarkedGysinNumerator.ProjectiveEdge.numerator_class
#print axioms CycleQ2MarkedGysinNumerator.ProjectiveEdge.numerator_trace_ne_zero

#print axioms CycleQ2MarkedGysinNumerator.ProjectiveEdge.exists_literal_graph_with_seed_trace
