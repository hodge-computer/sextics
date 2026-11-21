import Proposal.GeometricLocalGysinProjection
import Proposal.GeometricIncidenceLogarithmicSpecialization

/-! The regular numerator of the marked logarithmic cochain on the actual
dual-number chart specializes to the moving adjunction numerator on the seed curve.

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
