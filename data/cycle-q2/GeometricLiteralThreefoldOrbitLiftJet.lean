import Proposal.GeometricLiteralThreefoldLiftDifference
import Proposal.GeometricLiteralThreefoldLiftTransition

/-!
# Transporting first-order points of the test deformation

A chart substitution preserving the sextic and multiplying the test by a
complex scalar carries a point of the deformation to another such point
when it also scales the infinitesimal coefficient by that scalar. Subtracting
two lifts commutes with this operation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitLift

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldKodairaSpencer CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldTangentCoordinates CycleQ2LiteralThreefoldLiftDifference
  CycleQ2LiteralThreefoldLiftTransition CycleQ2GeometricSurfaceFirstOrder

variable {S U : Type*} [CommRing S] [Algebra ℂ S] [CommRing U] [Algebra ℂ U]

def scaleJet (z : ℂ) : Jet S →ₐ[ℂ] Jet S where
  __ := dualMapScaled (RingHom.id S) (algebraMap ℂ S z)
  commutes' c := by
    apply TrivSqZeroExt.ext
    · rfl
    · exact mul_zero _

@[simp] theorem scaleJet_fst (z : ℂ) (t : Jet S) : (scaleJet z t).fst = t.fst := rfl
@[simp] theorem scaleJet_snd (z : ℂ) (t : Jet S) :
    (scaleJet z t).snd = algebraMap ℂ S z * t.snd := rfl

theorem scaleJet_eps (z : ℂ) :
    scaleJet z (TrivSqZeroExt.inr 1 : Jet S) =
      (TrivSqZeroExt.inr 1 : Jet S) * algebraMap ℂ (Jet S) z := by
  apply TrivSqZeroExt.ext
  · exact (zero_mul _).symm
  · change algebraMap ℂ S z * 1 = 0 * 0 + 1 * algebraMap ℂ S z
    rw [zero_mul, zero_add, one_mul, mul_one]

private theorem aeval_coordinates (m : P →ₐ[ℂ] Jet S) :
    aeval (fun a => m (X a)) = m := by
  apply MvPolynomial.algHom_ext
  intro a
  exact aeval_X _ _

variable {i : Fin 4} (A : P →ₐ[ℂ] P) (z : ℂ)
    (hF : A (seedF i) = seedF i) (hB : A (test i) = C z * test i)

def transformBy (x : Lift i S) : Lift i S where
  x a := ((scaleJet z).comp ((aeval x.x).comp A)) (X a)
  equation := by
    rw [aeval_coordinates]
    simp only [AlgHom.comp_apply, hF, hB, x.equation, map_mul, aeval_C, AlgHom.commutes,
      scaleJet_eps, mul_assoc]

theorem transformBy_eval (x : Lift i S) (p : P) :
    aeval (transformBy A z hF hB x).x p = scaleJet z (aeval x.x (A p)) :=
  AlgHom.congr_fun (aeval_coordinates ((scaleJet z).comp ((aeval x.x).comp A))) p

variable (a : T i →ₐ[ℂ] T i) (ha : ∀ p, a (q i p) = q i (A p))

include ha in
theorem transformBy_liesOver {x : Lift i S} {f : T i →ₐ[ℂ] S} (hx : LiesOver x f) :
    LiesOver (transformBy A z hF hB x) (f.comp a) := by
  intro j
  change (aeval x.x (A (X j))).fst = f (a (q i (X j)))
  rw [ha, eval_fst x f hx]

theorem transformBy_fst_eq (x y : Lift i S) (h : ∀ j, (x.x j).fst = (y.x j).fst) (j : Index) :
    ((transformBy A z hF hB x).x j).fst = ((transformBy A z hF hB y).x j).fst :=
  aeval_fst_eq x.x y.x h (A (X j))

include ha in
theorem tangentPoint_transformBy (x y : Lift i S) (h : ∀ j, (x.x j).fst = (y.x j).fst) :
    tangentPoint (transformBy A z hF hB x) (transformBy A z hF hB y)
        (transformBy_fst_eq A z hF hB x y h) =
      (scaleJet z).comp ((tangentPoint x y h).comp a) := by
  apply AlgHom.ext
  intro t
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective t
  change tangentPoint _ _ _ (q i p) = scaleJet z (tangentPoint x y h (a (q i p)))
  rw [ha, tangentPoint_mk, tangentPoint_mk, transformBy_eval, transformBy_eval]
  apply TrivSqZeroExt.ext
  · rfl
  · exact (mul_sub _ _ _).symm

private theorem jetMap_scale (b : S →ₐ[ℂ] U) (x : Jet S) :
    jetMap b (scaleJet z x) = scaleJet z (jetMap b x) := by
  apply TrivSqZeroExt.ext
  · rfl
  · exact (map_mul b _ _).trans (congrArg (· * b x.snd) (b.commutes z))

theorem mapLift_transformBy (b : S →ₐ[ℂ] U) (x : Lift i S) :
    mapLift b (transformBy A z hF hB x) = transformBy A z hF hB (mapLift b x) := by
  apply lift_ext
  funext j
  change jetMap b (scaleJet z (aeval x.x (A (X j)))) = scaleJet z (aeval (mapLift b x).x (A (X j)))
  rw [jetMap_scale]
  apply congrArg (scaleJet z)
  exact AlgHom.congr_fun (show (jetMap b).comp (aeval x.x) = aeval (mapLift b x).x by
    apply MvPolynomial.algHom_ext
    intro k
    simp [mapLift]) (A (X j))

end CycleQ2LiteralThreefoldOrbitLift
end

#print axioms CycleQ2LiteralThreefoldOrbitLift.tangentPoint_transformBy
#print axioms CycleQ2LiteralThreefoldOrbitLift.mapLift_transformBy
