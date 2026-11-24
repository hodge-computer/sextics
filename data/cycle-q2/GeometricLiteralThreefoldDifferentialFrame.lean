import Proposal.GeometricSurfaceResidueOverlap
import Proposal.GeometricExteriorLocalFrames

/-!
# Determinant coordinates for genuine differential sheaves on a basis chart

The coefficient functionals of an affine Kähler basis extend to the sheaf of
one-forms on the chart. The universal property identifies reconstruction from
those functionals with the identity on every subopen. Taking the determinant
and sheafifying gives a coordinate on the top exterior sheaf which evaluates
the original chart forms by their ordinary basis determinant.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldDifferentialFrame

open CategoryTheory Opposite AlgebraicGeometry Module
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricAffineChartSections CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricExteriorSheaf
  CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2GeometricExteriorLocalFrames CycleQ2ExteriorTopBaseChange

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential ℂ A))

private abbrev lift (V : Over U) := sectionLift X.sheaf (schemeCoefficient f)
  (differentialSheaf X.sheaf (schemeCoefficient f)) (universalDifferential X.sheaf (schemeCoefficient f))
  V.left (chartSection e V) (chartSection_complex e f h V)

private abbrev coordinate (i : Fin n) := CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap e f h (b.coord i)

private theorem lift_restrict {V W : Over U} (a : V ⟶ W) (x : KaehlerDifferential ℂ A) :
    (ChartDifferentialModule f).val.map a.op (lift e f h W x) = lift e f h V x :=
  sectionLift_restriction X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f)) (universalDifferential X.sheaf (schemeCoefficient f))
    W.left (chartSection e W) (chartSection_complex e f h W) V.left a.left.le
    (chartSection e V) (chartSection_complex e f h V) (chartSection_naturality e a) x

private theorem coordinate_lift (i : Fin n) (V : Over U) (x : KaehlerDifferential ℂ A) :
    (coordinate e f h b i).val.app (op V) (lift e f h V x) = chartSection e V (b.coord i x) := by
  rw [← lift_restrict e f h (toChartTop V), PresheafOfModules.naturality_apply]
  rw [show (coordinate e f h b i).val.app (op (chartTop U)) (lift e f h (chartTop U) x) = _ from
    CycleQ2GeometricFunctionalDifferentials.chartCoefficientMap_sectionLift e f h (b.coord i) x]
  exact chartSection_naturality e (toChartTop V) _

private def reconstructTerm (i : Fin n) : ChartDifferentialModule (U := U) f ⟶ ChartDifferentialModule (U := U) f :=
  coordinate e f h b i ≫ unitMapFromChart (ChartDifferentialModule f) (lift e f h (chartTop U) (b i))

private def homEval (V : Over U) (x : (ChartDifferentialModule f).val.obj (op V)) :
    (ChartDifferentialModule (U := U) f ⟶ ChartDifferentialModule (U := U) f) →+
      (ChartDifferentialModule f).val.obj (op V) where
  toFun g := g.val.app (op V) x
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem reconstructTerm_eval (V : Over U) (x : (ChartDifferentialModule f).val.obj (op V)) (i : Fin n) :
    homEval f V x (reconstructTerm e f h b i) =
      ((coordinate e f h b i).val.app (op V) x : Γ(X,V.left)) • lift e f h V (b i) := by
  change (unitMapFromChart (ChartDifferentialModule f) (lift e f h (chartTop U) (b i))).val.app (op V) ((coordinate e f h b i).val.app (op V) x) = _
  rw [unitMapFromChart_apply, lift_restrict]

private theorem reconstruction : ∑ i : Fin n, reconstructTerm e f h b i = 𝟙 (ChartDifferentialModule f) := by
  apply restrictedLift_unique X.sheaf (schemeCoefficient f) U
  apply chartDerivation_ext e f h
  intro a
  let V := chartTop U
  let x := KaehlerDifferential.D ℂ A a
  let y := (universalDifferential X.sheaf (schemeCoefficient f)).d (X := op U) (chartSection e V a)
  have hxy : lift e f h V x = y := sectionLift_D X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f)) (universalDifferential X.sheaf (schemeCoefficient f))
    V.left (chartSection e V) (chartSection_complex e f h V) a
  change homEval f V y (∑ i : Fin n, reconstructTerm e f h b i) = y
  refine (congrArg (fun z => homEval f V z (∑ i : Fin n, reconstructTerm e f h b i)) hxy.symm).trans ?_
  refine Eq.trans ?_ hxy
  rw [map_sum]
  simp only [reconstructTerm_eval, coordinate_lift]
  calc
    _ = ∑ i : Fin n, lift e f h V (b.coord i x • b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (sectionLift_smul X.sheaf (schemeCoefficient f) (differentialSheaf X.sheaf (schemeCoefficient f))
        (universalDifferential X.sheaf (schemeCoefficient f)) V.left (chartSection e V)
        (chartSection_complex e f h V) (b.coord i x) (b i)).symm
    _ = _ := by rw [← map_sum]; exact congrArg (lift e f h V) (b.sum_repr x)

/-- The basis gives coordinates on all genuine one-form sections on a subopen. -/
def sectionEquiv (V : Over U) :
    (ChartDifferentialModule f).val.obj (op V) ≃ₗ[Γ(X,V.left)] (Fin n → Γ(X,V.left)) where
  toFun x i := (coordinate e f h b i).val.app (op V) x
  invFun c := ∑ i, c i • lift e f h V (b i)
  left_inv x := by
    have hh := congrArg (homEval f V x) (reconstruction e f h b)
    rw [map_sum] at hh
    simp only [reconstructTerm_eval] at hh
    exact hh.trans (show homEval f V x (𝟙 (ChartDifferentialModule f)) = x from rfl)
  right_inv c := by
    funext i
    change (coordinate e f h b i).val.app (op V) (∑ j, c j • lift e f h V (b j)) = c i
    simp only [map_sum, map_smul, coordinate_lift, Basis.coord_apply, Basis.repr_self_apply]
    simp [apply_ite, smul_eq_mul]
  map_add' x y := funext fun i => map_add _ x y
  map_smul' a x := funext fun i => map_smul _ a x

/-- The basis transported to the sheaf consists of the original affine basis sections. -/
def sectionBasis (V : Over U) : Basis (Fin n) Γ(X,V.left) ((ChartDifferentialModule f).val.obj (op V)) :=
  Basis.ofEquivFun (sectionEquiv e f h b V)

theorem sectionBasis_apply (V : Over U) (i : Fin n) : sectionBasis e f h b V i = lift e f h V (b i) := by
  apply (sectionEquiv e f h b V).injective
  rw [show sectionBasis e f h b V i = (sectionEquiv e f h b V).symm (Pi.single i 1) from
    congrFun (Basis.coe_ofEquivFun (sectionEquiv e f h b V)) i, LinearEquiv.apply_symm_apply]
  funext j
  change (Pi.single i 1 : Fin n → Γ(X,V.left)) j = (coordinate e f h b j).val.app (op V) (lift e f h V (b i))
  by_cases hij : i = j <;> simp [coordinate_lift, Basis.coord_apply, hij, eq_comm]

private theorem sectionBasis_restrict {V W : Over U} (a : V ⟶ W) (i : Fin n) :
    (ChartDifferentialModule f).val.map a.op (sectionBasis e f h b W i) = sectionBasis e f h b V i := by
  rw [sectionBasis_apply,sectionBasis_apply,lift_restrict]

private def coords (V : Over U) := topCoordinateEquiv (sectionBasis e f h b V)

private theorem topCoordinate_natural {R S M N : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] {d : ℕ}
    (φ : R →+* S) (g : M →ₛₗ[φ] N) (bR : Basis (Fin d) R M) (bS : Basis (Fin d) S N)
    (hb : ∀ i, g (bR i) = bS i) (ω : ⋀[R]^d M) :
    topCoordinate bS (exteriorMap φ g d ω) = φ (topCoordinate bR ω) := by
  refine (congrArg (fun z => topCoordinate bS (exteriorMap φ g d z)) (topCoordinate_smul_wedge bR ω).symm).trans ?_
  rw [map_smulₛₗ, exteriorMap_wedge, show (fun i => g (bR i)) = bS from funext hb,
    map_smul, topCoordinate_basis, smul_eq_mul, mul_one]

private theorem coords_restrict {V W : Over U} (a : V ⟶ W)
    (ω : ⋀[Γ(X,W.left)]^n ((ChartDifferentialModule f).val.obj (op W))) :
    coords e f h b V (exteriorMap (X.presheaf.map a.left.op).hom
      ((differentialSheaf X.sheaf (schemeCoefficient f)).val.restrictₛₗ a.left.op) n ω) =
      X.presheaf.map a.left.op (coords e f h b W ω) := by
  exact topCoordinate_natural (X.presheaf.map a.left.op).hom
    ((differentialSheaf X.sheaf (schemeCoefficient f)).val.restrictₛₗ a.left.op)
    (sectionBasis e f h b W) (sectionBasis e f h b V) (sectionBasis_restrict e f h b a) ω

/-- On each subopen of a Kähler basis chart, the genuine top differential
sheaf has its determinant coordinate. -/
def frameIso :
    (exteriorSheaf X.sheaf (differentialSheaf X.sheaf (schemeCoefficient f)).val n).over U ≅
      SheafOfModules.unit ((ringSheaf X.sheaf).over U) :=
  exteriorSheafOverIso X.sheaf _ n U (coords e f h b) (coords_restrict e f h b)

/-- The determinant coordinate on the sheaf recovers the original affine determinant. -/
theorem frameIso_on_section (V : Over U) (ω : ⋀[A]^n (KaehlerDifferential ℂ A)) :
    (frameIso e f h b).hom.val.app (op V) (chartExteriorSheafSection e f h n V ω) =
      chartSection e V (topCoordinate b ω) := by
  have hb : (frameIso e f h b).hom.val.app (op V)
      (chartExteriorSheafSection e f h n V (exteriorPower.ιMulti A n b)) = (1 : Γ(X,V.left)) := by
    change (frameIso e f h b).hom.val.app (op V) (exteriorSectionLift _ _ _ _ _ _ _ n _) = (1 : Γ(X,V.left))
    rw [exteriorSectionLift_wedge]
    change (frameIso e f h b).hom.val.app (op V) (exteriorSection _ _ n V.left (exteriorPower.ιMulti _ n _)) = (1 : Γ(X,V.left))
    rw [frameIso, exteriorSheafOverIso_exteriorSection]
    change topCoordinate (sectionBasis e f h b V)
      (exteriorPower.ιMulti _ n (fun i => lift e f h V (b i))) = 1
    simp only [← sectionBasis_apply e f h b V, topCoordinate_basis]
  refine (congrArg (fun z => (frameIso e f h b).hom.val.app (op V)
    (chartExteriorSheafSection e f h n V z)) (topCoordinate_smul_wedge b ω).symm).trans ?_
  rw [map_smulₛₗ, map_smul, hb]
  exact mul_one (chartSection e V (topCoordinate b ω))

end CycleQ2LiteralThreefoldDifferentialFrame
end
#print axioms CycleQ2LiteralThreefoldDifferentialFrame.frameIso_on_section
