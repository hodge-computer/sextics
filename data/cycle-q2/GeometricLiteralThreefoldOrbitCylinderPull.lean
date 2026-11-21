import Proposal.GeometricLiteralThreefoldOrbitHodgePullback
import Proposal.GeometricExteriorPullComposition

/-!
# Pullback along the translated moving-family projection

The pullback defined for a threefold automorphism and the inverse-image
construction for arbitrary scheme maps both evaluate on the same Čech
cocycle. This identifies the pullback along the second projection followed by
the automorphism with the original family's pullback of the acted class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralThreefoldOrbitCylinderPull

open CategoryTheory AlgebraicGeometry CycleQ2LiteralThreefoldHodgeCech
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechHOne CycleQ2FiniteCechOrbitPullback
  CycleQ2LiteralThreefoldOrbitHodgePullback CycleQ2LiteralAmbientCharts
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralAbelJacobiQPullback
  CycleQ2ExteriorPullComposition
open CycleQ2LiteralAbelJacobiQPullbackDerived (pullH qHodge)

local instance (S : Scheme.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from S)) :=
  HasExt.standard _

variable (e : Threefold ≅ Threefold) (hbase : e.hom ≫ structureMap = structureMap)

theorem pullH_eq_hodgePull (ω : NativeEdges) (hω) :
    pullH e.hom.base (hodgeAdd e hbase) 1 (hodgeClass ω hω) =
      hodgePull e hbase (hodgeClass ω hω) := by
  let a := hodgeCocycle ω hω
  have ha : IsOneCocycle HodgeSheaf fixedOpen a.val :=
    fun i j k W hi hj hk => (a.condition i j k W hi hj hk).symm
  exact (CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech e.hom.base (hodgeAdd e hbase)
    fixedOpen fixedOpen_cover a.val ha).trans
    (CycleQ2AutomorphismCohomology.pullH_cechOneClass (Scheme.forgetToTop.mapIso e)
      fixedOpen fixedOpen_cover (cover_top e.hom.base fixedOpen fixedOpen_cover) (hodgeAdd e hbase)
      a.val ha).symm

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ)

include hbase in
private theorem composed_overComplex :
    (toThreefold V t ≫ e.hom) ≫ structureMap =
      CycleQ2LiteralAbelJacobiTimeFamily.projection V t ≫
        (CycleQ2LiteralAbelJacobiTimeFamily.timeOpen V).ι ≫ CycleQ2LiteralIncidenceTimeCurve.toComplex := by
  rw [Category.assoc, hbase, toThreefold_overComplex]

/-- Pullback along the actual composite of the moving-family map and the automorphism. -/
def translatedCylinderPull : Hodge21 →+ (familyHodgeSheaf V t).H' 1 ⊤ :=
  pullH (toThreefold V t ≫ e.hom).base (additivePull _ (familyCoefficient V t) coefficients
    (compatible_over _ _ _ (composed_overComplex e hbase V t)) 2) 1

theorem translatedCylinderPull_class (ω : NativeEdges) (hω) :
    translatedCylinderPull e hbase V t (hodgeClass ω hω) =
      qHodge V t (hodgePull e hbase (hodgeClass ω hω)) := by
  let a := hodgeCocycle ω hω
  have ha : IsOneCocycle HodgeSheaf fixedOpen a.val :=
    fun i j k W hi hj hk => (a.condition i j k W hi hj hk).symm
  let hf := compatible_over (toThreefold V t) _ _ (toThreefold_overComplex V t)
  let hg := compatible_over e.hom structureMap structureMap hbase
  exact (pullH_comp_cech (toThreefold V t) e.hom (familyCoefficient V t) coefficients coefficients
    hf hg 2 fixedOpen a.val fixedOpen_cover ha).trans
    (congrArg (qHodge V t) (pullH_eq_hodgePull e hbase ω hω))

end CycleQ2LiteralThreefoldOrbitCylinderPull
end

#print axioms CycleQ2LiteralThreefoldOrbitCylinderPull.translatedCylinderPull_class
