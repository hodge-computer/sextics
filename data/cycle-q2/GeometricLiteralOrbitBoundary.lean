import Proposal.GeometricCotangentPairAction
import Proposal.GeometricLiteralOrbitAction

/-!
# Equivariance of the restricted cotangent sequence

The middle map is induced by the differential on the thick surface and the
closed-fibre square. On the canonical normal generator its adjoint multiplies
by the character of epsilon.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitBoundary

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSchemeCotangentMaps
  CycleQ2LiteralCotangentEpsilonComparison CycleQ2LiteralCotangentEpsilonMap
  CycleQ2SurfacePullbackFrame

open CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveComplexSplittings
  CycleQ2LiteralProjectiveCotangent CycleQ2LiteralCotangentEpsilon
  CycleQ2LiteralOrbitAction
  CycleQ2GeometricSchemeDifferentialMap

section Action

variable (z : ℂ) (hz : z ^ 3 = 1)

private abbrev g := (closedProjectiveAction z hz).hom
private abbrev G := (projectiveAction z hz).hom
private abbrev cs := CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1

theorem surfaceCoefficient (U : ClosedSurface.Opens) (a : ℂ) :
    (g z hz).app U (coefficientOn ClosedSurface.sheaf cs U a) =
      coefficientOn ClosedSurface.sheaf cs (g z hz ⁻¹ᵁ U) a :=
  coefficient_of_overComplex (g z hz) _ (surfaceAction_overComplex z hz) U a

theorem thickCoefficient (U : projectiveDeformation.Opens) (a : ℂ) :
    (G z hz).app U (coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient U a) =
      coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient (G z hz ⁻¹ᵁ U) a :=
  coefficient_of_overComplex (G z hz) _ (thickAction_overComplex z hz) U a

section Bundled
variable {X Y : Scheme.{0}} (j : X ⟶ Y) (p : X ⟶ X) (q : Y ⟶ Y)
    (eqn : p ≫ j = j ≫ q) (cx : ℂ →+* Γ(X,⊤)) (cy : ℂ →+* Γ(Y,⊤))
    (hj : ∀ U a, j.app U (coefficientOn Y.sheaf cy U a) = coefficientOn X.sheaf cx (j ⁻¹ᵁ U) a)
    (hp : ∀ U a, p.app U (coefficientOn X.sheaf cx U a) = coefficientOn X.sheaf cx (p ⁻¹ᵁ U) a)
    (hq : ∀ U a, q.app U (coefficientOn Y.sheaf cy U a) = coefficientOn Y.sheaf cy (q ⁻¹ᵁ U) a)

private theorem bundledReduction
    (red : (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy) ⟶ differentialSheaf X.sheaf cx)
    (hr : red = cotangentMap j cx cy hj)
    (m : (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy) ⟶
      (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy)))
    (hm : m = middleAdjoint j p q eqn cy hq)
    (d : differentialSheaf X.sheaf cx ⟶ (Scheme.Modules.pushforward p).obj (differentialSheaf X.sheaf cx))
    (hd : d = schemeDifferentialMap p cx cx hp) :
    m ≫ (Scheme.Modules.pushforward p).map red = red ≫ d := by
  subst red m d
  exact adjoint_reduction j p q eqn cx cy hj hp hq

include hj in
private theorem bundledInclusion
    (e : Γ(Y,⊤)) (a : ℂ) (he : q.appTop e = cy a * e)
    (inc : structureModule X ⟶ (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy))
    (hinc : onTop inc (1 : Γ(X,⊤)) =
      pullTop j (differentialSheaf Y.sheaf cy) ((universalDifferential Y.sheaf cy).d e))
    (n : structureModule X ⟶ (Scheme.Modules.pushforward p).obj (structureModule X))
    (hn : n = scalarAdjoint p cx a)
    (m : (Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy) ⟶
      (Scheme.Modules.pushforward p).obj ((Scheme.Modules.pullback j).obj (differentialSheaf Y.sheaf cy)))
    (hm : m = middleAdjoint j p q eqn cy hq) :
    n ≫ (Scheme.Modules.pushforward p).map inc = inc ≫ m := by
  subst n m
  exact adjoint_inclusion j p q eqn cx cy hj hq e a he inc hinc

end Bundled

section PairMaps

variable (f : ClosedSurface ⟶ ClosedSurface) (F : projectiveDeformation ⟶ projectiveDeformation)
    (h : f ≫ closedFiber = closedFiber ≫ F)
    (hf : ∀ U a, f.app U (coefficientOn ClosedSurface.sheaf cs U a) =
      coefficientOn ClosedSurface.sheaf cs (f ⁻¹ᵁ U) a)
    (hF : ∀ U a, F.app U (coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient U a) =
      coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient (F ⁻¹ᵁ U) a)

private def restrictedAdjointOf :
    restrictedCotangentSheaf ⟶ (Scheme.Modules.pushforward f).obj restrictedCotangentSheaf :=
  middleAdjoint closedFiber f F h totalGlobalCoefficient hF

private def differentialAdjointOf :
    originalDifferentialSheaf ⟶ (Scheme.Modules.pushforward f).obj originalDifferentialSheaf :=
  schemeDifferentialMap f cs cs hf

end PairMaps

def restrictedAdjoint := restrictedAdjointOf (g z hz) (G z hz)
  (closedFiber_equivariant z hz).symm (thickCoefficient z hz)

def differentialAdjoint := differentialAdjointOf (g z hz) (surfaceCoefficient z hz)

def normalAdjoint :
    structureModule ClosedSurface ⟶
      (Scheme.Modules.pushforward (g z hz)).obj (structureModule ClosedSurface) :=
  scalarAdjoint (g z hz) cs (z ^ 2)

theorem normalAdjoint_apply (U : ClosedSurface.Opens) (x : Γ(ClosedSurface, U)) :
    (normalAdjoint z hz).val.app (op U) x =
      (g z hz).app U x *
        (show Γ(ClosedSurface, g z hz ⁻¹ᵁ U) from
          coefficientOn ClosedSurface.sheaf cs (g z hz ⁻¹ᵁ U) (z ^ 2)) :=
  scalarAdjoint_apply (g z hz) cs (z^2) U x

theorem reduction_comm :
    restrictedAdjoint z hz ≫ (Scheme.Modules.pushforward (g z hz)).map cotangentReduction =
      cotangentReduction ≫ differentialAdjoint z hz :=
  bundledReduction (X := ClosedSurface) (Y := projectiveDeformation)
    closedFiber (g z hz) (G z hz) (closedFiber_equivariant z hz).symm
    cs totalGlobalCoefficient closedFiber_coefficient (surfaceCoefficient z hz) (thickCoefficient z hz)
    cotangentReduction rfl (restrictedAdjoint z hz) rfl (differentialAdjoint z hz) rfl

theorem inclusion_comm :
    normalAdjoint z hz ≫ (Scheme.Modules.pushforward (g z hz)).map epsilonInclusion =
      epsilonInclusion ≫ restrictedAdjoint z hz :=
  bundledInclusion (X := ClosedSurface) (Y := projectiveDeformation)
    closedFiber (g z hz) (G z hz) (closedFiber_equivariant z hz).symm
    cs totalGlobalCoefficient closedFiber_coefficient (thickCoefficient z hz)
    totalEpsilon (z ^ 2) (projectiveAction_epsilon z hz) epsilonInclusion epsilonInclusion_global_one
    (normalAdjoint z hz) rfl (restrictedAdjoint z hz) rfl

private abbrev forgetModules (S : Scheme.{0}) := SheafOfModules.toSheaf.{0} S.ringCatSheaf

private def additiveAlong {S : Scheme.{0}} (f : S ⟶ S) {M N : S.Modules}
    (l : M ⟶ (Scheme.Modules.pushforward f).obj N) :
    (forgetModules S).obj M ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f.base).obj ((forgetModules S).obj N) :=
  (forgetModules S).map l

theorem forget_comm {S : Scheme.{0}} (f : S ⟶ S) {M N : S.Modules} (u : M ⟶ N)
    (l : M ⟶ (Scheme.Modules.pushforward f).obj M) (m : N ⟶ (Scheme.Modules.pushforward f).obj N)
    (sq : l ≫ (Scheme.Modules.pushforward f).map u = u ≫ m)
    (a : (forgetModules S).obj M ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat f.base).obj ((forgetModules S).obj M))
    (ha : a = additiveAlong f l)
    (b : (forgetModules S).obj N ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat f.base).obj ((forgetModules S).obj N))
    (hb : b = additiveAlong f m) :
    (forgetModules S).map u ≫ b =
      a ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map ((forgetModules S).map u) := by
  subst a b
  exact ((forgetModules S).map_comp u m).symm.trans
    ((congrArg (forgetModules S).map sq.symm).trans ((forgetModules S).map_comp l _))

def additiveNormal := additiveAlong (g z hz) (normalAdjoint z hz)
def additiveMiddle := additiveAlong (g z hz) (restrictedAdjoint z hz)
def additiveDifferential := additiveAlong (g z hz) (differentialAdjoint z hz)

theorem additive_inclusion_comm :
    (forgetModules ClosedSurface).map epsilonInclusion ≫ additiveMiddle z hz =
      additiveNormal z hz ≫ (TopCat.Sheaf.pushforward AddCommGrpCat (g z hz).base).map
        ((forgetModules ClosedSurface).map epsilonInclusion) :=
  forget_comm (g z hz) epsilonInclusion (normalAdjoint z hz) (restrictedAdjoint z hz)
    (inclusion_comm z hz) (additiveNormal z hz) rfl (additiveMiddle z hz) rfl

theorem additive_reduction_comm :
    (forgetModules ClosedSurface).map cotangentReduction ≫ additiveDifferential z hz =
      additiveMiddle z hz ≫ (TopCat.Sheaf.pushforward AddCommGrpCat (g z hz).base).map
        ((forgetModules ClosedSurface).map cotangentReduction) :=
  forget_comm (g z hz) cotangentReduction (restrictedAdjoint z hz) (differentialAdjoint z hz)
    (reduction_comm z hz) (additiveMiddle z hz) rfl (additiveDifferential z hz) rfl

end Action
end CycleQ2LiteralOrbitBoundary
end

#print axioms CycleQ2LiteralOrbitBoundary.reduction_square
#print axioms CycleQ2LiteralOrbitBoundary.normal_generator
#print axioms CycleQ2LiteralOrbitBoundary.additive_inclusion_comm
#print axioms CycleQ2LiteralOrbitBoundary.additive_reduction_comm
