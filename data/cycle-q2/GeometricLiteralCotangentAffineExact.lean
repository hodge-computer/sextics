import Proposal.GeometricLiteralAffineCotangent
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Split exactness of the native affine cotangent sheaf sequence

The two arrows are induced by the original epsilon inclusion and cotangent
reduction. Each admissible splitting gives an explicit retraction and section
of these arrows. Applying the additive tilde functor preserves that splitting
on the spectrum of the native closed ring.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentAffineExact

open CategoryTheory AlgebraicGeometry CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralNativeCotangent
  CycleQ2GeometricSquareZeroReducedCotangent

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

def nativeComplex (s : Finset Vertex) : ShortComplex (ModuleCat.{0} (ClosedRing s)) :=
  ShortComplex.mk
    (X₁ := ModuleCat.of (ClosedRing s) (ClosedRing s))
    (X₂ := ModuleCat.of (ClosedRing s) (NativeCotangent s))
    (X₃ := ModuleCat.of (ClosedRing s) (KaehlerDifferential ℂ (ClosedRing s)))
    (ModuleCat.ofHom (nativeEpsilonInclusion s)) (ModuleCat.ofHom (nativeCotangentReduction s))
    (ModuleCat.hom_ext (LinearMap.ext (fun x =>
      reductionMap_epsilonInclusion (K := ℂ) (epsilonKernelEquiv s) x)))

def nativeSplitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    (nativeComplex s).Splitting where
  r := ModuleCat.ofHom (nativeCotangentRetraction s a ha)
  s := ModuleCat.ofHom (nativeCotangentSplitting s a ha)
  f_r := ModuleCat.hom_ext (LinearMap.ext (nativeEpsilonInclusion_retraction s a ha))
  s_g := ModuleCat.hom_ext (nativeCotangentReduction_splitting s a ha)
  id := by
    apply ModuleCat.hom_ext
    change (nativeEpsilonInclusion s).comp (nativeCotangentRetraction s a ha) +
      (nativeCotangentSplitting s a ha).comp (nativeCotangentReduction s) = LinearMap.id
    rw [add_comm]
    exact split_reconstruction (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha)
      (projectiveSplittingAlgHom_reduction s a ha)

private def tildeComplex (R : CommRingCat.{0}) (S : ShortComplex (ModuleCat.{0} R)) :
    ShortComplex (Spec R).Modules := by
  letI : (tilde.functor R).PreservesZeroMorphisms := ⟨fun _ _ => tilde.map_zero⟩
  exact S.map (tilde.functor R)

private def tildeSplitting (R : CommRingCat.{0}) {S : ShortComplex (ModuleCat.{0} R)}
    (t : S.Splitting) : (tildeComplex R S).Splitting := t.map (tilde.functor R)

def nativeTildeComplex (s : Finset Vertex) :
    ShortComplex (Scheme.Modules.{0} (Spec (CommRingCat.of (ClosedRing s)))) :=
  tildeComplex (CommRingCat.of (ClosedRing s)) (nativeComplex s)

theorem nativeTildeComplex_f (s : Finset Vertex) :
    (nativeTildeComplex s).f = tilde.map (R := CommRingCat.of (ClosedRing s))
      (show ModuleCat.of (ClosedRing s) (ClosedRing s) ⟶ ModuleCat.of (ClosedRing s) (NativeCotangent s)
        from ModuleCat.ofHom (nativeEpsilonInclusion s)) := rfl

theorem nativeTildeComplex_g (s : Finset Vertex) :
    (nativeTildeComplex s).g = tilde.map (R := CommRingCat.of (ClosedRing s))
      (show ModuleCat.of (ClosedRing s) (NativeCotangent s) ⟶
        ModuleCat.of (ClosedRing s) (KaehlerDifferential ℂ (ClosedRing s))
        from ModuleCat.ofHom (nativeCotangentReduction s)) := rfl

def nativeTildeSplitting (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    (nativeTildeComplex s).Splitting :=
  tildeSplitting (CommRingCat.of (ClosedRing s)) (S := nativeComplex s) (nativeSplitting s a ha)

theorem nativeTildeShortExact (s : Finset Vertex) (hs : s.Nonempty) :
    (nativeTildeComplex s).ShortExact := by
  obtain ⟨⟨a, i⟩, h⟩ := hs
  exact (nativeTildeSplitting s a ⟨i, h⟩).shortExact

end CycleQ2LiteralCotangentAffineExact

end

#print axioms CycleQ2LiteralCotangentAffineExact.nativeTildeShortExact
