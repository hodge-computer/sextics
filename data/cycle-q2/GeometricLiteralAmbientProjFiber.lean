import Proposal.GeometricLiteralAmbientProjFiberPolynomial
import Proposal.GeometricLiteralAmbientProjFiberDegree
import Proposal.GeometricLiteralAmbientProjFiberSquare

/-! Weighted polynomial quotients commute with a split surjective coefficient
specialization on native projective schemes. This applies to both original
parameter spaces for the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientProjFiber

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2GeometricIncidenceProj CycleQ2GeometricProjectiveCurve.HomogeneousQuotient
  CycleQ2LiteralAmbientProjFiberPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev Grade {R : Type} [CommRing R] (I : Ideal (MvPolynomial (Fin 5) R)) :=
  grade (PolynomialGrade R) I

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (s : S →+* R)
  (hs : φ.comp s = RingHom.id S) (I : Ideal (MvPolynomial (Fin 5) R))
  (J : Ideal (MvPolynomial (Fin 5) S)) (hIJ : I.map (MvPolynomial.map φ) = J)
  [GradedRing (Grade I)] [GradedRing (Grade J)]

def toBase {K : Type} [CommRing K] (L : Ideal (MvPolynomial (Fin 5) K))
    [GradedRing (Grade L)] : Proj (Grade L) ⟶ Spec (CommRingCat.of K) :=
  Proj.toSpecZero (Grade L) ≫ Spec.map (CommRingCat.ofHom (algebraMap K (Grade L 0)))

include s hs in
theorem irrelevant_le : HomogeneousIdeal.irrelevant (Grade J) ≤
    (HomogeneousIdeal.irrelevant (Grade I)).map (graded φ I J hIJ) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn b hb
  obtain ⟨a,ha,rfl⟩ := homogeneous_surjective φ I J hIJ s hs n b hb
  exact Ideal.mem_map_of_mem (graded φ I J hIJ)
    (HomogeneousIdeal.mem_irrelevant_of_mem (Grade I) hn ha)

def projective : Proj (Grade J) ⟶ Proj (Grade I) :=
  Proj.map (graded φ I J hIJ) (irrelevant_le φ s hs I J hIJ)

/-- Native projective specialization at a coefficient point is a genuine
pullback, with the original maps to the coefficient schemes. -/
theorem isPullback :
    IsPullback (projective φ s hs I J hIJ) (toBase J) (toBase I) (Spec.map (CommRingCat.ofHom φ)) := by
  let : Algebra R S := φ.toAlgebra
  have hsur : Function.Surjective (algebraMap R S) := by
    intro a
    exact ⟨s a, RingHom.congr_fun hs a⟩
  have hc : (graded φ I J hIJ).gradedZeroRingHom.comp (algebraMap R (Grade I 0)) =
      (algebraMap S (Grade J 0)).comp (algebraMap R S) := by
    apply RingHom.ext
    intro r
    apply Subtype.ext
    change Ideal.Quotient.mk J (MvPolynomial.map φ (C r)) = Ideal.Quotient.mk J (C (φ r))
    rw [map_C]
  apply CycleQ2LiteralAmbientProjFiberGluing.projective_isPullback_of_tensorCharts
  intro n _hn a ha
  apply CycleQ2LiteralAmbientProjFiberSquare.tensorChart (R := R) (K := S)
    (graded φ I J hIJ) (algebraMap R (Grade I 0)) (algebraMap S (Grade J 0))
    (fun _ => rfl) hc hsur (homogeneous_surjective φ I J hIJ s hs) _ ha
  exact CycleQ2LiteralAmbientProjFiberDegree.homogeneous_kernel_decomposition (K := S)
    (Grade I) (specialize φ I J hIJ) (ker_specialize φ I J hIJ hsur)

/-- The native weighted Proj is canonically isomorphic to the scheme-theoretic
fiber, in the same coefficient-first pullback order as the incidence families. -/
def fiberIso : Proj (Grade J) ≅ pullback (Spec.map (CommRingCat.ofHom φ)) (toBase I) :=
  (isPullback φ s hs I J hIJ).flip.isoPullback

@[reassoc, simp] theorem fiberIso_hom_fst :
    (fiberIso φ s hs I J hIJ).hom ≫ pullback.fst _ _ = toBase J := by simp [fiberIso]

@[reassoc, simp] theorem fiberIso_hom_snd :
    (fiberIso φ s hs I J hIJ).hom ≫ pullback.snd _ _ = projective φ s hs I J hIJ := by simp [fiberIso]

end CycleQ2LiteralAmbientProjFiber

#print axioms CycleQ2LiteralAmbientProjFiber.isPullback
