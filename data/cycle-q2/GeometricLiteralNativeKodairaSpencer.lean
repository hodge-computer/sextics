import Proposal.GeometricLiteralProjectiveIntersectionComplex

/-!
# Actual native splitting-difference derivations on the twelve-chart atlas

The source is the original projective flat dual-number family. Both
splittings are the same original singleton choices extended to the actual
finite intersection, with their actual complex coefficients. Their
faithfully normalized differences are genuine complex derivations of
these native projective rings. Restriction and the Cech law are proved.

The subsequent tangent-sheaf and normalized Chern-cup comparison remains
a separate binding through the actual differential-sheaf maps.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeKodairaSpencer

open CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionSplittings
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2GeometricSquareZeroSplittings

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

/-- The actual epsilon coefficient of sigma_b - sigma_a on the actual
native degree-zero intersection ring. -/
def kodairaSpencer (s : Finset Vertex) (a b : Fin 4) (ha : Admissible s a) (hb : Admissible s b) :
    Derivation ℂ (ClosedRing s) (ClosedRing s) :=
  difference (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom s b hb)
    (projectiveSplittingAlgHom_reduction s a ha) (projectiveSplittingAlgHom_reduction s b hb)

theorem epsilon_kodairaSpencer (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (x : ClosedRing s) :
    epsilonCoefficient s (kodairaSpencer s a b ha hb x) =
      projectiveSplittingAlgHom s b hb x - projectiveSplittingAlgHom s a ha x :=
  epsilon_difference (epsilonKernelEquiv s) (projectiveSplittingAlgHom s a ha) (projectiveSplittingAlgHom s b hb)
    (projectiveSplittingAlgHom_reduction s a ha) (projectiveSplittingAlgHom_reduction s b hb) x

/-- Faithful epsilon naturality identifies the actual derived difference
under the genuine structure-ring restriction. -/
theorem kodairaSpencer_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (a b : Fin 4) (ha : Admissible s a) (hb : Admissible s b) (x : ClosedRing s) :
    closedRestriction hst (kodairaSpencer s a b ha hb x) =
      kodairaSpencer t a b (admissible_mono hst ha) (admissible_mono hst hb) (closedRestriction hst x) := by
  apply epsilonCoefficient_injective t
  rw [← epsilonCoefficient_restrict, epsilon_kodairaSpencer, map_sub]
  change thickRestriction hst (projectiveSplitting s b hb x) -
    thickRestriction hst (projectiveSplitting s a ha x) = _
  rw [projectiveSplitting_restrict, projectiveSplitting_restrict, epsilon_kodairaSpencer]
  rfl

theorem kodairaSpencer_trans (s : Finset Vertex) (a b c : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (hc : Admissible s c) :
    kodairaSpencer s a c ha hc = kodairaSpencer s a b ha hb + kodairaSpencer s b c hb hc :=
  difference_trans _ _ _ _ _ _ _

theorem kodairaSpencer_self (s : Finset Vertex) (a : Fin 4) (ha : Admissible s a) :
    kodairaSpencer s a a ha ha = 0 := by
  apply DFunLike.ext
  intro x
  change kodairaSpencer s a a ha ha x = 0
  apply epsilonCoefficient_injective s
  rw [epsilon_kodairaSpencer, sub_self]
  exact (map_zero (epsilonLinear s)).symm

theorem kodairaSpencer_reverse (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) :
    kodairaSpencer s b a hb ha = -kodairaSpencer s a b ha hb := by
  have h := kodairaSpencer_trans s a b a ha hb ha
  rw [kodairaSpencer_self] at h
  exact eq_neg_of_add_eq_zero_right h.symm

def vertexKodairaSpencer (s : Finset Vertex) (v w : Vertex) (hv : v ∈ s) (hw : w ∈ s) :
    Derivation ℂ (ClosedRing s) (ClosedRing s) :=
  kodairaSpencer s v.1 w.1 ⟨v.2,hv⟩ ⟨w.2,hw⟩

/-- Different coordinate charts of the same singleton introduce no
additional splitting-difference derivation. -/
theorem vertexKodairaSpencer_sameCartier (s : Finset Vertex) (a : Fin 4) (l m : Fin 3)
    (hl : (a,l) ∈ s) (hm : (a,m) ∈ s) :
    vertexKodairaSpencer s (a,l) (a,m) hl hm = 0 :=
  kodairaSpencer_self s a ⟨l,hl⟩

theorem vertexKodairaSpencer_cocycle (s : Finset Vertex) (u v w : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (hw : w ∈ s) :
    vertexKodairaSpencer s u w hu hw =
      vertexKodairaSpencer s u v hu hv + vertexKodairaSpencer s v w hv hw :=
  kodairaSpencer_trans s u.1 v.1 w.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩ ⟨w.2,hw⟩

/-- Contraction is computed in the genuine native complex differential
module of this actual projective intersection ring. -/
theorem contraction_logDifferential (s : Finset Vertex) (a b : Fin 4)
    (ha : Admissible s a) (hb : Admissible s b) (g : (ClosedRing s)ˣ) :
    (kodairaSpencer s a b ha hb).liftKaehlerDifferential (logDifferential (K := ℂ) g) =
      (↑(g⁻¹) : ClosedRing s) * kodairaSpencer s a b ha hb (g : ClosedRing s) :=
  CycleQ2GeometricSquareZeroSplittings.contraction_logDifferential _ _ _ _ _ g

end CycleQ2LiteralNativeKodairaSpencer

end

#print axioms CycleQ2LiteralNativeKodairaSpencer.kodairaSpencer
#print axioms CycleQ2LiteralNativeKodairaSpencer.kodairaSpencer_restrict
#print axioms CycleQ2LiteralNativeKodairaSpencer.vertexKodairaSpencer_sameCartier
#print axioms CycleQ2LiteralNativeKodairaSpencer.vertexKodairaSpencer_cocycle
