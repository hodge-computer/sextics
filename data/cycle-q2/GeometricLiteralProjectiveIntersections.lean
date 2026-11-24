import Proposal.GeometricLiteralProjectiveDualFamily

/-!
# Actual finite intersections of the twelve projective deformation charts

The denominator is the product of the original chart denominators,
indexed by an actual finite set of the original twelve vertices.
Both native rings are genuine homogeneous localizations. The reduction
is induced by the original graded reduction and its affine Proj square
uses the actual finite intersection opens of the original schemes.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveIntersections

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2GeometricSeedNormalIdeals CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveDeformation
  CycleQ2GradedAwaySpecialization

abbrev Vertex := Fin 4 × Fin 3

def thickProduct (s : Finset Vertex) : GradedDeformation :=
  ∏ v ∈ s, chartDenominator v.1 v.2

def closedProduct (s : Finset Vertex) : SurfaceRing 57 1 :=
  ∏ v ∈ s, refinedDenominator 57 1 v.1 v.2

def productDegree (s : Finset Vertex) : ℕ :=
  ∑ v ∈ s, (coverDegree v.1 + 1)

theorem thickProduct_homogeneous (s : Finset Vertex) :
    thickProduct s ∈ deformationGrade (productDegree s) :=
  SetLike.prod_mem_graded deformationGrade _ _ (fun v _ => chartDenominator_homogeneous v.1 v.2)

theorem closedProduct_homogeneous (s : Finset Vertex) :
    closedProduct s ∈ surfaceGrade 57 1 (productDegree s) :=
  SetLike.prod_mem_graded (surfaceGrade 57 1) _ _
    (fun v _ => refinedDenominator_homogeneous 57 1 v.1 v.2)

theorem productDegree_pos {s : Finset Vertex} (hs : s.Nonempty) : 0 < productDegree s :=
  Finset.sum_pos (fun _ _ => by omega) hs

theorem reduction_thickProduct (s : Finset Vertex) :
    reductionGraded (thickProduct s) = closedProduct s := by
  rw [thickProduct, map_prod]
  exact Finset.prod_congr rfl (fun v _ => reduction_chartDenominator v.1 v.2)

theorem thickProduct_dvd {s t : Finset Vertex} (hst : s ⊆ t) : thickProduct s ∣ thickProduct t :=
  Finset.prod_dvd_prod_of_subset s t _ hst

theorem closedProduct_dvd {s t : Finset Vertex} (hst : s ⊆ t) : closedProduct s ∣ closedProduct t :=
  Finset.prod_dvd_prod_of_subset s t _ hst

theorem thickProduct_factor {s t : Finset Vertex} (hst : s ⊆ t) :
    thickProduct t = thickProduct s * thickProduct (t \ s) := by
  simpa only [thickProduct, mul_comm] using
    (Finset.prod_sdiff (f := fun v : Vertex => chartDenominator v.1 v.2) hst).symm

theorem closedProduct_factor {s t : Finset Vertex} (hst : s ⊆ t) :
    closedProduct t = closedProduct s * closedProduct (t \ s) := by
  simpa only [closedProduct, mul_comm] using
    (Finset.prod_sdiff (f := fun v : Vertex => refinedDenominator 57 1 v.1 v.2) hst).symm

abbrev ThickRing (s : Finset Vertex) := Away deformationGrade (thickProduct s)
abbrev ClosedRing (s : Finset Vertex) := Away (surfaceGrade 57 1) (closedProduct s)
abbrev ThickCone (s : Finset Vertex) := Localization.Away (thickProduct s)
abbrev ClosedCone (s : Finset Vertex) := Localization.Away (closedProduct s)

def thickOpen (s : Finset Vertex) : projectiveDeformation.Opens :=
  Proj.basicOpen deformationGrade (thickProduct s)

def closedOpen (s : Finset Vertex) : (CycleQ2CartierProjectiveCover.projectiveSurface 57 1).Opens :=
  Proj.basicOpen (surfaceGrade 57 1) (closedProduct s)

theorem thickOpen_eq (s : Finset Vertex) : thickOpen s = ⨅ v ∈ s, chartOpen v.1 v.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [thickOpen, thickProduct]
  | @insert v s hv ih =>
    simp only [thickOpen, thickProduct, Finset.prod_insert hv, Proj.basicOpen_mul] at *
    simpa only [Finset.iInf_insert, chartOpen] using
      congrArg (fun U => chartOpen v.1 v.2 ⊓ U) ih

theorem closedOpen_eq (s : Finset Vertex) :
    closedOpen s = ⨅ v ∈ s, refinedOpen 57 1 v.1 v.2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [closedOpen, closedProduct]
  | @insert v s hv ih =>
    simp only [closedOpen, closedProduct, Finset.prod_insert hv, Proj.basicOpen_mul] at *
    simpa only [Finset.iInf_insert, refinedOpen] using
      congrArg (fun U => refinedOpen 57 1 v.1 v.2 ⊓ U) ih

def nativeReduction (s : Finset Vertex) : ThickRing s →+* ClosedRing s :=
  awayMapOfEq reductionGraded (thickProduct s) (closedProduct s) (reduction_thickProduct s)

theorem nativeReduction_mk (s : Finset Vertex) (n : ℕ) (p : GradedDeformation)
    (hp : p ∈ deformationGrade (n • productDegree s)) :
    nativeReduction s (Away.mk deformationGrade (thickProduct_homogeneous s) n p hp) =
      Away.mk (surfaceGrade 57 1) (closedProduct_homogeneous s) n (reduction p) (reductionGraded.2 hp) :=
  awayMapOfEq_mk reductionGraded _ _ (reduction_thickProduct s)
    (thickProduct_homogeneous s) (closedProduct_homogeneous s) n p hp

theorem nativeReduction_surjective (s : Finset Vertex) : Function.Surjective (nativeReduction s) := by
  intro x
  obtain ⟨n,p,hp,rfl⟩ := Away.mk_surjective (surfaceGrade 57 1) (closedProduct_homogeneous s) x
  obtain ⟨q,hq,rfl⟩ := reduction_homogeneous_surjective _ p hp
  exact ⟨Away.mk deformationGrade (thickProduct_homogeneous s) n q hq, nativeReduction_mk s n q hq⟩

theorem closedFiber_preimage_thickOpen (s : Finset Vertex) :
    closedFiber ⁻¹ᵁ thickOpen s = closedOpen s := by
  change Proj.basicOpen (surfaceGrade 57 1) (reductionGraded (thickProduct s)) = _
  rw [reduction_thickProduct]
  rfl

@[reassoc] theorem nativeReduction_scheme_square (s : Finset Vertex) (hs : s.Nonempty) :
    Proj.awayι (surfaceGrade 57 1) (closedProduct s) (closedProduct_homogeneous s) (productDegree_pos hs) ≫
        closedFiber =
      Spec.map (CommRingCat.ofHom (nativeReduction s)) ≫
        Proj.awayι deformationGrade (thickProduct s) (thickProduct_homogeneous s) (productDegree_pos hs) :=
  awayι_comp_map_of_eq reductionGraded reduction_irrelevant_le _ _ (reduction_thickProduct s)
    (productDegree_pos hs) (thickProduct_homogeneous s) (closedProduct_homogeneous s)

end CycleQ2LiteralProjectiveIntersections

end

#print axioms CycleQ2LiteralProjectiveIntersections.thickOpen_eq
#print axioms CycleQ2LiteralProjectiveIntersections.nativeReduction_surjective
#print axioms CycleQ2LiteralProjectiveIntersections.nativeReduction_scheme_square
