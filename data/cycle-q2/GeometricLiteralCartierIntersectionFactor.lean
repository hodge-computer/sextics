import Proposal.GeometricLiteralNativeCupOriginalFaces

/-!
# A genuine homogeneous complement for every admissible Cartier product

Choose one original coordinate chart for each source Cartier index.
Those vertices are distinct because their first coordinates differ.
Their actual denominator product is the original Cartier product times
the chosen coordinate product. The remaining intersection factors give
an explicit homogeneous complement; no denominator cancellation is used.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCartierIntersectionFactor

open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCartierIdeal
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralConeIntersectionTransport

def chosenCoordinate (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (a : Fin 4) : Fin 3 :=
  if ha : a ∈ t then (ht a ha).choose else 0

def chosenVertex (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (a : Fin 4) : Vertex :=
  (a,chosenCoordinate s t ht a)

theorem chosenVertex_mem (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) (a : Fin 4) (ha : a ∈ t) :
    chosenVertex s t ht a ∈ s := by
  simp only [chosenVertex, chosenCoordinate, dif_pos ha]
  exact (ht a ha).choose_spec

theorem chosenVertex_injective (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    Function.Injective (chosenVertex s t ht) := by
  intro a b hab
  exact congrArg Prod.fst hab

def chosenVertices (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) : Finset Vertex :=
  t.image (chosenVertex s t ht)

theorem chosenVertices_subset (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    chosenVertices s t ht ⊆ s := by
  intro v hv
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
  exact chosenVertex_mem s t ht a ha

def coordinateProduct (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) : SurfaceRing 57 1 :=
  ∏ a ∈ t, CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 (chosenCoordinate s t ht a)

theorem coordinateProduct_homogeneous (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    coordinateProduct s t ht ∈ surfaceGrade 57 1 t.card := by
  simpa only [coordinateProduct, Finset.sum_const, nsmul_eq_mul, Nat.mul_one, Nat.cast_id] using
    SetLike.prod_mem_graded (surfaceGrade 57 1) (fun _ : Fin 4 => 1)
      (fun a => CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 (chosenCoordinate s t ht a))
      (fun a _ => CycleQ2GradedCechProjection.coordinateElement_homogeneous 57 1 (chosenCoordinate s t ht a))

theorem chosenProduct_factor (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    closedProduct (chosenVertices s t ht) = coverProduct 57 1 t * coordinateProduct s t ht := by
  change (∏ v ∈ t.image (chosenVertex s t ht), refinedDenominator 57 1 v.1 v.2) = _
  rw [Finset.prod_image (fun a _ b _ h => chosenVertex_injective s t ht h)]
  change (∏ a ∈ t, coverElement 57 1 a *
    CycleQ2GeometricSurfaceCoordinates.coordinateElement 57 1 (chosenCoordinate s t ht a)) = _
  exact Finset.prod_mul_distrib

def complement (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) : SurfaceRing 57 1 :=
  coordinateProduct s t ht * closedProduct (s \ chosenVertices s t ht)

theorem complement_homogeneous (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    complement s t ht ∈ surfaceGrade 57 1 (t.card + productDegree (s \ chosenVertices s t ht)) :=
  SetLike.mul_mem_graded (coordinateProduct_homogeneous s t ht)
    (closedProduct_homogeneous (s \ chosenVertices s t ht))

theorem originalProduct_factor (s : Finset Vertex) (t : Finset (Fin 4)) (ht : Admits s t) :
    closedProduct s = coverProduct 57 1 t * complement s t ht := by
  rw [closedProduct_factor (chosenVertices_subset s t ht), chosenProduct_factor]
  exact mul_assoc _ _ _

end CycleQ2LiteralCartierIntersectionFactor

end

#print axioms CycleQ2LiteralCartierIntersectionFactor.complement_homogeneous
#print axioms CycleQ2LiteralCartierIntersectionFactor.originalProduct_factor
