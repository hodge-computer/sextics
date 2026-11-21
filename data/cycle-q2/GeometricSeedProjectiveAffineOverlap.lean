import Proposal.GeometricSeedProjectiveSheafSections

/-!
# The original projective sheaves on the canonical affine pair overlap

The pair overlap is the degree-two projective basic open already used
for its section ring. Its canonical affine chart has coefficient ring
equal to that actual section ring. The four sheaves below are restrictions
of the existing projective image and orbit-dual sheaves along the two
actual inclusions of this same ordered overlap.

Quasi-coherence follows from the original associated-sheaf constructions
and restriction along open immersions. The vertical isomorphisms are the
restrictions of the original projectiveImageDualIso, with no replacement
duality map. The exact top-section normalization is a separate comparison.

Source-only draft: no Lean elaboration or kernel replay has been run.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md for
attribution of the geometric route and the protected certificate gap.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2SeedProjectiveAffineOverlap

open CategoryTheory AlgebraicGeometry
open CycleQ2CartierSurfaceGrading CycleQ2SurfaceCoordinateSections
  CycleQ2SeedProjectiveImageChart CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedProjectiveImageRestriction CycleQ2SeedProjectiveLocalizedDuality

/-- The actual pair overlap is a positive-degree projective basic open. -/
theorem overlap_isAffineOpen (i j : Fin 3) : IsAffineOpen (OverlapOpen i j) :=
  Proj.isAffineOpen_basicOpen (surfaceGrade 57 1) (pairDen 57 1 i.succ j.succ)
    (pairDen_mem_grade 57 1 i.succ j.succ) (by decide)

/-- Use the canonical affine chart over the actual overlap section ring. -/
def overlapSpecChart (i j : Fin 3) :
    (OverlapOpen i j).toScheme ≅ Spec (OverlapSections i j) :=
  (overlap_isAffineOpen i j).isoSpec

def leftOverlapMap (i j : Fin 3) :
    Spec (OverlapSections i j) ⟶ (Patch i).toScheme :=
  (overlapSpecChart i j).inv ≫
    Surface.homOfLE (pair_le_left 57 1 i.succ j.succ)

def rightOverlapMap (i j : Fin 3) :
    Spec (OverlapSections i j) ⟶ (Patch j).toScheme :=
  (overlapSpecChart i j).inv ≫
    Surface.homOfLE (pair_le_right 57 1 i.succ j.succ)

instance leftOverlapMap_isOpenImmersion (i j : Fin 3) :
    IsOpenImmersion (leftOverlapMap i j) := by
  dsimp [leftOverlapMap]
  infer_instance

instance rightOverlapMap_isOpenImmersion (i j : Fin 3) :
    IsOpenImmersion (rightOverlapMap i j) := by
  dsimp [rightOverlapMap]
  infer_instance

abbrev leftImageOverlap (i j : Fin 3) : (Spec (OverlapSections i j)).Modules :=
  (projectiveImageSheaf i).restrict (leftOverlapMap i j)

abbrev rightImageOverlap (i j : Fin 3) : (Spec (OverlapSections i j)).Modules :=
  (projectiveImageSheaf j).restrict (rightOverlapMap i j)

abbrev leftDualOverlap (i j : Fin 3) : (Spec (OverlapSections i j)).Modules :=
  (projectiveOrbitDualSheaf i).restrict (leftOverlapMap i j)

abbrev rightDualOverlap (i j : Fin 3) : (Spec (OverlapSections i j)).Modules :=
  (projectiveOrbitDualSheaf j).restrict (rightOverlapMap i j)

instance leftImageOverlap_isQuasicoherent (i j : Fin 3) :
    (leftImageOverlap i j).IsQuasicoherent := by
  dsimp [leftImageOverlap, projectiveImageSheaf, affineImageSheaf]
  infer_instance

instance rightImageOverlap_isQuasicoherent (i j : Fin 3) :
    (rightImageOverlap i j).IsQuasicoherent := by
  dsimp [rightImageOverlap, projectiveImageSheaf, affineImageSheaf]
  infer_instance

instance leftDualOverlap_isQuasicoherent (i j : Fin 3) :
    (leftDualOverlap i j).IsQuasicoherent := by
  dsimp [leftDualOverlap, projectiveOrbitDualSheaf, affineOrbitDualSheaf]
  infer_instance

instance rightDualOverlap_isQuasicoherent (i j : Fin 3) :
    (rightDualOverlap i j).IsQuasicoherent := by
  dsimp [rightDualOverlap, projectiveOrbitDualSheaf, affineOrbitDualSheaf]
  infer_instance

/-- The left vertical map is the restricted original projective duality. -/
def leftOverlapDuality (i j : Fin 3) :
    leftImageOverlap i j ≅ leftDualOverlap i j :=
  (Scheme.Modules.restrictFunctor (leftOverlapMap i j)).mapIso
    (projectiveImageDualIso i)

/-- The right vertical map uses the same ordered overlap and original duality. -/
def rightOverlapDuality (i j : Fin 3) :
    rightImageOverlap i j ≅ rightDualOverlap i j :=
  (Scheme.Modules.restrictFunctor (rightOverlapMap i j)).mapIso
    (projectiveImageDualIso j)

#print axioms overlap_isAffineOpen
#print axioms overlapSpecChart
#print axioms leftImageOverlap_isQuasicoherent
#print axioms rightImageOverlap_isQuasicoherent
#print axioms leftDualOverlap_isQuasicoherent
#print axioms rightDualOverlap_isQuasicoherent

end CycleQ2SeedProjectiveAffineOverlap
end
