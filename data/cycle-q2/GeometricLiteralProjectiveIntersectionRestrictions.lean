import Proposal.GeometricLiteralProjectiveIntersectionProjection

/-!
# Actual restriction maps on the finite projective intersections

Ordinary localization maps, homogeneous localization maps, and genuine
scheme section restrictions are bound to the same original product
factorization. Reduction, projection, and faithful epsilon coefficients
commute with these maps. The native restrictions satisfy the actual
composition law before any splitting difference or cup is assembled.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralProjectiveIntersectionRestrictions

open CategoryTheory AlgebraicGeometry HomogeneousLocalization
  CycleQ2GeometricSeedNormalIdeals CycleQ2CartierSurfaceGrading
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2GradedLocalizationProjection

def thickConeRestriction {s t : Finset Vertex} (hst : s ⊆ t) : ThickCone s →ₐ[GradedDeformation] ThickCone t :=
  CycleQ2GeometricKernelLocalization.thickRestriction GradedDeformation (thickProduct_dvd hst)

def closedConeRestriction {s t : Finset Vertex} (hst : s ⊆ t) : ClosedCone s →ₐ[SurfaceRing 57 1] ClosedCone t :=
  CycleQ2GeometricKernelLocalization.thickRestriction (SurfaceRing 57 1) (closedProduct_dvd hst)

theorem thickConeRestriction_base {s t : Finset Vertex} (hst : s ⊆ t) (x : GradedDeformation) :
    thickConeRestriction hst (algebraMap GradedDeformation (ThickCone s) x) =
      algebraMap GradedDeformation (ThickCone t) x := (thickConeRestriction hst).commutes x

theorem closedConeRestriction_base {s t : Finset Vertex} (hst : s ⊆ t) (x : SurfaceRing 57 1) :
    closedConeRestriction hst (algebraMap (SurfaceRing 57 1) (ClosedCone s) x) =
      algebraMap (SurfaceRing 57 1) (ClosedCone t) x := (closedConeRestriction hst).commutes x

def thickRestriction {s t : Finset Vertex} (hst : s ⊆ t) : ThickRing s →+* ThickRing t :=
  HomogeneousLocalization.awayMap deformationGrade (thickProduct_homogeneous (t \ s)) (thickProduct_factor hst)

def closedRestriction {s t : Finset Vertex} (hst : s ⊆ t) : ClosedRing s →+* ClosedRing t :=
  HomogeneousLocalization.awayMap (surfaceGrade 57 1) (closedProduct_homogeneous (t \ s)) (closedProduct_factor hst)

theorem thickRestriction_val {s t : Finset Vertex} (hst : s ⊆ t) (x : ThickRing s) :
    (thickRestriction hst x).val = thickConeRestriction hst x.val :=
  homogeneousRestriction_val deformationGrade (thickProduct_homogeneous (t \ s))
    (thickProduct_factor hst) (thickConeRestriction hst) x

theorem closedRestriction_val {s t : Finset Vertex} (hst : s ⊆ t) (x : ClosedRing s) :
    (closedRestriction hst x).val = closedConeRestriction hst x.val :=
  homogeneousRestriction_val (surfaceGrade 57 1) (closedProduct_homogeneous (t \ s))
    (closedProduct_factor hst) (closedConeRestriction hst) x

theorem thickProjection_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ThickCone s) :
    thickProjection t (thickConeRestriction hst x) = thickRestriction hst (thickProjection s x) :=
  degreeZero_naturality deformationGrade (thickProduct_homogeneous s)
    (thickProduct_homogeneous (t \ s)) (thickProduct_factor hst)
    (thickProduct_homogeneous t) (thickConeRestriction hst) x

theorem closedProjection_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ClosedCone s) :
    closedProjection t (closedConeRestriction hst x) = closedRestriction hst (closedProjection s x) :=
  degreeZero_naturality (surfaceGrade 57 1) (closedProduct_homogeneous s)
    (closedProduct_homogeneous (t \ s)) (closedProduct_factor hst)
    (closedProduct_homogeneous t) (closedConeRestriction hst) x

theorem ordinaryReduction_base (s : Finset Vertex) (x : GradedDeformation) :
    ordinaryReduction s (algebraMap GradedDeformation (ThickCone s) x) =
      algebraMap (SurfaceRing 57 1) (ClosedCone s) (reduction x) := IsLocalization.map_eq _ x

theorem ordinaryReduction_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ThickCone s) :
    ordinaryReduction t (thickConeRestriction hst x) = closedConeRestriction hst (ordinaryReduction s x) := by
  have he : (ordinaryReduction t).comp (thickConeRestriction hst).toRingHom =
      (closedConeRestriction hst).toRingHom.comp (ordinaryReduction s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickProduct s))
    apply RingHom.ext
    intro z
    change ordinaryReduction t (thickConeRestriction hst _) = closedConeRestriction hst (ordinaryReduction s _)
    rw [thickConeRestriction_base, ordinaryReduction_base, ordinaryReduction_base, closedConeRestriction_base]
  exact RingHom.congr_fun he x

theorem nativeReduction_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ThickRing s) :
    nativeReduction t (thickRestriction hst x) = closedRestriction hst (nativeReduction s x) := by
  apply HomogeneousLocalization.val_injective
  rw [← ordinaryReduction_val, thickRestriction_val, ordinaryReduction_restrict,
    ordinaryReduction_val, closedRestriction_val]

theorem thickConeRestriction_comp {s t u : Finset Vertex} (hst : s ⊆ t) (htu : t ⊆ u) (x : ThickCone s) :
    thickConeRestriction htu (thickConeRestriction hst x) = thickConeRestriction (hst.trans htu) x := by
  have he : (thickConeRestriction htu).comp (thickConeRestriction hst) = thickConeRestriction (hst.trans htu) := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (thickProduct s))
    apply RingHom.ext
    intro z
    change thickConeRestriction htu (thickConeRestriction hst _) = thickConeRestriction (hst.trans htu) _
    rw [thickConeRestriction_base, thickConeRestriction_base, thickConeRestriction_base]
  exact AlgHom.congr_fun he x

theorem closedConeRestriction_comp {s t u : Finset Vertex} (hst : s ⊆ t) (htu : t ⊆ u) (x : ClosedCone s) :
    closedConeRestriction htu (closedConeRestriction hst x) = closedConeRestriction (hst.trans htu) x := by
  have he : (closedConeRestriction htu).comp (closedConeRestriction hst) = closedConeRestriction (hst.trans htu) := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers (closedProduct s))
    apply RingHom.ext
    intro z
    change closedConeRestriction htu (closedConeRestriction hst _) = closedConeRestriction (hst.trans htu) _
    rw [closedConeRestriction_base, closedConeRestriction_base, closedConeRestriction_base]
  exact AlgHom.congr_fun he x

theorem thickRestriction_comp {s t u : Finset Vertex} (hst : s ⊆ t) (htu : t ⊆ u) (x : ThickRing s) :
    thickRestriction htu (thickRestriction hst x) = thickRestriction (hst.trans htu) x := by
  apply HomogeneousLocalization.val_injective
  rw [thickRestriction_val, thickRestriction_val, thickRestriction_val, thickConeRestriction_comp]

theorem closedRestriction_comp {s t u : Finset Vertex} (hst : s ⊆ t) (htu : t ⊆ u) (x : ClosedRing s) :
    closedRestriction htu (closedRestriction hst x) = closedRestriction (hst.trans htu) x := by
  apply HomogeneousLocalization.val_injective
  rw [closedRestriction_val, closedRestriction_val, closedRestriction_val, closedConeRestriction_comp]

theorem thickRestriction_epsilon {s t : Finset Vertex} (hst : s ⊆ t) :
    thickRestriction hst (nativeEpsilon s) = nativeEpsilon t :=
  HomogeneousLocalization.awayMap_fromZeroRingHom deformationGrade
    (thickProduct_homogeneous (t \ s)) (thickProduct_factor hst) _

/-- The unique genuine epsilon coefficient is preserved, before any
choice of split representative or any sheaf cup is made. -/
theorem epsilonCoefficient_restrict {s t : Finset Vertex} (hst : s ⊆ t) (x : ClosedRing s) :
    thickRestriction hst (epsilonCoefficient s x) = epsilonCoefficient t (closedRestriction hst x) := by
  obtain ⟨y,rfl⟩ := nativeReduction_surjective s x
  rw [epsilonCoefficient_of_reduction, map_mul, thickRestriction_epsilon,
    ← nativeReduction_restrict, epsilonCoefficient_of_reduction]

theorem thickOpen_mono {s t : Finset Vertex} (hst : s ⊆ t) : thickOpen t ≤ thickOpen s :=
  Proj.basicOpen_mono deformationGrade _ _ (thickProduct_dvd hst)

theorem closedOpen_mono {s t : Finset Vertex} (hst : s ⊆ t) : closedOpen t ≤ closedOpen s :=
  Proj.basicOpen_mono (surfaceGrade 57 1) _ _ (closedProduct_dvd hst)

def thickSectionsEquiv (s : Finset Vertex) (hs : s.Nonempty) : ThickRing s ≃+* Γ(projectiveDeformation, thickOpen s) :=
  (Proj.basicOpenIsoAway deformationGrade (thickProduct s) (thickProduct_homogeneous s)
    (productDegree_pos hs)).commRingCatIsoToRingEquiv

def closedSectionsEquiv (s : Finset Vertex) (hs : s.Nonempty) :
    ClosedRing s ≃+* Γ(CycleQ2CartierProjectiveCover.projectiveSurface 57 1, closedOpen s) :=
  (Proj.basicOpenIsoAway (surfaceGrade 57 1) (closedProduct s) (closedProduct_homogeneous s)
    (productDegree_pos hs)).commRingCatIsoToRingEquiv

/-- These are the restrictions of the actual deformed structure sheaf. -/
theorem thickSectionsEquiv_restrict {s t : Finset Vertex}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) (x : ThickRing s) :
    projectiveDeformation.presheaf.map (homOfLE (thickOpen_mono hst)).op (thickSectionsEquiv s hs x) =
      thickSectionsEquiv t ht (thickRestriction hst x) :=
  congrArg (fun k => k x) (Proj.awayMap_awayToSection deformationGrade
    (thickProduct_homogeneous (t \ s)) (thickProduct_factor hst)).symm

/-- These are the restrictions of the original closed structure sheaf. -/
theorem closedSectionsEquiv_restrict {s t : Finset Vertex}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) (x : ClosedRing s) :
    (CycleQ2CartierProjectiveCover.projectiveSurface 57 1).presheaf.map
        (homOfLE (closedOpen_mono hst)).op (closedSectionsEquiv s hs x) =
      closedSectionsEquiv t ht (closedRestriction hst x) :=
  congrArg (fun k => k x) (Proj.awayMap_awayToSection (surfaceGrade 57 1)
    (closedProduct_homogeneous (t \ s)) (closedProduct_factor hst)).symm

end CycleQ2LiteralProjectiveIntersectionRestrictions

end

#print axioms CycleQ2LiteralProjectiveIntersectionRestrictions.nativeReduction_restrict
#print axioms CycleQ2LiteralProjectiveIntersectionRestrictions.epsilonCoefficient_restrict
#print axioms CycleQ2LiteralProjectiveIntersectionRestrictions.thickSectionsEquiv_restrict
#print axioms CycleQ2LiteralProjectiveIntersectionRestrictions.closedSectionsEquiv_restrict
