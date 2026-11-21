import Proposal.GeometricLiteralNativeCupDerivedClass
import Proposal.GeometricSurfaceProjectiveCoefficients

/-!
# Native differentials map to the original projective differential sheaf

The actual native intersection/section equivalence preserves the original
complex coefficients. Universal differential maps and the existing
sheafification unit therefore give an additive, semilinear map from the
native Kähler module to the original projective differential sheaf.
This map commutes with the genuine restrictions and carries the actual
native transition dlog to the literal sheaf-valued logarithmic derivative.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralNativeDifferentialSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry HomogeneousLocalization
  CycleQ2CartierProjectiveCover CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSectionDifferentials
  CycleQ2GeometricAffineOverlap CycleQ2GeometricSquareZeroSplittings

abbrev Surface := projectiveSurface 57 1
abbrev globalCoefficient := CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1
abbrev DifferentialSheaf := differentialSheaf Surface.sheaf globalCoefficient

attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule

local instance sectionComplexAlgebra (U : Surface.Opens) : Algebra ℂ (SectionRing Surface.sheaf U) :=
  sectionAlgebra Surface.sheaf globalCoefficient U

local instance sectionComplexSMul (U : Surface.Opens) : SMul ℂ (SectionRing Surface.sheaf U) :=
  (sectionComplexAlgebra U).toSMul

local instance sectionComplexModule (U : Surface.Opens) : Module ℂ (SectionRing Surface.sheaf U) :=
  @Algebra.toModule ℂ (SectionRing Surface.sheaf U) _ _ (sectionComplexAlgebra U)

theorem closedSectionsEquiv_complex (s : Finset Vertex) (hs : s.Nonempty) (c : ℂ) :
    closedSectionsEquiv s hs (algebraMap ℂ (ClosedRing s) c) =
      coefficientOn Surface.sheaf globalCoefficient (closedOpen s) c := by
  apply (closedSectionsEquiv s hs).symm.injective
  rw [RingEquiv.symm_apply_apply]
  exact (CycleQ2GeometricSurfaceCoefficients.coefficientOn_basicOpen 57 1 (closedProduct s)
    (closedProduct_homogeneous s) (productDegree_pos hs) c).symm

def nativeSectionsAlgEquiv (s : Finset Vertex) (hs : s.Nonempty) :
    ClosedRing s ≃ₐ[ℂ] SectionRing Surface.sheaf (closedOpen s) where
  __ := closedSectionsEquiv s hs
  commutes' := closedSectionsEquiv_complex s hs

theorem nativeSectionsAlgEquiv_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (x : ClosedRing s) :
    sectionRestriction Surface.sheaf globalCoefficient (closedOpen_mono hst) (nativeSectionsAlgEquiv s hs x) =
      nativeSectionsAlgEquiv t ht (closedRestrictionAlgHom hst x) :=
  closedSectionsEquiv_restrict hs ht hst x

def nativeFormToSheaf (s : Finset Vertex) (hs : s.Nonempty) :
    KaehlerDifferential ℂ (ClosedRing s) →+ DifferentialSheaf.val.obj (op (closedOpen s)) :=
  (toSheaf Surface.sheaf globalCoefficient (closedOpen s)).toAddMonoidHom.comp
    (differentialMap (nativeSectionsAlgEquiv s hs).toAlgHom).toAddMonoidHom

theorem nativeFormToSheaf_smul (s : Finset Vertex) (hs : s.Nonempty) (a : ClosedRing s)
    (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    nativeFormToSheaf s hs (a • ω) = nativeSectionsAlgEquiv s hs a • nativeFormToSheaf s hs ω := by
  change toSheaf Surface.sheaf globalCoefficient (closedOpen s)
    (differentialMap (nativeSectionsAlgEquiv s hs).toAlgHom (a • ω)) = _
  rw [differentialMap_smul, map_smul]
  rfl

theorem nativeFormToSheaf_D (s : Finset Vertex) (hs : s.Nonempty) (a : ClosedRing s) :
    nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) a) =
      (universalDifferential Surface.sheaf globalCoefficient).d (X := op (closedOpen s)) (nativeSectionsAlgEquiv s hs a) := by
  change toSheaf Surface.sheaf globalCoefficient (closedOpen s)
    (differentialMap (nativeSectionsAlgEquiv s hs).toAlgHom (KaehlerDifferential.D ℂ (ClosedRing s) a)) = _
  rw [differentialMap_D]
  exact toSheaf_D Surface.sheaf globalCoefficient (closedOpen s) _

theorem nativeFormToSheaf_restrict {s t : Finset Vertex} (hst : s ⊆ t)
    (hs : s.Nonempty) (ht : t.Nonempty) (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    DifferentialSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeFormToSheaf s hs ω) =
      nativeFormToSheaf t ht (differentialMap (closedRestrictionAlgHom hst) ω) := by
  have he : (sectionRestriction Surface.sheaf globalCoefficient (closedOpen_mono hst)).comp
      (nativeSectionsAlgEquiv s hs).toAlgHom =
      (nativeSectionsAlgEquiv t ht).toAlgHom.comp (closedRestrictionAlgHom hst) := by
    apply AlgHom.ext
    intro x
    exact nativeSectionsAlgEquiv_restrict hst hs ht x
  change DifferentialSheaf.val.map (homOfLE (closedOpen_mono hst)).op
    (toSheaf Surface.sheaf globalCoefficient (closedOpen s)
      (differentialMap (nativeSectionsAlgEquiv s hs).toAlgHom ω)) =
    toSheaf Surface.sheaf globalCoefficient (closedOpen t)
      (differentialMap (nativeSectionsAlgEquiv t ht).toAlgHom (differentialMap (closedRestrictionAlgHom hst) ω))
  rw [toSheaf_restrict, differentialMap_comp, differentialMap_comp, he]

def sectionUnit (s : Finset Vertex) (hs : s.Nonempty) (g : (ClosedRing s)ˣ) :
    (SectionRing Surface.sheaf (closedOpen s))ˣ :=
  Units.map (nativeSectionsAlgEquiv s hs).toMonoidHom g

def sheafLogDifferential (U : Surface.Opens) (g : (SectionRing Surface.sheaf U)ˣ) : DifferentialSheaf.val.obj (op U) :=
  (↑(g⁻¹) : SectionRing Surface.sheaf U) •
    (universalDifferential Surface.sheaf globalCoefficient).d (X := op U) (g : SectionRing Surface.sheaf U)

theorem nativeFormToSheaf_logDifferential (s : Finset Vertex) (hs : s.Nonempty) (g : (ClosedRing s)ˣ) :
    nativeFormToSheaf s hs (logDifferential (K := ℂ) g) =
      sheafLogDifferential (closedOpen s) (sectionUnit s hs g) := by
  rw [logDifferential, nativeFormToSheaf_smul, nativeFormToSheaf_D]
  rfl

theorem differentialMap_logDifferential {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B) (g : Aˣ) :
    differentialMap f (logDifferential (K := ℂ) g) =
      logDifferential (K := ℂ) (Units.map f.toMonoidHom g) := by
  rw [logDifferential, differentialMap_smul, differentialMap_D]
  rfl

theorem sheafLogDifferential_toSheaf (U : Surface.Opens) (g : (SectionRing Surface.sheaf U)ˣ) :
    sheafLogDifferential U g = toSheaf Surface.sheaf globalCoefficient U (logDifferential (K := ℂ) g) := by
  rw [logDifferential, map_smul, toSheaf_D]
  rfl

def restrictSectionUnit {U V : Surface.Opens} (h : V ≤ U) (g : (SectionRing Surface.sheaf U)ˣ) :
    (SectionRing Surface.sheaf V)ˣ :=
  Units.map (sectionRestriction Surface.sheaf globalCoefficient h).toMonoidHom g

theorem sheafLogDifferential_restrict {U V : Surface.Opens} (h : V ≤ U) (g : (SectionRing Surface.sheaf U)ˣ) :
    DifferentialSheaf.val.map (homOfLE h).op (sheafLogDifferential U g) =
      sheafLogDifferential V (restrictSectionUnit h g) := by
  rw [sheafLogDifferential_toSheaf, sheafLogDifferential_toSheaf,
    toSheaf_restrict, differentialMap_logDifferential]
  rfl

theorem sheafLogDifferential_mul (U : Surface.Opens) (g h : (SectionRing Surface.sheaf U)ˣ) :
    sheafLogDifferential U (g * h) = sheafLogDifferential U g + sheafLogDifferential U h := by
  rw [sheafLogDifferential_toSheaf, sheafLogDifferential_toSheaf, sheafLogDifferential_toSheaf,
    logDifferential_mul, map_add]

theorem sheafLogDifferential_one (U : Surface.Opens) : sheafLogDifferential U 1 = 0 := by
  rw [sheafLogDifferential_toSheaf, logDifferential_one, map_zero]

end CycleQ2LiteralNativeDifferentialSections

end

#print axioms CycleQ2LiteralNativeDifferentialSections.nativeFormToSheaf_restrict
#print axioms CycleQ2LiteralNativeDifferentialSections.nativeFormToSheaf_logDifferential
#print axioms CycleQ2LiteralNativeDifferentialSections.sheafLogDifferential_restrict
