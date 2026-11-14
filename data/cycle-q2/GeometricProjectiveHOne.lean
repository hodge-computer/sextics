import Proposal.GeometricAffineCohomology
import Proposal.GeometricSheafCohomologyRestriction
import Proposal.GeometricProjectiveCohomologyLinear
import Proposal.GeometricAffineChartSections
import Proposal.GeometricTwistedModule
import Proposal.GeometricSheafLocalIso

/-!
# The full first cohomology of the actual projective canonical sheaf

The affine structure-sheaf vanishing theorem is transported through the
actual projective chart isomorphisms and the proved degree-one frames.
The resulting ambient-site vanishing makes the existing Mayer-Vietoris
injection from the concrete Cech quotient surjective.

At the sparse seed this identifies every class of actual H¹(Ω) with its
unique complex normalization coordinate, using the intrinsic complex
scalar action. The coordinate agrees with the already checked finite
degree-nine trace. No identification with a geometric Serre trace or
moving-cycle Abel-Jacobi map is asserted.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveHOne

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricAffineChartSections

abbrev additiveForget : CommRingCat.{0} ⥤ AddCommGrpCat.{0} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat

def structureAdditiveSheaf (X : Scheme.{0}) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} :=
  (sheafCompose _ additiveForget).obj X.sheaf

def overIsoOfPatchIso {X : TopCat.{0}} {F G : X.Sheaf AddCommGrpCat.{0}}
    {U : Opens X} (e : CycleQ2GeometricSheafLocalIso.PatchIso F G U) :
    F.over U ≅ G.over U :=
  ObjectProperty.isoMk _ (NatIso.ofComponents
    (fun V => (e.app V.unop.left V.unop.hom.le).toAddCommGrpIso)
    (by
      intro V W f
      ext x
      exact (e.naturality f.unop.left.le V.unop.hom.le x).symm))

def chartStructureOverIso {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A]
    (e : U.toScheme ≅ Spec (CommRingCat.of A)) :
    (structureAdditiveSheaf X).over U ≅
      ((chartOpensEquiv e).functor.sheafPushforwardContinuous AddCommGrpCat
        ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology (Spec (CommRingCat.of A)))).obj
          (structureAdditiveSheaf (Spec (CommRingCat.of A))) :=
  ObjectProperty.isoMk _
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (chartSectionsIso e) additiveForget ≪≫
        Functor.associator _ _ _)

def firstPatchAdditiveIso (r θ : ℂ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (degreeOneSheaf r θ)
      (structureAdditiveSheaf (projectiveCurve r θ)) (firstProjectivePatch r θ) where
  app O hO := Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  naturality hPO hO s :=
    (Twisted.firstLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) hPO hO s).symm

def secondPatchAdditiveIso (r θ : ℂ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (degreeOneSheaf r θ)
      (structureAdditiveSheaf (projectiveCurve r θ)) (secondProjectivePatch r θ) where
  app O hO := Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) O hO
  naturality hPO hO s :=
    (Twisted.secondLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
      (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
      (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ) hPO hO s).symm

open CycleQ2GeometricAffineCohomology CycleQ2GeometricSheafCohomologyRestriction
  CycleQ2GeometricProjectiveCohomologyLinear CycleQ2GeometricProjectiveCanonicalH1
  CycleQ2GeometricProjectiveNonzero CycleQ2GeometricCechPoleReduction
  CycleQ2GeometricCechTrace CycleQ2GeometricConeCech.HZero CycleQ2SeedTrace

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Affine vanishing is transported through an actual affine chart and
an actual frame of the given sheaf on that chart. -/
theorem affineFrameHOne_subsingleton {X : Scheme.{0}} {U : X.Opens}
    {A : Type} [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U) :
    Subsingleton (F.H' 1 U) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of A))).H 1) :=
    affine_H_one_subsingleton A
  exact ambientHOne_subsingleton_of_chart (Opens.grothendieckTopology X) U
    (Opens.grothendieckTopology (Spec (CommRingCat.of A))) (chartOpensEquiv e)
    ⊤ isTerminalTop F (structureAdditiveSheaf (Spec (CommRingCat.of A)))
    (frame ≪≫ chartStructureOverIso e)

/-- The first denominator open is actually affine and its degree-one
frame has been constructed, so its ambient-site H′¹ is zero. -/
theorem firstPatchHOne_subsingleton (r θ : ℂ) :
    Subsingleton ((degreeOneSheaf r θ).H' 1 (firstProjectivePatch r θ)) :=
  affineFrameHOne_subsingleton (firstProjectiveChart r θ) (degreeOneSheaf r θ)
    (overIsoOfPatchIso (firstPatchAdditiveIso r θ))

theorem secondPatchHOne_subsingleton (r θ : ℂ) :
    Subsingleton ((degreeOneSheaf r θ).H' 1 (secondProjectivePatch r θ)) :=
  affineFrameHOne_subsingleton (secondProjectiveChart r θ) (degreeOneSheaf r θ)
    (overIsoOfPatchIso (secondPatchAdditiveIso r θ))

/-- Surjectivity of the original actual Cech comparison, obtained from
Mayer-Vietoris exactness and the two proved affine vanishing statements. -/
theorem degreeOneToProjectiveH1_surjective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Surjective (degreeOneToProjectiveH1 r θ hr) := by
  let F := degreeOneSheaf r θ
  let S := projectiveMayerVietoris r θ hr
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₂)) :=
    firstPatchHOne_subsingleton r θ
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₃)) :=
    secondPatchHOne_subsingleton r θ
  intro y
  have hnext : S.toBiprod F 1 y = 0 := by
    rw [S.toBiprod_apply]
    have hp :
        (((F.cohomologyPresheaf 1).map S.f₂₄.op y),
          ((F.cohomologyPresheaf 1).map S.f₃₄.op y)) =
        (0, 0) := Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hp]
    exact map_zero _
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).mp
    ((S.sequence_exact F 0 1 rfl).exact 2) y hnext
  have hx' : S.δ F 0 1 rfl x = y := hx
  let a := (overlapDegreeOneSectionsEquiv r θ).symm
    (sectionsEquiv F (overlapProjectivePatch r θ) x)
  refine ⟨QuotientAddGroup.mk a, ?_⟩
  change S.δ F 0 1 rfl
      ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
        (overlapDegreeOneSectionsEquiv r θ a)) = y
  simpa only [a, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] using hx'

def degreeOneCechHOneEquiv (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ ≃+ ProjectiveSheafH1 r θ :=
  AddEquiv.ofBijective (degreeOneToProjectiveH1 r θ hr)
    ⟨degreeOneToProjectiveH1_injective r θ hr,
      degreeOneToProjectiveH1_surjective r θ hr⟩

theorem normalizedProjectiveClass_surjective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Surjective (normalizedProjectiveClass r hr) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  exact (degreeOneToProjectiveH1_surjective r 0 hr0).comp
    (normalizedCechClass_bijective r hr).surjective

theorem normalizedCanonicalClass_surjective (r : ℂ) (hr : r ^ 3 = 2) :
    Function.Surjective (normalizedCanonicalClass r hr) :=
  (canonicalH1Equiv r hr).surjective.comp (normalizedProjectiveClass_surjective r hr)

/-- Every class in genuine H¹(Ω) has one and only one intrinsic complex
normalization coordinate. -/
def canonicalNormalizationEquiv (r : ℂ) (hr : r ^ 3 = 2) :
    ℂ ≃ₗ[ℂ] DifferentialSheafH1 r 0 :=
  LinearEquiv.ofBijective (normalizedCanonicalLinear r hr)
    ⟨normalizedCanonicalLinear_injective r hr, normalizedCanonicalClass_surjective r hr⟩

/-- A linear coordinate on all genuine H¹(Ω), fixed by the displayed
normalization numerator. Its geometric Serre-trace interpretation is a
separate comparison, not a hypothesis or conclusion of this construction. -/
def canonicalResidueCoordinate (r : ℂ) (hr : r ^ 3 = 2) :
    DifferentialSheafH1 r 0 →ₗ[ℂ] ℂ :=
  (canonicalNormalizationEquiv r hr).symm.toLinearMap

@[simp] theorem canonicalResidueCoordinate_normalized (r : ℂ) (hr : r ^ 3 = 2)
    (z : ℂ) :
    canonicalResidueCoordinate r hr (normalizedCanonicalClass r hr z) = z :=
  (canonicalNormalizationEquiv r hr).symm_apply_apply z

theorem degreeNineCanonicalClass_eq_normalized (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    degreeNineCanonicalClass r hr p hp =
      normalizedCanonicalClass r hr (traceLinear r p) := by
  have hr0 : r ≠ 0 := by intro h; simp [h] at hr
  exact congrArg (fun z : DegreeOneCech r 0 =>
    canonicalH1Equiv r hr (degreeOneToProjectiveH1 r 0 hr0 z))
      (degreeNineCechClass_eq_normalized r hr p hp)

/-- The actual derived-cohomology coordinate equals the existing exact
finite trace on every homogeneous degree-nine representative. -/
theorem canonicalResidueCoordinate_degreeNine (r : ℂ) (hr : r ^ 3 = 2)
    (p : Poly) (hp : p.IsHomogeneous 9) :
    canonicalResidueCoordinate r hr (degreeNineCanonicalClass r hr p hp) =
      traceLinear r p := by
  rw [degreeNineCanonicalClass_eq_normalized, canonicalResidueCoordinate_normalized]

theorem canonicalResidueCoordinate_eq_zero_iff (r : ℂ) (hr : r ^ 3 = 2)
    (x : DifferentialSheafH1 r 0) :
    canonicalResidueCoordinate r hr x = 0 ↔ x = 0 :=
  (canonicalNormalizationEquiv r hr).symm.map_eq_zero_iff

#print axioms firstPatchHOne_subsingleton
#print axioms secondPatchHOne_subsingleton
#print axioms degreeOneToProjectiveH1_surjective
#print axioms canonicalNormalizationEquiv
#print axioms canonicalResidueCoordinate_degreeNine

end CycleQ2GeometricProjectiveHOne
end

