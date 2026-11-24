import Proposal.GeometricThreefoldExteriorOneFrame
import Proposal.GeometricLiteralThreefoldDifferentialFrame
import Proposal.GeometricAffineOpenOrdinaryDifferentials

/-!
# Actual Kähler frames and their one-form differential on affine subopens

A chart with an exact three-element Kähler basis gives such a basis on
every affine subopen. The ordinary-to-sheaf map is bijective there, and
the existing actual section frame transports the basis back to ordinary
Kähler differentials of that subopen's original function ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2AffineExactCotangentFrames
open AlgebraicGeometry CategoryTheory Opposite Module
open CycleQ2GeometricAffineChartSections
open CycleQ2GeometricSectionDifferentials
open CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricDifferentialChartTransport
open CycleQ2GeometricSheafKaehlerMap
open CycleQ2LiteralThreefoldDifferentialFrame (sectionBasis sectionBasis_apply)
variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  (b : Basis (Fin 3) A (KaehlerDifferential ℂ A))

def nativeEquiv (V : Over U) (hV : IsAffineOpen V.left) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    SectionForms X.sheaf (schemeCoefficient f) V.left ≃ₗ[SectionRing X.sheaf V.left]
      (ChartDifferentialModule f).val.obj (op V) := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  exact LinearEquiv.ofBijective (toSheaf X.sheaf (schemeCoefficient f) V.left)
    (CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen
      (schemeCoefficient f) V.left hV)

def nativeFrame (V : Over U) (hV : IsAffineOpen V.left) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    Basis (Fin 3) (SectionRing X.sheaf V.left) (SectionForms X.sheaf (schemeCoefficient f) V.left) := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  let B : Basis (Fin 3) (SectionRing X.sheaf V.left) ((ChartDifferentialModule f).val.obj (op V)) :=
    sectionBasis e f h b V
  exact B.map (nativeEquiv f V hV).symm

theorem nativeFrame_apply (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (V : Over U) (hV : IsAffineOpen V.left) (i : Fin 3) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    nativeFrame e f h b V hV i =
      KaehlerDifferential.D ℂ (SectionRing X.sheaf V.left) (chartSection e V (u i)) := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  apply (nativeEquiv f V hV).injective
  rw [nativeFrame,Basis.map_apply,LinearEquiv.apply_symm_apply,sectionBasis_apply,hu]
  change sectionLift X.sheaf (schemeCoefficient f)
    (differentialSheaf X.sheaf (schemeCoefficient f)) (universalDifferential X.sheaf (schemeCoefficient f))
    V.left (chartSection e V) (chartSection_complex e f h V) (KaehlerDifferential.D ℂ A (u i)) = _
  rw [sectionLift_D]
  rfl

def differential (V : Over U) (hV : IsAffineOpen V.left) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    SectionForms X.sheaf (schemeCoefficient f) V.left →+
      ⋀[SectionRing X.sheaf V.left]^2 (SectionForms X.sheaf (schemeCoefficient f) V.left) := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  exact CycleQ2ThreefoldExteriorOneFrame.differential (nativeFrame e f h b V hV)

theorem differential_D (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (V : Over U) (hV : IsAffineOpen V.left) (a : SectionRing X.sheaf V.left) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    differential e f h b V hV (KaehlerDifferential.D ℂ (SectionRing X.sheaf V.left) a) = 0 := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  exact CycleQ2ThreefoldExteriorOneFrame.differential_D (nativeFrame e f h b V hV)
    (fun i => chartSection e V (u i)) (nativeFrame_apply e f h b u hu V hV) a

/-- The operator commutes with the actual section-ring restriction map. -/
theorem differential_restrict (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    {V W : Over U} (a : V ⟶ W) (hV : IsAffineOpen V.left) (hW : IsAffineOpen W.left)
    (ω : SectionForms X.sheaf (schemeCoefficient f) W.left) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) W.left
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap
        (sectionRestriction X.sheaf (schemeCoefficient f) a.left.le) 2 (differential e f h b W hW ω) =
      differential e f h b V hV (CycleQ2GeometricAffineOverlap.differentialMap
        (sectionRestriction X.sheaf (schemeCoefficient f) a.left.le) ω) := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) W.left
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  exact CycleQ2ThreefoldExteriorOneFrame.differential_natural (nativeFrame e f h b W hW)
    (fun i => chartSection e W (u i)) (nativeFrame_apply e f h b u hu W hW)
    (sectionRestriction X.sheaf (schemeCoefficient f) a.left.le) (nativeFrame e f h b V hV)
    (fun i => chartSection e V (u i)) (nativeFrame_apply e f h b u hu V hV) ω

/-- Canonical scalar multiples of unit dlogs are closed in the actual
ordinary Kähler module of each affine subopen. -/
theorem differential_scalar_log (u : Fin 3 → A) (hu : ∀ i, b i = KaehlerDifferential.D ℂ A (u i))
    (V : Over U) (hV : IsAffineOpen V.left) (c : ℂ) (v : (SectionRing X.sheaf V.left)ˣ) :
    letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
    differential e f h b V hV ((coefficientOn X.sheaf (schemeCoefficient f) V.left c) •
      ((v⁻¹ : (SectionRing X.sheaf V.left)ˣ).val • KaehlerDifferential.D ℂ (SectionRing X.sheaf V.left) (v : SectionRing X.sheaf V.left))) = 0 := by
  letI := sectionAlgebra X.sheaf (schemeCoefficient f) V.left
  exact CycleQ2ThreefoldExteriorOneFrame.differential_scalar_log (nativeFrame e f h b V hV)
    (fun i => chartSection e V (u i)) (nativeFrame_apply e f h b u hu V hV) c v

end CycleQ2AffineExactCotangentFrames
end
#print axioms CycleQ2AffineExactCotangentFrames.nativeFrame_apply
#print axioms CycleQ2AffineExactCotangentFrames.differential_D

#print axioms CycleQ2AffineExactCotangentFrames.differential_restrict
#print axioms CycleQ2AffineExactCotangentFrames.differential_scalar_log
