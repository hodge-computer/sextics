import Proposal.GeometricSurfaceSectionCoefficients
import Proposal.GeometricSurfaceCoordinateCubicFrames
import Proposal.GeometricCanonicalCoordinateH2

/-!
# Canonical two-forms in the original coordinate localizations

On a nonempty coordinate intersection, take the coordinate of an actual
canonical-form section in any of the constructed whole-coordinate frames.
The signed factor εi Xi³ turns that degree-zero coefficient into an element
of the original ordinary coordinate localization. The actual frame
transition proves independence of the selected chart, and actual frame and
homogeneous-section naturality prove compatibility with restriction.

Consequently every actual canonical pair-boundary maps to the original
ordinary coordinate boundary. Multiplication by the constructed global
cubic maps to multiplication by that same polynomial in the original
coordinate ring. These are representative-level statements; no inverse,
Laurent range, abstract trace, or extension hypothesis is needed.

Status: source-only proof draft. Compilation and independent kernel replay
are deferred at the user's request. No new axioms or admissions are used.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CanonicalCoordinateCoefficients

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading
  CycleQ2CartierProjectiveCover CycleQ2GeometricSeedNormalIdeals
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2SurfaceSectionCoefficients CycleQ2SurfaceCoordinateSections
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateCubicFrames
  CycleQ2CanonicalResidueDiagram

abbrev Surface := CycleQ2CanonicalCoordinateH2.Surface
abbrev CanonicalForms := CycleQ2SurfaceCoordinateFrames.CanonicalForms
abbrev CanonicalSheaf := CycleQ2CanonicalCoordinateH2.CanonicalSheaf
abbrev CoordinateOpen := CycleQ2CanonicalCoordinateH2.CoordinateOpen
abbrev TripleOpen := CycleQ2CanonicalCoordinateH2.TripleOpen
abbrev WeightedCubic := CycleQ2SurfaceCubicGluing.WeightedCubic

theorem orientation_local_mul_self (s : Finset (Fin 3)) (i : Fin 3) :
    (orientation i : CoordinateLocal 57 1 s) *
      (orientation i : CoordinateLocal 57 1 s) = 1 := by
  fin_cases i <;> norm_num [orientation]

/-- The actual canonical coordinate, multiplied by its signed cubic
denominator, in the unchanged ordinary coordinate localization. -/
def coefficientInChart (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) :
    CanonicalForms.val.obj (op (coordinateIntersection 57 1 s)) →+
      CoordinateLocal 57 1 s where
  toFun ω := (orientation i : CoordinateLocal 57 1 s) *
    algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
    sectionCoefficient 57 1 s hs
      ((coordinateExteriorFrame i).app (coordinateIntersection 57 1 s)
        (intersection_le_chart 57 1 i hi) ω)
  map_zero' := by simp
  map_add' ω η := by simp only [map_add, mul_add]

/-- The sign and cubic denominator exactly cancel the proved raw-frame
transition. This is independence for arbitrary actual two-forms. -/
theorem coefficientInChart_independent (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i j : Fin 3) (hi : i ∈ s) (hj : j ∈ s)
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 s))) :
    coefficientInChart s hs i hi ω = coefficientInChart s hs j hj ω := by
  let ratio := sectionCoefficient 57 1 s hs
    (coordinatePolynomialSection 57 1 (chartIndex i) (coordinateIntersection 57 1 s)
      (intersection_le_chart 57 1 i hi) (X (chartIndex j).castSucc))
  have hden : ratio^3 *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) =
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 j)^3) := by
    have h := sectionCoefficient_homogeneous 57 1 hs i hi 3
      (coordinateCube j).val (coordinateCube j).property
    simpa only [ratio, coordinateCube, map_pow, coordinateElement_eq] using h
  have htransition := congrArg (sectionCoefficient 57 1 s hs)
    (coordinateExteriorFrame_transition i j (coordinateIntersection 57 1 s)
      (intersection_le_chart 57 1 i hi) (intersection_le_chart 57 1 j hj) ω)
  simp only [map_mul, map_intCast, map_pow] at htransition
  change (orientation i : CoordinateLocal 57 1 s) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
      sectionCoefficient 57 1 s hs
        ((coordinateExteriorFrame i).app _ (intersection_le_chart 57 1 i hi) ω) = _
  rw [htransition]
  change (orientation i : CoordinateLocal 57 1 s) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
      (((orientation i : CoordinateLocal 57 1 s) * (orientation j : CoordinateLocal 57 1 s)) *
        ratio^3 * sectionCoefficient 57 1 s hs
          ((coordinateExteriorFrame j).app _ (intersection_le_chart 57 1 j hj) ω)) = _
  calc
    _ = ((orientation i : CoordinateLocal 57 1 s) *
          (orientation i : CoordinateLocal 57 1 s)) *
        (orientation j : CoordinateLocal 57 1 s) *
        (ratio^3 * algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s)
          ((coordinateElement 57 1 i)^3)) *
        sectionCoefficient 57 1 s hs
          ((coordinateExteriorFrame j).app _ (intersection_le_chart 57 1 j hj) ω) := by ring
    _ = _ := by rw [orientation_local_mul_self, hden, one_mul]; rfl

/-- Naturality when the same coordinate chart is used on source and
target. Both restrictions are the existing original restrictions. -/
theorem coefficientInChart_restrict {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (i : Fin 3) (hi : i ∈ s)
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 s))) :
    coefficientInChart t ht i (hst hi)
        (CanonicalForms.val.map (homOfLE (coordinateIntersection_mono 57 1 hst)).op ω) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1 hst
        (coefficientInChart s hs i hi ω) := by
  change (orientation i : CoordinateLocal 57 1 t) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 t) ((coordinateElement 57 1 i)^3) *
      sectionCoefficient 57 1 t ht
        ((coordinateExteriorFrame i).app _ (intersection_le_chart 57 1 i (hst hi))
          (CanonicalForms.val.map (homOfLE (coordinateIntersection_mono 57 1 hst)).op ω)) = _
  rw [← (coordinateExteriorFrame i).naturality
    (coordinateIntersection_mono 57 1 hst) (intersection_le_chart 57 1 i hi) ω,
    sectionCoefficient_restrict]
  change _ = CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1 hst
    ((orientation i : CoordinateLocal 57 1 s) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
      sectionCoefficient 57 1 s hs
        ((coordinateExteriorFrame i).app _ (intersection_le_chart 57 1 i hi) ω))
  rw [map_mul, map_mul, map_intCast, coordinateRestriction_base]

/-- The selected chart is irrelevant by `coefficientInChart_independent`. -/
def canonicalCoefficientOn (s : Finset (Fin 3)) (hs : s.Nonempty) :
    CanonicalForms.val.obj (op (coordinateIntersection 57 1 s)) →+
      CoordinateLocal 57 1 s :=
  coefficientInChart s hs hs.choose hs.choose_spec

theorem canonicalCoefficientOn_eq (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s)
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 s))) :
    canonicalCoefficientOn s hs ω = coefficientInChart s hs i hi ω :=
  coefficientInChart_independent s hs hs.choose i hs.choose_spec hi ω

theorem canonicalCoefficientOn_restrict {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (ω : CanonicalForms.val.obj (op (coordinateIntersection 57 1 s))) :
    canonicalCoefficientOn t ht
        (CanonicalForms.val.map (homOfLE (coordinateIntersection_mono 57 1 hst)).op ω) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1 hst
        (canonicalCoefficientOn s hs ω) := by
  rw [canonicalCoefficientOn_eq t ht hs.choose (hst hs.choose_spec)]
  exact coefficientInChart_restrict hs ht hst hs.choose hs.choose_spec ω

/-- The same actual coefficient map on an equal actual open. -/
def canonicalCoefficientAt (s : Finset (Fin 3)) (hs : s.Nonempty)
    (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 s) :
    CanonicalForms.val.obj (op O) →+ CoordinateLocal 57 1 s := by
  subst O
  exact canonicalCoefficientOn s hs

theorem canonicalCoefficientAt_restrict {s t : Finset (Fin 3)}
    (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t)
    (O P : Surface.Opens)
    (hO : O = coordinateIntersection 57 1 s) (hP : P = coordinateIntersection 57 1 t)
    (hPO : P ≤ O) (ω : CanonicalForms.val.obj (op O)) :
    canonicalCoefficientAt t ht P hP (CanonicalForms.val.map (homOfLE hPO).op ω) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1 hst
        (canonicalCoefficientAt s hs O hO ω) := by
  subst O
  subst P
  exact canonicalCoefficientOn_restrict hs ht hst ω

/-- Multiplication by an actual global cubic becomes multiplication by
its unchanged homogeneous numerator, for an arbitrary scalar section. -/
theorem coefficientInChart_cubic_smul (s : Finset (Fin 3)) (hs : s.Nonempty)
    (i : Fin 3) (hi : i ∈ s) (p : WeightedCubic)
    (a : Γ(Surface, coordinateIntersection 57 1 s)) :
    coefficientInChart s hs i hi
        (a • formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p)
          (coordinateIntersection 57 1 s)) =
      sectionCoefficient 57 1 s hs a *
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) (surfaceQuotient 57 1 p.val) := by
  change (orientation i : CoordinateLocal 57 1 s) *
      algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3) *
      sectionCoefficient 57 1 s hs
        ((coordinateExteriorFrame i).app _ (intersection_le_chart 57 1 i hi)
          (a • CanonicalForms.val.map (homOfLE (show coordinateIntersection 57 1 s ≤ ⊤ from le_top)).op
            (CycleQ2GlobalSurfaceCubics.globalCubicSection p))) = _
  rw [map_smul, coordinateExteriorFrame_globalCubic, smul_eq_mul]
  simp only [map_mul, map_intCast]
  calc
    _ = sectionCoefficient 57 1 s hs a *
        (((orientation i : CoordinateLocal 57 1 s) *
          (orientation i : CoordinateLocal 57 1 s)) *
          (sectionCoefficient 57 1 s hs
            (coordinatePolynomialSection 57 1 (chartIndex i) (coordinateIntersection 57 1 s)
              (intersection_le_chart 57 1 i hi) p.val) *
            algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s)
              ((coordinateElement 57 1 i)^3))) := by ring
    _ = _ := by
      rw [orientation_local_mul_self, one_mul,
        sectionCoefficient_homogeneous 57 1 hs i hi 3 p.val p.property]

theorem canonicalCoefficientOn_cubic_smul (s : Finset (Fin 3)) (hs : s.Nonempty)
    (p : WeightedCubic) (a : Γ(Surface, coordinateIntersection 57 1 s)) :
    canonicalCoefficientOn s hs
        (a • formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p)
          (coordinateIntersection 57 1 s)) =
      sectionCoefficient 57 1 s hs a *
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) (surfaceQuotient 57 1 p.val) :=
  coefficientInChart_cubic_smul s hs hs.choose hs.choose_spec p a

theorem canonicalCoefficientAt_cubic_smul (s : Finset (Fin 3)) (hs : s.Nonempty)
    (O : Surface.Opens) (hO : O = coordinateIntersection 57 1 s)
    (p : WeightedCubic) (a : Γ(Surface, O)) :
    canonicalCoefficientAt s hs O hO
        (a • formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p) O) =
      sectionCoefficientAt 57 1 s hs O hO a *
        algebraMap (SurfaceRing 57 1) (CoordinateLocal 57 1 s) (surfaceQuotient 57 1 p.val) := by
  subst O
  simpa [canonicalCoefficientAt, sectionCoefficientAt, sectionCoefficient,
    sectionsAt, Iso.commRingCatIsoToRingEquiv] using
    canonicalCoefficientOn_cubic_smul s hs p a

/-- Pair coefficients on the exact original three-open intersections. -/
def canonicalPairCoefficient (i j : Fin 3) :
    CanonicalSheaf.obj.obj (op (CoordinateOpen i ⊓ CoordinateOpen j)) →+
      CoordinateLocal 57 1 {i,j} :=
  canonicalCoefficientAt {i,j} (by simp) _ (coordinateIntersection_pair 57 1 i j).symm

/-- The top coefficient on the exact original Mayer--Vietoris triple open. -/
def canonicalCoefficient : CanonicalSheaf.obj.obj (op TripleOpen) →+
    CoordinateLocal 57 1 Finset.univ :=
  canonicalCoefficientAt Finset.univ (by simp) _ (coordinateIntersection_univ 57 1).symm

/-- Every actual canonical boundary maps to the unchanged ordinary
coordinate boundary, including the original three alternating signs. -/
theorem canonicalCoefficient_boundary
    (a : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 1)))
    (b : CanonicalSheaf.obj.obj (op (CoordinateOpen 0 ⊓ CoordinateOpen 2)))
    (c : CanonicalSheaf.obj.obj (op (CoordinateOpen 1 ⊓ CoordinateOpen 2))) :
    canonicalCoefficient (CycleQ2ThreeOpenSectionH2.boundary CanonicalSheaf
      (CoordinateOpen 0) (CoordinateOpen 1) (CoordinateOpen 2) (a,b,c)) =
      CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1
          (Finset.subset_univ {1,2}) (canonicalPairCoefficient 1 2 c) -
        CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1
          (Finset.subset_univ {0,2}) (canonicalPairCoefficient 0 2 b) +
        CycleQ2GeometricSurfaceCoordinates.coordinateRestriction 57 1
          (Finset.subset_univ {0,1}) (canonicalPairCoefficient 0 1 a) := by
  have h12 := canonicalCoefficientAt_restrict (s := {1,2}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {1,2})
    (CoordinateOpen 1 ⊓ CoordinateOpen 2) TripleOpen
    (coordinateIntersection_pair 57 1 1 2).symm (coordinateIntersection_univ 57 1).symm
    inf_le_right c
  have h02 := canonicalCoefficientAt_restrict (s := {0,2}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {0,2})
    (CoordinateOpen 0 ⊓ CoordinateOpen 2) TripleOpen
    (coordinateIntersection_pair 57 1 0 2).symm (coordinateIntersection_univ 57 1).symm
    inf_le_left b
  have h01 := canonicalCoefficientAt_restrict (s := {0,1}) (t := Finset.univ)
    (by simp) (by simp) (Finset.subset_univ {0,1})
    (CoordinateOpen 0 ⊓ CoordinateOpen 1) TripleOpen
    (coordinateIntersection_pair 57 1 0 1).symm (coordinateIntersection_univ 57 1).symm
    (inf_le_inf (inf_le_left : CoordinateOpen 0 ⊓ CoordinateOpen 2 ≤ CoordinateOpen 0)
      (inf_le_left : CoordinateOpen 1 ⊓ CoordinateOpen 2 ≤ CoordinateOpen 1)) a
  change canonicalCoefficient
    (CanonicalForms.val.map (homOfLE inf_le_right).op c -
      CanonicalForms.val.map (homOfLE inf_le_left).op b +
      CanonicalForms.val.map (homOfLE
        (inf_le_inf (inf_le_left : CoordinateOpen 0 ⊓ CoordinateOpen 2 ≤ CoordinateOpen 0)
          (inf_le_left : CoordinateOpen 1 ⊓ CoordinateOpen 2 ≤ CoordinateOpen 1))).op a) = _
  rw [map_add, map_sub]
  exact congrArg₂ (· + ·) (congrArg₂ (· - ·) h12 h02) h01

/-- Multiplication of the original homogeneous triple representative by
the genuine global cubic has the exact original polynomial coefficient. -/
theorem canonicalCoefficient_cubicTripleSection (p : WeightedCubic)
    (q : CycleQ2GeometricHomogeneousWeight.HomogeneousCoordinateTop 57) :
    canonicalCoefficient (CycleQ2CanonicalCoordinateH2.cubicTripleSection p q) =
      surfaceQuotient 57 1 p.val • q.val := by
  change canonicalCoefficient
    (tripleSections 57 1 q •
      formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p) TripleOpen) = _
  change canonicalCoefficientAt Finset.univ (by simp) TripleOpen
      (coordinateIntersection_univ 57 1).symm
      (tripleSections 57 1 q •
        formRestriction (CycleQ2GlobalSurfaceCubics.globalCubicSection p) TripleOpen) = _
  rw [canonicalCoefficientAt_cubic_smul]
  change sectionCoefficientAt 57 1 Finset.univ (by simp) TripleOpen
      (coordinateIntersection_univ 57 1).symm
      (sectionsAt 57 1 Finset.univ (by simp) TripleOpen
        (coordinateIntersection_univ 57 1).symm q) * _ = _
  rw [sectionCoefficientAt_sectionsAt, Algebra.smul_def]
  exact mul_comm _ _

#print axioms canonicalCoefficient_boundary
#print axioms canonicalCoefficient_cubicTripleSection

end CycleQ2CanonicalCoordinateCoefficients

end
