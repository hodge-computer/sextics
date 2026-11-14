import Proposal.GeometricProjectiveCech
import Proposal.GeometricTraceBoundary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.Topology.Sheaves.Functors
import Proposal.GeometricConeCech

/-!
# Projective curves, twisted cohomology, and incidence schemes

The projective charts, homogeneous frames, twisted additive sheaf, and
Mayer--Vietoris injection are checked in the small imported helper modules.
The remaining cone and incidence continuation in this file is source-only.

The existing normal calculation uses the sparse cubic
`CycleQ2SeedCechTheta.curveH θ`.  We construct the genuine projective spectrum
of its homogeneous coordinate ring.  The construction first supplies the
quotient grading, including its direct-sum decomposition, rather than
assuming a grading on the quotient.  The two denominator opens then give
an actual affine cover of this projective scheme. Its degree-one localized
modules have explicit affine frames and an invertible transition section.
Those data construct an actual additive sheaf; its chart-section comparison
and the Mayer--Vietoris sequence put the literal nonzero incidence class
in genuine derived cohomology on the projective curve.

The incidence tangent at `(r,θ)=(57,1)` gives a nonzero class in the
degree-one Cech quotient. Its two constructed images are the actual cone
and projective derived classes. No general comparison between those two
derived groups or surjectivity onto projective cohomology is asserted.

This curve is the sparse family already used by `CurveRing r θ`.  It is
not silently identified with the different full cubic occurring in the
written rank computations.  No smoothness, Serre trace, or comparison with
Betti cohomology is assumed here. The additive construction does not yet
provide the canonical module-sheaf identification or geometric Serre trace.

The final namespace uses the same quotient-grading factory to construct
the actual weighted incidence surface and the projective zero locus of
its three generic section equations. Their morphisms to the parameter
base and ambient scheme, and their binding to the existing section ideal,
are explicit. Flatness, smooth curve fibers, and the Cartier and
Abel--Jacobi identifications remain separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped DirectSum
open MvPolynomial CycleQ2SeedTrace CycleQ2ConormalJacobian
  CycleQ2NormalConnecting CycleQ2SeedCechTheta CycleQ2ActualNormalCech

attribute [local instance] MvPolynomial.gradedAlgebra

def degreeOneToScalarRepresentative (r θ : ℂ) :
    OverlapDegreeOne r θ →+ ScalarCech r θ :=
  (scalarBoundaries r θ).mkQ.toAddMonoidHom.comp
    (OverlapDegreeOne r θ).subtype.toAddMonoidHom

theorem degreeOneBoundaries_toScalar_zero (r θ : ℂ) :
    degreeOneBoundaries r θ ≤ (degreeOneToScalarRepresentative r θ).ker := by
  rintro z ⟨⟨a, b⟩, rfl⟩
  change (Submodule.Quotient.mk
    ((firstDegreeOneRestriction r θ a : Overlap r θ) -
      (secondDegreeOneRestriction r θ b : Overlap r θ)) : ScalarCech r θ) = 0
  rw [firstDegreeOneRestriction_coe, secondDegreeOneRestriction_coe]
  apply (Submodule.Quotient.mk_eq_zero (scalarBoundaries r θ)).mpr
  exact Submodule.sub_mem _
    (le_sup_left (show firstRestriction r θ a ∈
      LinearMap.range (firstRestrictionAlg r θ).toLinearMap from ⟨a, rfl⟩))
    (le_sup_right (show secondRestriction r θ b ∈
      LinearMap.range (secondRestrictionAlg r θ).toLinearMap from ⟨b, rfl⟩))

/-- Forgetting degree respects the genuine single-chart coboundaries. -/
def degreeOneCechToScalar (r θ : ℂ) : DegreeOneCech r θ →+ ScalarCech r θ :=
  QuotientAddGroup.lift (degreeOneBoundaries r θ)
    (degreeOneToScalarRepresentative r θ) (degreeOneBoundaries_toScalar_zero r θ)

@[simp] theorem degreeOneCechToScalar_mk (r θ : ℂ) (z : OverlapDegreeOne r θ) :
    degreeOneCechToScalar r θ (QuotientAddGroup.mk z) =
      (Submodule.Quotient.mk (z : Overlap r θ) : ScalarCech r θ) := rfl

/-- Compose with the previously constructed scalar injection into actual
derived structure-sheaf cohomology of the punctured cone. -/
def degreeOneCechToConeH1 (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ →+ CycleQ2GeometricConeCech.ConeSheafH1 r θ :=
  (CycleQ2GeometricConeCech.scalarToSheafH1 r θ hr).comp (degreeOneCechToScalar r θ)

open CycleQ2NormalKoszulBridge CycleQ2SeedBoundaryProjection

/-- The homogeneous fraction is exactly the earlier simple-pole
representative, with both inverse units fixed by the actual chart maps. -/
theorem simplePoleRepresentative_eq_fraction (r θ : ℂ) (p : Poly) :
    simplePoleRepresentative r θ (polynomialLift p) =
      awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ p) := by
  rw [awayFraction, Localization.mk_eq_mk', IsLocalization.eq_mk'_iff_mul_eq]
  simp only [pow_one, Subtype.coe_mk, map_mul]
  rw [simplePoleRepresentative_apply, overlap_algebraMap]
  have hbase : overlapAmbient r θ (polynomialLift p) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) := by
    simp only [overlapAmbient, ambientCurveMap, RingHom.comp_apply,
      substitute_polynomialLift]
  rw [hbase, ← coe_firstOverlapUnit, ← coe_secondOverlapUnit]
  calc
    algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) *
          (↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) *
          (↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) *
          ((firstOverlapUnit r θ : Overlap r θ) * (secondOverlapUnit r θ : Overlap r θ)) =
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) *
          ((↑((firstOverlapUnit r θ)⁻¹) : Overlap r θ) * (firstOverlapUnit r θ)) *
          ((↑((secondOverlapUnit r θ)⁻¹) : Overlap r θ) * (secondOverlapUnit r θ)) := by ring
    _ = _ := by rw [(firstOverlapUnit r θ).inv_mul, (secondOverlapUnit r θ).inv_mul,
      mul_one, mul_one]

@[simp] theorem degreeNineCechClass_toScalar (r θ : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) :
    degreeOneCechToScalar r θ (degreeNineCechClass r θ p hp) =
      simplePoleClass r θ (polynomialLift p) := by
  change (Submodule.Quotient.mk
    (awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ p)) :
      ScalarCech r θ) = _
  rw [simplePoleClass_apply, simplePoleRepresentative_eq_fraction]

/-- The paired normal class is represented in the degree-one chart
modules, rather than only in the ungraded cone localization. -/
def pairedDegreeOneClass (r θ : ℂ) (v : Fin 9 → ℂ) : DegreeOneCech r θ :=
  degreeNineCechClass r θ (-derivativeNumerator (cubicDeformation v))
    (derivativeNumerator_homogeneous v).neg

theorem pairedDegreeOneClass_toScalar (r θ : ℂ) (v : Fin 9 → ℂ) :
    degreeOneCechToScalar r θ (pairedDegreeOneClass r θ v) =
      (Submodule.Quotient.mk (pairedNormalOverlap r θ (cubicDeformation v)) :
        ScalarCech r θ) := by
  rw [pairedDegreeOneClass, degreeNineCechClass_toScalar, simplePoleClass_apply,
    simplePoleRepresentative_lift_derivative]

theorem pairedDegreeOneClass_ne_zero (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0) :
    pairedDegreeOneClass r θ v ≠ 0 := by
  intro hz
  apply pairedScalarClass_ne_zero r θ hr v hv
  rw [← pairedDegreeOneClass_toScalar, hz, map_zero]

/-- The literal incidence seed uses theta = 1, r = 57, and the cubic
component of the proved fixed-sextic incidence tangent. -/
def incidenceDegreeOneClass : DegreeOneCech 57 1 :=
  pairedDegreeOneClass 57 1 CycleQ2GeometricConeCech.incidenceCubicCoefficients

theorem incidenceDegreeOneClass_toScalar :
    degreeOneCechToScalar 57 1 incidenceDegreeOneClass =
      CycleQ2GeometricConeCech.incidenceScalarClass := by
  rw [incidenceDegreeOneClass, pairedDegreeOneClass_toScalar,
    CycleQ2GeometricConeCech.incidenceScalarClass_eq]

theorem incidenceDegreeOneClass_ne_zero : incidenceDegreeOneClass ≠ 0 := by
  intro hz
  apply CycleQ2GeometricConeCech.incidenceScalarClass_ne_zero
  rw [← incidenceDegreeOneClass_toScalar, hz, map_zero]

theorem incidenceDegreeOneClass_toConeH1 :
    degreeOneCechToConeH1 57 1 (by norm_num) incidenceDegreeOneClass =
      CycleQ2GeometricConeCech.incidenceSheafClass := by
  change CycleQ2GeometricConeCech.scalarToSheafH1 57 1 _
      (degreeOneCechToScalar 57 1 incidenceDegreeOneClass) = _
  rw [incidenceDegreeOneClass_toScalar]
  rfl

/-! ## The actual topological cone projection

The homogeneous core sends every punctured-cone point to a relevant
homogeneous prime.  This is a continuous map of the actual underlying
spaces.  Its extension to a scheme morphism requires the structure-sheaf
map and is not asserted here.
-/

def coneProjectivePoint (r θ : ℂ)
    (q : CycleQ2GeometricConeCech.puncturedOpen r θ) :
    ProjectiveSpectrum (curveGrade r θ) where
  asHomogeneousIdeal := q.1.asIdeal.homogeneousCore (curveGrade r θ)
  isPrime := Ideal.IsPrime.homogeneousCore _
    (inferInstance : q.1.asIdeal.IsPrime)
  not_irrelevant_le := by
    intro h
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp q.property
    apply hj
    exact Ideal.toIdeal_homogeneousCore_le _ _
      (h (HomogeneousIdeal.mem_irrelevant_of_mem _ (by decide)
        (coordinate_mem_grade r θ j)))

theorem coneProjectivePoint_mem_basicOpen (r θ : ℂ)
    {d : ℕ} {f : CurveRing r θ} (hf : f ∈ curveGrade r θ d)
    (q : CycleQ2GeometricConeCech.puncturedOpen r θ) :
    coneProjectivePoint r θ q ∈ Proj.basicOpen (curveGrade r θ) f ↔
      q.1 ∈ PrimeSpectrum.basicOpen f := by
  change (f ∉ q.1.asIdeal.homogeneousCore (curveGrade r θ)) ↔ f ∉ q.1.asIdeal
  constructor
  · intro h hmem
    exact h (Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨d, hf⟩ hmem)
  · intro h hmem
    exact h (Ideal.toIdeal_homogeneousCore_le _ _ hmem)

theorem coneProjectivePoint_preimage_zeroLocus (r θ : ℂ)
    (J : HomogeneousIdeal (curveGrade r θ)) :
    coneProjectivePoint r θ ⁻¹'
        ProjectiveSpectrum.zeroLocus (curveGrade r θ) (J : Set (CurveRing r θ)) =
      (Subtype.val : CycleQ2GeometricConeCech.puncturedOpen r θ →
        PrimeSpectrum (CurveRing r θ)) ⁻¹'
          PrimeSpectrum.zeroLocus (J.toIdeal : Set (CurveRing r θ)) := by
  ext q
  change J ≤ q.1.asIdeal.homogeneousCore (curveGrade r θ) ↔ J.toIdeal ≤ q.1.asIdeal
  exact (Ideal.homogeneousCore.gc (curveGrade r θ) J q.1.asIdeal).symm

theorem continuous_coneProjectivePoint (r θ : ℂ) :
    Continuous (coneProjectivePoint r θ) := by
  apply continuous_iff_isClosed.mpr
  intro Z hZ
  let J : HomogeneousIdeal (curveGrade r θ) := ProjectiveSpectrum.vanishingIdeal Z
  have hJ : ProjectiveSpectrum.zeroLocus (curveGrade r θ)
      (J : Set (CurveRing r θ)) = Z :=
    (ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure _ _).trans hZ.closure_eq
  rw [← hJ, coneProjectivePoint_preimage_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).preimage continuous_subtype_val

def coneToProjectiveTop (r θ : ℂ) :
    C(CycleQ2GeometricConeCech.puncturedOpen r θ, projectiveCurve r θ) :=
  ⟨coneProjectivePoint r θ, continuous_coneProjectivePoint r θ⟩

def incidenceProjectiveSheafClass : ProjectiveSheafH1 57 1 :=
  degreeOneToProjectiveH1 57 1 (by norm_num) incidenceDegreeOneClass

theorem incidenceProjectiveSheafClass_ne_zero :
    incidenceProjectiveSheafClass ≠ 0 := by
  intro h
  apply incidenceDegreeOneClass_ne_zero
  apply degreeOneToProjectiveH1_injective 57 1 (by norm_num)
  simpa only [incidenceProjectiveSheafClass, map_zero] using h

/-- Both genuine derived classes come from the same explicitly bound
degree-one incidence numerator. This states the two constructed maps,
without inventing a global comparison between the two derived groups. -/
theorem incidence_class_images :
    degreeOneToProjectiveH1 57 1 (by norm_num) incidenceDegreeOneClass =
        incidenceProjectiveSheafClass ∧
      degreeOneCechToConeH1 57 1 (by norm_num) incidenceDegreeOneClass =
        CycleQ2GeometricConeCech.incidenceSheafClass :=
  ⟨rfl, incidenceDegreeOneClass_toConeH1⟩

end CycleQ2GeometricProjectiveCurve
end

/-!
# The actual projective morphism of a homogeneous quotient

Source-only continuation. No elaborator or compiler has been run.
The grading factory used below proves the quotient grading from homogeneity
of the ideal. The map is the actual scheme morphism supplied by `Proj.map`.
No closed-immersion, base-change, smoothness, or fiber claim is made here.

The common universe for `R` and `A` follows the pinned `Proj.map` API.
The quotient graded ring homomorphism itself does not need `hI`; the
projective source uses `gradedRing 𝒜 I hI` to construct its grading.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2GeometricProjectiveCurve.HomogeneousQuotient

open CategoryTheory AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] (I : Ideal A)

/-- The literal quotient ring map preserves every homogeneous component. -/
def quotientMap : 𝒜 →+*ᵍ grade 𝒜 I where
  toRingHom := Ideal.Quotient.mk I
  map_mem hp := ⟨_, hp, rfl⟩

@[simp] theorem quotientMap_apply (a : A) :
    quotientMap 𝒜 I a = Ideal.Quotient.mk I a := rfl

theorem quotientMap_surjective : Function.Surjective (quotientMap 𝒜 I) :=
  Ideal.Quotient.mk_surjective

/-- Positive-degree quotient elements lift to positive-degree ambient
elements. Thus the irrelevant ideal condition for `Proj.map` is proved. -/
theorem irrelevant_le_map_quotientMap [GradedRing (grade 𝒜 I)] :
    HomogeneousIdeal.irrelevant (grade 𝒜 I) ≤
      (HomogeneousIdeal.irrelevant 𝒜).map (quotientMap 𝒜 I) := by
  apply HomogeneousIdeal.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (grade 𝒜 I)).mpr
  intro n hn a ha
  obtain ⟨p, hp, rfl⟩ := ha
  exact Ideal.mem_map_of_mem (quotientMap 𝒜 I)
    (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn hp)

/-- Projective spectrum of the actual quotient with its proved grading. -/
def projectiveScheme (hI : I.IsHomogeneous 𝒜) : Scheme.{u} :=
  letI := gradedRing 𝒜 I hI
  Proj (grade 𝒜 I)

/-- The genuine scheme morphism induced by the quotient map. -/
def projectiveMap (hI : I.IsHomogeneous 𝒜) :
    projectiveScheme 𝒜 I hI ⟶ Proj 𝒜 := by
  letI := gradedRing 𝒜 I hI
  exact Proj.map (quotientMap 𝒜 I) (irrelevant_le_map_quotientMap 𝒜 I)

/-- The actual basic open in the projective quotient. -/
def projectiveBasicOpen (hI : I.IsHomogeneous 𝒜) (a : A) :
    (projectiveScheme 𝒜 I hI).Opens :=
  letI := gradedRing 𝒜 I hI
  Proj.basicOpen (grade 𝒜 I) (Ideal.Quotient.mk I a)

@[simp] theorem projectiveMap_preimage_basicOpen (hI : I.IsHomogeneous 𝒜) (a : A) :
    projectiveMap 𝒜 I hI ⁻¹ᵁ Proj.basicOpen 𝒜 a =
      projectiveBasicOpen 𝒜 I hI a := by
  letI := gradedRing 𝒜 I hI
  exact Proj.map_preimage_basicOpen (quotientMap 𝒜 I)
    (irrelevant_le_map_quotientMap 𝒜 I) a

end CycleQ2GeometricProjectiveCurve.HomogeneousQuotient

end

/-!
# Actual projective schemes for the incidence equations

Source-only continuation; no elaborator or compiler has been run.

The coefficient ring has degree zero and the five geometric coordinates
have weights `(1,1,1,1,2)`.  The degree-three cubic, degree-six sextic, and
degree-fourteen matrix entries are the literal polynomials already used
by `CycleQ2IncidenceImageLine.PointSurface`.  Their homogeneity is proved
from the existing degree/character grading.  No homogeneous-ideal input
is supplied by a caller.

Over the polynomial coefficient ring `S[T0,T1,T2]`, the three entries of
the literal product `M*T` give a homogeneous ideal and hence an actual
projective scheme, with maps to the incidence surface, weighted ambient
projective scheme, and affine parameter base.  This construction does
not assert flatness, nonemptiness, smoothness, or a relative Cartier
property for this candidate curve scheme.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace CycleQ2GeometricIncidenceProj

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceGenericPointSemantics
  CycleQ2IncidenceImageLine

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-! ## The actual homogeneous incidence surface -/

def geometricWeight : Fin 5 → ℕ := ![1, 1, 1, 1, 2]

theorem geometricWeight_weight (e : FullExponent) :
    Finsupp.weight geometricWeight e = fullDegree e := by
  rw [Finsupp.weight_eq_sum]
  simp [geometricWeight, fullDegree, Fin.sum_univ_succ, nsmul_eq_mul] <;> ring

theorem homogeneous_of_character {S : Type*} [CommRing S]
    {p : MvPolynomial (Fin 5) S} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) :
    p.IsWeightedHomogeneous geometricWeight d := by
  intro e he
  rw [geometricWeight_weight]
  have hd := congrArg Prod.fst (hp he)
  simpa only [fullGrading_weight] using hd

abbrev PolynomialGrade (S : Type) [CommRing S] (d : ℕ) :
    Submodule S (MvPolynomial (Fin 5) S) :=
  weightedHomogeneousSubmodule S geometricWeight d

variable {S : Type} [CommRing S] [Algebra ℂ S]

def pointEquationH (y : ParameterIndex → S) : MvPolynomial (Fin 5) S :=
  map (pointMap y) CycleQ2IncidenceBasepointOpen.familyH

def pointEquationF (y : ParameterIndex → S) : MvPolynomial (Fin 5) S :=
  map (pointMap y) CycleQ2IncidenceBasepointOpen.familyF

def pointEquations (y : ParameterIndex → S) : Ideal (MvPolynomial (Fin 5) S) :=
  equationsIdeal (pointEquationH y) (pointEquationF y)

theorem pointEquationH_homogeneous (y : ParameterIndex → S) :
    pointEquationH y ∈ PolynomialGrade S 3 := by
  rw [pointEquationH, pointMap_familyH]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 3 (pointCubic y))

theorem pointEquationF_homogeneous (y : ParameterIndex → S) :
    pointEquationF y ∈ PolynomialGrade S 6 := by
  rw [pointEquationF, pointMap_familyF]
  exact homogeneous_of_character (fullInvariantPolynomial_homogeneous 6 (pointSextic y))

theorem pointEquations_homogeneous (y : ParameterIndex → S) :
    (pointEquations y).IsHomogeneous (PolynomialGrade S) := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨3, pointEquationH_homogeneous y⟩
  · exact ⟨6, pointEquationF_homogeneous y⟩

/-- This is a grading on the existing literal `PointSurface y` quotient. -/
abbrev surfaceGrade (y : ParameterIndex → S) (d : ℕ) :
    Submodule S (PointSurface y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade S) (pointEquations y) d

instance surfaceGradedRing (y : ParameterIndex → S) : GradedRing (surfaceGrade y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (PolynomialGrade S) (pointEquations y) (pointEquations_homogeneous y)

/-- The projective scheme of the literal weighted cubic/sextic quotient. -/
def surface (y : ParameterIndex → S) : Scheme := Proj (surfaceGrade y)

def weightedAmbient (S : Type) [CommRing S] : Scheme := Proj (PolynomialGrade S)

def surfaceCoefficient (y : ParameterIndex → S) : S →+* surfaceGrade y 0 :=
  algebraMap S (surfaceGrade y 0)

@[simp] theorem surfaceCoefficient_val (y : ParameterIndex → S) (s : S) :
    (surfaceCoefficient y s : PointSurface y) = algebraMap S (PointSurface y) s := rfl

/-- An actual structure morphism to the coefficient base, obtained from
the canonical map of coefficients into degree zero. -/
def surfaceToBase (y : ParameterIndex → S) :
    surface y ⟶ Spec (CommRingCat.of S) :=
  Proj.toSpecZero (surfaceGrade y) ≫
    Spec.map (CommRingCat.ofHom (surfaceCoefficient y))

/-- The actual morphism induced by the homogeneous quotient map. -/
def surfaceToAmbient (y : ParameterIndex → S) :
    surface y ⟶ weightedAmbient S :=
  Proj.map
    (CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.quotientMap
      (PolynomialGrade S) (pointEquations y))
    (CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.irrelevant_le_map_quotientMap
      (PolynomialGrade S) (pointEquations y))

@[simp] theorem surfaceToAmbient_preimage_basicOpen
    (y : ParameterIndex → S) (p : MvPolynomial (Fin 5) S) :
    surfaceToAmbient y ⁻¹ᵁ Proj.basicOpen (PolynomialGrade S) p =
      Proj.basicOpen (surfaceGrade y) (Ideal.Quotient.mk (pointEquations y) p) :=
  Proj.map_preimage_basicOpen _ _ p

/-! ## The literal matrix and the three generic section equations -/

def pointMatrixPolynomial (y : ParameterIndex → S) (i j : Fin 3) :
    MvPolynomial (Fin 5) S :=
  incidenceMatrix (57 : S) (pointMatrix y) i j

theorem pointMatrixPolynomial_eq (y : ParameterIndex → S) (i j : Fin 3) :
    pointMatrixPolynomial y i j =
      map (pointMap y) (CycleQ2IncidenceBasepointOpen.familyMatrix i j) :=
  (congrArg (fun M => M i j) (pointMap_familyMatrix y)).symm

theorem pointMatrixPolynomial_homogeneous (y : ParameterIndex → S) (i j : Fin 3) :
    pointMatrixPolynomial y i j ∈ PolynomialGrade S 14 :=
  homogeneous_of_character (incidenceMatrix_homogeneous (57 : S) (pointMatrix y) i j)

abbrev SectionBase (S : Type) [CommRing S] := MvPolynomial (Fin 3) S

def sectionPoint (y : ParameterIndex → S) : ParameterIndex → SectionBase S :=
  fun k => C (y k)

theorem pointEquationH_sectionPoint (y : ParameterIndex → S) :
    pointEquationH (sectionPoint y) = map (C : S →+* SectionBase S) (pointEquationH y) := by
  simp only [pointEquationH, pointMap_familyH, map_fullInvariantPolynomial] <;> rfl

theorem pointEquationF_sectionPoint (y : ParameterIndex → S) :
    pointEquationF (sectionPoint y) = map (C : S →+* SectionBase S) (pointEquationF y) := by
  simp only [pointEquationF, pointMap_familyF, map_fullInvariantPolynomial] <;> rfl

theorem pointMatrixPolynomial_sectionPoint (y : ParameterIndex → S) (i j : Fin 3) :
    pointMatrixPolynomial (sectionPoint y) i j =
      map (C : S →+* SectionBase S) (pointMatrixPolynomial y i j) := by
  have h := congrArg (fun M => M i j)
    (map_incidenceMatrix (C : S →+* SectionBase S) (57 : S) (pointMatrix y))
  simpa only [pointMatrixPolynomial, RingHom.mapMatrix_apply, map_ofNat,
    pointMatrix, sectionPoint] using h.symm

/-- The `i`th entry of `M*T`.  The independent variables `Tj` belong to
the coefficient ring and therefore have geometric degree zero. -/
def genericSectionEquation (y : ParameterIndex → S) (i : Fin 3) :
    MvPolynomial (Fin 5) (SectionBase S) :=
  ∑ j : Fin 3, C (X j : SectionBase S) * pointMatrixPolynomial (sectionPoint y) i j

theorem genericSectionEquation_homogeneous (y : ParameterIndex → S) (i : Fin 3) :
    genericSectionEquation y i ∈ PolynomialGrade (SectionBase S) 14 := by
  apply (PolynomialGrade (SectionBase S) 14).sum_mem
  intro j _
  exact (pointMatrixPolynomial_homogeneous (sectionPoint y) i j).C_mul (X j)

def genericSectionIdeal (y : ParameterIndex → S) :
    Ideal (MvPolynomial (Fin 5) (SectionBase S)) :=
  Ideal.span (Set.range (genericSectionEquation y))

theorem genericSectionIdeal_homogeneous (y : ParameterIndex → S) :
    (genericSectionIdeal y).IsHomogeneous (PolynomialGrade (SectionBase S)) := by
  apply Ideal.homogeneous_span
  rintro p ⟨i, rfl⟩
  exact ⟨14, genericSectionEquation_homogeneous y i⟩

def genericCurveIdeal (y : ParameterIndex → S) :
    Ideal (MvPolynomial (Fin 5) (SectionBase S)) :=
  pointEquations (sectionPoint y) ⊔ genericSectionIdeal y

theorem genericCurveIdeal_homogeneous (y : ParameterIndex → S) :
    (genericCurveIdeal y).IsHomogeneous (PolynomialGrade (SectionBase S)) :=
  (pointEquations_homogeneous (sectionPoint y)).sup (genericSectionIdeal_homogeneous y)

abbrev GenericCurveRing (y : ParameterIndex → S) :=
  MvPolynomial (Fin 5) (SectionBase S) ⧸ genericCurveIdeal y

abbrev genericCurveGrade (y : ParameterIndex → S) (d : ℕ) :
    Submodule (SectionBase S) (GenericCurveRing y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.grade
    (PolynomialGrade (SectionBase S)) (genericCurveIdeal y) d

instance genericCurveGradedRing (y : ParameterIndex → S) :
    GradedRing (genericCurveGrade y) :=
  CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.gradedRing
    (PolynomialGrade (SectionBase S)) (genericCurveIdeal y) (genericCurveIdeal_homogeneous y)

/-- The actual candidate curve scheme cut out by `(h,F,M*T)`. -/
def genericCurve (y : ParameterIndex → S) : Scheme := Proj (genericCurveGrade y)

def genericCurveToBase (y : ParameterIndex → S) :
    genericCurve y ⟶ Spec (CommRingCat.of (SectionBase S)) :=
  Proj.toSpecZero (genericCurveGrade y) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (SectionBase S) (genericCurveGrade y 0)))

def genericCurveToAmbient (y : ParameterIndex → S) :
    genericCurve y ⟶ weightedAmbient (SectionBase S) :=
  Proj.map
    (CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.quotientMap
      (PolynomialGrade (SectionBase S)) (genericCurveIdeal y))
    (CycleQ2GeometricProjectiveCurve.HomogeneousQuotient.irrelevant_le_map_quotientMap
      (PolynomialGrade (SectionBase S)) (genericCurveIdeal y))

theorem pointEquations_le_genericCurveIdeal (y : ParameterIndex → S) :
    pointEquations (sectionPoint y) ≤ genericCurveIdeal y := le_sup_left

def genericCurveSurfaceRingMap (y : ParameterIndex → S) :
    surfaceGrade (sectionPoint y) →+*ᵍ genericCurveGrade y where
  toRingHom := Ideal.Quotient.factor (pointEquations_le_genericCurveIdeal y)
  map_mem := by
    intro d q hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact ⟨p, hp, rfl⟩

theorem irrelevant_le_map_genericCurveSurfaceRingMap (y : ParameterIndex → S) :
    HomogeneousIdeal.irrelevant (genericCurveGrade y) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade (sectionPoint y))).map
        (genericCurveSurfaceRingMap y) := by
  apply HomogeneousIdeal.toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (genericCurveGrade y)).mpr
  intro d hd q hq
  obtain ⟨p, hp, rfl⟩ := hq
  exact Ideal.mem_map_of_mem (genericCurveSurfaceRingMap y)
    (HomogeneousIdeal.mem_irrelevant_of_mem (surfaceGrade (sectionPoint y)) hd
      (show Ideal.Quotient.mk (pointEquations (sectionPoint y)) p ∈
        surfaceGrade (sectionPoint y) d from ⟨p, hp, rfl⟩))

/-- The actual scheme map from the candidate zero locus to the surface
over `S[T0,T1,T2]`.  No fiber or flatness assertion is part of this map. -/
def genericCurveToSurface (y : ParameterIndex → S) :
    genericCurve y ⟶ surface (sectionPoint y) :=
  Proj.map (genericCurveSurfaceRingMap y)
    (irrelevant_le_map_genericCurveSurfaceRingMap y)

@[simp] theorem genericCurve_equation_zero (y : ParameterIndex → S) (i : Fin 3) :
    Ideal.Quotient.mk (genericCurveIdeal y) (genericSectionEquation y i) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (le_sup_right (Ideal.subset_span (Set.mem_range_self i)))

/-! ## Binding to the existing generic-section ideal

The earlier local regularity calculation puts the three section variables
outside the surface quotient.  Swapping the two polynomial-variable sets
and then quotienting the geometric coefficients sends our literal section
equations to those exact `sectionVector` entries.  The image of the full
homogeneous ideal is the existing `sectionIdeal`, as proved below.  This
does not transfer local regularity to specialized fibers.
-/

private theorem commute_map_constants (p : MvPolynomial (Fin 5) S) :
    commAlgEquiv S (Fin 5) (Fin 3) (map (C : S →+* SectionBase S) p) =
      (C : MvPolynomial (Fin 5) S →+*
        MvPolynomial (Fin 3) (MvPolynomial (Fin 5) S)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, map_X, commAlgEquiv_X, hp]

def toSectionPolynomial (y : ParameterIndex → S) :
    MvPolynomial (Fin 5) (SectionBase S) →+*
      MvPolynomial (Fin 3) (PointSurface y) :=
  (map (CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y))).comp
    (commAlgEquiv S (Fin 5) (Fin 3)).toRingHom

@[simp] theorem toSectionPolynomial_map (y : ParameterIndex → S)
    (p : MvPolynomial (Fin 5) S) :
    toSectionPolynomial y (map (C : S →+* SectionBase S) p) =
      C (CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y) p) := by
  change map (CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y))
    (commAlgEquiv S (Fin 5) (Fin 3) (map (C : S →+* SectionBase S) p)) = _
  rw [commute_map_constants, map_C]

@[simp] theorem toSectionPolynomial_parameter (y : ParameterIndex → S) (j : Fin 3) :
    toSectionPolynomial y (C (X j : SectionBase S)) = X j := by
  change map (CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y))
    (commAlgEquiv S (Fin 5) (Fin 3) (C (X j : SectionBase S))) = _
  rw [commAlgEquiv_C_X, map_X]

@[simp] theorem toSectionPolynomial_matrix (y : ParameterIndex → S) (i j : Fin 3) :
    toSectionPolynomial y (pointMatrixPolynomial (sectionPoint y) i j) =
      C (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y) i j) := by
  rw [pointMatrixPolynomial_sectionPoint, toSectionPolynomial_map,
    pointMatrixPolynomial_eq]
  rfl

@[simp] theorem toSectionPolynomial_equation (y : ParameterIndex → S) (i : Fin 3) :
    toSectionPolynomial y (genericSectionEquation y i) =
      CycleQ2SegreGenericSection.sectionVector
        (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) i := by
  simp only [genericSectionEquation, map_sum, map_mul, toSectionPolynomial_parameter,
    toSectionPolynomial_matrix, CycleQ2SegreGenericSection.sectionVector,
    CycleQ2GenericLinearSection.linearForm]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

@[simp] theorem toSectionPolynomial_H (y : ParameterIndex → S) :
    toSectionPolynomial y (pointEquationH (sectionPoint y)) = 0 := by
  rw [pointEquationH_sectionPoint, toSectionPolynomial_map]
  have hz : CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y)
      (pointEquationH y) = 0 :=
    CycleQ2IncidenceBasepointOpen.quotient_h (pointMap y)
  rw [hz, map_zero]

@[simp] theorem toSectionPolynomial_F (y : ParameterIndex → S) :
    toSectionPolynomial y (pointEquationF (sectionPoint y)) = 0 := by
  rw [pointEquationF_sectionPoint, toSectionPolynomial_map]
  have hz : CycleQ2IncidenceBasepointOpen.curveQuotient (pointMap y)
      (pointEquationF y) = 0 :=
    CycleQ2IncidenceBasepointOpen.quotient_F (pointMap y)
  rw [hz, map_zero]

theorem toSectionPolynomial_pointEquations (y : ParameterIndex → S) :
    (pointEquations (sectionPoint y)).map (toSectionPolynomial y) = ⊥ := by
  apply le_antisymm ?_ bot_le
  rw [Ideal.map_le_iff_le_comap]
  apply Ideal.span_le.mpr
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · change toSectionPolynomial y (pointEquationH (sectionPoint y)) = 0
    exact toSectionPolynomial_H y
  · change toSectionPolynomial y (pointEquationF (sectionPoint y)) = 0
    exact toSectionPolynomial_F y

theorem toSectionPolynomial_genericSectionIdeal (y : ParameterIndex → S) :
    (genericSectionIdeal y).map (toSectionPolynomial y) =
      CycleQ2SegreGenericSection.sectionIdeal
        (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) := by
  rw [genericSectionIdeal, Ideal.map_span, CycleQ2SegreGenericSection.sectionIdeal]
  apply congrArg Ideal.span
  ext p
  constructor
  · rintro ⟨q, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (toSectionPolynomial_equation y i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨genericSectionEquation y i, Set.mem_range_self i,
      toSectionPolynomial_equation y i⟩

/-- The literal homogeneous candidate maps to the exact generic-section
ideal whose unit-pivot regularity was proved earlier in the project. -/
theorem toSectionPolynomial_genericCurveIdeal (y : ParameterIndex → S) :
    (genericCurveIdeal y).map (toSectionPolynomial y) =
      CycleQ2SegreGenericSection.sectionIdeal
        (CycleQ2IncidenceBasepointOpen.curveMatrix (pointMap y)) := by
  simp only [genericCurveIdeal, Ideal.map_sup, toSectionPolynomial_pointEquations,
    toSectionPolynomial_genericSectionIdeal, bot_sup_eq]

end CycleQ2GeometricIncidenceProj

end
