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

This source-only continuation has not been elaborated or compiled.

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

/-! ## The grading of a homogeneous quotient -/

namespace HomogeneousQuotient

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜]

/-- The degree `n` part consists of images of homogeneous elements of
degree `n`.  This definition does not yet assert the direct-sum property. -/
def grade (I : Ideal A) (n : ℕ) : Submodule R (A ⧸ I) :=
  (𝒜 n).map (Ideal.Quotient.mkₐ R I).toLinearMap

theorem mem_grade (I : Ideal A) (n : ℕ) (q : A ⧸ I) :
    q ∈ grade 𝒜 I n ↔
      ∃ p : A, p ∈ 𝒜 n ∧ Ideal.Quotient.mk I p = q := Iff.rfl

def gradeMap (I : Ideal A) (n : ℕ) :
    𝒜 n →ₗ[R] grade 𝒜 I n where
  toFun p := ⟨Ideal.Quotient.mk I p, ⟨p, p.property, rfl⟩⟩
  map_add' p q := Subtype.ext (map_add (Ideal.Quotient.mk I) (p : A) (q : A))
  map_smul' c p := Subtype.ext ((Ideal.Quotient.mkₐ R I).toLinearMap.map_smul c (p : A))

instance grade_gradedMonoid (I : Ideal A) :
    SetLike.GradedMonoid (grade 𝒜 I) where
  one_mem := ⟨1, SetLike.one_mem_graded 𝒜, map_one (Ideal.Quotient.mk I)⟩
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨p, hp, rfl⟩ := ha
    obtain ⟨q, hq, rfl⟩ := hb
    exact ⟨p * q, SetLike.mul_mem_graded hp hq, map_mul (Ideal.Quotient.mk I) p q⟩

/-- Decompose an element and then pass every homogeneous component to
the quotient. -/
def toQuotientGrades (I : Ideal A) :
    A →ₗ[R] (⨁ n : ℕ, grade 𝒜 I n) :=
  (DirectSum.lmap (gradeMap 𝒜 I)).comp
    (DirectSum.decomposeLinearEquiv 𝒜).toLinearMap

theorem toQuotientGrades_vanishes (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) :
    I.restrictScalars R ≤ LinearMap.ker (toQuotientGrades 𝒜 I) := by
  intro p hp
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  change Ideal.Quotient.mk I (DirectSum.decompose 𝒜 p n) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hI n hp)

/-- Homogeneity of the ideal makes componentwise decomposition descend
to the actual ring quotient. -/
def decompose (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) :
    (A ⧸ I) →ₗ[R] (⨁ n : ℕ, grade 𝒜 I n) := by
  let f : A →ₗ[R] (⨁ n : ℕ, grade 𝒜 I n) := toQuotientGrades 𝒜 I
  have hf : I.restrictScalars R ≤ LinearMap.ker f :=
    toQuotientGrades_vanishes 𝒜 I hI
  exact ((I.restrictScalars R).liftQ f hf).comp
    (Submodule.Quotient.restrictScalarsEquiv R I).symm.toLinearMap

@[simp] theorem decompose_mk (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) (p : A) :
    decompose 𝒜 I hI (Ideal.Quotient.mk I p) =
      toQuotientGrades 𝒜 I p := rfl

theorem coeLinearMap_gradeMap (I : Ideal A) :
    (DirectSum.coeLinearMap (grade 𝒜 I)).comp
        (DirectSum.lmap (gradeMap 𝒜 I)) =
      (Ideal.Quotient.mkₐ R I).toLinearMap.comp
        (DirectSum.coeLinearMap 𝒜) := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, DirectSum.lmap_lof,
    DirectSum.coeLinearMap_lof] <;> rfl

theorem decompose_leftInverse (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) :
    (DirectSum.coeLinearMap (grade 𝒜 I)).comp (decompose 𝒜 I hI) =
      LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  rw [LinearMap.comp_apply, decompose_mk]
  change ((DirectSum.coeLinearMap (grade 𝒜 I)).comp
    (DirectSum.lmap (gradeMap 𝒜 I)))
      (DirectSum.decomposeLinearEquiv 𝒜 p) = Ideal.Quotient.mk I p
  rw [coeLinearMap_gradeMap, LinearMap.comp_apply]
  change Ideal.Quotient.mk I
    ((DirectSum.decomposeLinearEquiv 𝒜).symm
      (DirectSum.decomposeLinearEquiv 𝒜 p)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem decompose_rightInverse (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) :
    (decompose 𝒜 I hI).comp (DirectSum.coeLinearMap (grade 𝒜 I)) =
      LinearMap.id := by
  apply DirectSum.linearMap_ext
  intro n
  apply LinearMap.ext
  intro q
  obtain ⟨p, hp, hpq⟩ := q.property
  have hq : gradeMap 𝒜 I n ⟨p, hp⟩ = q := Subtype.ext hpq
  rw [← hq]
  simp only [LinearMap.comp_apply, DirectSum.coeLinearMap_lof, LinearMap.id_apply]
  change decompose 𝒜 I hI (Ideal.Quotient.mk I p) = _
  rw [decompose_mk]
  change DirectSum.lmap (gradeMap 𝒜 I)
      (DirectSum.decomposeLinearEquiv 𝒜 p) = _
  rw [DirectSum.decomposeLinearEquiv_apply_coe 𝒜 n ⟨p, hp⟩,
    DirectSum.lmap_lof]

/-- A homogeneous ideal gives a genuine internal grading of its quotient.
Both decomposition inverses have been proved above. -/
def gradedRing (I : Ideal A)
    (hI : I.IsHomogeneous 𝒜) : GradedRing (grade 𝒜 I) where
  toGradedMonoid := grade_gradedMonoid 𝒜 I
  toDecomposition := DirectSum.Decomposition.ofLinearMap _ (decompose 𝒜 I hI)
    (decompose_leftInverse 𝒜 I hI) (decompose_rightInverse 𝒜 I hI)

end HomogeneousQuotient

abbrev PolynomialGrade (n : ℕ) : Submodule ℂ Poly :=
  homogeneousSubmodule (Fin 4) ℂ n

abbrev quotientGrade (I : Ideal Poly) (n : ℕ) : Submodule ℂ (Poly ⧸ I) :=
  HomogeneousQuotient.grade PolynomialGrade I n

abbrev quotientGradedRing (I : Ideal Poly)
    (hI : I.IsHomogeneous PolynomialGrade) : GradedRing (quotientGrade I) :=
  HomogeneousQuotient.gradedRing PolynomialGrade I hI

/-! ## The actual sparse projective curve -/

theorem curveIdeal_homogeneous (r θ : ℂ) :
    (curveIdeal r θ).IsHomogeneous PolynomialGrade := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨2, CycleQ2SeedCech.curveF1_homogeneous r⟩
  · exact ⟨3, CycleQ2SeedCechTheta.curveH_homogeneous θ⟩

abbrev curveGrade (r θ : ℂ) (n : ℕ) : Submodule ℂ (CurveRing r θ) :=
  quotientGrade (curveIdeal r θ) n

instance curveGradedRing (r θ : ℂ) : GradedRing (curveGrade r θ) :=
  quotientGradedRing (curveIdeal r θ) (curveIdeal_homogeneous r θ)

theorem curveMap_mem_grade (r θ : ℂ) {n : ℕ} {p : Poly}
    (hp : p.IsHomogeneous n) : curveMap r θ p ∈ curveGrade r θ n :=
  ⟨p, hp, rfl⟩

theorem coordinate_mem_grade (r θ : ℂ) (j : Fin 4) :
    curveMap r θ (X j) ∈ curveGrade r θ 1 :=
  curveMap_mem_grade r θ (isHomogeneous_X ℂ j)

theorem curveG1_mem_grade (r θ : ℂ) : curveG1 r θ ∈ curveGrade r θ 4 := by
  change ambientCurveMap r θ (originalG1 r) ∈ _
  rw [ambientCurveMap_g1]
  apply curveMap_mem_grade
  exact ((isHomogeneous_X ℂ (1 : Fin 4)).mul
    (isHomogeneous_X ℂ (3 : Fin 4))).pow 2 |>.C_mul (3 * r ^ 2)

theorem curveG2_mem_grade (r θ : ℂ) : curveG2 r θ ∈ curveGrade r θ 4 := by
  change ambientCurveMap r θ originalG2 ∈ _
  rw [ambientCurveMap_g2]
  apply curveMap_mem_grade
  exact ((isHomogeneous_X ℂ (2 : Fin 4)).pow 4).C_mul 3

theorem curveG12_mem_grade (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ ∈ curveGrade r θ 8 :=
  SetLike.mul_mem_graded (curveG1_mem_grade r θ) (curveG2_mem_grade r θ)

/-- The actual scheme `Proj (ℂ[x0,x1,x2,x3]/(f1,hθ))`. -/
def projectiveCurve (r θ : ℂ) : Scheme := Proj (curveGrade r θ)

def coordinateProjectivePatch (r θ : ℂ) (j : Fin 4) :
    (projectiveCurve r θ).Opens :=
  Proj.basicOpen (curveGrade r θ) (curveMap r θ (X j))

def firstProjectivePatch (r θ : ℂ) : (projectiveCurve r θ).Opens :=
  Proj.basicOpen (curveGrade r θ) (curveG1 r θ)

def secondProjectivePatch (r θ : ℂ) : (projectiveCurve r θ).Opens :=
  Proj.basicOpen (curveGrade r θ) (curveG2 r θ)

def overlapProjectivePatch (r θ : ℂ) : (projectiveCurve r θ).Opens :=
  Proj.basicOpen (curveGrade r θ) (curveG1 r θ * curveG2 r θ)

theorem overlapProjectivePatch_eq (r θ : ℂ) :
    overlapProjectivePatch r θ =
      firstProjectivePatch r θ ⊓ secondProjectivePatch r θ :=
  Proj.basicOpen_mul _ _ _

theorem irrelevant_le_coordinateIdeal (r θ : ℂ) :
    (HomogeneousIdeal.irrelevant (curveGrade r θ)).toIdeal ≤
      Ideal.span (Set.range (fun j : Fin 4 => curveMap r θ (X j))) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn q hq
  obtain ⟨p, hp, rfl⟩ := hq
  have hpI : p ∈ MvPolynomial.idealOfVars (Fin 4) ℂ := by
    have hpow : p ∈ MvPolynomial.idealOfVars (Fin 4) ℂ ^ 1 := by
      apply (MvPolynomial.mem_pow_idealOfVars_iff' 1 p).mpr
      intro d hd
      exact hp.coeff_eq_zero (by omega)
    simpa only [pow_one] using hpow
  have hmap : MvPolynomial.idealOfVars (Fin 4) ℂ ≤
      (Ideal.span (Set.range (fun j : Fin 4 => curveMap r θ (X j)))).comap
        (curveMap r θ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact Ideal.subset_span ⟨j, rfl⟩
  exact hmap hpI

theorem coordinateProjectivePatches_cover (r θ : ℂ) :
    (⨆ j : Fin 4, coordinateProjectivePatch r θ j) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (curveGrade r θ) _ (irrelevant_le_coordinateIdeal r θ)

/-- The two specific denominator opens really cover the projective curve
when `r ≠ 0`; this is not cover data supplied as a hypothesis. -/
theorem projective_twoOpen_cover (r θ : ℂ) (hr : r ≠ 0) :
    firstProjectivePatch r θ ⊔ secondProjectivePatch r θ = ⊤ := by
  apply top_le_iff.mp
  intro q hq
  have hcoordinates : q ∈ ⨆ j : Fin 4, coordinateProjectivePatch r θ j := by
    rw [coordinateProjectivePatches_cover]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcoordinates
  exact CycleQ2SeedTwoOpenCover.relevant_prime_cover r θ hr
    q.asHomogeneousIdeal.toIdeal ⟨j, hj⟩

/-! ## Canonical affine charts, with their actual structure sheaves -/

abbrev FirstProjectiveRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (curveGrade r θ) (curveG1 r θ)

abbrev SecondProjectiveRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (curveGrade r θ) (curveG2 r θ)

abbrev OverlapProjectiveRing (r θ : ℂ) :=
  HomogeneousLocalization.Away (curveGrade r θ) (curveG1 r θ * curveG2 r θ)

def firstProjectiveChart (r θ : ℂ) :
    (firstProjectivePatch r θ).toScheme ≅
      Spec (CommRingCat.of (FirstProjectiveRing r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveG1 r θ)
    (curveG1_mem_grade r θ) (by decide)

def secondProjectiveChart (r θ : ℂ) :
    (secondProjectivePatch r θ).toScheme ≅
      Spec (CommRingCat.of (SecondProjectiveRing r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveG2 r θ)
    (curveG2_mem_grade r θ) (by decide)

def overlapProjectiveChart (r θ : ℂ) :
    (overlapProjectivePatch r θ).toScheme ≅
      Spec (CommRingCat.of (OverlapProjectiveRing r θ)) :=
  Proj.basicOpenIsoSpec (curveGrade r θ) (curveG1 r θ * curveG2 r θ)
    (curveG12_mem_grade r θ) (by decide)

def firstProjectiveSectionsIso (r θ : ℂ) :
    CommRingCat.of (FirstProjectiveRing r θ) ≅
      Γ(projectiveCurve r θ, firstProjectivePatch r θ) :=
  Proj.basicOpenIsoAway (curveGrade r θ) (curveG1 r θ)
    (curveG1_mem_grade r θ) (by decide)

def secondProjectiveSectionsIso (r θ : ℂ) :
    CommRingCat.of (SecondProjectiveRing r θ) ≅
      Γ(projectiveCurve r θ, secondProjectivePatch r θ) :=
  Proj.basicOpenIsoAway (curveGrade r θ) (curveG2 r θ)
    (curveG2_mem_grade r θ) (by decide)

def overlapProjectiveSectionsIso (r θ : ℂ) :
    CommRingCat.of (OverlapProjectiveRing r θ) ≅
      Γ(projectiveCurve r θ, overlapProjectivePatch r θ) :=
  Proj.basicOpenIsoAway (curveGrade r θ) (curveG1 r θ * curveG2 r θ)
    (curveG12_mem_grade r θ) (by decide)

/-! ## The genuine degree-one local modules -/

/-- A literal fraction in the ordinary localization; its degree is a
separate property, not an identification imposed on the localization. -/
def awayFraction (r θ : ℂ) (f : CurveRing r θ) (n : ℕ) (a : CurveRing r θ) :
    Localization.Away f :=
  Localization.mk a ⟨f ^ n, n, rfl⟩

theorem awayFraction_add (r θ : ℂ) (f : CurveRing r θ)
    (n m : ℕ) (a b : CurveRing r θ) :
    awayFraction r θ f n a + awayFraction r θ f m b =
      awayFraction r θ f (n + m) (a * f ^ m + b * f ^ n) := by
  simp only [awayFraction, Localization.add_mk, pow_add]
  congr 1
  ring

theorem awayFraction_mul (r θ : ℂ) (f : CurveRing r θ)
    (n m : ℕ) (a b : CurveRing r θ) :
    awayFraction r θ f n a * awayFraction r θ f m b =
      awayFraction r θ f (n + m) (a * b) := by
  simp only [awayFraction, Localization.mk_mul, pow_add] <;> rfl

/-- The degree-one part of `A[f⁻¹]`, as an actual module over `(A[f⁻¹])₀`.
Every element has a homogeneous numerator of degree `1 + n*d`; closure is
proved by clearing denominators. -/
def degreeOneModule (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) :
    Submodule (HomogeneousLocalization.Away (curveGrade r θ) f)
      (Localization.Away f) where
  carrier := {z | ∃ n a, a ∈ curveGrade r θ (1 + n * d) ∧
    awayFraction r θ f n a = z}
  zero_mem' := ⟨0, 0, (curveGrade r θ _).zero_mem, Localization.mk_zero _⟩
  add_mem' := by
    rintro _ _ ⟨n, a, ha, rfl⟩ ⟨m, b, hb, rfl⟩
    refine ⟨n + m, a * f ^ m + b * f ^ n, ?_,
      (awayFraction_add r θ f n m a b).symm⟩
    apply (curveGrade r θ _).add_mem
    · simpa only [nsmul_eq_mul, Nat.add_mul, Nat.add_assoc] using
        SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hf)
    · simpa only [nsmul_eq_mul, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded hb (SetLike.pow_mem_graded n hf)
  smul_mem' := by
    rintro c _ ⟨n, a, ha, rfl⟩
    obtain ⟨m, b, hb, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (curveGrade r θ) hf c
    refine ⟨m + n, b * a, ?_, ?_⟩
    · simpa only [nsmul_eq_mul, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using SetLike.mul_mem_graded hb ha
    · change awayFraction r θ f (m + n) (b * a) =
        (HomogeneousLocalization.Away.mk (curveGrade r θ) hf m b hb).val *
          awayFraction r θ f n a
      exact (awayFraction_mul r θ f m n b a).symm

theorem awayFraction_mem_degreeOne (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (n : ℕ) (a : CurveRing r θ)
    (ha : a ∈ curveGrade r θ (1 + n * d)) :
    awayFraction r θ f n a ∈ degreeOneModule r θ f d hf :=
  ⟨n, a, ha, rfl⟩

/-- The usual localization restriction from `f` to a homogeneous product.
The equality parameter also handles the second restriction with reversed
factors. -/
def awayRestriction (r θ : ℂ) (f g x : CurveRing r θ) (hx : x = f * g) :
    Localization.Away f →+* Localization.Away x :=
  Localization.awayLift (algebraMap (CurveRing r θ) (Localization.Away x)) f
    (isUnit_of_dvd_unit (map_dvd _ ⟨g, hx⟩)
      (IsLocalization.Away.algebraMap_isUnit x))

@[simp] theorem awayRestriction_base (r θ : ℂ)
    (f g x : CurveRing r θ) (hx : x = f * g) (a : CurveRing r θ) :
    awayRestriction r θ f g x hx (algebraMap _ (Localization.Away f) a) =
      algebraMap _ (Localization.Away x) a :=
  IsLocalization.Away.lift_eq _ _ _

theorem awayRestriction_fraction (r θ : ℂ)
    (f g x : CurveRing r θ) (hx : x = f * g) (n : ℕ) (a : CurveRing r θ) :
    awayRestriction r θ f g x hx (awayFraction r θ f n a) =
      awayFraction r θ x n (a * g ^ n) := by
  have hu : algebraMap (CurveRing r θ) (Localization.Away x) f *
      Localization.mk g ⟨x, 1, pow_one x⟩ = 1 := by
    rw [← Algebra.smul_def, Localization.smul_mk, ← hx]
    exact Localization.mk_self ⟨x, 1, pow_one x⟩
  rw [awayRestriction, awayFraction, Localization.awayLift_mk (hv := hu),
    ← Algebra.smul_def, Localization.mk_pow, Localization.smul_mk] <;> rfl

theorem awayRestriction_val (r θ : ℂ) (f g x : CurveRing r θ)
    {e : ℕ} (hg : g ∈ curveGrade r θ e) (hx : x = f * g)
    (a : HomogeneousLocalization.Away (curveGrade r θ) f) :
    (HomogeneousLocalization.awayMap (curveGrade r θ) hg hx a).val =
      awayRestriction r θ f g x hx a.val :=
  HomogeneousLocalization.val_awayMap _ _ _ _

theorem awayRestriction_degreeOne (r θ : ℂ) (f g x : CurveRing r θ)
    (d e : ℕ) (hf : f ∈ curveGrade r θ d) (hg : g ∈ curveGrade r θ e)
    (hx : x = f * g) {z : Localization.Away f}
    (hz : z ∈ degreeOneModule r θ f d hf) :
    awayRestriction r θ f g x hx z ∈
      degreeOneModule r θ x (d + e) (hx ▸ SetLike.mul_mem_graded hf hg) := by
  obtain ⟨n, a, ha, rfl⟩ := hz
  refine ⟨n, a * g ^ n, ?_, (awayRestriction_fraction r θ f g x hx n a).symm⟩
  simpa only [nsmul_eq_mul, Nat.mul_add, Nat.add_assoc] using
    SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n hg)

/-- These are the actual module restrictions over the homogeneous affine
coordinate-ring maps. -/
def degreeOneRestriction (r θ : ℂ) (f g x : CurveRing r θ)
    (d e : ℕ) (hf : f ∈ curveGrade r θ d) (hg : g ∈ curveGrade r θ e)
    (hx : x = f * g) :
    degreeOneModule r θ f d hf →ₛₗ[HomogeneousLocalization.awayMap (curveGrade r θ) hg hx]
      degreeOneModule r θ x (d + e) (hx ▸ SetLike.mul_mem_graded hf hg) where
  toFun z := ⟨awayRestriction r θ f g x hx z,
    awayRestriction_degreeOne r θ f g x d e hf hg hx z.property⟩
  map_add' z w := Subtype.ext (map_add (awayRestriction r θ f g x hx) z w)
  map_smul' c z := by
    apply Subtype.ext
    change awayRestriction r θ f g x hx (c.val * (z : Localization.Away f)) =
      (HomogeneousLocalization.awayMap (curveGrade r θ) hg hx c).val * _
    rw [map_mul, awayRestriction_val]

abbrev FirstDegreeOne (r θ : ℂ) :=
  degreeOneModule r θ (curveG1 r θ) 4 (curveG1_mem_grade r θ)

abbrev SecondDegreeOne (r θ : ℂ) :=
  degreeOneModule r θ (curveG2 r θ) 4 (curveG2_mem_grade r θ)

abbrev OverlapDegreeOne (r θ : ℂ) :=
  degreeOneModule r θ (curveG1 r θ * curveG2 r θ) 8 (curveG12_mem_grade r θ)

def firstDegreeOneRestriction (r θ : ℂ) :
    FirstDegreeOne r θ →+ OverlapDegreeOne r θ :=
  (degreeOneRestriction r θ (curveG1 r θ) (curveG2 r θ)
    (curveG1 r θ * curveG2 r θ) 4 4
    (curveG1_mem_grade r θ) (curveG2_mem_grade r θ) rfl).toAddMonoidHom

def secondDegreeOneRestriction (r θ : ℂ) :
    SecondDegreeOne r θ →+ OverlapDegreeOne r θ :=
  (degreeOneRestriction r θ (curveG2 r θ) (curveG1 r θ)
    (curveG1 r θ * curveG2 r θ) 4 4
    (curveG2_mem_grade r θ) (curveG1_mem_grade r θ) (mul_comm _ _)).toAddMonoidHom

@[simp] theorem firstDegreeOneRestriction_coe (r θ : ℂ) (z : FirstDegreeOne r θ) :
    (firstDegreeOneRestriction r θ z : Overlap r θ) =
      firstRestriction r θ z := by
  have hmap : awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
        (curveG1 r θ * curveG2 r θ) rfl = firstRestriction r θ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (curveG1 r θ))
    ext a
    exact (awayRestriction_base r θ _ _ _ rfl a).trans
      (IsLocalization.Away.awayToAwayRight_eq _ _ _).symm
  exact RingHom.congr_fun hmap z

@[simp] theorem secondDegreeOneRestriction_coe (r θ : ℂ) (z : SecondDegreeOne r θ) :
    (secondDegreeOneRestriction r θ z : Overlap r θ) =
      secondRestriction r θ z := by
  have hmap : awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
        (curveG1 r θ * curveG2 r θ) (mul_comm _ _) = secondRestriction r θ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (curveG2 r θ))
    ext a
    exact (awayRestriction_base r θ _ _ _ (mul_comm _ _) a).trans
      (IsLocalization.Away.awayToAwayLeft_eq _ _ _).symm
  exact RingHom.congr_fun hmap z

/-! ## The degree-one Cech class and its literal cone image -/

def degreeOneCoboundary (r θ : ℂ) :
    FirstDegreeOne r θ × SecondDegreeOne r θ →+ OverlapDegreeOne r θ :=
  (firstDegreeOneRestriction r θ).comp (AddMonoidHom.fst _ _) -
    (secondDegreeOneRestriction r θ).comp (AddMonoidHom.snd _ _)

def degreeOneBoundaries (r θ : ℂ) : AddSubgroup (OverlapDegreeOne r θ) :=
  (degreeOneCoboundary r θ).range

/-- The degree-one quotient of the actual graded affine-chart modules.
This is not declared to be derived projective sheaf cohomology. -/
abbrev DegreeOneCech (r θ : ℂ) :=
  OverlapDegreeOne r θ ⧸ degreeOneBoundaries r θ

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

/-- A homogeneous degree-nine numerator divided by the two degree-four
denominators is a genuine degree-one local section. -/
def degreeNineRepresentative (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 9) :
    OverlapDegreeOne r θ :=
  ⟨awayFraction r θ (curveG1 r θ * curveG2 r θ) 1 (curveMap r θ p),
    awayFraction_mem_degreeOne r θ _ 8 (curveG12_mem_grade r θ) 1 _
      (curveMap_mem_grade r θ hp)⟩

def degreeNineCechClass (r θ : ℂ) (p : Poly) (hp : p.IsHomogeneous 9) :
    DegreeOneCech r θ :=
  QuotientAddGroup.mk (degreeNineRepresentative r θ p hp)

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

/-! ## Local frames and the actual invertible transition section -/

def degreeOneFrame (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) : degreeOneModule r θ f d hf :=
  ⟨algebraMap (CurveRing r θ) (Localization.Away f) x,
    ⟨0, x, hx, Localization.mk_one_eq_algebraMap x⟩⟩

def degreeOneFrameMap (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) :
    HomogeneousLocalization.Away (curveGrade r θ) f →ₗ[
        HomogeneousLocalization.Away (curveGrade r θ) f] degreeOneModule r θ f d hf :=
  LinearMap.toSpanSingleton _ _ (degreeOneFrame r θ f d hf x hx)

@[simp] theorem degreeOneFrameMap_coe (r θ : ℂ) (f : CurveRing r θ) (d : ℕ)
    (hf : f ∈ curveGrade r θ d) (x : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1)
    (a : HomogeneousLocalization.Away (curveGrade r θ) f) :
    (degreeOneFrameMap r θ f d hf x hx a : Localization.Away f) =
      a.val * algebraMap (CurveRing r θ) (Localization.Away f) x := rfl

theorem frameCoordinate_isUnit (r θ : ℂ) (f x g : CurveRing r θ)
    (hfg : f = x * g) :
    IsUnit (algebraMap (CurveRing r θ) (Localization.Away f) x) :=
  isUnit_of_dvd_unit (map_dvd _ ⟨g, hfg⟩)
    (IsLocalization.Away.algebraMap_isUnit f)

/-- If a degree-one coordinate divides the inverted homogeneous function,
multiplication by that coordinate trivializes the degree-one local module. -/
def degreeOneFrameEquiv (r θ : ℂ) (f : CurveRing r θ) (e : ℕ)
    (hf : f ∈ curveGrade r θ (1 + e)) (x g : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) (hg : g ∈ curveGrade r θ e)
    (hfg : f = x * g) :
    HomogeneousLocalization.Away (curveGrade r θ) f ≃ₗ[
        HomogeneousLocalization.Away (curveGrade r θ) f]
      degreeOneModule r θ f (1 + e) hf :=
  LinearEquiv.ofBijective (degreeOneFrameMap r θ f (1 + e) hf x hx) (by
    constructor
    · intro a b hab
      apply HomogeneousLocalization.val_injective
      apply (frameCoordinate_isUnit r θ f x g hfg).mul_right_cancel
      exact congrArg (fun z : degreeOneModule r θ f (1 + e) hf =>
        (z : Localization.Away f)) hab
    · intro z
      obtain ⟨n, a, ha, haz⟩ := z.property
      have hag : a * g ∈ curveGrade r θ ((n + 1) • (1 + e)) := by
        convert SetLike.mul_mem_graded ha hg using 1
        simp only [nsmul_eq_mul, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
        omega
      refine ⟨HomogeneousLocalization.Away.mk (curveGrade r θ) hf (n + 1) (a * g) hag, ?_⟩
      apply Subtype.ext
      rw [degreeOneFrameMap_coe, HomogeneousLocalization.Away.val_mk, ← haz,
        ← Localization.mk_one_eq_algebraMap, Localization.mk_mul, awayFraction,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [Submonoid.coe_one, Submonoid.coe_mul, Subtype.coe_mk, one_mul, mul_one]
      rw [pow_succ, hfg]
      ring)

@[simp] theorem degreeOneFrameEquiv_coe (r θ : ℂ) (f : CurveRing r θ) (e : ℕ)
    (hf : f ∈ curveGrade r θ (1 + e)) (x g : CurveRing r θ)
    (hx : x ∈ curveGrade r θ 1) (hg : g ∈ curveGrade r θ e)
    (hfg : f = x * g) (a : HomogeneousLocalization.Away (curveGrade r θ) f) :
    (degreeOneFrameEquiv r θ f e hf x g hx hg hfg a : Localization.Away f) =
      a.val * algebraMap (CurveRing r θ) (Localization.Away f) x := rfl

def firstFrameComplement (r θ : ℂ) : CurveRing r θ :=
  curveMap r θ (C (3 * r ^ 2) * X 1 * X 3 ^ 2)

def secondFrameComplement (r θ : ℂ) : CurveRing r θ :=
  curveMap r θ (C 3 * X 2 ^ 3)

theorem firstFrameComplement_grade (r θ : ℂ) :
    firstFrameComplement r θ ∈ curveGrade r θ 3 := by
  apply curveMap_mem_grade
  simpa only [mul_assoc] using
    (((isHomogeneous_X ℂ (1 : Fin 4)).mul
      ((isHomogeneous_X ℂ (3 : Fin 4)).pow 2)).C_mul (3 * r ^ 2))

theorem secondFrameComplement_grade (r θ : ℂ) :
    secondFrameComplement r θ ∈ curveGrade r θ 3 :=
  curveMap_mem_grade r θ (((isHomogeneous_X ℂ (2 : Fin 4)).pow 3).C_mul 3)

theorem firstFrame_factorization (r θ : ℂ) :
    curveG1 r θ = curveMap r θ (X 1) * firstFrameComplement r θ := by
  change ambientCurveMap r θ (originalG1 r) = _
  rw [ambientCurveMap_g1]
  change curveMap r θ (C (3 * r ^ 2) * CycleQ2SeedCech.curveA ^ 2) =
    curveMap r θ (X 1) * curveMap r θ (C (3 * r ^ 2) * X 1 * X 3 ^ 2)
  rw [← map_mul]
  congr 1
  dsimp [CycleQ2SeedCech.curveA]
  ring

theorem secondFrame_factorization (r θ : ℂ) :
    curveG2 r θ = curveMap r θ (X 2) * secondFrameComplement r θ := by
  change ambientCurveMap r θ originalG2 = _
  rw [ambientCurveMap_g2]
  change curveMap r θ (C 3 * X 2 ^ 4) =
    curveMap r θ (X 2) * curveMap r θ (C 3 * X 2 ^ 3)
  rw [← map_mul]
  congr 1
  ring

def firstDegreeOneEquiv (r θ : ℂ) :
    FirstProjectiveRing r θ ≃ₗ[FirstProjectiveRing r θ] FirstDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ) 3 (curveG1_mem_grade r θ)
    (curveMap r θ (X 1)) (firstFrameComplement r θ)
    (coordinate_mem_grade r θ 1) (firstFrameComplement_grade r θ)
    (firstFrame_factorization r θ)

def secondDegreeOneEquiv (r θ : ℂ) :
    SecondProjectiveRing r θ ≃ₗ[SecondProjectiveRing r θ] SecondDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG2 r θ) 3 (curveG2_mem_grade r θ)
    (curveMap r θ (X 2)) (secondFrameComplement r θ)
    (coordinate_mem_grade r θ 2) (secondFrameComplement_grade r θ)
    (secondFrame_factorization r θ)

theorem overlapFirstFrame_factorization (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ = curveMap r θ (X 1) *
      (firstFrameComplement r θ * curveG2 r θ) := by
  rw [firstFrame_factorization, mul_assoc]

theorem overlapSecondFrame_factorization (r θ : ℂ) :
    curveG1 r θ * curveG2 r θ = curveMap r θ (X 2) *
      (curveG1 r θ * secondFrameComplement r θ) := by
  rw [secondFrame_factorization]
  ring

def overlapFirstDegreeOneEquiv (r θ : ℂ) :
    OverlapProjectiveRing r θ ≃ₗ[OverlapProjectiveRing r θ] OverlapDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ * curveG2 r θ) 7 (curveG12_mem_grade r θ)
    (curveMap r θ (X 1)) (firstFrameComplement r θ * curveG2 r θ)
    (coordinate_mem_grade r θ 1)
    (SetLike.mul_mem_graded (firstFrameComplement_grade r θ) (curveG2_mem_grade r θ))
    (overlapFirstFrame_factorization r θ)

def overlapSecondDegreeOneEquiv (r θ : ℂ) :
    OverlapProjectiveRing r θ ≃ₗ[OverlapProjectiveRing r θ] OverlapDegreeOne r θ :=
  degreeOneFrameEquiv r θ (curveG1 r θ * curveG2 r θ) 7 (curveG12_mem_grade r θ)
    (curveMap r θ (X 2)) (curveG1 r θ * secondFrameComplement r θ)
    (coordinate_mem_grade r θ 2)
    (SetLike.mul_mem_graded (curveG1_mem_grade r θ) (secondFrameComplement_grade r θ))
    (overlapSecondFrame_factorization r θ)

/-- In the first frame, the second frame is the genuine ratio `x2/x1`. -/
def overlapTransition (r θ : ℂ) : OverlapProjectiveRing r θ :=
  (overlapFirstDegreeOneEquiv r θ).symm (overlapSecondDegreeOneEquiv r θ 1)

def overlapReverseTransition (r θ : ℂ) : OverlapProjectiveRing r θ :=
  (overlapSecondDegreeOneEquiv r θ).symm (overlapFirstDegreeOneEquiv r θ 1)

theorem overlapTransition_coordinate (r θ : ℂ) :
    (overlapTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2)) := by
  have hh := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    ((overlapFirstDegreeOneEquiv r θ).apply_symm_apply
      (overlapSecondDegreeOneEquiv r θ 1))
  change (overlapTransition r θ).val * _ = (1 : OverlapProjectiveRing r θ).val * _ at hh
  simpa only [HomogeneousLocalization.val_one, one_mul] using hh

theorem overlapReverseTransition_coordinate (r θ : ℂ) :
    (overlapReverseTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2)) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) := by
  have hh := congrArg (fun z : OverlapDegreeOne r θ => (z : Overlap r θ))
    ((overlapSecondDegreeOneEquiv r θ).apply_symm_apply
      (overlapFirstDegreeOneEquiv r θ 1))
  change (overlapReverseTransition r θ).val * _ = (1 : OverlapProjectiveRing r θ).val * _ at hh
  simpa only [HomogeneousLocalization.val_one, one_mul] using hh

theorem overlapTransition_mul_reverse (r θ : ℂ) :
    overlapTransition r θ * overlapReverseTransition r θ = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  apply (frameCoordinate_isUnit r θ _ _ _ (overlapSecondFrame_factorization r θ)).mul_right_cancel
  rw [mul_assoc, overlapReverseTransition_coordinate, overlapTransition_coordinate, one_mul]

def overlapTransitionUnit (r θ : ℂ) : (OverlapProjectiveRing r θ)ˣ where
  val := overlapTransition r θ
  inv := overlapReverseTransition r θ
  val_inv := overlapTransition_mul_reverse r θ
  inv_val := (mul_comm _ _).trans (overlapTransition_mul_reverse r θ)

/-- The transition is an invertible section of the actual projective
structure sheaf on the overlap of the two actual affine opens. -/
def projectiveTransitionUnit (r θ : ℂ) :
    Γ(projectiveCurve r θ, overlapProjectivePatch r θ)ˣ :=
  Units.map (overlapProjectiveSectionsIso r θ).hom.hom.toMonoidHom
    (overlapTransitionUnit r θ)

def firstProjectiveRestriction (r θ : ℂ) :
    FirstProjectiveRing r θ →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ) (curveG2_mem_grade r θ) rfl

def secondProjectiveRestriction (r θ : ℂ) :
    SecondProjectiveRing r θ →+* OverlapProjectiveRing r θ :=
  HomogeneousLocalization.awayMap (curveGrade r θ) (curveG1_mem_grade r θ) (mul_comm _ _)

theorem firstProjectiveRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : FirstProjectiveRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (Proj.basicOpen_mono (curveGrade r θ) (curveG1 r θ)
          (curveG1 r θ * curveG2 r θ) ⟨_, rfl⟩)).op
          ((firstProjectiveSectionsIso r θ).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (firstProjectiveRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ) (curveG2_mem_grade r θ) rfl).symm

theorem secondProjectiveRestriction_is_sheaf_restriction (r θ : ℂ)
    (a : SecondProjectiveRing r θ) :
    (projectiveCurve r θ).presheaf.map
        (homOfLE (Proj.basicOpen_mono (curveGrade r θ) (curveG2 r θ)
          (curveG1 r θ * curveG2 r θ) ⟨_, mul_comm _ _⟩)).op
          ((secondProjectiveSectionsIso r θ).hom a) =
      (overlapProjectiveSectionsIso r θ).hom (secondProjectiveRestriction r θ a) := by
  exact congrArg (fun k => k a)
    (Proj.awayMap_awayToSection (curveGrade r θ)
      (curveG1_mem_grade r θ) (mul_comm _ _)).symm

theorem firstDegreeOneEquiv_restriction (r θ : ℂ) (a : FirstProjectiveRing r θ) :
    firstDegreeOneRestriction r θ (firstDegreeOneEquiv r θ a) =
      overlapFirstDegreeOneEquiv r θ (firstProjectiveRestriction r θ a) := by
  apply Subtype.ext
  rw [firstDegreeOneRestriction_coe]
  change awayRestriction r θ (curveG1 r θ) (curveG2 r θ) _ rfl
      (a.val * algebraMap _ (FirstOpen r θ) (curveMap r θ (X 1))) =
    (HomogeneousLocalization.awayMap (curveGrade r θ) (curveG2_mem_grade r θ) rfl a).val * _
  rw [map_mul, awayRestriction_base, awayRestriction_val]

theorem secondDegreeOneEquiv_restriction (r θ : ℂ) (a : SecondProjectiveRing r θ) :
    secondDegreeOneRestriction r θ (secondDegreeOneEquiv r θ a) =
      overlapSecondDegreeOneEquiv r θ (secondProjectiveRestriction r θ a) := by
  apply Subtype.ext
  rw [secondDegreeOneRestriction_coe]
  change awayRestriction r θ (curveG2 r θ) (curveG1 r θ) _ (mul_comm _ _)
      (a.val * algebraMap _ (SecondOpen r θ) (curveMap r θ (X 2))) =
    (HomogeneousLocalization.awayMap (curveGrade r θ)
      (curveG1_mem_grade r θ) (mul_comm _ _) a).val * _
  rw [map_mul, awayRestriction_base, awayRestriction_val]

theorem overlapTransition_frame (r θ : ℂ) (b : OverlapProjectiveRing r θ) :
    overlapFirstDegreeOneEquiv r θ (overlapTransition r θ * b) =
      overlapSecondDegreeOneEquiv r θ b := by
  apply Subtype.ext
  change (overlapTransition r θ * b).val *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
    b.val * algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 2))
  rw [HomogeneousLocalization.val_mul]
  calc
    (overlapTransition r θ).val * b.val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1)) =
      b.val * ((overlapTransition r θ).val *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (X 1))) := by ring
    _ = _ := by rw [overlapTransition_coordinate]

/-- In the actual projective affine frames, the homogeneous degree-one
coboundary is `a|₁₂ - (x2/x1)b|₁₂`, with the literal structure-sheaf
restrictions identified above. -/
theorem degreeOneCoboundary_in_frames (r θ : ℂ)
    (a : FirstProjectiveRing r θ) (b : SecondProjectiveRing r θ) :
    degreeOneCoboundary r θ (firstDegreeOneEquiv r θ a, secondDegreeOneEquiv r θ b) =
      overlapFirstDegreeOneEquiv r θ
        (firstProjectiveRestriction r θ a -
          overlapTransition r θ * secondProjectiveRestriction r θ b) := by
  change firstDegreeOneRestriction r θ (firstDegreeOneEquiv r θ a) -
    secondDegreeOneRestriction r θ (secondDegreeOneEquiv r θ b) = _
  rw [firstDegreeOneEquiv_restriction, secondDegreeOneEquiv_restriction,
    map_sub, overlapTransition_frame]

/-! ## The actual additive sheaf glued by the transition unit

The kernel below is taken in the category of sheaves on the actual
projective space. Its sections will be identified with compatible pairs.
No module-sheaf, canonical-bundle, or Serre-trace identification is
asserted by this additive construction.
-/

namespace Twisted

variable {X : TopCat.{0}}

/-- Intersecting every test open with a fixed open, with strict objects. -/
def intersectFunctor (U : Opens X) : Opens X ⥤ Opens X where
  obj O := O ⊓ U
  map f := homOfLE (inf_le_inf_right U (leOfHom f))

def intersectFunctorIso (U : Opens X) :
    Opens.map U.inclusion' ⋙ U.isOpenEmbedding.functor ≅ intersectFunctor U :=
  NatIso.ofComponents
    (fun O => eqToIso (TopologicalSpace.Opens.functor_map_eq_inf U O))
    (fun _ _ _ => Subsingleton.elim _ _)

variable (R : X.Sheaf CommRingCat.{0})

/-- The genuine restriction followed by direct image, presented with
sections over O equal to sections of R over O intersect U. -/
def patchRing (U : Opens X) : X.Sheaf CommRingCat.{0} := by
  let F := (TopCat.Sheaf.pushforward CommRingCat U.inclusion').obj
    ((U.sheafRestrict).obj R)
  have e : F.obj ≅ (intersectFunctor U).op ⋙ R.obj :=
    Functor.isoWhiskerRight (NatIso.op (intersectFunctorIso U).symm) R.obj
  exact ⟨(intersectFunctor U).op ⋙ R.obj,
    (CategoryTheory.Presheaf.isSheaf_of_iso_iff e).mp F.property⟩

def patchAdd (U : Opens X) : X.Sheaf AddCommGrpCat.{0} :=
  (sheafCompose _ (forget₂ CommRingCat AddCommGrpCat)).obj (patchRing R U)

def res {U V : Opens X} (h : V ≤ U) :
    R.obj.obj (op U) →+* R.obj.obj (op V) :=
  (R.obj.map (homOfLE h).op).hom

@[simp] theorem res_self (U : Opens X) (a : R.obj.obj (op U)) :
    res R (le_refl U) a = a := by
  change (R.obj.map (𝟙 (op U))) a = a
  simp

theorem res_comp {U V W : Opens X} (hVU : V ≤ U) (hWV : W ≤ V)
    (a : R.obj.obj (op U)) :
    res R hWV (res R hVU a) = res R (hWV.trans hVU) a := by
  change (R.obj.map (homOfLE hVU).op ≫ R.obj.map (homOfLE hWV).op) a =
    (R.obj.map (homOfLE (hWV.trans hVU)).op) a
  rw [← R.obj.map_comp] <;>
    exact congrArg (fun k : op U ⟶ op W => R.obj.map k a) (Subsingleton.elim _ _)

def resEquiv {U V : Opens X} (hVU : V ≤ U) (hUV : U ≤ V) :
    R.obj.obj (op U) ≃+* R.obj.obj (op V) where
  toFun := res R hVU
  invFun := res R hUV
  left_inv a := by rw [res_comp]; exact res_self R U a
  right_inv a := by rw [res_comp]; exact res_self R V a
  map_add' := map_add (res R hVU)
  map_mul' := map_mul (res R hVU)

def patchRestriction {U V : Opens X} (h : V ≤ U) :
    patchRing R U ⟶ patchRing R V where
  hom :=
    { app := fun O => R.obj.map (homOfLE (inf_le_inf_left O.unop h)).op
      naturality := by
        intro O P f
        change R.obj.map _ ≫ R.obj.map _ = R.obj.map _ ≫ R.obj.map _
        rw [← R.obj.map_comp, ← R.obj.map_comp] <;>
          congr 1 <;> apply Subsingleton.elim }

def patchAddRestriction {U V : Opens X} (h : V ≤ U) :
    patchAdd R U ⟶ patchAdd R V :=
  (sheafCompose _ (forget₂ CommRingCat AddCommGrpCat)).map (patchRestriction R h)

/-- Multiplication uses the restriction of one actual overlap section. -/
def patchMul (W : Opens X) (t : R.obj.obj (op W)) :
    patchAdd R W ⟶ patchAdd R W where
  hom :=
    { app := fun O => AddCommGrpCat.ofHom
        (AddMonoidHom.mulLeft (res R (show O.unop ⊓ W ≤ W from inf_le_right) t))
      naturality := by
        intro O P f
        apply AddCommGrpCat.ext
        intro a
        change res R (show P.unop ⊓ W ≤ W from inf_le_right) t *
            res R (inf_le_inf_right W (leOfHom f.unop)) a =
          res R (inf_le_inf_right W (leOfHom f.unop))
            (res R (show O.unop ⊓ W ≤ W from inf_le_right) t * a)
        rw [map_mul, res_comp] }

variable (U V W : Opens X) (hW : W = U ⊓ V)
  (t : (R.obj.obj (op W))ˣ)

def difference : patchAdd R U ⊞ patchAdd R V ⟶ patchAdd R W :=
  biprod.desc (patchAddRestriction R (hW.le.trans inf_le_left))
    (-(patchAddRestriction R (hW.le.trans inf_le_right) ≫ patchMul R W (t : _)))

/-- An actual sheaf kernel, with gluing equation a = t*b on the overlap. -/
def sheaf : X.Sheaf AddCommGrpCat.{0} :=
  kernel (difference R U V W hW t)

def firstProjection : sheaf R U V W hW t ⟶ patchAdd R U :=
  kernel.ι (difference R U V W hW t) ≫ biprod.fst

def secondProjection : sheaf R U V W hW t ⟶ patchAdd R V :=
  kernel.ι (difference R U V W hW t) ≫ biprod.snd

theorem projections_compatible :
    firstProjection R U V W hW t ≫
        patchAddRestriction R (hW.le.trans inf_le_left) =
      secondProjection R U V W hW t ≫
        patchAddRestriction R (hW.le.trans inf_le_right) ≫ patchMul R W (t : _) := by
  apply sub_eq_zero.mp
  simpa only [firstProjection, secondProjection, difference, biprod.desc_eq,
    Preadditive.comp_add, Preadditive.comp_neg, Category.assoc, sub_eq_add_neg]
    using kernel.condition (difference R U V W hW t)

def pairDifference (O : Opens X) :
    R.obj.obj (op (O ⊓ U)) × R.obj.obj (op (O ⊓ V)) →+
      R.obj.obj (op (O ⊓ W)) :=
  (res R (inf_le_inf_left O (hW.le.trans inf_le_left))).toAddMonoidHom.comp
      (AddMonoidHom.fst _ _) -
    (AddMonoidHom.mulLeft (res R (show O ⊓ W ≤ W from inf_le_right) (t : _))).comp
      ((res R (inf_le_inf_left O (hW.le.trans inf_le_right))).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))

abbrev Pairs (O : Opens X) :=
  (pairDifference R U V W hW t O).ker

theorem section_pair_mem (O : Opens X) (s : (sheaf R U V W hW t).obj.obj (op O)) :
    ((firstProjection R U V W hW t).hom.app (op O) s,
      (secondProjection R U V W hW t).hom.app (op O) s) ∈
        Pairs R U V W hW t O := by
  have hs := congrArg
    (fun k : sheaf R U V W hW t ⟶ patchAdd R W => k.hom.app (op O) s)
    (projections_compatible R U V W hW t)
  change res R (inf_le_inf_left O (hW.le.trans inf_le_left))
      ((firstProjection R U V W hW t).hom.app (op O) s) =
    res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
      res R (inf_le_inf_left O (hW.le.trans inf_le_right))
        ((secondProjection R U V W hW t).hom.app (op O) s) at hs
  exact sub_eq_zero.mpr hs

def sectionPairMap (O : Opens X) :
    (sheaf R U V W hW t).obj.obj (op O) →+ Pairs R U V W hW t O :=
  (((firstProjection R U V W hW t).hom.app (op O)).hom.prod
    ((secondProjection R U V W hW t).hom.app (op O)).hom).codRestrict _
      (section_pair_mem R U V W hW t O)

/-! Evaluation of the actual kernel uses the free sheaf representing
sections. This makes the comparison independent of chosen categorical
models for kernels and biproducts. -/

def sectionsHomEquiv (F : X.Sheaf AddCommGrpCat.{0}) (O : Opens X) :
    ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (yoneda.obj O ⋙ AddCommGrpCat.free) ⟶ F) ≃+ F.obj.obj (op O) :=
  ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homAddEquiv
    (yoneda.obj O ⋙ AddCommGrpCat.free) F).trans
      (CycleQ2GeometricConeCech.HZero.freeYonedaSections F.obj O)

theorem sectionsHomEquiv_comp {F G : X.Sheaf AddCommGrpCat.{0}} (O : Opens X)
    (a : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
      (yoneda.obj O ⋙ AddCommGrpCat.free) ⟶ F) (f : F ⟶ G) :
    sectionsHomEquiv G O (a ≫ f) =
      f.hom.app (op O) (sectionsHomEquiv F O a) := by
  change CycleQ2GeometricConeCech.HZero.freeYonedaSections G.obj O
    ((sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).homEquiv
      _ _ (a ≫ f)) = _
  rw [(sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat).
    homEquiv_naturality_right] <;> rfl

theorem sectionPairMap_injective (O : Opens X) :
    Function.Injective (sectionPairMap R U V W hW t O) := by
  intro s s' h
  apply (sectionsHomEquiv (sheaf R U V W hW t) O).symm.injective
  apply (cancel_mono (kernel.ι (difference R U V W hW t))).mp
  apply biprod.hom_ext
  · apply (sectionsHomEquiv (patchAdd R U) O).injective
    simpa only [Category.assoc, sectionsHomEquiv_comp, AddEquiv.apply_symm_apply]
      using congrArg (fun p : Pairs R U V W hW t O => p.val.1) h
  · apply (sectionsHomEquiv (patchAdd R V) O).injective
    simpa only [Category.assoc, sectionsHomEquiv_comp, AddEquiv.apply_symm_apply]
      using congrArg (fun p : Pairs R U V W hW t O => p.val.2) h

theorem sectionPairMap_surjective (O : Opens X) :
    Function.Surjective (sectionPairMap R U V W hW t O) := by
  intro p
  let a := (sectionsHomEquiv (patchAdd R U) O).symm p.val.1
  let b := (sectionsHomEquiv (patchAdd R V) O).symm p.val.2
  have hab : biprod.lift a b ≫ difference R U V W hW t = 0 := by
    apply (sectionsHomEquiv (patchAdd R W) O).injective
    have hc : sectionsHomEquiv (patchAdd R W) O
        (biprod.lift a b ≫ difference R U V W hW t) =
          pairDifference R U V W hW t O p.val := by
      simp only [difference, biprod.lift_desc, Preadditive.comp_neg, map_add, map_neg,
        sectionsHomEquiv_comp, a, b, AddEquiv.apply_symm_apply]
      change _ + -_ = _ - _
      rw [sub_eq_add_neg]
    rw [hc, map_zero]
    exact p.property
  refine ⟨sectionsHomEquiv (sheaf R U V W hW t) O
    (kernel.lift (difference R U V W hW t) (biprod.lift a b) hab), ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · change (firstProjection R U V W hW t).hom.app (op O)
      (sectionsHomEquiv _ O (kernel.lift _ _ hab)) = p.val.1
    rw [← sectionsHomEquiv_comp, firstProjection, ← Category.assoc,
      kernel.lift_ι, biprod.lift_fst]
    exact (sectionsHomEquiv (patchAdd R U) O).apply_symm_apply p.val.1
  · change (secondProjection R U V W hW t).hom.app (op O)
      (sectionsHomEquiv _ O (kernel.lift _ _ hab)) = p.val.2
    rw [← sectionsHomEquiv_comp, secondProjection, ← Category.assoc,
      kernel.lift_ι, biprod.lift_snd]
    exact (sectionsHomEquiv (patchAdd R V) O).apply_symm_apply p.val.2

/-- Actual sections of the sheaf kernel are exactly the compatible pairs
of actual structure-sheaf sections, with no comparison premise. -/
def sectionPairsEquiv (O : Opens X) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ Pairs R U V W hW t O :=
  AddEquiv.ofBijective (sectionPairMap R U V W hW t O)
    ⟨sectionPairMap_injective R U V W hW t O,
      sectionPairMap_surjective R U V W hW t O⟩

theorem sectionPairs_fst_naturality {O P : Opens X} (h : P ≤ O)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t P
      ((sheaf R U V W hW t).obj.map (homOfLE h).op s)).val.1 =
      res R (inf_le_inf_right U h) (sectionPairsEquiv R U V W hW t O s).val.1 := by
  have hh := congrArg (fun k => k s)
    ((firstProjection R U V W hW t).hom.naturality (homOfLE h).op)
  exact hh

theorem sectionPairs_snd_naturality {O P : Opens X} (h : P ≤ O)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    (sectionPairsEquiv R U V W hW t P
      ((sheaf R U V W hW t).obj.map (homOfLE h).op s)).val.2 =
      res R (inf_le_inf_right V h) (sectionPairsEquiv R U V W hW t O s).val.2 := by
  have hh := congrArg (fun k => k s)
    ((secondProjection R U V W hW t).hom.naturality (homOfLE h).op)
  exact hh

/-! ## Actual sections in each local frame -/

def unitMulEquiv {A : Type} [CommRing A] (u : Aˣ) : A ≃+ A where
  toFun a := (u : A) * a
  invFun a := (↑(u⁻¹) : A) * a
  left_inv a := by rw [← mul_assoc, u.inv_mul, one_mul]
  right_inv a := by rw [← mul_assoc, u.mul_inv, one_mul]
  map_add' := mul_add (u : A)

def pairFirstEquiv (O : Opens X) (hO : O ≤ U) :
    Pairs R U V W hW t O ≃+ R.obj.obj (op (O ⊓ U)) := by
  let e : R.obj.obj (op (O ⊓ V)) ≃+ R.obj.obj (op (O ⊓ W)) :=
    (resEquiv R (inf_le_inf_left O (hW.le.trans inf_le_right)) (by
      rw [hW, ← inf_assoc, inf_eq_left.mpr hO] <;> exact le_rfl)).toAddEquiv.trans
        (unitMulEquiv (Units.map
          (res R (show O ⊓ W ≤ W from inf_le_right)).toMonoidHom t))
  let f := res R (inf_le_inf_left O (hW.le.trans inf_le_left))
  exact
    { toFun := fun p => p.val.1
      invFun := fun a => ⟨(a, e.symm (f a)), by
        change f a - e (e.symm (f a)) = 0
        rw [AddEquiv.apply_symm_apply, sub_self]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext rfl
        apply e.injective
        rw [AddEquiv.apply_symm_apply]
        exact sub_eq_zero.mp p.property
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

def pairSecondEquiv (O : Opens X) (hO : O ≤ V) :
    Pairs R U V W hW t O ≃+ R.obj.obj (op (O ⊓ V)) := by
  let e : R.obj.obj (op (O ⊓ U)) ≃+ R.obj.obj (op (O ⊓ W)) :=
    (resEquiv R (inf_le_inf_left O (hW.le.trans inf_le_left)) (by
      rw [hW]
      exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hO)))).toAddEquiv
  let g : R.obj.obj (op (O ⊓ V)) → R.obj.obj (op (O ⊓ W)) := fun b =>
    res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
      res R (inf_le_inf_left O (hW.le.trans inf_le_right)) b
  exact
    { toFun := fun p => p.val.2
      invFun := fun b => ⟨(e.symm (g b), b), by
        change e (e.symm (g b)) - g b = 0
        rw [AddEquiv.apply_symm_apply, sub_self]⟩
      left_inv := by
        intro p
        apply Subtype.ext
        apply Prod.ext _ rfl
        apply e.injective
        rw [AddEquiv.apply_symm_apply]
        exact (sub_eq_zero.mp p.property).symm
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }

/-- On every open contained in the first chart, the actual sheaf kernel
is additively identified with the actual structure-sheaf sections. -/
def firstLocalSectionsEquiv (O : Opens X) (hO : O ≤ U) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ R.obj.obj (op O) :=
  (sectionPairsEquiv R U V W hW t O).trans
    ((pairFirstEquiv R U V W hW t O hO).trans
      (resEquiv R (le_inf le_rfl hO) inf_le_left).toAddEquiv)

def secondLocalSectionsEquiv (O : Opens X) (hO : O ≤ V) :
    (sheaf R U V W hW t).obj.obj (op O) ≃+ R.obj.obj (op O) :=
  (sectionPairsEquiv R U V W hW t O).trans
    ((pairSecondEquiv R U V W hW t O hO).trans
      (resEquiv R (le_inf le_rfl hO) inf_le_left).toAddEquiv)

theorem firstLocalSectionsEquiv_apply (O : Opens X) (hO : O ≤ U)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t O hO s =
      res R (le_inf le_rfl hO) (sectionPairsEquiv R U V W hW t O s).val.1 := rfl

theorem secondLocalSectionsEquiv_apply (O : Opens X) (hO : O ≤ V)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsEquiv R U V W hW t O hO s =
      res R (le_inf le_rfl hO) (sectionPairsEquiv R U V W hW t O s).val.2 := rfl

theorem firstLocalSectionsEquiv_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ U)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (firstLocalSectionsEquiv R U V W hW t O hO s) := by
  simp only [firstLocalSectionsEquiv_apply, sectionPairs_fst_naturality, res_comp]

theorem secondLocalSectionsEquiv_naturality {O P : Opens X} (h : P ≤ O) (hO : O ≤ V)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    secondLocalSectionsEquiv R U V W hW t P (h.trans hO)
        ((sheaf R U V W hW t).obj.map (homOfLE h).op s) =
      res R h (secondLocalSectionsEquiv R U V W hW t O hO s) := by
  simp only [secondLocalSectionsEquiv_apply, sectionPairs_snd_naturality, res_comp]

/-- The two actual section coordinates have the prescribed transition on
every open contained in the overlap. -/
theorem localSections_transition (O : Opens X) (hO : O ≤ W)
    (s : (sheaf R U V W hW t).obj.obj (op O)) :
    firstLocalSectionsEquiv R U V W hW t O (hO.trans (hW.le.trans inf_le_left)) s =
      res R hO (t : _) *
        secondLocalSectionsEquiv R U V W hW t O
          (hO.trans (hW.le.trans inf_le_right)) s := by
  let p := sectionPairsEquiv R U V W hW t O s
  have hp : res R (inf_le_inf_left O (hW.le.trans inf_le_left)) p.val.1 =
      res R (show O ⊓ W ≤ W from inf_le_right) (t : _) *
        res R (inf_le_inf_left O (hW.le.trans inf_le_right)) p.val.2 :=
    sub_eq_zero.mp p.property
  have hh := congrArg (res R (show O ≤ O ⊓ W from le_inf le_rfl hO)) hp
  simpa only [firstLocalSectionsEquiv_apply, secondLocalSectionsEquiv_apply,
    map_mul, res_comp] using hh

end Twisted

/-! ## The degree-one modules are actual sections of the glued sheaf -/

def degreeOneSheaf (r θ : ℂ) :
    (projectiveCurve r θ).Sheaf AddCommGrpCat.{0} :=
  Twisted.sheaf (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)

def firstSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, firstProjectivePatch r θ) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (firstProjectivePatch r θ) le_rfl

def secondSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, secondProjectivePatch r θ) :=
  Twisted.secondLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (secondProjectivePatch r θ) le_rfl

def overlapSheafFrame (r θ : ℂ) :
    (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) ≃+
      Γ(projectiveCurve r θ, overlapProjectivePatch r θ) :=
  Twisted.firstLocalSectionsEquiv (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)

def firstDegreeOneSectionsEquiv (r θ : ℂ) :
    FirstDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ)) :=
  (firstDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((firstProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (firstSheafFrame r θ).symm)

def secondDegreeOneSectionsEquiv (r θ : ℂ) :
    SecondDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ)) :=
  (secondDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((secondProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (secondSheafFrame r θ).symm)

def overlapDegreeOneSectionsEquiv (r θ : ℂ) :
    OverlapDegreeOne r θ ≃+
      (degreeOneSheaf r θ).obj.obj (op (overlapProjectivePatch r θ)) :=
  (overlapFirstDegreeOneEquiv r θ).symm.toAddEquiv.trans
    ((overlapProjectiveSectionsIso r θ).commRingCatIsoToRingEquiv.toAddEquiv.trans
      (overlapSheafFrame r θ).symm)

@[simp] theorem firstDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : FirstDegreeOne r θ) :
    firstSheafFrame r θ (firstDegreeOneSectionsEquiv r θ z) =
      (firstProjectiveSectionsIso r θ).hom ((firstDegreeOneEquiv r θ).symm z) :=
  (firstSheafFrame r θ).apply_symm_apply _

@[simp] theorem secondDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : SecondDegreeOne r θ) :
    secondSheafFrame r θ (secondDegreeOneSectionsEquiv r θ z) =
      (secondProjectiveSectionsIso r θ).hom ((secondDegreeOneEquiv r θ).symm z) :=
  (secondSheafFrame r θ).apply_symm_apply _

@[simp] theorem overlapDegreeOneSectionsEquiv_coordinate (r θ : ℂ) (z : OverlapDegreeOne r θ) :
    overlapSheafFrame r θ (overlapDegreeOneSectionsEquiv r θ z) =
      (overlapProjectiveSectionsIso r θ).hom ((overlapFirstDegreeOneEquiv r θ).symm z) :=
  (overlapSheafFrame r θ).apply_symm_apply _

theorem firstSheafFrame_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ))) :
    overlapSheafFrame r θ
        ((degreeOneSheaf r θ).obj.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op s) =
      (projectiveCurve r θ).presheaf.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
          (firstSheafFrame r θ s) :=
  Twisted.firstLocalSectionsEquiv_naturality (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    ((overlapProjectivePatch_eq r θ).le.trans inf_le_left) le_rfl s

theorem secondSheafFrame_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ))) :
    overlapSheafFrame r θ
        ((degreeOneSheaf r θ).obj.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s) =
      (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) *
        (projectiveCurve r θ).presheaf.map
          (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op
            (secondSheafFrame r θ s) := by
  have h := Twisted.localSections_transition (projectiveCurve r θ).sheaf
    (firstProjectivePatch r θ) (secondProjectivePatch r θ) (overlapProjectivePatch r θ)
    (overlapProjectivePatch_eq r θ) (projectiveTransitionUnit r θ)
    (overlapProjectivePatch r θ) le_rfl
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s)
  rw [Twisted.secondLocalSectionsEquiv_naturality] at h
  simpa only [Twisted.res_self] using h

theorem firstDegreeOneSectionsEquiv_restriction (r θ : ℂ) (z : FirstDegreeOne r θ) :
    (degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op
          (firstDegreeOneSectionsEquiv r θ z) =
      overlapDegreeOneSectionsEquiv r θ (firstDegreeOneRestriction r θ z) := by
  obtain ⟨a, rfl⟩ := (firstDegreeOneEquiv r θ).surjective z
  apply (overlapSheafFrame r θ).injective
  rw [firstSheafFrame_restriction, firstDegreeOneSectionsEquiv_coordinate,
    overlapDegreeOneSectionsEquiv_coordinate, firstDegreeOneEquiv_restriction]
  simpa only [LinearEquiv.symm_apply_apply] using
    firstProjectiveRestriction_is_sheaf_restriction r θ a

theorem secondDegreeOneSectionsEquiv_restriction (r θ : ℂ) (z : SecondDegreeOne r θ) :
    (degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op
          (secondDegreeOneSectionsEquiv r θ z) =
      overlapDegreeOneSectionsEquiv r θ (secondDegreeOneRestriction r θ z) := by
  obtain ⟨b, rfl⟩ := (secondDegreeOneEquiv r θ).surjective z
  apply (overlapSheafFrame r θ).injective
  rw [secondSheafFrame_restriction, secondDegreeOneSectionsEquiv_coordinate,
    overlapDegreeOneSectionsEquiv_coordinate, secondDegreeOneEquiv_restriction,
    ← overlapTransition_frame]
  simpa only [LinearEquiv.symm_apply_apply, map_mul] using
    congrArg
      (fun a : Γ(projectiveCurve r θ, overlapProjectivePatch r θ) =>
        (projectiveTransitionUnit r θ : Γ(projectiveCurve r θ, overlapProjectivePatch r θ)) * a)
      (secondProjectiveRestriction_is_sheaf_restriction r θ b)

theorem firstDegreeOneSectionsEquiv_symm_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (firstProjectivePatch r θ))) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)).op s) =
      firstDegreeOneRestriction r θ ((firstDegreeOneSectionsEquiv r θ).symm s) := by
  obtain ⟨z, rfl⟩ := (firstDegreeOneSectionsEquiv r θ).surjective s
  rw [firstDegreeOneSectionsEquiv_restriction, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

theorem secondDegreeOneSectionsEquiv_symm_restriction (r θ : ℂ)
    (s : (degreeOneSheaf r θ).obj.obj (op (secondProjectivePatch r θ))) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      ((degreeOneSheaf r θ).obj.map
        (homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)).op s) =
      secondDegreeOneRestriction r θ ((secondDegreeOneSectionsEquiv r θ).symm s) := by
  obtain ⟨z, rfl⟩ := (secondDegreeOneSectionsEquiv r θ).surjective s
  rw [secondDegreeOneSectionsEquiv_restriction, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

/-! ## Actual derived projective sheaf cohomology

Mayer-Vietoris exactness gives an injection from the degree-one Cech
quotient. It does not require affine acyclicity, and no surjectivity onto
derived cohomology is claimed.
-/

def projectiveMayerVietoris (r θ : ℂ) (hr : r ≠ 0) :
    (Opens.grothendieckTopology (projectiveCurve r θ)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := overlapProjectivePatch r θ
      X₂ := firstProjectivePatch r θ
      X₃ := secondProjectivePatch r θ
      X₄ := ⊤
      f₁₂ := homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_left)
      f₁₃ := homOfLE ((overlapProjectivePatch_eq r θ).le.trans inf_le_right)
      f₂₄ := homOfLE le_top
      f₃₄ := homOfLE le_top
      fac := Subsingleton.elim _ _ }
    (projective_twoOpen_cover r θ hr).symm (overlapProjectivePatch_eq r θ)

local instance projectiveSheavesHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveCurve r θ))
      AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Derived cohomology of the constructed additive sheaf on the actual
projective scheme. The sheaf has the proved degree-one affine frames. -/
abbrev ProjectiveSheafH1 (r θ : ℂ) :=
  (degreeOneSheaf r θ).H' 1 ⊤

open CycleQ2GeometricConeCech.HZero

def degreeOneConnecting (r θ : ℂ) (hr : r ≠ 0) :
    OverlapDegreeOne r θ →+ ProjectiveSheafH1 r θ :=
  ((projectiveMayerVietoris r θ hr).δ (degreeOneSheaf r θ) 0 1 rfl).hom.comp
    ((sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)).symm.toAddMonoidHom.comp
      (overlapDegreeOneSectionsEquiv r θ).toAddMonoidHom)

private theorem fromBiprod_degreeOne (r θ : ℂ) (hr : r ≠ 0)
    (a : (degreeOneSheaf r θ).H' 0 (firstProjectivePatch r θ))
    (b : (degreeOneSheaf r θ).H' 0 (secondProjectivePatch r θ)) :
    (overlapDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv (degreeOneSheaf r θ) (overlapProjectivePatch r θ)
        ((projectiveMayerVietoris r θ hr).fromBiprod (degreeOneSheaf r θ) 0
          ((AddCommGrpCat.biprodIsoProd _ _).inv (a, b)))) =
      degreeOneCoboundary r θ
        ((firstDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv (degreeOneSheaf r θ) (firstProjectivePatch r θ) a),
        (secondDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv (degreeOneSheaf r θ) (secondProjectivePatch r θ) b)) := by
  rw [GrothendieckTopology.MayerVietorisSquare.fromBiprod_biprodIsoProd_inv_apply,
    map_sub, sectionsEquiv_naturality, sectionsEquiv_naturality, map_sub,
    firstDegreeOneSectionsEquiv_symm_restriction,
    secondDegreeOneSectionsEquiv_symm_restriction] <;> rfl

theorem degreeOneConnecting_coboundary (r θ : ℂ) (hr : r ≠ 0)
    (x : FirstDegreeOne r θ) (y : SecondDegreeOne r θ) :
    degreeOneConnecting r θ hr (degreeOneCoboundary r θ (x, y)) = 0 := by
  let F := degreeOneSheaf r θ
  let S := projectiveMayerVietoris r θ hr
  let a := (sectionsEquiv F (firstProjectivePatch r θ)).symm
    (firstDegreeOneSectionsEquiv r θ x)
  let b := (sectionsEquiv F (secondProjectivePatch r θ)).symm
    (secondDegreeOneSectionsEquiv r θ y)
  let z := (AddCommGrpCat.biprodIsoProd _ _).inv (a, b)
  have hz : (sectionsEquiv F (overlapProjectivePatch r θ)).symm
      (overlapDegreeOneSectionsEquiv r θ (degreeOneCoboundary r θ (x, y))) =
        S.fromBiprod F 0 z := by
    apply (sectionsEquiv F (overlapProjectivePatch r θ)).injective
    apply (overlapDegreeOneSectionsEquiv r θ).symm.injective
    rw [AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply, fromBiprod_degreeOne]
    simp only [a, b, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply]
  change S.δ F 0 1 rfl
    ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
      (overlapDegreeOneSectionsEquiv r θ (degreeOneCoboundary r θ (x, y)))) = 0
  rw [hz]
  have h := congrArg
    (fun f : (F.H' 0 (firstProjectivePatch r θ) ⊞ F.H' 0 (secondProjectivePatch r θ)) ⟶
      ProjectiveSheafH1 r θ => f z) (S.fromBiprod_δ F 0 1 rfl)
  exact h

/-- The exact kernel is the actual image of the two homogeneous chart
restrictions. No extra boundary or vanishing assumption is introduced. -/
theorem degreeOneConnecting_ker (r θ : ℂ) (hr : r ≠ 0) :
    (degreeOneConnecting r θ hr).ker = degreeOneBoundaries r θ := by
  ext z
  constructor
  · intro hz
    let F := degreeOneSheaf r θ
    let S := projectiveMayerVietoris r θ hr
    have hz' : S.δ F 0 1 rfl
        ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z)) = 0 := hz
    obtain ⟨w, hw⟩ := (ShortComplex.ab_exact_iff _).mp
      ((S.sequence_exact F 0 1 rfl).exact 1)
        ((sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z)) hz'
    have hw' : S.fromBiprod F 0 w =
        (sectionsEquiv F (overlapProjectivePatch r θ)).symm
          (overlapDegreeOneSectionsEquiv r θ z) := hw
    obtain ⟨⟨a, b⟩, rfl⟩ :=
      (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective w
    refine ⟨((firstDegreeOneSectionsEquiv r θ).symm
      (sectionsEquiv F (firstProjectivePatch r θ) a),
      (secondDegreeOneSectionsEquiv r θ).symm
        (sectionsEquiv F (secondProjectivePatch r θ) b)), ?_⟩
    have hh := congrArg
      (fun v : F.H' 0 (overlapProjectivePatch r θ) =>
        (overlapDegreeOneSectionsEquiv r θ).symm
          (sectionsEquiv F (overlapProjectivePatch r θ) v)) hw'
    rw [fromBiprod_degreeOne, AddEquiv.apply_symm_apply, AddEquiv.symm_apply_apply] at hh
    exact hh
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact degreeOneConnecting_coboundary r θ hr x y

/-- A proved injection from the concrete homogeneous Cech quotient into
actual derived cohomology of the constructed projective additive sheaf. -/
def degreeOneToProjectiveH1 (r θ : ℂ) (hr : r ≠ 0) :
    DegreeOneCech r θ →+ ProjectiveSheafH1 r θ :=
  QuotientAddGroup.lift (degreeOneBoundaries r θ) (degreeOneConnecting r θ hr)
    (degreeOneConnecting_ker r θ hr).symm.le

theorem degreeOneToProjectiveH1_injective (r θ : ℂ) (hr : r ≠ 0) :
    Function.Injective (degreeOneToProjectiveH1 r θ hr) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2
    (degreeOneConnecting_ker r θ hr).symm

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
