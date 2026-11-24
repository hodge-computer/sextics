import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.LinearAlgebra.Quotient.Basic
import Proposal.GeometricCurveCoordinates

/-!
# Existing degree-one Cech objects on the sparse projective curve

The homogeneous localization modules and degree-nine Cech numerator classes
are moved from `GeometricProjectiveCurve` with their existing namespaces.
Their coordinate rings, fraction formulas, and quotient-class definitions
are unchanged. The restriction maps retain the same pointwise functions;
their additive wrappers, the quotient-grading construction, and supporting
proofs are repaired for the pinned Lean toolchain. The larger projective-scheme
and additive-sheaf constructions import this module and use these same objects.

This algebraic core can be checked independently of the earlier aggregate
files. The elementary homogeneity proofs now use the literal curve equations
so they do not require unrelated constructions from those aggregates.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

noncomputable section

namespace CycleQ2GeometricProjectiveCurve

open scoped DirectSum
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta

attribute [local instance] MvPolynomial.gradedAlgebra

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
  refine
    { QuotientAddGroup.lift I.toAddSubgroup f.toAddMonoidHom
        (fun p hp => hf hp) with
      map_smul' := ?_ }
  intro c q
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact f.map_smul c p

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

theorem relation_zero_homogeneous (r : ℂ) :
    (relation r 0).IsHomogeneous 2 := by
  simpa only [relation, Matrix.cons_val_zero, mul_assoc] using
    (isHomogeneous_X_pow (0 : Fin 4) 2).sub
      (((isHomogeneous_X ℂ (1 : Fin 4)).mul
        (isHomogeneous_X ℂ (3 : Fin 4))).C_mul r)

theorem sparse_curveH_homogeneous (θ : ℂ) :
    (curveH θ).IsHomogeneous 3 := by
  have hb : b.IsHomogeneous 3 :=
    ((((isHomogeneous_X_pow (3 : Fin 4) 3).add
      (isHomogeneous_X_pow (2 : Fin 4) 3)).add
      (((isHomogeneous_X ℂ (1 : Fin 4)).mul (isHomogeneous_X ℂ (2 : Fin 4))).mul
        (isHomogeneous_X ℂ (3 : Fin 4)))).add
      (((isHomogeneous_X ℂ (0 : Fin 4)).mul (isHomogeneous_X ℂ (2 : Fin 4))).mul
        (isHomogeneous_X ℂ (3 : Fin 4)))).add
      ((isHomogeneous_X ℂ (0 : Fin 4)).mul (isHomogeneous_X_pow (1 : Fin 4) 2))
  have hh : h.IsHomogeneous 3 :=
    hb.sub (((isHomogeneous_X_pow (1 : Fin 4) 3).add
      (isHomogeneous_X_pow (3 : Fin 4) 3)).C_mul Complex.I)
  exact hh.add ((isHomogeneous_X_pow (0 : Fin 4) 3).C_mul θ)

theorem curveIdeal_homogeneous (r θ : ℂ) :
    (curveIdeal r θ).IsHomogeneous PolynomialGrade := by
  apply Ideal.homogeneous_span
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨2, relation_zero_homogeneous r⟩
  · exact ⟨3, sparse_curveH_homogeneous θ⟩

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
    · simpa only [nsmul_eq_mul, Nat.cast_id, Nat.add_mul, Nat.add_assoc] using
        SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hf)
    · simpa only [nsmul_eq_mul, Nat.cast_id, Nat.add_mul, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using
        SetLike.mul_mem_graded hb (SetLike.pow_mem_graded n hf)
  smul_mem' := by
    rintro c _ ⟨n, a, ha, rfl⟩
    obtain ⟨m, b, hb, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (curveGrade r θ) hf c
    refine ⟨m + n, b * a, ?_, ?_⟩
    · simpa only [nsmul_eq_mul, Nat.cast_id, Nat.add_mul, Nat.add_assoc,
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
  IsLocalization.Away.lift_eq f
    (isUnit_of_dvd_unit
      (map_dvd (algebraMap (CurveRing r θ) (Localization.Away x)) ⟨g, hx⟩)
      (IsLocalization.Away.algebraMap_isUnit x)) a

theorem awayRestriction_fraction (r θ : ℂ)
    (f g x : CurveRing r θ) (hx : x = f * g) (n : ℕ) (a : CurveRing r θ) :
    awayRestriction r θ f g x hx (awayFraction r θ f n a) =
      awayFraction r θ x n (a * g ^ n) := by
  have hu : algebraMap (CurveRing r θ) (Localization.Away x) f *
      Localization.mk g (⟨x, 1, pow_one x⟩ : Submonoid.powers x) = 1 := by
    rw [← Algebra.smul_def, Localization.smul_mk]
    change Localization.mk (f * g) (⟨x, 1, pow_one x⟩ : Submonoid.powers x) = 1
    rw [← hx]
    exact Localization.mk_self (⟨x, 1, pow_one x⟩ : Submonoid.powers x)
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
  simpa only [nsmul_eq_mul, Nat.cast_id, Nat.mul_add, Nat.add_assoc] using
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
  map_add' z w := Subtype.ext
    (map_add (awayRestriction r θ f g x hx)
      (z : Localization.Away f) (w : Localization.Away f))
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
    SecondDegreeOne r θ →+ OverlapDegreeOne r θ where
  toFun z := ⟨awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
      (curveG1 r θ * curveG2 r θ) (mul_comm _ _) z,
    by
      change ∃ n a, a ∈ curveGrade r θ (1 + n * 8) ∧
        awayFraction r θ (curveG1 r θ * curveG2 r θ) n a =
          awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
            (curveG1 r θ * curveG2 r θ) (mul_comm _ _) (z : SecondOpen r θ)
      obtain ⟨n, a, ha, hza⟩ := z.property
      refine ⟨n, a * curveG1 r θ ^ n, ?_, ?_⟩
      · have hgrade : a * curveG1 r θ ^ n ∈ curveGrade r θ (1 + n * 4 + n * 4) := by
          simpa only [nsmul_eq_mul, Nat.cast_id] using
            SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n (curveG1_mem_grade r θ))
        have hn : 1 + n * 4 + n * 4 = 1 + n * 8 := by omega
        simpa only [hn] using hgrade
      · rw [← hza]
        exact (awayRestriction_fraction r θ (curveG2 r θ) (curveG1 r θ)
          (curveG1 r θ * curveG2 r θ) (mul_comm _ _) n a).symm⟩
  map_zero' := Subtype.ext (map_zero (awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
    (curveG1 r θ * curveG2 r θ) (mul_comm _ _)))
  map_add' z w := Subtype.ext
    (map_add (awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
      (curveG1 r θ * curveG2 r θ) (mul_comm _ _))
      (z : SecondOpen r θ) (w : SecondOpen r θ))

@[simp] theorem firstDegreeOneRestriction_coe (r θ : ℂ) (z : FirstDegreeOne r θ) :
    (firstDegreeOneRestriction r θ z : Overlap r θ) =
      firstRestriction r θ z := by
  have hmap : awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
        (curveG1 r θ * curveG2 r θ) rfl = firstRestriction r θ := by
    apply IsLocalization.ringHom_ext (R := CurveRing r θ) (S := FirstOpen r θ)
      (P := Overlap r θ) (Submonoid.powers (curveG1 r θ))
    apply RingHom.ext
    intro a
    change awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
        (curveG1 r θ * curveG2 r θ) rfl
        (algebraMap (CurveRing r θ) (FirstOpen r θ) a) =
      firstRestriction r θ (algebraMap (CurveRing r θ) (FirstOpen r θ) a)
    exact (awayRestriction_base r θ (curveG1 r θ) (curveG2 r θ)
      (curveG1 r θ * curveG2 r θ) rfl a).trans
      (IsLocalization.Away.awayToAwayRight_eq (R := CurveRing r θ)
        (S := FirstOpen r θ) (P := Overlap r θ) (curveG1 r θ) (curveG2 r θ) a).symm
  change awayRestriction r θ (curveG1 r θ) (curveG2 r θ)
    (curveG1 r θ * curveG2 r θ) rfl (z : FirstOpen r θ) = firstRestriction r θ z
  exact RingHom.congr_fun hmap (z : FirstOpen r θ)

@[simp] theorem secondDegreeOneRestriction_coe (r θ : ℂ) (z : SecondDegreeOne r θ) :
    (secondDegreeOneRestriction r θ z : Overlap r θ) =
      secondRestriction r θ z := by
  have hmap : awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
        (curveG1 r θ * curveG2 r θ) (mul_comm _ _) = secondRestriction r θ := by
    apply IsLocalization.ringHom_ext (R := CurveRing r θ) (S := SecondOpen r θ)
      (P := Overlap r θ) (Submonoid.powers (curveG2 r θ))
    apply RingHom.ext
    intro a
    change awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
        (curveG1 r θ * curveG2 r θ) (mul_comm _ _)
        (algebraMap (CurveRing r θ) (SecondOpen r θ) a) =
      secondRestriction r θ (algebraMap (CurveRing r θ) (SecondOpen r θ) a)
    exact (awayRestriction_base r θ (curveG2 r θ) (curveG1 r θ)
      (curveG1 r θ * curveG2 r θ) (mul_comm _ _) a).trans
      (IsLocalization.Away.awayToAwayLeft_eq (R := CurveRing r θ)
        (S := SecondOpen r θ) (P := Overlap r θ) (curveG2 r θ) (curveG1 r θ) a).symm
  change awayRestriction r θ (curveG2 r θ) (curveG1 r θ)
    (curveG1 r θ * curveG2 r θ) (mul_comm _ _) (z : SecondOpen r θ) =
      secondRestriction r θ z
  exact RingHom.congr_fun hmap (z : SecondOpen r θ)

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

end CycleQ2GeometricProjectiveCurve

end
