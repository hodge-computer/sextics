import Proposal.GeometricCanonicalCoordinateCoefficients
import Proposal.GeometricGradedCechDescent

/-!
# Degree-three projection on the literal coordinate localizations

Projecting the numerator of a fraction of pole order `n` onto its component of
degree `t + n*d` extracts its degree-`t` component. On the actual coordinate
cover this gives an additive projection that commutes with restriction and
fixes the signed cubic coefficient of every canonical form.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCanonicalDegreeProjection

open CycleQ2GradedLocalizationProjection

section Projection

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (t : ℕ)

include hf in
private theorem shiftedProj_mul_pow (n m : ℕ) (a : A) :
    GradedRing.proj 𝒜 (t + (n + m) * d) (a * f ^ m) =
      GradedRing.proj 𝒜 (t + n * d) a * f ^ m := by
  rw [Nat.add_mul, ← Nat.add_assoc]
  exact DirectSum.coe_decompose_mul_add_of_right_mem 𝒜
    (show f ^ m ∈ 𝒜 (m * d) by simpa using SetLike.pow_mem_graded m hf)

include hf in
private theorem projectedFraction_eq {n m : ℕ} {a b : A}
    (h : fraction f n a = fraction f m b) :
    fraction f n (GradedRing.proj 𝒜 (t + n * d) a) =
      fraction f m (GradedRing.proj 𝒜 (t + m * d) b) := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalization.eq.mp h
  have hk' : a * f ^ (m + k) = b * f ^ (n + k) := by
    simpa only [powerDenominator, pow_add, mul_assoc, mul_comm, mul_left_comm] using hk
  have hy := shiftedProj_mul_pow 𝒜 hf t m (n + k) b
  rw [show m + (n + k) = n + (m + k) by omega] at hy
  have hp := (shiftedProj_mul_pow 𝒜 hf t n (m + k) a).symm.trans
    ((congrArg (GradedRing.proj 𝒜 (t + (n + (m + k)) * d)) hk').trans hy)
  apply IsLocalization.eq.mpr
  refine ⟨powerDenominator f k, ?_⟩
  simpa only [powerDenominator, pow_add, mul_assoc, mul_comm, mul_left_comm] using hp

private def projection (z : Localization.Away f) : Localization.Away f :=
  let p := IsLocalization.Away.sec f z
  fraction f p.2 (GradedRing.proj 𝒜 (t + p.2 * d) p.1)

include hf in
private theorem projection_fraction (n : ℕ) (a : A) :
    projection 𝒜 (d := d) t (fraction f n a) =
      fraction f n (GradedRing.proj 𝒜 (t + n * d) a) :=
  projectedFraction_eq 𝒜 hf t (sec_fraction (fraction f n a))

include hf in
private theorem projection_add (z w : Localization.Away f) :
    projection 𝒜 (d := d) t (z + w) =
      projection 𝒜 (d := d) t z + projection 𝒜 (d := d) t w := by
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  obtain ⟨m, b, rfl⟩ := exists_fraction f w
  rw [← fraction_add]
  simp only [projection_fraction 𝒜 hf t, map_add, shiftedProj_mul_pow 𝒜 hf t n m a]
  have hb := shiftedProj_mul_pow 𝒜 hf t m n b
  rw [Nat.add_comm m n] at hb
  rw [hb, fraction_add]

/-- The homogeneous degree-`t` component of an ordinary principal localization. -/
def degreePlus : Localization.Away f →+ Localization.Away f where
  toFun := projection 𝒜 (d := d) t
  map_add' := projection_add 𝒜 hf t
  map_zero' := by
    have h := projection_add 𝒜 hf t (0 : Localization.Away f) 0
    apply add_left_cancel (a := projection 𝒜 (d := d) t 0)
    simpa only [zero_add, add_zero] using h.symm

theorem degreePlus_fraction (n : ℕ) (a : A) :
    degreePlus 𝒜 hf t (fraction f n a) = fraction f n (GradedRing.proj 𝒜 (t + n*d) a) :=
  projection_fraction 𝒜 hf t n a

theorem degreePlus_restrict {g x : A} {e dx : ℕ} (hg : g ∈ 𝒜 e) (hxhom : x ∈ 𝒜 dx)
    (hx : x = f * g) (hdx : dx = d + e) (ρ : Localization.Away f →ₐ[A] Localization.Away x)
    (z : Localization.Away f) :
    degreePlus 𝒜 hxhom t (ρ z) = ρ (degreePlus 𝒜 hf t z) := by
  subst dx
  obtain ⟨n, a, rfl⟩ := exists_fraction f z
  rw [fraction_map ρ hx, degreePlus_fraction, degreePlus_fraction, fraction_map ρ hx]
  congr 1
  rw [Nat.mul_add, ← Nat.add_assoc]
  exact DirectSum.coe_decompose_mul_add_of_right_mem 𝒜
    (show g ^ n ∈ 𝒜 (n * e) by simpa using SetLike.pow_mem_graded n hg)

theorem degreePlus_mul_homogeneous_val {b : A} (hb : b ∈ 𝒜 t)
    (q : HomogeneousLocalization.Away 𝒜 f) :
    degreePlus 𝒜 hf t (algebraMap A (Localization.Away f) b * q.val) =
      algebraMap A (Localization.Away f) b * q.val := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hf q
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  change degreePlus 𝒜 hf t (algebraMap A (Localization.Away f) b * fraction f n a) =
    algebraMap A (Localization.Away f) b * fraction f n a
  have hm : algebraMap A (Localization.Away f) b * fraction f n a = fraction f n (b * a) := by
    exact IsLocalization.mul_mk'_eq_mk'_of_mul b a (powerDenominator f n)
  rw [hm, degreePlus_fraction]
  congr 1
  exact DirectSum.decompose_of_mem_same 𝒜 (SetLike.mul_mem_graded hb ha)

end Projection

open CategoryTheory Opposite CycleQ2GeometricSurfaceCoordinates CycleQ2CartierSurfaceGrading
  CycleQ2GeometricCartierNormalLift CycleQ2ProjectiveCoordinateCohomology
  CycleQ2CanonicalCoordinateCoefficients CycleQ2SurfaceSectionCoefficients
  CycleQ2SurfaceCoordinateFrames CycleQ2SurfaceCoordinateCubicFrames

/-- Degree three in the actual coordinate localization. -/
def degreeThree (s : Finset (Fin 3)) (_hs : s.Nonempty) :
    CoordinateLocal 57 1 s →+ CoordinateLocal 57 1 s :=
  degreePlus (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 s) 3

theorem degreeThree_restrict {s t : Finset (Fin 3)} (hs : s.Nonempty) (ht : t.Nonempty)
    (hst : s ⊆ t) (p : CoordinateLocal 57 1 s) :
    degreeThree t ht (coordinateRestriction 57 1 hst p) =
      coordinateRestriction 57 1 hst (degreeThree s hs p) :=
  degreePlus_restrict _ _ 3 (coordinateProduct_mem_grade 57 1 (t \ s)) _
    (coordinateProduct_factor 57 1 hst)
    (by rw [Nat.add_comm, Finset.card_sdiff_add_card_eq_card hst]) _ p

theorem degreeThree_canonicalCoefficientOn (s : Finset (Fin 3)) (hs : s.Nonempty)
    (ω : CycleQ2CanonicalCoordinateCoefficients.CanonicalForms.val.obj
      (op (coordinateIntersection 57 1 s))) :
    degreeThree s hs (canonicalCoefficientOn s hs ω) = canonicalCoefficientOn s hs ω := by
  let i := hs.choose
  let hi : i ∈ s := hs.choose_spec
  let q := (coordinateSections 57 1 s hs).symm
    ((coordinateExteriorFrame i).app _ (intersection_le_chart 57 1 i hi) ω)
  let x := algebraMap (CycleQ2GeometricSeedNormalIdeals.SurfaceRing 57 1)
    (CoordinateLocal 57 1 s) ((coordinateElement 57 1 i)^3)
  have hf : degreeThree s hs (x * q.val) = x * q.val :=
    degreePlus_mul_homogeneous_val _ _ _ (by
      simpa using SetLike.pow_mem_graded 3 (coordinateElement_mem_grade 57 1 i)) q
  change degreeThree s hs ((orientation i : _) * x * q.val) = _
  change _ = (orientation i : _) * x * q.val
  rw [mul_assoc, ← zsmul_eq_mul, map_zsmul, hf]

end CycleQ2LiteralCanonicalDegreeProjection

end

#print axioms CycleQ2LiteralCanonicalDegreeProjection.degreeThree_restrict
#print axioms CycleQ2LiteralCanonicalDegreeProjection.degreeThree_canonicalCoefficientOn
