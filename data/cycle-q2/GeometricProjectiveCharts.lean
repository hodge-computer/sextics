import Proposal.GeometricDegreeOneCech
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Actual projective curve charts

The projective scheme and its affine denominator opens use the existing
homogeneous quotient and literal coordinate ring. The cover is proved
from the two actual curve equations without using cone or incidence data.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricProjectiveCurve

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped DirectSum
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta
open CycleQ2SeedCech (curveA curveB)
attribute [local instance] MvPolynomial.gradedAlgebra

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

private theorem mem_of_C_mul (Q : Ideal Poly) (c : ℂ) (hc : c ≠ 0) (p : Poly)
    (hp : C c * p ∈ Q) : p ∈ Q := by
  have hh := Q.mul_mem_left (C (c⁻¹)) hp
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

private theorem one_sub_I_ne_zero : (1 - Complex.I : ℂ) ≠ 0 := by
  intro hzero
  have hh := congrArg Complex.im hzero
  norm_num at hh

/-- The two small homogeneous functions have no common relevant prime
on the literal theta-family curve. -/
private theorem coordinates_mem_of_A_B (r θ : ℂ) (Q : Ideal Poly) [Q.IsPrime]
    (hcurve : curveIdeal r θ ≤ Q) (hA : curveA ∈ Q) (hB : curveB ∈ Q) :
    ∀ j : Fin 4, X j ∈ Q := by
  have hF : relation r 0 ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hH : curveH θ ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hx0sq : (X (0 : Fin 4)) ^ 2 ∈ Q := by
    have hh := Q.add_mem hF (Q.mul_mem_left (C r) hA)
    simpa [relation, curveA, mul_assoc] using hh
  have hx0 : (X (0 : Fin 4)) ∈ Q :=
    (inferInstance : Q.IsPrime).mem_of_pow_mem 2 hx0sq
  have hx2 : (X (2 : Fin 4)) ∈ Q := hB
  have hrest : X (2 : Fin 4) * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
      X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2) ∈ Q :=
    Q.add_mem (Q.mul_mem_right _ hx2) (Q.mul_mem_right _ hx0)
  have hshape : curveH θ =
      (C (1 - Complex.I) * X 3 ^ 3 - C Complex.I * X 1 ^ 3) +
        (X 2 * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
          X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2)) := by
    simp [curveH, h, b, map_sub]
    ring
  have htail : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 -
      C Complex.I * X 1 ^ 3 ∈ Q := by
    have hh := Q.sub_mem hH hrest
    simpa only [hshape, add_sub_cancel_right] using hh
  have h13 : X (1 : Fin 4) ∈ Q ∧ X (3 : Fin 4) ∈ Q := by
    rcases (inferInstance : Q.IsPrime).mem_or_mem hA with hx1 | hx3
    · have hx1pow := Q.pow_mem_of_mem hx1 3 (by decide)
      have hh := Q.add_mem htail (Q.mul_mem_left (C Complex.I) hx1pow)
      have hc : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_add_cancel] using hh
      exact ⟨hx1, (inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ one_sub_I_ne_zero _ hc)⟩
    · have hx3pow := Q.pow_mem_of_mem hx3 3 (by decide)
      have hh := Q.sub_mem (Q.mul_mem_left (C (1 - Complex.I)) hx3pow) htail
      have hc : C Complex.I * X (1 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_sub_cancel] using hh
      exact ⟨(inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ Complex.I_ne_zero _ hc), hx3⟩
  intro j
  fin_cases j
  · exact hx0
  · exact h13.1
  · exact hx2
  · exact h13.2

/-- If both denominator functions lie in a prime of the actual curve,
then all four ordinary homogeneous coordinates lie in that prime. -/
private theorem coordinates_mem_of_denominators (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (h1 : curveG1 r θ ∈ Q) (h2 : curveG2 r θ ∈ Q) :
    ∀ j : Fin 4, curveMap r θ (X j) ∈ Q := by
  let T : Ideal Poly := Q.comap (curveMap r θ)
  letI : T.IsPrime := Ideal.comap_isPrime _ _
  have hcurve : curveIdeal r θ ≤ T := by
    intro p hp
    change curveMap r θ p ∈ Q
    have hz : curveMap r θ p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hz]
    exact Q.zero_mem
  have hg1 : C (3 * r ^ 2) * curveA ^ 2 ∈ T := by
    change curveMap r θ (C (3 * r ^ 2) * curveA ^ 2) ∈ Q
    rw [← ambientCurveMap_g1]
    exact h1
  have hg2 : C 3 * curveB ^ 4 ∈ T := by
    change curveMap r θ (C 3 * curveB ^ 4) ∈ Q
    rw [← ambientCurveMap_g2]
    exact h2
  have hA : curveA ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 2
    (mem_of_C_mul T _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) _ hg1)
  have hB : curveB ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 4
    (mem_of_C_mul T _ (by norm_num) _ hg2)
  exact coordinates_mem_of_A_B r θ T hcurve hA hB

/-- The actual denominator opens cover every relevant prime of the
ordinary homogeneous curve presentation. -/
private theorem relevant_prime_cover (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (hx : ∃ j : Fin 4, curveMap r θ (X j) ∉ Q) :
    curveG1 r θ ∉ Q ∨ curveG2 r θ ∉ Q := by
  by_contra! hbad
  obtain ⟨j, hj⟩ := hx
  exact hj (coordinates_mem_of_denominators r θ hr Q hbad.1 hbad.2 j)

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
  exact relevant_prime_cover r θ hr
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


end CycleQ2GeometricProjectiveCurve
end
