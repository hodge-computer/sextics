import Proposal.GeometricProjectiveCharts
import Proposal.GeometricCartierCechNonboundary
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# The literal projective curve as a closed subscheme of its surface

Both schemes use their original graded quotient rings. The surface here
is exactly the surface used by the projective Cartier cocycle. The curve
map is induced by the original polynomial substitution and quotient.
Surjectivity on each homogeneous piece proves that the scheme maps are
closed immersions. The kernel of the actual surface-to-curve ring map is
exactly the curve ideal used by the existing normal calculations.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped BigOperators DirectSum
namespace CycleQ2GeometricLiteralSurface
open MvPolynomial CategoryTheory AlgebraicGeometry
open CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2SeedCechTheta
open CycleQ2ConormalJacobian CycleQ2GeometricSeedNormalIdeals
open CycleQ2GeometricProjectiveCurve

/-- The already constructed weighted ambient and surface grading. -/
abbrev weight := CycleQ2CartierSurfaceGrading.weight
abbrev AmbientGrade := CycleQ2CartierSurfaceGrading.PolynomialGrade
abbrev surfaceGrade := CycleQ2CartierSurfaceGrading.surfaceGrade

/-- The exact projective surface on which the Cartier cocycle is defined. -/
abbrev surface := CycleQ2CartierProjectiveCover.projectiveSurface

attribute [local instance] MvPolynomial.weightedGradedAlgebra MvPolynomial.gradedAlgebra

private theorem x0h : (X 0 : WeightedPoly).IsWeightedHomogeneous weight 1 :=
  isWeightedHomogeneous_X ℂ weight 0
private theorem x1h : (X 1 : WeightedPoly).IsWeightedHomogeneous weight 1 :=
  isWeightedHomogeneous_X ℂ weight 1
private theorem x2h : (X 2 : WeightedPoly).IsWeightedHomogeneous weight 1 :=
  isWeightedHomogeneous_X ℂ weight 2
private theorem x3h : (X 3 : WeightedPoly).IsWeightedHomogeneous weight 1 :=
  isWeightedHomogeneous_X ℂ weight 3

def quotient (r θ : ℂ) : WeightedPoly →ₐ[ℂ] SurfaceRing r θ :=
  Ideal.Quotient.mkₐ ℂ (surfaceIdeal r θ)

@[simp] theorem quotient_eq (r θ : ℂ) (p : WeightedPoly) :
    quotient r θ p = Ideal.Quotient.mk (surfaceIdeal r θ) p := rfl

def ambientGradedMap (r θ : ℂ) : AmbientGrade →+*ᵍ surfaceGrade r θ where
  toRingHom := (quotient r θ).toRingHom
  map_mem hp := ⟨_,hp,rfl⟩

theorem ambient_irrelevant_le (r θ : ℂ) :
    HomogeneousIdeal.irrelevant (surfaceGrade r θ) ≤
      (HomogeneousIdeal.irrelevant AmbientGrade).map (ambientGradedMap r θ) := by
  change (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant AmbientGrade).map (ambientGradedMap r θ)).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (surfaceGrade r θ)).mpr
  intro n hn a ha
  obtain ⟨p,hp,rfl⟩ := ha
  exact Ideal.mem_map_of_mem (ambientGradedMap r θ)
    (HomogeneousIdeal.mem_irrelevant_of_mem AmbientGrade hn hp)

def ambient : Scheme := Proj AmbientGrade

def surfaceToAmbient (r θ : ℂ) : surface r θ ⟶ ambient :=
  Proj.map (ambientGradedMap r θ) (ambient_irrelevant_le r θ)

@[simp] theorem surfaceToAmbient_preimage_basicOpen (r θ : ℂ) (p : WeightedPoly) :
    surfaceToAmbient r θ ⁻¹ᵁ Proj.basicOpen AmbientGrade p =
      Proj.basicOpen (surfaceGrade r θ) (quotient r θ p) := rfl


/-- Evaluation into a graded algebra preserves the declared variable weights. -/
theorem eval₂_mem_grade {σ A : Type*} [DecidableEq σ] [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedRing 𝒜] (w : σ → ℕ)
    (c : ℂ →+* A) (x : σ → A)
    (hc : ∀ a, c a ∈ 𝒜 0) (hx : ∀ j, x j ∈ 𝒜 (w j))
    {n : ℕ} {p : MvPolynomial σ ℂ} (hp : p.IsWeightedHomogeneous w n) :
    eval₂ c x p ∈ 𝒜 n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simpa only [eval₂_zero] using (𝒜 n).zero_mem
  | add p q hp hq ihp ihq => simpa only [eval₂_add] using (𝒜 n).add_mem ihp ihq
  | monomial d a hd =>
    rw [eval₂_monomial]
    have hprod := SetLike.prod_pow_mem_graded 𝒜 w x d
      (F := d.support) (fun i _ => hx i)
    have hs : (∑ i ∈ d.support, d i • w i)=n := by
      simpa only [Finsupp.weight_apply,Finsupp.sum] using hd
    have hh := SetLike.mul_mem_graded (hc a) hprod
    rw [zero_add,hs] at hh
    exact hh

theorem substitute_homogeneous {n : ℕ} {p : WeightedPoly}
    (hp : p.IsWeightedHomogeneous weight n) : (substitute p).IsHomogeneous n := by
  change eval₂ C ![X 0,X 1,X 2,X 3,-(X 2 ^ 2)] p ∈ PolynomialGrade n
  apply eval₂_mem_grade PolynomialGrade weight C _ (fun a => isHomogeneous_C _ a) _ hp
  intro j
  fin_cases j
  · exact isHomogeneous_X ℂ 0
  · exact isHomogeneous_X ℂ 1
  · exact isHomogeneous_X ℂ 2
  · exact isHomogeneous_X ℂ 3
  · exact (isHomogeneous_X_pow (2 : Fin 4) 2).neg

/-- The ordinary four coordinates embed with their actual ambient weights. -/
def includePoly : Poly →ₐ[ℂ] WeightedPoly :=
  MvPolynomial.aeval (fun j : Fin 4 => X j.castSucc)

theorem includePoly_homogeneous {n : ℕ} {p : Poly} (hp : p.IsHomogeneous n) :
    (includePoly p).IsWeightedHomogeneous weight n := by
  change eval₂ C (fun j : Fin 4 => X j.castSucc) p ∈ AmbientGrade n
  apply eval₂_mem_grade AmbientGrade (fun _ : Fin 4 => 1) C _
    (fun a => isWeightedHomogeneous_C weight a) _ hp
  intro j
  fin_cases j
  · exact x0h
  · exact x1h
  · exact x2h
  · exact x3h

@[simp] theorem substitute_includePoly (p : Poly) : substitute (includePoly p)=p := by
  have he : substitute.comp includePoly=AlgHom.id ℂ Poly := by
    ext j
    fin_cases j <;> simp [includePoly,substitute]
  exact congrArg (fun f : Poly →ₐ[ℂ] Poly => f p) he

/-- The actual quotient map of the containing surface to its curve. -/
def curveRestriction (r θ : ℂ) : SurfaceRing r θ →ₐ[ℂ] CurveRing r θ :=
  Ideal.Quotient.liftₐ (surfaceIdeal r θ) (CycleQ2ActualNormalCech.ambientCurveAlg r θ)
    (fun p hp => CycleQ2ActualNormalCech.ambientCurveMap_kills r θ p
      (surfaceIdeal_le_curveIdeal r θ hp))

@[simp] theorem curveRestriction_quotient (r θ : ℂ) (p : WeightedPoly) :
    curveRestriction r θ (quotient r θ p)=ambientCurveMap r θ p := rfl

def curveGradedMap (r θ : ℂ) : surfaceGrade r θ →+*ᵍ curveGrade r θ where
  toRingHom := (curveRestriction r θ).toRingHom
  map_mem := by
    intro n q hq
    obtain ⟨p,hp,rfl⟩ := hq
    exact ⟨substitute p,substitute_homogeneous hp,rfl⟩

/-- Homogeneous curve sections lift through the actual surface quotient. -/
theorem curveGradedMap_homogeneous_surjective (r θ : ℂ) (n : ℕ)
    (q : CurveRing r θ) (hq : q ∈ curveGrade r θ n) :
    ∃ p : SurfaceRing r θ, p ∈ surfaceGrade r θ n ∧ curveGradedMap r θ p=q := by
  obtain ⟨p,hp,rfl⟩ := hq
  refine ⟨quotient r θ (includePoly p),⟨includePoly p,includePoly_homogeneous hp,rfl⟩,?_⟩
  change curveMap r θ (substitute (includePoly p))=curveMap r θ p
  rw [substitute_includePoly]

theorem curveGradedMap_surjective (r θ : ℂ) : Function.Surjective (curveGradedMap r θ) := by
  intro q
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
  refine ⟨quotient r θ (includePoly p),?_⟩
  change curveMap r θ (substitute (includePoly p))=curveMap r θ p
  rw [substitute_includePoly]

theorem curve_irrelevant_le (r θ : ℂ) :
    HomogeneousIdeal.irrelevant (curveGrade r θ) ≤
      (HomogeneousIdeal.irrelevant (surfaceGrade r θ)).map (curveGradedMap r θ) := by
  change (HomogeneousIdeal.irrelevant (curveGrade r θ)).toIdeal ≤
    ((HomogeneousIdeal.irrelevant (surfaceGrade r θ)).map (curveGradedMap r θ)).toIdeal
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (curveGrade r θ)).mpr
  intro n hn q hq
  obtain ⟨p,hp,rfl⟩ := curveGradedMap_homogeneous_surjective r θ n q hq
  exact Ideal.mem_map_of_mem (curveGradedMap r θ)
    (HomogeneousIdeal.mem_irrelevant_of_mem (surfaceGrade r θ) hn hp)

/-- The actual projective curve maps to the same literal containing surface. -/
def curveToSurface (r θ : ℂ) : projectiveCurve r θ ⟶ surface r θ :=
  Proj.map (curveGradedMap r θ) (curve_irrelevant_le r θ)

@[simp] theorem curveToSurface_preimage_basicOpen (r θ : ℂ) (p : WeightedPoly) :
    curveToSurface r θ ⁻¹ᵁ Proj.basicOpen (surfaceGrade r θ) (quotient r θ p) =
      Proj.basicOpen (curveGrade r θ) (ambientCurveMap r θ p) := rfl

open HomogeneousLocalization

section ClosedProj
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B)
variable [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable (hsur : ∀ (n : ℕ) (b : B), b ∈ ℬ n → ∃ a : A, a ∈ 𝒜 n ∧ f a=b)

include hsur in
theorem gradedAwayMap_surjective (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n,b,hb,rfl⟩ := Away.mk_surjective ℬ (f.2 hs) z
  obtain ⟨a,ha,rfl⟩ := hsur (n • d) b hb
  refine ⟨Away.mk 𝒜 hs n a ha,?_⟩
  simp only [Away.map_mk]

theorem projMap_restrict_eq (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (Proj.map f hf ∣_ Proj.basicOpen 𝒜 s) =
      (Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hd).hom ≫
        Spec.map (CommRingCat.ofHom (Away.map f s)) ≫
          (Proj.basicOpenIsoSpec 𝒜 s hs hd).inv := by
  have hcomm := Proj.awayι_comp_map f hf hd s hs
  apply (cancel_mono (Proj.basicOpen 𝒜 s).ι).mp
  rw [morphismRestrict_ι]
  change (Proj.basicOpen ℬ (f s)).ι ≫ Proj.map f hf =
    (Proj.basicOpenIsoSpec ℬ (f s) (f.2 hs) hd).hom ≫
      (Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ Proj.awayι 𝒜 s hs hd)
  rw [← hcomm]
  simp only [Proj.awayι,Category.assoc,Iso.hom_inv_id_assoc]

include hsur in
theorem projMap_restrict_isClosedImmersion (s : A) {d : ℕ}
    (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    IsClosedImmersion (Proj.map f hf ∣_ Proj.basicOpen 𝒜 s) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Away.map f s))) :=
    IsClosedImmersion.spec_of_surjective _ (gradedAwayMap_surjective 𝒜 ℬ f hsur s hs)
  rw [projMap_restrict_eq 𝒜 ℬ f hf s hs hd]
  infer_instance

include hsur in
/-- A map surjective on every actual graded piece induces a closed immersion
of projective schemes. The proof uses the real homogeneous affine charts. -/
theorem projMap_isClosedImmersion : IsClosedImmersion (Proj.map f hf) := by
  have hc : (⨆ i : Σ n : PNat, 𝒜 n, Proj.basicOpen 𝒜 (i.2 : A))=⊤ := by
    have hh := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
    change (⨆ i : Σ n : PNat, 𝒜 n,
      (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2).opensRange)=⊤ at hh
    simpa only [Proj.opensRange_awayι] using hh
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion) (f := Proj.map f hf)
    (fun i : Σ n : PNat, 𝒜 n => Proj.basicOpen 𝒜 (i.2 : A)) hc ?_
  intro i
  exact projMap_restrict_isClosedImmersion 𝒜 ℬ f hf hsur i.2 i.2.2 i.1.2

end ClosedProj

instance surfaceToAmbient_isClosedImmersion (r θ : ℂ) :
    IsClosedImmersion (surfaceToAmbient r θ) := by
  apply projMap_isClosedImmersion AmbientGrade (surfaceGrade r θ)
    (ambientGradedMap r θ) (ambient_irrelevant_le r θ)
  rintro n q ⟨p,hp,rfl⟩
  exact ⟨p,hp,rfl⟩

instance curveToSurface_isClosedImmersion (r θ : ℂ) :
    IsClosedImmersion (curveToSurface r θ) :=
  projMap_isClosedImmersion (surfaceGrade r θ) (curveGrade r θ)
    (curveGradedMap r θ) (curve_irrelevant_le r θ)
    (curveGradedMap_homogeneous_surjective r θ)

@[simp] theorem includePoly_f1 (r : ℂ) :
    includePoly (relation r 0) = originalF1 r := by
  simp [includePoly,relation,originalF1]

@[simp] theorem includePoly_h (θ : ℂ) : includePoly (curveH θ)=thetaH θ := by
  simp [includePoly,curveH,thetaH,originalH,originalB,h,b]

/-- The inverse polynomial presentation eliminates the weighted coordinate
using the actual equation `w + x₂² = 0`. -/
def curveQuotientLift (r θ : ℂ) :
    CurveRing r θ →ₐ[ℂ] (WeightedPoly ⧸ ambientCurveIdeal r θ) :=
  Ideal.Quotient.liftₐ (curveIdeal r θ)
    ((Ideal.Quotient.mkₐ ℂ (ambientCurveIdeal r θ)).comp includePoly) (by
      have hi : curveIdeal r θ ≤ RingHom.ker
          (((Ideal.Quotient.mkₐ ℂ (ambientCurveIdeal r θ)).comp includePoly).toRingHom) := by
        rw [curveIdeal,Ideal.span_le]
        intro p hp
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
        rcases hp with rfl | hp
        · change Ideal.Quotient.mk (ambientCurveIdeal r θ) (includePoly (relation r 0))=0
          rw [includePoly_f1]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (curveEquation_mem r θ 0)
        · subst hp
          change Ideal.Quotient.mk (ambientCurveIdeal r θ) (includePoly (curveH θ))=0
          rw [includePoly_h]
          exact Ideal.Quotient.eq_zero_iff_mem.mpr (curveEquation_mem r θ 2)
      intro p hp
      exact hi hp)

@[simp] theorem curveQuotientLift_curveMap (r θ : ℂ) (p : Poly) :
    curveQuotientLift r θ (curveMap r θ p)=
      Ideal.Quotient.mk (ambientCurveIdeal r θ) (includePoly p) := rfl

theorem curveQuotientLift_comp (r θ : ℂ) :
    (curveQuotientLift r θ).comp (CycleQ2ActualNormalCech.ambientCurveAlg r θ)=
      Ideal.Quotient.mkₐ ℂ (ambientCurveIdeal r θ) := by
  ext j
  have hvar (j : Fin 5) :
      (curveQuotientLift r θ).comp (CycleQ2ActualNormalCech.ambientCurveAlg r θ) (X j)=
        Ideal.Quotient.mk (ambientCurveIdeal r θ) (includePoly (substitute (X j))) := rfl
  rw [hvar]
  fin_cases j
  · simp [substitute,includePoly]
  · simp [substitute,includePoly]
  · simp [substitute,includePoly]
  · simp [substitute,includePoly]
  · have hf2 : Ideal.Quotient.mk (ambientCurveIdeal r θ) originalF2=0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (curveEquation_mem r θ 1)
    simp only [originalF2,map_add,map_pow] at hf2
    simpa [substitute,includePoly] using (eq_neg_of_add_eq_zero_left hf2).symm

theorem ambientCurveMap_eq_zero_iff (r θ : ℂ) (p : WeightedPoly) :
    ambientCurveMap r θ p=0 ↔ p ∈ ambientCurveIdeal r θ := by
  constructor
  · intro hp
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have hh := congrArg (fun f : WeightedPoly →ₐ[ℂ] (WeightedPoly ⧸ ambientCurveIdeal r θ) => f p)
      (curveQuotientLift_comp r θ)
    change curveQuotientLift r θ (ambientCurveMap r θ p)=
      Ideal.Quotient.mk (ambientCurveIdeal r θ) p at hh
    rw [hp,map_zero] at hh
    exact hh.symm
  · exact CycleQ2ActualNormalCech.ambientCurveMap_kills r θ p

/-- The polynomial ideal used by the normal calculations is exactly the
kernel of the actual ring map defining the projective closed immersion. -/
theorem curveRestriction_ker (r θ : ℂ) :
    RingHom.ker (curveRestriction r θ).toRingHom=curveIdealOnSurface r θ := by
  apply le_antisymm
  · intro q hq
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective q
    change ambientCurveMap r θ p=0 at hq
    exact Ideal.mem_map_of_mem _ ((ambientCurveMap_eq_zero_iff r θ p).mp hq)
  · change (ambientCurveIdeal r θ).map (Ideal.Quotient.mk (surfaceIdeal r θ)) ≤ _
    rw [Ideal.map_le_iff_le_comap]
    intro p hp
    change ambientCurveMap r θ p=0
    exact CycleQ2ActualNormalCech.ambientCurveMap_kills r θ p hp


section ChartKernel
variable {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
variable (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B)
variable [GradedRing 𝒜] [GradedRing ℬ]
variable (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

def projChartSectionsEquiv (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    Away 𝒜 s ≃+* Γ(Proj 𝒜,Proj.basicOpen 𝒜 s) :=
  (Proj.basicOpenIsoAway 𝒜 s hs hd).commRingCatIsoToRingEquiv

/-- The actual scheme section map is the original homogeneous-localization
map under the canonical affine chart equivalences. -/
theorem projMap_app_basicOpen (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d)
    (z : Away 𝒜 s) :
    (Proj.map f hf).app (Proj.basicOpen 𝒜 s) (projChartSectionsEquiv 𝒜 s hs hd z)=
      projChartSectionsEquiv ℬ (f s) (f.2 hs) hd (Away.map f s z) := by
  have h := ConcreteCategory.congr_hom (Proj.awayToSection_comp_appLE f hf hs) z
  change (Proj.map f hf).appLE (Proj.basicOpen 𝒜 s)
      ((Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 s) le_rfl
      (Proj.awayToSection 𝒜 s z) = Proj.awayToSection ℬ (f s) (Away.map f s z) at h
  rw [Scheme.Hom.appLE_eq_app] at h
  exact h

/-- The ideal of the closed subscheme on a basic projective open is exactly
the kernel of the homogeneous localization map, transported by its canonical chart. -/
theorem projMap_chart_ker (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    (RingHom.ker ((Proj.map f hf).app (Proj.basicOpen 𝒜 s)).hom).comap
      (projChartSectionsEquiv 𝒜 s hs hd).toRingHom = RingHom.ker (Away.map f s) := by
  ext z
  change (Proj.map f hf).app (Proj.basicOpen 𝒜 s) (projChartSectionsEquiv 𝒜 s hs hd z)=0 ↔ _
  rw [projMap_app_basicOpen 𝒜 ℬ f hf s hs hd]
  exact (projChartSectionsEquiv ℬ (f s) (f.2 hs) hd).map_eq_zero_iff

theorem projMap_chart_ker_eq_map (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) (hd : 0 < d) :
    RingHom.ker ((Proj.map f hf).app (Proj.basicOpen 𝒜 s)).hom =
      (RingHom.ker (Away.map f s)).map (projChartSectionsEquiv 𝒜 s hs hd).toRingHom := by
  rw [← projMap_chart_ker 𝒜 ℬ f hf s hs hd]
  exact (Ideal.map_comap_of_surjective _ (projChartSectionsEquiv 𝒜 s hs hd).surjective _).symm

end ChartKernel

/-- A homogeneous fraction belongs to the localized curve ideal exactly
when an actual power of its denominator carries its numerator into the
original ideal on the surface. -/
theorem curveChartMap_mk_eq_zero_iff (r θ : ℂ) (s : SurfaceRing r θ) {d : ℕ}
    (hs : s ∈ surfaceGrade r θ d) (n : ℕ) (p : SurfaceRing r θ)
    (hp : p ∈ surfaceGrade r θ (n • d)) :
    Away.map (curveGradedMap r θ) s (Away.mk (surfaceGrade r θ) hs n p hp)=0 ↔
      ∃ k : ℕ, s^k*p ∈ curveIdealOnSurface r θ := by
  rw [Away.map_mk,HomogeneousLocalization.ext_iff_val,HomogeneousLocalization.val_zero,
    Away.val_mk,Localization.mk_eq_mk',IsLocalization.mk'_eq_zero_iff]
  constructor
  · rintro ⟨⟨b,hb⟩,hzero⟩
    obtain ⟨k,rfl⟩ := hb
    refine ⟨k,?_⟩
    rw [← curveRestriction_ker]
    change curveRestriction r θ (s^k*p)=0
    change curveRestriction r θ s ^ k * curveRestriction r θ p=0 at hzero
    simpa only [map_mul,map_pow] using hzero
  · rintro ⟨k,hk⟩
    refine ⟨⟨(curveGradedMap r θ s)^k,Submonoid.pow_mem _ (Submonoid.mem_powers _) _⟩,?_⟩
    rw [← curveRestriction_ker] at hk
    change curveRestriction r θ (s^k*p)=0 at hk
    change curveRestriction r θ s ^ k * curveRestriction r θ p=0
    simpa only [map_mul,map_pow] using hk

theorem curveToSurface_chart_ker (r θ : ℂ) (s : SurfaceRing r θ) {d : ℕ}
    (hs : s ∈ surfaceGrade r θ d) (hd : 0 < d) :
    (RingHom.ker ((curveToSurface r θ).app (Proj.basicOpen (surfaceGrade r θ) s)).hom).comap
      (projChartSectionsEquiv (surfaceGrade r θ) s hs hd).toRingHom =
        RingHom.ker (Away.map (curveGradedMap r θ) s) :=
  projMap_chart_ker (surfaceGrade r θ) (curveGrade r θ) (curveGradedMap r θ)
    (curve_irrelevant_le r θ) s hs hd

end CycleQ2GeometricLiteralSurface
end
