import Proposal.GeometricLiteralAmbientSmooth
import Proposal.GeometricIncidenceFamilyContainment
import Proposal.GeometricLiteralSurfaceSmooth

/-! The trace surface inside the actual incidence fiber of the cubic family.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralAmbientSurface

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open CycleQ2GeometricIncidenceProj CycleQ2GeometricSeedSmooth CycleQ2SeedCubicFamily
  CycleQ2SeedProjectiveFamily CycleQ2SeedProjectiveSpecialization CycleQ2LiteralAmbientSmooth
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricSurfaceCoefficients CycleQ2CartierProjectiveCover

local instance (r : ℂ) : CommRing (FamilyRing r) := Ideal.Quotient.commRing _

private abbrev S := SurfaceRing (57 : ℂ) 1
private abbrev G := CycleQ2CartierSurfaceGrading.surfaceGrade (57 : ℂ) 1

/-- Specialize the cubic coefficients at the trace seed and then impose the
surface equation. The resulting ring map preserves all five coordinates. -/
def toSurfaceRing : FamilyRing 57 →+* S :=
  Ideal.Quotient.lift (familyIdeal 57)
    ((surfaceQuotient 57 1).comp (MvPolynomial.map (coefficientEvaluation incidenceCoefficients))) (by
      intro p hp
      suffices familyIdeal 57 ≤ RingHom.ker
          ((surfaceQuotient 57 1).comp (MvPolynomial.map (coefficientEvaluation incidenceCoefficients)))
        from this hp
      apply Ideal.span_le.mpr
      rintro _ ⟨⟩
      change surfaceQuotient 57 1 (MvPolynomial.map _ (familyEquation 57)) = 0
      rw [specialize_incidence, ← CycleQ2NormalConnecting.actualSeedEquation_eq_smoothF]
      exact surfaceQuotient_F 57 1)

private theorem homogeneous_map {R T : Type} [CommRing R] [CommRing T] (φ : R →+* T)
    {p : MvPolynomial (Fin 5) R} {n : ℕ} (hp : p.IsWeightedHomogeneous geometricWeight n) :
    (MvPolynomial.map φ p).IsWeightedHomogeneous geometricWeight n := by
  intro m hm
  apply hp
  intro hz
  exact hm (by rw [MvPolynomial.coeff_map, hz, map_zero])

def toSurfaceGraded : familyGrade 57 →+*ᵍ G where
  toRingHom := toSurfaceRing
  map_mem := by
    rintro n a ⟨p,hp,rfl⟩
    exact ⟨_, homogeneous_map (coefficientEvaluation incidenceCoefficients) hp, rfl⟩

theorem graded_surjective (n : ℕ) (a : S) (ha : a ∈ G n) :
    ∃ b : FamilyRing 57, b ∈ familyGrade 57 n ∧ toSurfaceGraded b = a := by
  obtain ⟨p,hp,rfl⟩ := ha
  refine ⟨familyQuotient 57 (coefficientLift p),
    ⟨_, homogeneous_map (algebraMap ℂ ParameterRing) hp, rfl⟩, ?_⟩
  change surfaceQuotient 57 1 (MvPolynomial.map _ (coefficientLift p)) = surfaceQuotient 57 1 p
  rw [coefficientLift, coefficientEvaluation_constantPolynomial]

theorem irrelevant_le : HomogeneousIdeal.irrelevant G ≤
    (HomogeneousIdeal.irrelevant (familyGrade 57)).map toSurfaceGraded := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn a ha
  obtain ⟨b,hb,rfl⟩ := graded_surjective n a ha
  exact Ideal.mem_map_of_mem toSurfaceGraded
    (HomogeneousIdeal.mem_irrelevant_of_mem (familyGrade 57) hn hb)

def surfaceToFamily : projectiveSurface 57 1 ⟶ family 57 := Proj.map toSurfaceGraded irrelevant_le

theorem surfaceToFamily_overBase : surfaceToFamily ≫ familyToParameters 57 =
    projectiveToComplex 57 1 ≫ incidenceParameter := by
  rw [surfaceToFamily, familyToParameters, ← Category.assoc,
    CycleQ2IncidenceFamilyContainment.projectiveMap_toSpecZero, Category.assoc,
    projectiveToComplex, incidenceParameter, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  apply Subtype.ext
  change surfaceQuotient 57 1 (MvPolynomial.map _ (C a)) = _
  rw [MvPolynomial.map_C]
  rfl

/-- The source is the projective surface carrying the certified Cartier trace. -/
def surfaceToFiber : projectiveSurface 57 1 ⟶ IncidenceFiber 57 :=
  pullback.lift (projectiveToComplex 57 1) surfaceToFamily surfaceToFamily_overBase.symm

@[reassoc, simp] theorem surfaceToFiber_overComplex :
    surfaceToFiber ≫ incidenceFiberToComplex 57 = projectiveToComplex 57 1 := by
  simp [surfaceToFiber, incidenceFiberToComplex]

section ClosedGradedMap


variable {A B σ τ : Type} [CommRing A] [CommRing B]
  [SetLike σ A] [SetLike τ B] [AddSubgroupClass σ A] [AddSubgroupClass τ B]
variable (𝒜 : ℕ → σ) (ℬ : ℕ → τ)
  [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
variable (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
variable (hsur : ∀ (n : ℕ) (b : B), b ∈ ℬ n → ∃ a : A, a ∈ 𝒜 n ∧ f a = b)

include hsur in
private theorem gradedAwayMap_surjective (s : A) {d : ℕ} (hs : s ∈ 𝒜 d) :
    Function.Surjective (Away.map f s) := by
  intro z
  obtain ⟨n, b, hb, rfl⟩ := Away.mk_surjective ℬ (f.2 hs) z
  obtain ⟨a, ha, rfl⟩ := hsur (n • d) b hb
  refine ⟨Away.mk 𝒜 hs n a ha, ?_⟩
  simp only [Away.map_mk]

include hsur in
private theorem projectiveMap_closedImmersion : IsClosedImmersion (Proj.map f hf) := by
  have hc : (⨆ i : Σ n : PNat, 𝒜 n, Proj.basicOpen 𝒜 (i.2 : A)) = ⊤ := by
    have hh := (Proj.affineOpenCover 𝒜).openCover.iSup_opensRange
    change (⨆ i : Σ n : PNat, 𝒜 n,
      (Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2).opensRange) = ⊤ at hh
    simpa only [Proj.opensRange_awayι] using hh
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := @IsClosedImmersion) (f := Proj.map f hf)
    (fun i : Σ n : PNat, 𝒜 n => Proj.basicOpen 𝒜 (i.2 : A)) hc ?_
  intro i
  have he : (Proj.map f hf ∣_ Proj.basicOpen 𝒜 (i.2 : A)) =
      (Proj.basicOpenIsoSpec ℬ (f i.2) (f.2 i.2.2) i.1.2).hom ≫
        Spec.map (CommRingCat.ofHom (R := Away 𝒜 (i.2 : A))
          (S := Away ℬ (f i.2)) (Away.map f i.2)) ≫
          (Proj.basicOpenIsoSpec 𝒜 (i.2 : A) i.2.2 i.1.2).inv := by
    have hcomm := Proj.awayι_comp_map f hf i.1.2 (i.2 : A) i.2.2
    apply (cancel_mono (Proj.basicOpen 𝒜 (i.2 : A)).ι).mp
    rw [morphismRestrict_ι]
    change (Proj.basicOpen ℬ (f i.2)).ι ≫ Proj.map f hf =
      (Proj.basicOpenIsoSpec ℬ (f i.2) (f.2 i.2.2) i.1.2).hom ≫
        (Spec.map (CommRingCat.ofHom (R := Away 𝒜 (i.2 : A))
          (S := Away ℬ (f i.2)) (Away.map f i.2)) ≫
          Proj.awayι 𝒜 (i.2 : A) i.2.2 i.1.2)
    rw [← hcomm]
    simp only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (R := Away 𝒜 (i.2 : A)) (S := Away ℬ (f i.2)) (Away.map f i.2))) :=
    IsClosedImmersion.spec_of_surjective _
      (gradedAwayMap_surjective 𝒜 ℬ f hsur i.2 i.2.2)
  rw [he]
  infer_instance

end ClosedGradedMap

/-- The literal trace surface is a closed subscheme of the smooth proper threefold. -/
theorem surfaceToFiber_isClosedImmersion : IsClosedImmersion surfaceToFiber := by
  let : IsSeparated incidenceParameter := by unfold incidenceParameter; infer_instance
  let : IsClosedImmersion (surfaceToFiber ≫ pullback.snd incidenceParameter (familyToParameters 57)) := by
    rw [surfaceToFiber, pullback.lift_snd]
    exact projectiveMap_closedImmersion (familyGrade 57) G toSurfaceGraded irrelevant_le graded_surjective
  exact IsClosedImmersion.of_comp surfaceToFiber (pullback.snd incidenceParameter (familyToParameters 57))

end CycleQ2LiteralAmbientSurface

#print axioms CycleQ2LiteralAmbientSurface.surfaceToFiber_overComplex
#print axioms CycleQ2LiteralAmbientSurface.surfaceToFiber_isClosedImmersion
