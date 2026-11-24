import Proposal.GeometricLiteralOrbitAction
import Proposal.GeometricLiteralAmbientCylinder

/-! The diagonal cubic-root action on the fixed projective sextic and its trace surface.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitAction

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceFamilyContainment
  CycleQ2LiteralAmbientCylinder CycleQ2LiteralAmbientSurface CycleQ2LiteralAmbientSmooth
  CycleQ2SeedCyclicAction CycleQ2LiteralOrbitAction CycleQ2GeometricCartierNormalLift
  CycleQ2CartierProjectiveCover CycleQ2GeometricSurfaceCoefficients
  CycleQ2SeedProjectiveFamily CycleQ2GeometricSeedNormalIdeals CycleQ2ConormalJacobian

def char (z : ℂ) : Fin 5 → ℂ := ![z^2,z^2,z,1,1]

theorem action_X (z : ℂ) (j : Fin 5) : polynomialAction z (X j) = C (char z j) * X j := by
  fin_cases j <;> simp [actionValues, char]

theorem char_cube (z : ℂ) (hz : z^3 = 1) (j : Fin 5) : char z j ^ 3 = 1 := by
  have h : (z^2)^3 = 1 := by rw [← pow_mul, Nat.mul_comm, pow_mul, hz, one_pow]
  fin_cases j <;> simp [char, hz, h]

theorem polynomialAction_cube (z : ℂ) (hz : z^3 = 1) (p : MvPolynomial (Fin 5) ℂ) :
    polynomialAction z (polynomialAction z (polynomialAction z p)) = p := by
  let f := polynomialAction z
  have he : f.comp (f.comp f) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [f, AlgHom.comp_apply, action_X, map_mul, polynomialAction_C, AlgHom.id_apply]
    have h : (C (char z i) : MvPolynomial (Fin 5) ℂ)^3 = 1 := by
      rw [← map_pow, char_cube z hz, map_one]
    linear_combination X i * h
  exact AlgHom.congr_fun he p

theorem equation_fixed (z : ℂ) (hz : z^3 = 1) :
    polynomialAction z (pointEquationF point) = pointEquationF point := by
  rw [CycleQ2IncidenceChartSeedFiber.literal_pointEquationF]
  exact polynomialAction_smoothF z hz _ _

def nativeRingAction (z : ℂ) (hz : z^3 = 1) : SexticRing point →ₐ[ℂ] SexticRing point :=
  Ideal.quotientMapₐ (sexticIdeal point) (polynomialAction z) (by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change polynomialAction z (pointEquationF point) ∈ sexticIdeal point
    rw [equation_fixed z hz]
    exact Ideal.subset_span (Set.mem_singleton _))

def nativeGradedAction (z : ℂ) (hz : z^3 = 1) : sexticGrade point →+*ᵍ sexticGrade point where
  toRingHom := (nativeRingAction z hz).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨polynomialAction z p, polynomialAction_weighted z hp, rfl⟩

theorem nativeGradedAction_cube (z : ℂ) (hz : z^3 = 1) (x : SexticRing point) :
    nativeGradedAction z hz (nativeGradedAction z hz (nativeGradedAction z hz x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (Ideal.Quotient.mk (sexticIdeal point)) (polynomialAction_cube z hz p)

def nativeAction (z : ℂ) (hz : z^3 = 1) : Native ≅ Native :=
  cyclicProjIso (nativeGradedAction z hz) (nativeGradedAction_cube z hz)

def threefoldAction (z : ℂ) (hz : z^3 = 1) : IncidenceFiber 57 ≅ IncidenceFiber 57 :=
  nativeToIncidence.symm ≪≫ nativeAction z hz ≪≫ nativeToIncidence

theorem nativeAction_overComplex (z : ℂ) (hz : z^3 = 1) :
    (nativeAction z hz).hom ≫ weightedThreefoldToBase point = weightedThreefoldToBase point := by
  apply projectiveMap_coefficientBase (nativeGradedAction z hz)
    (cyclic_irrelevant_le_map _ (nativeGradedAction_cube z hz))
  ext c
  exact (nativeRingAction z hz).commutes c

theorem threefoldAction_overComplex (z : ℂ) (hz : z^3 = 1) :
    (threefoldAction z hz).hom ≫ incidenceFiberToComplex 57 = incidenceFiberToComplex 57 := by
  apply (cancel_epi nativeToIncidence.hom).mp
  simp [threefoldAction, nativeAction_overComplex]

private theorem nativeIdeal_le_surface : sexticIdeal point ≤ surfaceIdeal 57 1 := by
  apply (Ideal.span_singleton_le_iff_mem _).mpr
  rw [CycleQ2IncidenceChartSeedFiber.literal_pointEquationF,
    ← CycleQ2NormalConnecting.actualSeedEquation_eq_smoothF]
  exact Ideal.subset_span ⟨0,rfl⟩

def toTraceGraded : sexticGrade point →+*ᵍ CycleQ2CartierSurfaceGrading.surfaceGrade 57 1 where
  toRingHom := Ideal.Quotient.factor nativeIdeal_le_surface
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨p,hp,rfl⟩

theorem trace_irrelevant : HomogeneousIdeal.irrelevant (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1) ≤
    (HomogeneousIdeal.irrelevant (sexticGrade point)).map toTraceGraded := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  rintro n hn _ ⟨p,hp,rfl⟩
  exact Ideal.mem_map_of_mem toTraceGraded (HomogeneousIdeal.mem_irrelevant_of_mem
    (sexticGrade point) hn (show Ideal.Quotient.mk (sexticIdeal point) p ∈ sexticGrade point n from ⟨p,hp,rfl⟩))

def surfaceToNative : projectiveSurface 57 1 ⟶ Native := Proj.map toTraceGraded trace_irrelevant

theorem surfaceToNative_overComplex :
    surfaceToNative ≫ weightedThreefoldToBase point = projectiveToComplex 57 1 := by
  apply projectiveMap_coefficientBase toTraceGraded trace_irrelevant
  rfl

theorem surfaceToNative_toIncidence : surfaceToNative ≫ nativeToIncidence.hom = surfaceToFiber := by
  apply pullback.hom_ext
  · change _ ≫ nativeToIncidence.hom ≫ incidenceFiberToComplex 57 = _
    rw [nativeToIncidence_overComplex, surfaceToNative_overComplex]
    exact surfaceToFiber_overComplex.symm
  · rw [Category.assoc, nativeToIncidence_snd]
    change Proj.map _ _ ≫ Proj.map _ _ = surfaceToFiber ≫ _
    rw [surfaceToFiber, pullback.lift_snd, ← Proj.map_comp]
    have he : toTraceGraded.comp (CycleQ2LiteralAmbientProjFiberPolynomial.graded
        cubicEval (familyIdeal 57) (sexticIdeal point) cubicIdeal_map) = toSurfaceGraded := by
      apply GradedRingHom.ext
      intro x
      obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl
    simp only [he, surfaceToFamily]

theorem surfaceToNative_equivariant (z : ℂ) (hz : z^3 = 1) :
    surfaceToNative ≫ (nativeAction z hz).hom = (closedProjectiveAction z hz).hom ≫ surfaceToNative := by
  apply cyclicProjMap_naturality (nativeGradedAction z hz) (nativeGradedAction_cube z hz)
    (surfaceGradedAction z hz) (surfaceAction_cube z hz) toTraceGraded trace_irrelevant
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

theorem surfaceToFiber_equivariant (z : ℂ) (hz : z^3 = 1) :
    surfaceToFiber ≫ (threefoldAction z hz).hom = (closedProjectiveAction z hz).hom ≫ surfaceToFiber := by
  rw [← surfaceToNative_toIncidence]
  simp only [threefoldAction, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, surfaceToNative_equivariant, Category.assoc]

end CycleQ2LiteralThreefoldOrbitAction
end

#print axioms CycleQ2LiteralThreefoldOrbitAction.threefoldAction_overComplex
#print axioms CycleQ2LiteralThreefoldOrbitAction.surfaceToFiber_equivariant
