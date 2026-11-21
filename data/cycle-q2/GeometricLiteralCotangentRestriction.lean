import Proposal.GeometricLiteralCotangentEpsilon
import Proposal.GeometricLiteralCotangentOrderedLift
import Proposal.GeometricLiteralSurface
import Proposal.GeometricLiteralNativeDifferentialSections
import Proposal.GeometricSheafKaehlerMap

/-!
# Sections of the restricted cotangent sheaf from the native tensors

The pullback unit acts on the universal differential of a function on a
thick projective chart. Multiplication by a function of the closed chart
extends this operation to the reduced tensor product on that chart.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralCotangentRestriction

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralNativeCotangent CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveCotangent
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricAffineOverlap

open scoped TensorProduct

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower

section NativeSections

open CategoryTheory Opposite AlgebraicGeometry HomogeneousLocalization
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralAffineCotangent
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction CycleQ2CartierSurfaceGrading
  CycleQ2LiteralProjectiveDeformation CycleQ2GradedAwaySpecialization
  CycleQ2GeometricLiteralSurface CycleQ2LiteralProjectiveCotangent
  CycleQ2GeometricDifferentialSheaf CycleQ2LiteralCotangentEpsilon
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveDualFamily
  CycleQ2LiteralProjectiveComplexSplittings

open scoped DualNumber
attribute [local instance] CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra

private theorem chartReductionOfEq
    {A B : Type} [CommRing A] [CommRing B] [Algebra ℂ A] [Algebra ℂ B]
    (𝒜 : ℕ → Submodule ℂ A) (ℬ : ℕ → Submodule ℂ B) [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (u : A) (v : B) (e : f u = v) {n : ℕ} (hu : u ∈ 𝒜 n) (hv : v ∈ ℬ n)
    (hn : 0 < n) (z : Away 𝒜 u)
    (le : Proj.basicOpen ℬ v ≤ (Proj.map f hf) ⁻¹ᵁ Proj.basicOpen 𝒜 u) :
    (Proj ℬ).presheaf.map (homOfLE le).op
      ((Proj.map f hf).app (Proj.basicOpen 𝒜 u) (projChartSectionsEquiv 𝒜 u hu hn z)) =
      projChartSectionsEquiv ℬ v hv hn (awayMapOfEq f u v e z) := by
  subst v
  change (Proj ℬ).presheaf.map (𝟙 _) _ = _
  rw [(Proj ℬ).presheaf.map_id]
  exact projMap_app_basicOpen 𝒜 ℬ f hf u hu hn z

theorem nativeReduction_section (s : Finset Vertex) (hs : s.Nonempty) (b : ThickRing s) :
    ClosedSurface.presheaf.map (homOfLE (closedFiber_preimage_thickOpen s).symm.le).op
      (closedFiber.app (thickOpen s) (thickSectionsEquiv s hs b)) =
      closedSectionsEquiv s hs (nativeReduction s b) :=
  chartReductionOfEq deformationGrade (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1) reductionGraded reduction_irrelevant_le
    (thickProduct s) (closedProduct s) (reduction_thickProduct s)
    (thickProduct_homogeneous s) (closedProduct_homogeneous s) (productDegree_pos hs) b _

private theorem chartTopRestriction (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private theorem chartCoefficientOfSquare {A : Type} [CommRing A] [Algebra ℂ A]
    (𝒜 : ℕ → Submodule ℂ A) [GradedRing 𝒜] (x : A) {n : ℕ} (hx : x ∈ 𝒜 n) (hn : 0 < n)
    (R : CommRingCat.{0}) (p : Proj 𝒜 ⟶ Spec R) (i : R ⟶ CommRingCat.of (Away 𝒜 x))
    (h : Proj.awayι 𝒜 x hx hn ≫ p = Spec.map i) (r : R) :
    projChartSectionsEquiv 𝒜 x hx hn (i r) =
      (Proj 𝒜).presheaf.map (homOfLE (show Proj.basicOpen 𝒜 x ≤ ⊤ from le_top)).op
        (p.appTop ((Scheme.ΓSpecIso R).inv r)) := by
  have hg := congrArg (fun k => (Proj.basicOpenIsoSpec 𝒜 x hx hn).hom ≫ k) h
  have hg' : (Proj.basicOpen 𝒜 x).ι ≫ p =
      (Proj.basicOpenIsoSpec 𝒜 x hx hn).hom ≫ Spec.map i := by
    simpa only [Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc] using hg
  have hs := congrArg (fun k : (Proj.basicOpen 𝒜 x).toScheme ⟶ Spec R =>
    (Scheme.ΓSpecIso R).inv ≫ k.appTop ≫ (Proj.basicOpen 𝒜 x).topIso.hom) hg'
  simp only [Scheme.Hom.comp_appTop, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, chartTopRestriction] at hs
  exact (ConcreteCategory.congr_hom hs r).symm

theorem thickSectionsEquiv_complex (s : Finset Vertex) (hs : s.Nonempty) (c : ℂ) :
    thickSectionsEquiv s hs (algebraMap ℂ (ThickRing s) c) =
      coefficientOn projectiveDeformation.sheaf totalGlobalCoefficient (thickOpen s) c :=
  chartCoefficientOfSquare deformationGrade (thickProduct s) (thickProduct_homogeneous s)
    (productDegree_pos hs) (CommRingCat.of ℂ) deformationToComplex
    (CommRingCat.ofHom (thickCoefficient s)) (thickCoefficient_scheme s hs) c

theorem thickSectionsEquiv_epsilon (s : Finset Vertex) (hs : s.Nonempty) :
    thickSectionsEquiv s hs (nativeEpsilon s) =
      projectiveDeformation.presheaf.map (homOfLE (show thickOpen s ≤ ⊤ from le_top)).op totalEpsilon := by
  rw [← nativeDualCoefficient_epsilon]
  exact chartCoefficientOfSquare deformationGrade (thickProduct s) (thickProduct_homogeneous s)
    (productDegree_pos hs) (CommRingCat.of ℂ[ε]) firstOrderStructure
    (CommRingCat.ofHom (nativeDualCoefficient s)) (native_firstOrderStructure s hs) ε

end NativeSections

section BaseChange

variable {B C R M N : Type} [CommRing B] [CommRing C] [CommRing R] [Algebra B C]
  [AddCommGroup M] [Module B M] [AddCommGroup N] [Module R N]
  (c : C →+* R) (d : M →+ N)
  (hd : ∀ b m, d (b • m) = c (algebraMap B C b) • d m)

private def baseChange : C ⊗[B] M →+ N := by
  letI : Module C N := Module.compHom N c
  letI : Module B N := Module.compHom N (algebraMap B C)
  letI : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let l : M →ₗ[B] N := { d with map_smul' := hd }
  exact (l.liftBaseChange C).toAddMonoidHom

private theorem baseChange_tmul (a : C) (m : M) :
    baseChange c d hd (a ⊗ₜ[B] m) = c a • d m := by
  let : Module C N := Module.compHom N c
  let : Module B N := Module.compHom N (algebraMap B C)
  let : IsScalarTower B C N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let l : M →ₗ[B] N := { d with map_smul' := hd }
  exact LinearMap.liftBaseChange_tmul C l a m

end BaseChange

/-- The additive group of the native tensor module is generated by the pure
tensors with a universal function differential in their second factor. -/
theorem nativeTensor_induction (s : Finset Vertex) {P : NativeCotangent s → Prop} (hzero : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y))
    (hgen : ∀ (a : ClosedRing s) (b : ThickRing s),
      P (a ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b)) (z : NativeCotangent s) : P z := by
  induction z using TensorProduct.induction_on with
  | zero => exact hzero
  | add x y hx hy => exact hadd _ _ hx hy
  | tmul a ω =>
    have hω : ω ∈ Submodule.span (ThickRing s) (Set.range (KaehlerDifferential.D ℂ (ThickRing s))) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hω using Submodule.span_induction generalizing a with
    | mem _ h => obtain ⟨b,rfl⟩ := h; exact hgen a b
    | zero => simpa only [TensorProduct.tmul_zero] using hzero
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add]; exact hadd _ _ (hx _) (hy _)
    | smul b x _ hx =>
      rw [← TensorProduct.smul_tmul]
      exact hx _

private abbrev pullUnit := (Scheme.Modules.pullbackPushforwardAdjunction closedFiber).unit.app
  totalDifferentialSheaf

private def thickForm (s : Finset Vertex) (hs : s.Nonempty) :
    KaehlerDifferential ℂ (ThickRing s) →+
      ((Scheme.Modules.pushforward closedFiber).obj restrictedCotangentSheaf).val.obj (op (thickOpen s)) :=
  sectionLift projectiveDeformation.sheaf totalGlobalCoefficient
    ((Scheme.Modules.pushforward closedFiber).obj restrictedCotangentSheaf)
    ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).postcomp pullUnit.val)
    (thickOpen s) (thickSectionsEquiv s hs).toRingHom (thickSectionsEquiv_complex s hs)

private def reducedForm (s : Finset Vertex) (hs : s.Nonempty) :
    KaehlerDifferential ℂ (ThickRing s) →+ restrictedCotangentSheaf.val.obj (op (closedOpen s)) :=
  (restrictedCotangentSheaf.val.map (homOfLE (closedFiber_preimage_thickOpen s).symm.le).op).hom.toAddMonoidHom.comp
    (thickForm s hs)

private theorem reducedForm_smul (s : Finset Vertex) (hs : s.Nonempty)
    (b : ThickRing s) (ω : KaehlerDifferential ℂ (ThickRing s)) :
    reducedForm s hs (b • ω) = closedSectionsEquiv s hs (nativeReduction s b) • reducedForm s hs ω := by
  have h : thickForm s hs (b • ω) = thickSectionsEquiv s hs b • thickForm s hs ω :=
    sectionLift_smul projectiveDeformation.sheaf totalGlobalCoefficient _ _ _ _ _ b ω
  change restrictedCotangentSheaf.val.map _ (thickForm s hs (b • ω)) = _
  rw [h]
  change restrictedCotangentSheaf.val.map _ (closedFiber.app (thickOpen s) (thickSectionsEquiv s hs b) • _) = _
  rw [restrictedCotangentSheaf.val.map_smul]
  exact congrArg (fun a : Γ(ClosedSurface, closedOpen s) => a • reducedForm s hs ω)
    (nativeReduction_section s hs b)

def nativeTensorToSheaf (s : Finset Vertex) (hs : s.Nonempty) :
    NativeCotangent s →+ restrictedCotangentSheaf.val.obj (op (closedOpen s)) :=
  baseChange (closedSectionsEquiv s hs).toRingHom (reducedForm s hs) (reducedForm_smul s hs)

theorem nativeTensorToSheaf_tmul_D (s : Finset Vertex) (hs : s.Nonempty)
    (a : ClosedRing s) (b : ThickRing s) :
    nativeTensorToSheaf s hs (a ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b) =
      closedSectionsEquiv s hs a • restrictedCotangentSheaf.val.map
        (homOfLE (closedFiber_preimage_thickOpen s).symm.le).op
        (pullUnit.val.app (op (thickOpen s))
          ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d
            (thickSectionsEquiv s hs b))) := by
  rw [nativeTensorToSheaf, baseChange_tmul]
  have h : thickForm s hs (KaehlerDifferential.D ℂ (ThickRing s) b) =
      pullUnit.val.app (op (thickOpen s)) ((universalDifferential projectiveDeformation.sheaf
        totalGlobalCoefficient).d (thickSectionsEquiv s hs b)) :=
    sectionLift_D projectiveDeformation.sheaf totalGlobalCoefficient _ _ _ _ _ b
  exact congrArg (fun w => closedSectionsEquiv s hs a • restrictedCotangentSheaf.val.map
    (homOfLE (closedFiber_preimage_thickOpen s).symm.le).op w) h

private theorem restrictPulledDifferential {U U' : projectiveDeformation.Opens}
    {V V' : ClosedSurface.Opens} (i : U' ≤ U) (j : V' ≤ V)
    (h : V ≤ closedFiber ⁻¹ᵁ U) (h' : V' ≤ closedFiber ⁻¹ᵁ U') (x : Γ(projectiveDeformation, U)) :
    restrictedCotangentSheaf.val.map (homOfLE j).op
      (restrictedCotangentSheaf.val.map (homOfLE h).op (pullUnit.val.app (op U)
        ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d x))) =
    restrictedCotangentSheaf.val.map (homOfLE h').op (pullUnit.val.app (op U')
      ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d
        (projectiveDeformation.presheaf.map (homOfLE i).op x))) := by
  let d := universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient
  have hd : d.d (projectiveDeformation.presheaf.map (homOfLE i).op x) =
      totalDifferentialSheaf.val.map (homOfLE i).op (d.d x) := d.d_map (homOfLE i).op x
  have hn : pullUnit.val.app (op U') (totalDifferentialSheaf.val.map (homOfLE i).op (d.d x)) =
      restrictedCotangentSheaf.val.map (homOfLE (closedFiber.preimage_mono i)).op
        (pullUnit.val.app (op U) (d.d x)) :=
    PresheafOfModules.naturality_apply pullUnit.val (homOfLE i).op (d.d x)
  change _ = restrictedCotangentSheaf.val.map (homOfLE h').op (pullUnit.val.app (op U')
    (d.d (X := op U') (projectiveDeformation.presheaf.map (homOfLE i).op x)))
  rw [hd, hn, ← restrictedCotangentSheaf.val.map_comp_apply, ← restrictedCotangentSheaf.val.map_comp_apply]
  congr 2

open CycleQ2LiteralCotangentOrderedLift CycleQ2LiteralCotangentEpsilon

theorem nativeTensorToSheaf_restrict {s t : Finset Vertex} (hst : s ⊆ t) (hs : s.Nonempty)
    (ht : t.Nonempty) (z : NativeCotangent s) :
    restrictedCotangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeTensorToSheaf s hs z) =
      nativeTensorToSheaf t ht (nativeTensorRestriction hst z) := by
  induction z using nativeTensor_induction s with
  | hzero => simp only [map_zero]
  | hadd x y hx hy => simp only [map_add, hx, hy]
  | hgen a b =>
    rw [nativeTensorRestriction_tmul, differentialMap_D, nativeTensorToSheaf_tmul_D,
      nativeTensorToSheaf_tmul_D, restrictedCotangentSheaf.val.map_smul]
    change ClosedSurface.presheaf.map (homOfLE (closedOpen_mono hst)).op (closedSectionsEquiv s hs a) • _ = _
    rw [closedSectionsEquiv_restrict hs ht hst]
    apply congrArg (fun w => closedSectionsEquiv t ht (closedRestriction hst a) • w)
    exact (restrictPulledDifferential (thickOpen_mono hst) (closedOpen_mono hst)
      (closedFiber_preimage_thickOpen s).symm.le (closedFiber_preimage_thickOpen t).symm.le
      (thickSectionsEquiv s hs b)).trans
      (congrArg (fun y : Γ(projectiveDeformation, thickOpen t) =>
        restrictedCotangentSheaf.val.map (homOfLE (closedFiber_preimage_thickOpen t).symm.le).op
          (pullUnit.val.app (op (thickOpen t))
            ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d y)))
        (thickSectionsEquiv_restrict hs ht hst b))

private theorem restrictedEpsilon_on_subopen (U : projectiveDeformation.Opens)
    (V : ClosedSurface.Opens) (h : V ≤ closedFiber ⁻¹ᵁ U) :
    restrictedCotangentSheaf.val.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction closedFiber).unit.app
          totalDifferentialSheaf).val.app (op U)
            ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d
              (projectiveDeformation.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op totalEpsilon))) =
      restrictedCotangentSheaf.val.map (homOfLE (show V ≤ ⊤ from le_top)).op
        restrictedEpsilonDifferential := by
  let e := (Scheme.Modules.pullbackPushforwardAdjunction closedFiber).unit.app totalDifferentialSheaf
  let i := (homOfLE (show U ≤ ⊤ from le_top)).op
  let d := universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient
  have hd : d.d (projectiveDeformation.presheaf.map i totalEpsilon) =
      totalDifferentialSheaf.val.map i (d.d totalEpsilon) := d.d_map i totalEpsilon
  have hn : e.val.app (op U) (totalDifferentialSheaf.val.map i (d.d totalEpsilon)) =
      restrictedCotangentSheaf.val.map (homOfLE (show closedFiber ⁻¹ᵁ U ≤ ⊤ from le_top)).op
        restrictedEpsilonDifferential :=
    PresheafOfModules.naturality_apply e.val i (d.d totalEpsilon)
  change restrictedCotangentSheaf.val.map (homOfLE h).op (e.val.app (op U)
      (d.d (projectiveDeformation.presheaf.map i totalEpsilon))) = _
  rw [hd, hn]
  rw [← restrictedCotangentSheaf.val.map_comp_apply]
  congr 2

theorem nativeTensorToSheaf_epsilon (s : Finset Vertex) (hs : s.Nonempty) (a : ClosedRing s) :
    nativeTensorToSheaf s hs (nativeEpsilonInclusion s a) =
      epsilonInclusion.val.app (op (closedOpen s)) (closedSectionsEquiv s hs a) := by
  rw [nativeEpsilonInclusion_tmul, nativeTensorToSheaf_tmul_D, thickSectionsEquiv_epsilon,
    restrictedEpsilon_on_subopen, epsilonInclusion_apply]

private theorem reducedPullbackDifferential (U : projectiveDeformation.Opens)
    (b : Γ(projectiveDeformation,U)) (V : ClosedSurface.Opens) (h : V ≤ closedFiber ⁻¹ᵁ U) :
    cotangentReduction.val.app (op V)
      (restrictedCotangentSheaf.val.map (homOfLE h).op
        (((Scheme.Modules.pullbackPushforwardAdjunction closedFiber).unit.app
          totalDifferentialSheaf).val.app (op U)
            ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d b))) =
      (universalDifferential ClosedSurface.sheaf globalCoefficient).d
        (ClosedSurface.presheaf.map (homOfLE h).op (closedFiber.app U b)) := by
  have he := congrArg (fun f => f.val.app (op U)
    ((universalDifferential projectiveDeformation.sheaf totalGlobalCoefficient).d b))
    cotangentReduction_adjunct
  have hd := he.trans (pushedCotangentReduction_D U b)
  rw [PresheafOfModules.naturality_apply]
  exact (congrArg (fun x => originalDifferentialSheaf.val.map (homOfLE h).op x) hd).trans
    ((universalDifferential ClosedSurface.sheaf globalCoefficient).d_map
      (homOfLE h).op (closedFiber.app U b)).symm

private theorem nativeCotangentReduction_tmul_D (s : Finset Vertex) (a : ClosedRing s) (b : ThickRing s) :
    nativeCotangentReduction s (a ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b) =
      a • KaehlerDifferential.D ℂ (ClosedRing s) (nativeReduction s b) := by
  have he : a ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b =
      a • ((1 : ClosedRing s) ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) b) := by
    rw [TensorProduct.smul_tmul',smul_eq_mul,mul_one]
  rw [he, map_smul, nativeCotangentReduction_D]

theorem nativeTensorToSheaf_reduce (s : Finset Vertex) (hs : s.Nonempty) (z : NativeCotangent s) :
    cotangentReduction.val.app (op (closedOpen s)) (nativeTensorToSheaf s hs z) =
      nativeFormToSheaf s hs (nativeCotangentReduction s z) := by
  refine nativeTensor_induction s (P := fun w =>
    cotangentReduction.val.app (op (closedOpen s)) (nativeTensorToSheaf s hs w) =
      nativeFormToSheaf s hs (nativeCotangentReduction s w)) ?_ ?_ ?_ z
  · simp only [map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a b
    rw [nativeTensorToSheaf_tmul_D, (cotangentReduction.val.app _).hom.map_smul,
      reducedPullbackDifferential, nativeReduction_section, nativeCotangentReduction_tmul_D,
      nativeFormToSheaf_smul, nativeFormToSheaf_D]
    rfl

end CycleQ2LiteralCotangentRestriction

end

#print axioms CycleQ2LiteralCotangentRestriction.nativeTensorToSheaf_restrict
#print axioms CycleQ2LiteralCotangentRestriction.nativeTensorToSheaf_reduce
#print axioms CycleQ2LiteralCotangentRestriction.nativeTensorToSheaf_epsilon
