import Proposal.GeometricLiteralCotangentSplitIdentities
import Proposal.GeometricLiteralCotangentRestriction
import Proposal.GeometricLiteralNativeKodairaSpencerCocycle

/-!
# Chart splittings and evaluation of the surface cotangent extension

The affine splittings of the cotangent extension induce linear splittings
on every open contained in a native chart. Reduction and the epsilon
coordinate are computed in the original cotangent sequence.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 100000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAbelJacobiSplittingEvaluation

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricDifferentialSheaf
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralAffineCotangent CycleQ2LiteralProjectiveCotangent
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralCotangentAffineExact
  CycleQ2LiteralCotangentEpsilon CycleQ2LiteralCotangentReduction
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeTangentEvaluation
  CycleQ2LiteralCotangentRestriction CycleQ2LiteralNativeCotangent
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeCupSectionValues
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionComplex

open scoped TensorProduct

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower


/-- On every native form, the change of the two chart lifts is the epsilon inclusion
of the actual surface tangent evaluation. -/
theorem nativeSection_change (s : Finset Vertex) (hs : s.Nonempty) (u v : Vertex)
    (hu : u ∈ s) (hv : v ∈ s) (ω : KaehlerDifferential ℂ (ClosedRing s)) :
    nativeTensorToSheaf s hs (nativeCotangentSplitting s v.1 ⟨v.2,hv⟩ ω) -
      nativeTensorToSheaf s hs (nativeCotangentSplitting s u.1 ⟨u.2,hu⟩ ω) =
    epsilonInclusion.val.app (op (closedOpen s))
      (evaluateTangent (closedOpen s) (nativeKodairaSpencerSection s hs u v hu hv) (nativeFormToSheaf s hs ω)) := by
  have h := congrArg (nativeTensorToSheaf s hs) (nativeCotangentSplitting_change s u v hu hv ω)
  rw [map_sub, nativeTensorToSheaf_epsilon] at h
  exact h.trans (congrArg (epsilonInclusion.val.app _) (nativeTangent_on_form s hs _ ω).symm)


variable (s : Finset Vertex) (hs : s.Nonempty) (a : Fin 4) (ha : Admissible s a)
private abbrev LiftHom := LocalLinearHom Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf
private abbrev evalLift {U : Surface.Opens} (l : LiftHom U) :=
  localLinearHomEvaluate Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf U l
private abbrev restrictLift {U V : Surface.Opens} (h : V ≤ U) (l : LiftHom U) :=
  restrictLocalLinearHom Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf (homOfLE h).op l

private theorem eval_add {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens)
    (f g : LocalLinearHom X.sheaf M N U) (x : M.val.obj (op U)) :
    localLinearHomEvaluate X.sheaf M N U (f+g) x =
      localLinearHomEvaluate X.sheaf M N U f x + localLinearHomEvaluate X.sheaf M N U g x := rfl
private theorem tensorToSheaf_smul (c : ClosedRing s) (x : NativeCotangent s) :
    nativeTensorToSheaf s hs (c • x) = closedSectionsEquiv s hs c • nativeTensorToSheaf s hs x := by
  induction x using nativeTensor_induction s with
  | hzero => simp only [smul_zero, map_zero]
  | hadd x y hx hy => simp only [smul_add, map_add, hx, hy]
  | hgen b z =>
      let e := KaehlerDifferential.D ℂ (ThickRing s) z
      have ht := TensorProduct.smul_tmul' (R := ThickRing s) c b e
      exact (congrArg (nativeTensorToSheaf s hs) ht).trans <| by
        rw [nativeTensorToSheaf_tmul_D, nativeTensorToSheaf_tmul_D, smul_eq_mul, map_mul, smul_smul]


private abbrev Form (s : Finset Vertex) := KaehlerDifferential ℂ (ClosedRing s)
private abbrev Target (s : Finset Vertex) := restrictedCotangentSheaf.val.obj (op (closedOpen s))

private def difference (l : LiftHom (closedOpen s)) : Form s →+ Target s :=
  (nativeTensorToSheaf s hs).comp (nativeCotangentSplitting s a ha).toAddMonoidHom -
    (evalLift l).toAddMonoidHom.comp (nativeFormToSheaf s hs)

private theorem difference_smul (l : LiftHom (closedOpen s)) (c : ClosedRing s) (ω : Form s) :
    difference s hs a ha l (c • ω) = closedSectionsEquiv s hs c • difference s hs a ha l ω := by
  have h₁ := (congrArg (nativeTensorToSheaf s hs) ((nativeCotangentSplitting s a ha).map_smul c ω)).trans
    (tensorToSheaf_smul s hs c (nativeCotangentSplitting s a ha ω))
  have h₂ := (congrArg (evalLift l) (nativeFormToSheaf_smul s hs c ω)).trans
    ((evalLift l).map_smul (closedSectionsEquiv s hs c : Γ(Surface,closedOpen s)) (nativeFormToSheaf s hs ω))
  exact (congrArg₂ (· - ·) h₁ h₂).trans (smul_sub _ _ _).symm

private def correction (l : LiftHom (closedOpen s))
    (r : Target s →ₗ[Γ(Surface,closedOpen s)] Γ(Surface,closedOpen s)) :
    Form s →ₗ[ClosedRing s] ClosedRing s where
  toFun ω := (closedSectionsEquiv s hs).symm (r (difference s hs a ha l ω))
  map_add' ω η := by rw [map_add, map_add, map_add]
  map_smul' c ω := by
    let e := closedSectionsEquiv s hs
    have h := (congrArg r (difference_smul s hs a ha l c ω)).trans (r.map_smul (e c) _)
    change e.symm (r (difference s hs a ha l (c • ω))) = c * e.symm (r (difference s hs a ha l ω))
    exact (congrArg e.symm h).trans ((e.symm.map_mul _ _).trans (congrArg (· * _) (e.symm_apply_apply c)))

private def adjusted (l : LiftHom (closedOpen s))
    (r : Target s →ₗ[Γ(Surface,closedOpen s)] Γ(Surface,closedOpen s)) : LiftHom (closedOpen s) :=
  l + localLinearHomPostcompose Surface.sheaf originalDifferentialSheaf epsilonInclusion (closedOpen s)
    (nativeTangent s hs ((correction s hs a ha l r).compDer (KaehlerDifferential.D ℂ (ClosedRing s))))

private theorem add_correction {A : Type*} [AddCommGroup A] (x y : A) : x + (y - x) = y := by abel

private theorem adjusted_native (l : LiftHom (closedOpen s))
    (r : Target s →ₗ[Γ(Surface,closedOpen s)] Γ(Surface,closedOpen s))
    (hl : ∀ x, cotangentReduction.val.app (op (closedOpen s)) (evalLift l x) = x)
    (hr : ∀ x, cotangentReduction.val.app (op (closedOpen s)) x = 0 →
       epsilonInclusion.val.app (op (closedOpen s)) (r x) = x) (ω : Form s) :
    evalLift (adjusted s hs a ha l r) (nativeFormToSheaf s hs ω) =
      nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω) := by
  let d := difference s hs a ha l ω
  have hd : cotangentReduction.val.app (op (closedOpen s)) d = 0 := by
    dsimp only [d, difference, AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe]
    rw [map_sub, nativeTensorToSheaf_reduce, hl]
    have h := LinearMap.congr_fun (nativeCotangentReduction_splitting s a ha) ω
    change nativeCotangentReduction s (nativeCotangentSplitting s a ha ω) = ω at h
    rw [h]
    exact sub_self (nativeFormToSheaf s hs ω)
  let z := correction s hs a ha l r
  let δ := z.compDer (KaehlerDifferential.D ℂ (ClosedRing s))
  have he : δ.liftKaehlerDifferential = z :=
    Derivation.liftKaehlerDifferential_unique _ _ δ.liftKaehlerDifferential_comp
  unfold adjusted
  rw [eval_add, localLinearHomEvaluate_postcompose]
  change _ + epsilonInclusion.val.app _ (evaluateTangent _ (nativeTangent s hs δ) (nativeFormToSheaf s hs ω)) = _
  rw [nativeTangent_on_form, he]
  change _ + epsilonInclusion.val.app _ ((closedSectionsEquiv s hs) ((closedSectionsEquiv s hs).symm (r d))) = _
  rw [RingEquiv.apply_symm_apply, hr _ hd]
  exact add_correction (evalLift l (nativeFormToSheaf s hs ω)) (nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω))
private theorem nativeSplit_restrict_D {t : Finset Vertex} (hst : s ⊆ t) (b : ClosedRing s) :
    CycleQ2LiteralCotangentOrderedLift.nativeTensorRestriction hst
      (nativeCotangentSplitting s a ha (KaehlerDifferential.D ℂ (ClosedRing s) b)) =
    nativeCotangentSplitting t a (admissible_mono hst ha)
      (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst b)) := by
  unfold nativeCotangentSplitting
  rw [CycleQ2GeometricSquareZeroReducedCotangent.splittingLift_D,
      CycleQ2GeometricSquareZeroReducedCotangent.splittingLift_D]
  change CycleQ2LiteralCotangentOrderedLift.nativeTensorRestriction hst
    ((1 : ClosedRing s) ⊗ₜ[ThickRing s] KaehlerDifferential.D ℂ (ThickRing s) (projectiveSplittingAlgHom s a ha b)) =
    (1 : ClosedRing t) ⊗ₜ[ThickRing t] KaehlerDifferential.D ℂ (ThickRing t)
      (projectiveSplittingAlgHom t a (admissible_mono hst ha) (closedRestrictionAlgHom hst b))
  rw [CycleQ2LiteralCotangentOrderedLift.nativeTensorRestriction_tmul, CycleQ2GeometricAffineOverlap.differentialMap_D,
    map_one, projectiveSplittingAlgHom_restrict]

private theorem nativeLift_ext (f g : LiftHom (closedOpen s))
    (h : ∀ b : ClosedRing s, evalLift f (nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) b)) =
      evalLift g (nativeFormToSheaf s hs (KaehlerDifferential.D ℂ (ClosedRing s) b))) : f = g := by
  apply (localLinearHomEquiv Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf (closedOpen s)).injective
  apply CycleQ2GeometricDifferentialRestriction.restrictedLift_unique Surface.sheaf
    CycleQ2LiteralNativeDifferentialSections.globalCoefficient (closedOpen s) (restrictedCotangentSheaf.over (closedOpen s))
  apply CycleQ2GeometricDifferentialChartTransport.chartDerivation_ext (nativeChart s hs)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) (nativeChart_coefficient s hs)
    (restrictedCotangentSheaf.over (closedOpen s))
  intro b
  have he := (nativeFormToSheaf_D s hs b).trans
    (congrArg ((universalDifferential Surface.sheaf CycleQ2LiteralNativeDifferentialSections.globalCoefficient).d
      (X := op (closedOpen s))) (nativeChart_section s hs b).symm)
  exact (congrArg (evalLift f) he).symm.trans ((h b).trans (congrArg (evalLift g) he))

include hs in
private theorem localizedForm_ext {t : Finset Vertex} (hst : s ⊆ t) {N : Type}
    [AddCommGroup N] [Module (ClosedRing t) N]
    (f g : KaehlerDifferential ℂ (ClosedRing t) →ₗ[ClosedRing t] N)
    (h : ∀ b : ClosedRing s,
      f (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst b)) =
      g (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst b))) : f = g := by
  letI := (closedRestrictionAlgHom hst).toRingHom.toAlgebra
  letI : IsScalarTower ℂ (ClosedRing s) (ClosedRing t) := IsScalarTower.of_algHom (closedRestrictionAlgHom hst)
  letI : IsLocalization.Away (CycleQ2LiteralNativeRestrictionLocalization.restrictionElement s t) (ClosedRing t) :=
    CycleQ2LiteralNativeRestrictionLocalization.closedRestriction_isLocalization hst hs
  letI : Module (ClosedRing s) N := Module.compHom N (algebraMap (ClosedRing s) (ClosedRing t))
  letI : IsScalarTower (ClosedRing s) (ClosedRing t) N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  apply LinearMap.restrictScalars_injective (ClosedRing s)
  apply IsLocalizedModule.ext (Submonoid.powers (CycleQ2LiteralNativeRestrictionLocalization.restrictionElement s t))
    (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t))
  · intro a
    exact (IsLocalization.map_units (ClosedRing t) a).map (Algebra.lsmul (ClosedRing s) (ClosedRing s) N)
  · apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation ℂ (ClosedRing s))
    intro b
    change f (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t) (KaehlerDifferential.D ℂ (ClosedRing s) b)) =
      g (KaehlerDifferential.map ℂ ℂ (ClosedRing s) (ClosedRing t) (KaehlerDifferential.D ℂ (ClosedRing s) b))
    rw [KaehlerDifferential.map_D]
    exact h b

private theorem restrict_twice {X : Scheme.{0}} (M N : X.Modules) {W V U : X.Opens}
    (h : W ≤ V) (k : V ≤ U) (f : LocalLinearHom X.sheaf M N U) :
    restrictLocalLinearHom X.sheaf M N (homOfLE (h.trans k)).op f =
      restrictLocalLinearHom X.sheaf M N (homOfLE h).op
        (restrictLocalLinearHom X.sheaf M N (homOfLE k).op f) :=
  ConcreteCategory.congr_hom ((moduleHomAdditivePresheaf X.sheaf M N).map_comp
    (homOfLE k).op (homOfLE h).op) f

private theorem evaluate_adjustment {X : Scheme.{0}} {M A N : X.Modules}
    (ε : A ⟶ N) {U W : X.Opens} (h : W ≤ U)
    (l : LocalLinearHom X.sheaf M N U) (t : LocalLinearHom X.sheaf M A U)
    (γ : M.val.obj (op W)) :
    localLinearHomEvaluate X.sheaf M N W
      (restrictLocalLinearHom X.sheaf M N (homOfLE h).op
        (l + localLinearHomPostcompose X.sheaf M ε U t)) γ =
      localLinearHomEvaluate X.sheaf M N W (restrictLocalLinearHom X.sheaf M N (homOfLE h).op l) γ +
        ε.val.app (op W) (localLinearHomEvaluate X.sheaf M A W
          (restrictLocalLinearHom X.sheaf M A (homOfLE h).op t) γ) := by
  have ha := (restrictLocalLinearHom X.sheaf M N (homOfLE h).op).map_add l
    (localLinearHomPostcompose X.sheaf M ε U t)
  exact (congrArg (fun k => localLinearHomEvaluate X.sheaf M N W k γ) ha).trans
    ((eval_add M N W _ _ γ).trans (congrArg (_ + ·)
      ((congrArg (fun k => localLinearHomEvaluate X.sheaf M N W k γ)
        (localLinearHomPostcompose_restrict X.sheaf M ε (homOfLE h).op t)).trans
        (localLinearHomEvaluate_postcompose X.sheaf M ε W _ γ))))

@[instance_reducible] private def nativeTargetModule (s : Finset Vertex) (hs : s.Nonempty) : Module (ClosedRing s) (Target s) :=
  Module.compHom _ (closedSectionsEquiv s hs).toRingHom

private def nativeEval (f : LiftHom (closedOpen s)) :
    letI := nativeTargetModule s hs
    KaehlerDifferential ℂ (ClosedRing s) →ₗ[ClosedRing s] Target s := by
  letI := nativeTargetModule s hs
  exact
    { toFun := fun ω => evalLift f (nativeFormToSheaf s hs ω)
      map_add' := fun ω η => by rw [map_add, map_add]
      map_smul' := fun c ω => by
        exact (congrArg (evalLift f) (nativeFormToSheaf_smul s hs c ω)).trans ((evalLift f).map_smul (closedSectionsEquiv s hs c : Γ(Surface,closedOpen s)) _) }

section Calibrated
variable (F : (s : Finset Vertex) → s.Nonempty → (a : Fin 4) → Admissible s a → LiftHom (closedOpen s))
  (hF : ∀ s hs a ha (ω : Form s), evalLift (F s hs a ha) (nativeFormToSheaf s hs ω) =
    nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω))

include hF in
private theorem chartHom_restrict {t : Finset Vertex} (ht : t.Nonempty) (hst : s ⊆ t) :
    restrictLift (closedOpen_mono hst) (F s hs a ha) =
      F t ht a (admissible_mono hst ha) := by
  letI := nativeTargetModule t ht
  let f := restrictLift (closedOpen_mono hst) (F s hs a ha)
  let g := F t ht a (admissible_mono hst ha)
  have he : nativeEval t ht f = nativeEval t ht g := by
    apply localizedForm_ext s hs hst
    intro b
    let ω := KaehlerDifferential.D ℂ (ClosedRing s) b
    have hr := localLinearHomEvaluate_restrict Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf
      (homOfLE (closedOpen_mono hst)) (F s hs a ha) (nativeFormToSheaf s hs ω)
    have hd := (nativeFormToSheaf_restrict hst hs ht ω).trans
      (congrArg (nativeFormToSheaf t ht) (CycleQ2GeometricAffineOverlap.differentialMap_D (closedRestrictionAlgHom hst) b))
    change evalLift f (nativeFormToSheaf t ht _) = evalLift g (nativeFormToSheaf t ht _)
    calc
      _ = evalLift f (originalDifferentialSheaf.val.map (homOfLE (closedOpen_mono hst)).op (nativeFormToSheaf s hs ω)) := congrArg (evalLift f) hd.symm
      _ = restrictedCotangentSheaf.val.map (homOfLE (closedOpen_mono hst)).op
          (evalLift (F s hs a ha) (nativeFormToSheaf s hs ω)) := hr
      _ = nativeTensorToSheaf t ht (CycleQ2LiteralCotangentOrderedLift.nativeTensorRestriction hst
          (nativeCotangentSplitting s a ha ω)) := by
        rw [hF, nativeTensorToSheaf_restrict]
      _ = nativeTensorToSheaf t ht (nativeCotangentSplitting t a (admissible_mono hst ha)
          (KaehlerDifferential.D ℂ (ClosedRing t) (closedRestrictionAlgHom hst b))) := by
        exact congrArg (nativeTensorToSheaf t ht) (nativeSplit_restrict_D s a ha hst b)
      _ = _ := (hF t ht a (admissible_mono hst ha) _).symm
  exact nativeLift_ext t ht f g (fun b => LinearMap.congr_fun he (KaehlerDifferential.D ℂ (ClosedRing t) b))

include hF in
private theorem chartHom_change (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    F s hs v.1 ⟨v.2,hv⟩ = F s hs u.1 ⟨u.2,hu⟩ +
      localLinearHomPostcompose Surface.sheaf originalDifferentialSheaf epsilonInclusion (closedOpen s)
        (nativeKodairaSpencerSection s hs u v hu hv) := by
  apply nativeLift_ext s hs
  intro b
  let ω := KaehlerDifferential.D ℂ (ClosedRing s) b
  change evalLift (F s hs v.1 ⟨v.2,hv⟩) (nativeFormToSheaf s hs ω) =
    evalLift (F s hs u.1 ⟨u.2,hu⟩) (nativeFormToSheaf s hs ω) +
    epsilonInclusion.val.app (op (closedOpen s)) (evaluateTangent (closedOpen s)
      (nativeTangent s hs (vertexKodairaSpencer s u v hu hv)) (nativeFormToSheaf s hs ω))
  rw [hF, hF]
  exact (sub_eq_iff_eq_add'.mp (nativeSection_change s hs u v hu hv ω))

private theorem singleton_le (u : Vertex) {W : Surface.Opens} (hu : W ≤ cover u) : W ≤ closedOpen {u} := by
  simpa only [closedOpen_eq, Finset.iInf_singleton, CycleQ2LiteralNativeGaugeSections.cover] using hu

/-- The splitting over every subopen of a vertex, calibrated against its original ring splitting. -/
private def splitFor (u : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) :
    originalDifferentialSheaf.val.obj (op W) →ₗ[Γ(Surface,W)] restrictedCotangentSheaf.val.obj (op W) :=
  evalLift (restrictLift (singleton_le u hu)
    (F {u} (Finset.singleton_nonempty u) u.1 ⟨u.2,Finset.mem_singleton_self u⟩))

private theorem splitFor_restrict (u : Vertex) {W V : Surface.Opens} (h : V ≤ W) (hu : W ≤ cover u)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    restrictedCotangentSheaf.val.map (homOfLE h).op (splitFor F u W hu γ) =
      splitFor F u V (h.trans hu) (originalDifferentialSheaf.val.map (homOfLE h).op γ) := by
  let H := restrictLift (singleton_le u hu)
    (F {u} (Finset.singleton_nonempty u) u.1 ⟨u.2,Finset.mem_singleton_self u⟩)
  have hcomp := restrict_twice originalDifferentialSheaf restrictedCotangentSheaf h (singleton_le u hu)
    (F {u} (Finset.singleton_nonempty u) u.1 ⟨u.2,Finset.mem_singleton_self u⟩)
  exact (localLinearHomEvaluate_restrict Surface.sheaf originalDifferentialSheaf restrictedCotangentSheaf (homOfLE h) H γ).symm.trans
    (congrArg (fun f => evalLift f (originalDifferentialSheaf.val.map (homOfLE h).op γ)) hcomp.symm)

include hF in
private theorem split_pair (u v : Vertex) (x : Vertex) (hx : x ∈ ({u,v} : Finset Vertex))
    (W : Surface.Opens) (hw : W ≤ closedOpen {u,v}) (hX : W ≤ cover x)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    splitFor F x W hX γ = evalLift (restrictLift hw (F {u,v} (by simp) x.1 ⟨x.2,hx⟩)) γ := by
  have hst : ({x} : Finset Vertex) ⊆ {u,v} := Finset.singleton_subset_iff.mpr hx
  have he := chartHom_restrict (F := F) (hF := hF) {x} (Finset.singleton_nonempty x) x.1
    ⟨x.2,Finset.mem_singleton_self x⟩ (by simp) hst
  have e := restrict_twice originalDifferentialSheaf restrictedCotangentSheaf hw (closedOpen_mono hst)
    (F {x} (Finset.singleton_nonempty x) x.1 ⟨x.2,Finset.mem_singleton_self x⟩)
  exact (congrArg (fun l => evalLift l γ) e).trans (congrArg (fun l => evalLift (restrictLift hw l) γ) he)

include hF in
private theorem splitFor_change (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    splitFor F v W hv γ - splitFor F u W hu γ = epsilonInclusion.val.app (op W)
      (evaluateTangent W (kodairaSpencerValue u v W hu hv) γ) := by
  let Wle := common_le_pair u v W hu hv
  rw [split_pair (F := F) (hF := hF) u v v (by simp) W Wle hv γ, split_pair (F := F) (hF := hF) u v u (by simp) W Wle hu γ]
  have he := congrArg (fun l => evalLift (restrictLift Wle l) γ)
    (chartHom_change (F := F) (hF := hF) {u,v} (by simp) u v (by simp) (by simp))
  exact sub_eq_iff_eq_add'.mpr (he.trans (evaluate_adjustment epsilonInclusion Wle _ _ γ))

end Calibrated

private theorem restrict_id {X : Scheme.{0}} (M N : X.Modules) (U : X.Opens) (l : LocalLinearHom X.sheaf M N U) :
    restrictLocalLinearHom X.sheaf M N (homOfLE (le_refl U)).op l = l :=
  ConcreteCategory.congr_hom ((moduleHomAdditivePresheaf X.sheaf M N).map_id (op U)) l

private theorem comp_zero_apply {X : Scheme.{0}} {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P)
    (h : f ≫ g = 0) (W : X.Opens) (c : M.val.obj (op W)) :
    g.val.app (op W) (f.val.app (op W) c) = 0 :=
  congrArg (fun k => k.val.app (op W) c) h

private theorem calibrate (l : LiftHom (closedOpen s))
    (r : Target s →ₗ[Γ(Surface,closedOpen s)] Γ(Surface,closedOpen s))
    (hQ : ∀ (W : Surface.Opens) (h : W ≤ closedOpen s) (γ : originalDifferentialSheaf.val.obj (op W)),
      cotangentReduction.val.app (op W) (evalLift (restrictLift h l) γ) = γ)
    (hE : ∀ x, cotangentReduction.val.app (op (closedOpen s)) x = 0 →
      epsilonInclusion.val.app (op (closedOpen s)) (r x) = x) :
    ∃ H : LiftHom (closedOpen s),
      (∀ ω : Form s, evalLift H (nativeFormToSheaf s hs ω) =
        nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω)) ∧
      ∀ (W : Surface.Opens) (h : W ≤ closedOpen s) (γ : originalDifferentialSheaf.val.obj (op W)),
        cotangentReduction.val.app (op W) (evalLift (restrictLift h H) γ) = γ := by
  refine ⟨adjusted s hs a ha l r, adjusted_native s hs a ha l r ?_ hE, ?_⟩
  · intro γ
    have hi := restrict_id originalDifferentialSheaf restrictedCotangentSheaf (closedOpen s) l
    exact (congrArg (fun k => cotangentReduction.val.app (op (closedOpen s)) (evalLift k γ)) hi.symm).trans
      (hQ (closedOpen s) le_rfl γ)
  · intro W h γ
    let δ := (correction s hs a ha l r).compDer (KaehlerDifferential.D ℂ (ClosedRing s))
    let t := nativeTangent s hs δ
    let c := evaluateTangent W (tangentSheaf.val.map (homOfLE h).op t) γ
    have he : cotangentReduction.val.app (op W) (epsilonInclusion.val.app (op W) c) = 0 :=
      comp_zero_apply epsilonInclusion cotangentReduction
        CycleQ2LiteralCotangentEpsilonKernel.epsilonInclusion_cotangentReduction W c
    have hp := evaluate_adjustment epsilonInclusion h l t γ
    exact (congrArg (cotangentReduction.val.app (op W)) hp).trans
      (((cotangentReduction.val.app (op W)).hom.map_add _ _).trans
        ((congrArg₂ (· + ·) (hQ W h γ) he).trans (add_zero γ)))

private theorem calibrated_exists :
    ∃ H : LiftHom (closedOpen s),
      (∀ ω : Form s, evalLift H (nativeFormToSheaf s hs ω) =
        nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω)) ∧
      ∀ (W : Surface.Opens) (h : W ≤ closedOpen s) (γ : originalDifferentialSheaf.val.obj (op W)),
        cotangentReduction.val.app (op W) (evalLift (restrictLift h H) γ) = γ := by
  obtain ⟨l,r,hQ,hE⟩ := CycleQ2LiteralCotangentSplitIdentities.chart s hs a ha
  exact calibrate s hs a ha l r hQ hE

private def chartHom : LiftHom (closedOpen s) := (calibrated_exists s hs a ha).choose

private theorem chartHom_native (ω : Form s) :
    evalLift (chartHom s hs a ha) (nativeFormToSheaf s hs ω) =
      nativeTensorToSheaf s hs (nativeCotangentSplitting s a ha ω) :=
  (calibrated_exists s hs a ha).choose_spec.1 ω

/-- The cotangent splitting of a vertex acts on all subopens of its chart. -/
def split (u : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) :
    originalDifferentialSheaf.val.obj (op W) →ₗ[Γ(Surface,W)] restrictedCotangentSheaf.val.obj (op W) :=
  splitFor chartHom u W hu

theorem split_restrict (u : Vertex) {W V : Surface.Opens} (h : V ≤ W) (hu : W ≤ cover u)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    restrictedCotangentSheaf.val.map (homOfLE h).op (split u W hu γ) =
      split u V (h.trans hu) (originalDifferentialSheaf.val.map (homOfLE h).op γ) :=
  splitFor_restrict chartHom u h hu γ

theorem split_reduce (u : Vertex) (W : Surface.Opens) (hu : W ≤ cover u)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    cotangentReduction.val.app (op W) (split u W hu γ) = γ :=
  (calibrated_exists {u} (Finset.singleton_nonempty u) u.1 ⟨u.2,Finset.mem_singleton_self u⟩).choose_spec.2 W (singleton_le u hu) γ

/-- On a common subopen the difference of the two vertex splittings is the epsilon
inclusion of the genuine Kodaira–Spencer tangent applied to the given one-form. -/
theorem split_change (u v : Vertex) (W : Surface.Opens) (hu : W ≤ cover u) (hv : W ≤ cover v)
    (γ : originalDifferentialSheaf.val.obj (op W)) :
    split v W hv γ - split u W hu γ = epsilonInclusion.val.app (op W)
      (evaluateTangent W (kodairaSpencerValue u v W hu hv) γ) :=
  splitFor_change (F := chartHom) (hF := chartHom_native) u v W hu hv γ

end CycleQ2LiteralAbelJacobiSplittingEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiSplittingEvaluation.split_restrict
#print axioms CycleQ2LiteralAbelJacobiSplittingEvaluation.split_reduce
#print axioms CycleQ2LiteralAbelJacobiSplittingEvaluation.split_change
