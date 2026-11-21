import Proposal.GeometricMonicGenericSupport
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.BifunctorHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy

/-! The proper-curve trace on degree-two de Rham hypercohomology agrees with the
Laurent trace on the overlap of the two affine curve charts. On the tensor
complex, cup product with a degree-one curve cocycle followed by this trace
lowers degree by one and depends only on the cohomology class of the cocycle.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

noncomputable section
set_option autoImplicit false

namespace CycleQ2CurveTraceComparison
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2ClosedSupportCohomology (sectionBoundary sectionBoundary_zero_iff)
open CycleQ2ClosedSupportBoundary (sectionBoundary_map)
open CycleQ2HypercohomologyTraceGluing (source cohomologyDerivative)
open CycleQ2TwoTermTopComparison (topMap topMap_surjective)
open CycleQ2TwoTermTopQuotient (topMap_zero_iff upperDerivative)
open CycleQ2RankOneDifferentialSheaf (oneForms derivative functions)
open CycleQ2RankOneAffineForms (affineForms restrict_affine affine_derivative forms_HOne)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2FiniteCurveCover (square zero_affine infinity_affine torus_affine)
open CycleQ2NativeCurveTraceComplex (complex)

local instance (X : TopCat.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance (X : TopCat.{0}) : HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _

section
variable {Y : TopCat.{0}} {F G : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}}
  (d : F ⟶ G) (S : (Opens.grothendieckTopology Y).MayerVietorisSquare)
private def overlapMap : ↑(G.obj.obj (op S.X₁)) →+ ↑(CycleQ2CurveHypercohomologyClass.space d S) := by
  letI : AddCommGroup (Abelian.Ext (source S) G 1) := inferInstanceAs (AddCommGroup ↑(G.H' 1 S.X₄))
  exact (topMap d (source S)).comp (sectionBoundary G S)

theorem class_zero_iff (hF : Function.Surjective (sectionBoundary F S)) (z : G.obj.obj (op S.X₁)) :
    CycleQ2CurveHypercohomologyClass.ofOverlap d S z = 0 ↔
      ∃ (a : G.obj.obj (op S.X₂)) (b : G.obj.obj (op S.X₃)) (f : F.obj.obj (op S.X₁)),
        G.obj.map S.f₁₂.op a - G.obj.map S.f₁₃.op b - d.hom.app (op S.X₁) f = z := by
  change topMap d (source S) (sectionBoundary G S z) = 0 ↔ _
  erw [topMap_zero_iff]
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨f,rfl⟩ := hF x
    rw [cohomologyDerivative,sectionBoundary_map] at hx
    have hz : sectionBoundary G S (z + d.hom.app (op S.X₁) f) = 0 := by
      rw [map_add,← hx,neg_add_cancel]
    obtain ⟨a,b,h⟩ := (sectionBoundary_zero_iff G S _).mp hz
    exact ⟨a,b,f,by rw [h,add_sub_cancel_right]⟩
  · rintro ⟨a,b,f,rfl⟩
    refine ⟨sectionBoundary F S f,?_⟩
    have hab := (sectionBoundary_zero_iff G S _).mpr ⟨a,b,rfl⟩
    rw [cohomologyDerivative,sectionBoundary_map,map_sub,hab,zero_sub]
end

variable (k : Type) [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ line k)
  [IsFinite q] [IsDominant q] [SmoothOfRelativeDimension 1 (q ≫ structureMap k)]

private abbrev S := square k q
private abbrev p := q ≫ structureMap k

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance : HasDerivedCategory.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  HasDerivedCategory.standard _

def toDerived : (complex k q).X 2 →+ CycleQ2ProperCurveTrace.TopDeRham k q :=
  (overlapMap (derivative (p k q)) (S k q)).comp
    (affineForms (p k q) (S k q).X₁ (torus_affine k q)).toAddMonoidHom

theorem toDerived_surjective : Function.Surjective (toDerived k q) := by
  let S := square k q
  let p := q ≫ structureMap k
  have h₂ : Subsingleton ((functions (X := X)).H' 2 S.X₄) :=
    CycleQ2StructureAffineTwoCover.HTwo S (torus_affine k q) (zero_affine k q) (infinity_affine k q)
  let : Subsingleton ((oneForms p).H' 1 S.X₂) := forms_HOne p (zero_affine k q)
  let : Subsingleton ((oneForms p).H' 1 S.X₃) := forms_HOne p (infinity_affine k q)
  exact (topMap_surjective (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (derivative p) (source S) h₂).comp
    ((CycleQ2ProjectiveLineFunctions.boundary_surjective (oneForms p) S).comp
      (affineForms p S.X₁ (torus_affine k q)).surjective)

theorem toDerived_zero_iff (ω : (complex k q).X 2) :
    toDerived k q ω = 0 ↔ ∃ x : (complex k q).X 1, (complex k q).d 1 2 x = ω := by
  let S := square k q
  let p := q ≫ structureMap k
  let F := functions (X := X)
  let G := oneForms p
  let e := affineForms p S.X₁ (torus_affine k q)
  let eA := affineForms p S.X₂ (zero_affine k q)
  let eB := affineForms p S.X₃ (infinity_affine k q)
  have hF : Function.Surjective (sectionBoundary F S) :=
    CycleQ2StructureAffineTwoCover.boundary_surjective S (zero_affine k q) (infinity_affine k q)
  change CycleQ2CurveHypercohomologyClass.ofOverlap (derivative p) S (e ω) = 0 ↔ _
  erw [class_zero_iff (derivative p) S hF (e ω)]
  have hd (x : (complex k q).X 1) :
      e ((complex k q).d 1 2 x) =
      G.obj.map S.f₁₂.op (eA x.2.1) - G.obj.map S.f₁₃.op (eB x.2.2) -
        (derivative p).hom.app (op S.X₁) x.1 := by
    let u := CycleQ2NativeTraceRestrictions.formRestriction p S.f₁₂.le x.2.1
    let v := CycleQ2NativeTraceRestrictions.formRestriction p S.f₁₃.le x.2.2
    let df := CycleQ2NativeTraceRestrictions.section_d p S.X₁ x.1
    have hu : e u = G.obj.map S.f₁₂.op (eA x.2.1) :=
      (restrict_affine p S.f₁₂.le (zero_affine k q) (torus_affine k q) x.2.1).symm
    have hv : e v = G.obj.map S.f₁₃.op (eB x.2.2) :=
      (restrict_affine p S.f₁₃.le (infinity_affine k q) (torus_affine k q) x.2.2).symm
    have hf : e df = (derivative p).hom.app (op S.X₁) x.1 :=
      (affine_derivative p S.X₁ (torus_affine k q) x.1).symm
    change e (u-v-df) = _
    rw [map_sub,map_sub,hu,hv,hf]
  constructor
  · rintro ⟨a,b,f,h⟩
    refine ⟨⟨f,eA.symm a,eB.symm b⟩,e.injective ?_⟩
    refine (hd ⟨f,eA.symm a,eB.symm b⟩).trans ?_
    simpa only [AddEquiv.apply_symm_apply] using h
  · rintro ⟨x,rfl⟩
    exact ⟨eA x.2.1,eB x.2.2,x.1,(hd x).symm⟩

theorem trace_toDerived (ω : (complex k q).X 2) :
    CycleQ2ProperCurveTrace.trace k q (toDerived k q ω) =
      (((CycleQ2NativeCurveTraceComplex.traceMap k q).f 2 ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 2 (ModuleCat.of k k)).hom) ω) := by
  rw [CycleQ2NativeCurveTraceComplex.degreeTwo]
  unfold CycleQ2ProperCurveTrace.trace
  erw [show toDerived k q ω = topMap (C := Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) (derivative (p k q)) (source (S k q))
    (sectionBoundary (oneForms (p k q)) (S k q)
      (affineForms (p k q) (S k q).X₁ (torus_affine k q) ω)) from rfl,
      CycleQ2HypercohomologyTraceGluing.hyperTrace_boundary]
  change CycleQ2ProperCurveOverlapTrace.overlapTrace k q
    ((affineForms (p k q) (S k q).X₁ (torus_affine k q)).symm
      ((affineForms (p k q) (S k q).X₁ (torus_affine k q)) ω)) = _
  erw [AddEquiv.symm_apply_apply]
  rfl

private abbrev T := (complex k q).sc 2

omit [SmoothOfRelativeDimension 1 (q ≫ structureMap k)] in
private theorem outgoing_zero : (T k q).g = 0 := by
  change (complex k q).d 2 ((ComplexShape.up ℕ).next 2) = 0
  rw [(ComplexShape.up ℕ).next_eq' (j := 3) (by rfl)]
  rfl

/-- The ordinary projection of top cochains to the cohomology of the very complex
used as the curve factor in the product integration. -/
def topClass : (complex k q).X 2 →+ (complex k q).homology 2 :=
  ((T k q).pOpcycles ≫ ((T k q).asIsoHomologyι (outgoing_zero k q)).inv).hom.toAddMonoidHom

omit [SmoothOfRelativeDimension 1 (q ≫ structureMap k)] in
private theorem topClass_surjective : Function.Surjective (topClass k q) := by
  let φ := (T k q).pOpcycles ≫ ((T k q).asIsoHomologyι (outgoing_zero k q)).inv
  exact (ModuleCat.epi_iff_surjective φ).mp inferInstance

omit [SmoothOfRelativeDimension 1 (q ≫ structureMap k)] in
private theorem topClass_zero_iff (ω : (complex k q).X 2) :
    topClass k q ω = 0 ↔ ∃ x : (complex k q).X 1, (complex k q).d 1 2 x = ω := by
  have hi := (ModuleCat.mono_iff_injective ((T k q).asIsoHomologyι (outgoing_zero k q)).inv).mp inferInstance
  change ((T k q).asIsoHomologyι (outgoing_zero k q)).inv ((T k q).pOpcycles ω) = 0 ↔ _
  erw [← map_zero ((T k q).asIsoHomologyι (outgoing_zero k q)).inv.hom, hi.eq_iff,
      (T k q).moduleCat_pOpcycles_eq_zero_iff]
  change (∃ x, (complex k q).d ((ComplexShape.up ℕ).prev 2) 2 x = ω) ↔ _
  rw [show (ComplexShape.up ℕ).prev 2 = 1 from (ComplexShape.up ℕ).prev_eq' (by rfl)]

def comparisonMap : (complex k q).homology 2 →+ CycleQ2ProperCurveTrace.TopDeRham k q :=
  AddMonoidHom.liftOfSurjective (topClass k q) (topClass_surjective k q)
    ⟨toDerived k q,fun ω hω => (toDerived_zero_iff k q ω).mpr ((topClass_zero_iff k q ω).mp hω)⟩

@[simp]
theorem comparisonMap_topClass (ω : (complex k q).X 2) :
    comparisonMap k q (topClass k q ω) = toDerived k q ω := by
  simp [comparisonMap]

def comparison : (complex k q).homology 2 ≃+ CycleQ2ProperCurveTrace.TopDeRham k q :=
  AddEquiv.ofBijective (comparisonMap k q) ⟨by
    apply (injective_iff_map_eq_zero (comparisonMap k q)).mpr
    intro z hz
    obtain ⟨ω,rfl⟩ := topClass_surjective k q z
    rw [comparisonMap_topClass] at hz
    exact (topClass_zero_iff k q ω).mpr ((toDerived_zero_iff k q ω).mp hz),
  by
    intro y
    obtain ⟨ω,rfl⟩ := toDerived_surjective k q y
    exact ⟨_,comparisonMap_topClass k q ω⟩⟩

@[simp]
theorem comparison_topClass (ω : (complex k q).X 2) :
    comparison k q (topClass k q ω) = toDerived k q ω :=
  comparisonMap_topClass k q ω

open HomologicalComplex

/-- On all degree-two classes, the de Rham hypercohomology trace
is the map on cohomology of the residue morphism used in the cylinder
tensor complex. -/
theorem trace_comparison (x : (complex k q).homology 2) :
    CycleQ2ProperCurveTrace.trace k q (comparison k q x) =
    ((homologyMap (CycleQ2NativeCurveTraceComplex.traceMap k q) 2 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℕ) 2 (ModuleCat.of k k)).hom) x) := by
  obtain ⟨ω,rfl⟩ := topClass_surjective k q x
  rw [comparison_topClass,trace_toDerived]
  let α := CycleQ2NativeCurveTraceComplex.traceMap k q
  let e := (T k q).asIsoHomologyι (outgoing_zero k q)
  let A := ModuleCat.of k k
  let M := (single (ModuleCat.{0} k) (ComplexShape.up ℕ) 2).obj A
  have hn : e.inv ≫ homologyMap α 2 ≫ M.homologyι 2 = opcyclesMap α 2 := by
    erw [homologyι_naturality]
    change e.inv ≫ e.hom ≫ _ = _
    erw [Iso.inv_hom_id_assoc]
  have h : (complex k q).pOpcycles 2 ≫ e.inv ≫ homologyMap α 2 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℕ) 2 A).hom =
      α.f 2 ≫ (singleObjXSelf (ComplexShape.up ℕ) 2 A).hom := by
    erw [← homologyι_singleObjOpcyclesSelfIso_inv,← Category.assoc (homologyMap α 2),
      ← Category.assoc e.inv,hn,p_opcyclesMap_assoc,pOpcycles_singleObjOpcyclesSelfIso_inv]
  exact congrArg (fun f => (f : (complex k q).X 2 ⟶ A) ω) h.symm

open CycleQ2CurveTensorTrace (curve trace)
open CycleQ2NativeCurveTraceComplex (traceMap)

private abbrev E := ComplexShape.embeddingUpNat
private abbrev U := (single (ModuleCat.{0} k) (ComplexShape.up ℕ) 2).obj (ModuleCat.of k k)

omit [CharZero k] in
private theorem scalar_extension :
    homologyMap (extendSingleIso E (ModuleCat.of k k) 2 (2:ℤ) rfl).hom 2 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 2 (ModuleCat.of k k)).hom =
      ((U k).extendHomologyIso E (j := 2) (j' := 2) rfl).hom ≫
        (singleObjHomologySelfIso (ComplexShape.up ℕ) 2 (ModuleCat.of k k)).hom := by
  rw [← cancel_epi (((U k).extend E).homologyπ (2:ℤ))]
  erw [homologyπ_extendHomologyIso_hom_assoc (U k) E (j := 2) (j' := 2) rfl]
  simp only [homologyπ_naturality_assoc,
    homologyπ_singleObjHomologySelfIso_hom,singleObjCyclesSelfIso_hom,cyclesMap_i_assoc,
    extendCyclesIso_hom_iCycles_assoc (U k) E (j := 2) (j' := 2) rfl,
    extendSingleIso_hom_f E (ModuleCat.of k k) 2 (2:ℤ) rfl,Category.assoc,Iso.inv_hom_id,Category.comp_id]

def comparisonInt : (curve k q).homology 2 ≃+ CycleQ2ProperCurveTrace.TopDeRham k q :=
  (((complex k q).extendHomologyIso E (j := 2) (j' := 2) rfl).toLinearEquiv.toAddEquiv).trans
    (comparison k q)

/-- The integer-graded factor that is actually tensored with the target complex
induces the geometric finite-curve trace on every degree-two class. -/
theorem trace_tensor_factor (x : (curve k q).homology 2) :
    CycleQ2ProperCurveTrace.trace k q (comparisonInt k q x) =
    ((homologyMap (trace k q) 2 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 2 (ModuleCat.of k k)).hom) x) := by
  unfold comparisonInt
  rw [AddEquiv.trans_apply]
  rw [trace_comparison]
  have h : homologyMap (trace k q) 2 ≫
      (singleObjHomologySelfIso (ComplexShape.up ℤ) 2 (ModuleCat.of k k)).hom =
    ((complex k q).extendHomologyIso E (j := 2) (j' := 2) rfl).hom ≫
    homologyMap (traceMap k q) 2 ≫ (singleObjHomologySelfIso _ _ _).hom := by
    unfold trace
    erw [homologyMap_comp,Category.assoc,scalar_extension,
      extendHomologyIso_hom_naturality_assoc]
  exact congrArg (fun f => (f : (curve k q).homology 2 ⟶ ModuleCat.of k k) x) h.symm

end CycleQ2CurveTraceComparison

namespace CycleQ2CurveOnePairing

open scoped KaehlerDifferential
open CycleQ2ExactFrameThreeDeRham (onePullback onePullback_d)
open CategoryTheory AlgebraicGeometry TopologicalSpace

section Rings
variable {k A B R : Type} [Field k] [CommRing A] [CommRing B] [CommRing R]
  [Algebra k A] [Algebra k B] [Algebra k R]
variable (u : A →ₐ[k] R) (v : B →ₐ[k] R)

abbrev Cochain (k A B R : Type) [CommRing k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] := R × Ω[A⁄k] × Ω[B⁄k]

def Closed (z : Cochain k A B R) : Prop :=
  onePullback u z.2.1 - onePullback v z.2.2 = KaehlerDifferential.D k R z.1

def boundary (a : A) (b : B) : Cochain k A B R :=
  (u a - v b, KaehlerDifferential.D k A a, KaehlerDifferential.D k B b)

variable (τ : Ω[R⁄k] →ₗ[k] k)

def overlapCup (z x : Cochain k A B R) : Ω[R⁄k] :=
  z.1 • onePullback u x.2.1 - x.1 • onePullback v z.2.2

def pairing (z x : Cochain k A B R) : k := τ (overlapCup u v z x)

variable (hU : ∀ a, τ (onePullback u a) = 0)
  (hV : ∀ b, τ (onePullback v b) = 0)
  (hD : ∀ f, τ (KaehlerDifferential.D k R f) = 0)

include hU hV hD in
theorem pairing_boundary_right (z : Cochain k A B R) (hz : Closed u v z)
    (a : A) (b : B) : pairing u v τ z (boundary u v a b) = 0 := by
  have hu : τ (u a • onePullback u z.2.1) = 0 := by
    exact (congrArg τ ((onePullback u).map_smulₛₗ a z.2.1)).symm.trans (hU (a • z.2.1))
  have hv : τ (v b • onePullback v z.2.2) = 0 := by
    exact (congrArg τ ((onePullback v).map_smulₛₗ b z.2.2)).symm.trans (hV (b • z.2.2))
  have h := hD (z.1 * u a)
  rw [Derivation.leibniz, ← hz, smul_sub, map_add, map_sub, hu] at h
  change τ (z.1 • onePullback u ((KaehlerDifferential.D k A) a) -
    (u a - v b) • onePullback v z.2.2) = 0
  rw [onePullback_d u a, sub_smul, map_sub, map_sub, hv]
  linear_combination h

include hD in
theorem pairing_skew (z x : Cochain k A B R) (hz : Closed u v z) (hx : Closed u v x) :
    pairing u v τ z x + pairing u v τ x z = 0 := by
  have h := hD (z.1 * x.1)
  rw [Derivation.leibniz, ← hz, ← hx, smul_sub, smul_sub, map_add, map_sub, map_sub] at h
  simp only [pairing,overlapCup, map_sub]
  linear_combination h

def functional (z : Cochain k A B R) : Cochain k A B R →ₗ[k] k where
  toFun := pairing u v τ z
  map_add' x y := by
    change τ (z.1 • onePullback u (x.2.1 + y.2.1) -
      (x.1 + y.1) • onePullback v z.2.2) = _
    simp only [pairing,overlapCup, map_add, smul_add, add_smul, map_sub]
    abel
  map_smul' a x := by
    have h : onePullback u (a • x.2.1) = a • onePullback u x.2.1 :=
      (CycleQ2NativeCurveTraceComplex.pullLinear u).map_smul a x.2.1
    change τ (z.1 • onePullback u (a • x.2.1) -
      (a • x.1) • onePullback v z.2.2) = a • τ _
    rw [h, smul_comm z.1 a, smul_assoc a x.1, ← smul_sub, map_smul]
    rfl

theorem pairing_sub_left (z y x : Cochain k A B R) :
    pairing u v τ (z-y) x = pairing u v τ z x - pairing u v τ y x := by
  change τ ((z.1-y.1) • onePullback u x.2.1 - x.1 • onePullback v (z.2.2-y.2.2)) = _
  simp only [pairing,overlapCup,sub_smul,map_sub,smul_sub]
  abel

end Rings

theorem pairing_boundary_formula {k A B R : Type} [Field k] [CommRing A] [CommRing B] [CommRing R]
    [Algebra k A] [Algebra k B] [Algebra k R]
    (u : A →ₐ[k] R) (v : B →ₐ[k] R) (τ : Ω[R⁄k] →ₗ[k] k)
    (hU : ∀ a, τ (onePullback u a) = 0) (hV : ∀ b, τ (onePullback v b) = 0)
    (hD : ∀ f, τ (KaehlerDifferential.D k R f) = 0)
    (a : A) (b : B) (x : Cochain k A B R) :
    pairing u v τ (boundary u v a b) x =
      -τ (v b • (onePullback u x.2.1 - onePullback v x.2.2 - KaehlerDifferential.D k R x.1)) := by
  have hu : τ (u a • onePullback u x.2.1) = 0 :=
    (congrArg τ ((onePullback u).map_smulₛₗ a x.2.1)).symm.trans (hU _)
  have hv : τ (v b • onePullback v x.2.2) = 0 :=
    (congrArg τ ((onePullback v).map_smulₛₗ b x.2.2)).symm.trans (hV _)
  have h := hD (x.1 * v b)
  rw [Derivation.leibniz, map_add] at h
  change τ ((u a - v b) • onePullback u x.2.1 - x.1 • onePullback v ((KaehlerDifferential.D k B) b)) = _
  rw [onePullback_d, sub_smul, map_sub, map_sub, hu, smul_sub, smul_sub, map_sub, map_sub, hv]
  linear_combination -h

open HomologicalComplex
open CycleQ2NativeCurveTraceComplex (complex)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)

variable (k : Type) [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  (q : X ⟶ line k) [IsFinite q] [IsDominant q]

/-- Cup followed by the overlap trace, as a cochain map to the coefficient field
in degree one. The two restrictions and the derivative killed by the trace are
the ones on the actual inverse images of the projective-line charts. -/
def traceAgainst (z : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0) :
    complex k q ⟶ (single (ModuleCat.{0} k) (ComplexShape.up ℕ) 1).obj (ModuleCat.of k k) := by
  let S := CycleQ2FiniteCurveCover.square k q
  let p := q ≫ structureMap k
  letI (U : X.Opens) : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  let u := restrict p S.f₁₂.le
  let v := restrict p S.f₁₃.le
  let τ := CycleQ2CurveOverlapLinearTrace.overlapLinear k q
  have hc : Closed u v z := by
    apply sub_eq_zero.mp
    exact hz
  let z' : Cochain k Γ(X,S.X₂) Γ(X,S.X₃) Γ(X,S.X₁) := z
  let φ := ModuleCat.ofHom (functional u v τ z')
  refine mkHomToSingle φ (fun i hi => ?_)
  have ei : i = 0 := by change i+1 = 1 at hi; omega
  subst i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact pairing_boundary_right u v τ
    (CycleQ2ProperCurveOverlapTrace.restrict_zero k q)
    (CycleQ2ProperCurveOverlapTrace.restrict_infinity k q)
    (CycleQ2ProperCurveOverlapTrace.exact_zero k q) z hc x.1 x.2

/-- A degree-one functional that factors through the next differential is nullhomotopic. -/
private def boundaryHomotopy {V : Type*} [Category V] [Preadditive V] [Limits.HasZeroObject V]
    (K : CochainComplex V ℕ) {A : V}
    (φ : K ⟶ (single V (.up ℕ) 1).obj A) (ψ : K.X 2 ⟶ A)
    (hφ : φ.f 1 = K.d 1 2 ≫ ψ ≫ (singleObjXSelf (.up ℕ) 1 A).inv) : Homotopy φ 0 := by
  let S := (single V (.up ℕ) 1).obj A
  let s : ∀ n m : ℕ, K.X n ⟶ S.X m := fun n m => by
    by_cases hn : n = 2
    · subst n
      by_cases hm : m = 1
      · subst m
        exact ψ ≫ (singleObjXSelf (.up ℕ) 1 A).inv
      · exact 0
    · exact 0
  refine ⟨s,?_,?_⟩
  · intro n m h
    by_cases hn : n = 2 <;> by_cases hm : m = 1 <;> subst_vars <;> simp_all [s, ComplexShape.up_Rel]
  · intro n
    by_cases hn : n = 1
    · subst n
      rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel 1 2 from rfl),
        prevD_eq _ (show (ComplexShape.up ℕ).Rel 0 1 from rfl)]
      simpa [s] using hφ
    · exact (isZero_single_obj_X _ _ _ _ hn).eq_of_tgt _ _

def traceBoundaryHomotopy (a : (complex k q).X 0) :
    Homotopy (traceAgainst k q ((complex k q).d 0 1 a)
      (by exact congrArg (fun f : (complex k q).X 0 ⟶ (complex k q).X 2 => f a) ((complex k q).d_comp_d 0 1 2))) 0 := by
  let S := CycleQ2FiniteCurveCover.square k q
  let p := q ≫ structureMap k
  letI (U : X.Opens) : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  let u := restrict p S.f₁₂.le
  let v := restrict p S.f₁₃.le
  let τ := CycleQ2CurveOverlapLinearTrace.overlapLinear k q
  let ψ : Ω[Γ(X,S.X₁)⁄k] →ₗ[k] k :=
    - τ.comp ((v a.2) • LinearMap.id : Ω[Γ(X,S.X₁)⁄k] →ₗ[k] Ω[Γ(X,S.X₁)⁄k])
  apply boundaryHomotopy _ _ (ModuleCat.ofHom ψ)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact pairing_boundary_formula u v τ (CycleQ2ProperCurveOverlapTrace.restrict_zero k q)
    (CycleQ2ProperCurveOverlapTrace.restrict_infinity k q) (CycleQ2ProperCurveOverlapTrace.exact_zero k q)
    a.1 a.2 x

/-- Changing the time-curve representative by a boundary gives a cochain homotopy. -/
private def traceHomotopy (z y : (complex k q).X 1)
    (hz : (complex k q).d 1 2 z = 0) (hy : (complex k q).d 1 2 y = 0)
    (a : (complex k q).X 0) (ha : z-y = (complex k q).d 0 1 a) :
    Homotopy (traceAgainst k q z hz) (traceAgainst k q y hy) := by
  let S := CycleQ2FiniteCurveCover.square k q
  let p := q ≫ structureMap k
  letI (U : X.Opens) : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  let u := restrict p S.f₁₂.le
  let v := restrict p S.f₁₃.le
  let τ := CycleQ2CurveOverlapLinearTrace.overlapLinear k q
  refine Homotopy.equivSubZero.symm ?_
  refine (Homotopy.ofEq ?_).trans (traceBoundaryHomotopy k q a)
  apply to_single_hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change pairing u v τ z x - pairing u v τ y x = pairing u v τ ((complex k q).d 0 1 a) x
  exact (pairing_sub_left u v τ z y x).symm.trans (congrArg (fun t => pairing u v τ t x) ha)

/-- Tensoring the degree-one curve functional with horizontal cochains. -/
def cylinderOnTensor (z : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0)
    (L : CycleQ2CurveTensorTrace.C k) :
    tensorObj (CycleQ2CurveTensorTrace.curve k q) L ⟶
      tensorObj ((single (ModuleCat.{0} k) (ComplexShape.up ℤ) 1).obj (ModuleCat.of k k)) L :=
  tensorHom (extendMap (traceAgainst k q z hz) ComplexShape.embeddingUpNat ≫
    (extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of k k) 1 1 rfl).hom) (𝟙 L)
open CategoryTheory.MonoidalCategory
open CycleQ2CurveTensorTrace (C)
private abbrev mcat := ModuleCat.{0} k
/-- Placing the scalar factor in degree d shifts the horizontal complex by −d.
The comparison commutes with the sign on the first differential. -/
def scalarTensorInDegree (d : ℤ) (L : C k) :
    tensorObj ((single (mcat k) (ComplexShape.up ℤ) d).obj (ModuleCat.of k k)) L ≅ L⟦-d⟧ := by
  let A := tensorUnit (mcat k) (ComplexShape.up ℤ)
  let e := (((CochainComplex.singleFunctors (mcat k)).shiftIso (-d) d 0 (by omega)).app
    (ModuleCat.of k k)).symm
  exact (((curriedTensor (mcat k)).map₂CochainComplex).mapIso e).app L ≪≫
    CochainComplex.mapBifunctorShift₁Iso A L (curriedTensor (mcat k)) (-d) ≪≫
    (shiftFunctor (C k) (-d)).mapIso (HomologicalComplex.leftUnitor L)

/-- A closed degree-one time-curve cochain acts on the tensor model by a map
lowering total degree by one. In total degree four it takes values in degree three. -/
def cylinderInto (z : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0)
    (L : C k) : tensorObj (CycleQ2CurveTensorTrace.curve k q) L ⟶ L⟦(-1:ℤ)⟧ :=
  cylinderOnTensor k q z hz L ≫ (scalarTensorInDegree k 1 L).hom

/-- The action on horizontal cohomology depends only on the degree-one curve class.
In degree four it lands in degree three of the horizontal complex. -/
theorem cylinder_cohomologous (z y : (complex k q).X 1)
    (hz : (complex k q).d 1 2 z = 0) (hy : (complex k q).d 1 2 y = 0)
    (a : (complex k q).X 0) (ha : z-y = (complex k q).d 0 1 a)
    (L : C k) (n : ℤ) :
    homologyMap (cylinderInto k q z hz L) n = homologyMap (cylinderInto k q y hy L) n := by
  let e := extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of k k) 1 1 rfl
  let h := ((traceHomotopy k q z y hz hy a ha).extend ComplexShape.embeddingUpNat).compRight e.hom
  let H := (mapBifunctorMapHomotopy₁ h (𝟙 L) (curriedTensor (ModuleCat.{0} k)) (.up ℤ)).compRight
    (scalarTensorInDegree k 1 L).hom
  exact H.homologyMap_eq n

/-- The degree-two overlap representative for the product of the two degree-one
cochains, in the native two-chart complex of the finite curve. -/
def cupRepresentative (z x : (complex k q).X 1) : (complex k q).X 2 := by
  let S := CycleQ2FiniteCurveCover.square k q
  let p := q ≫ structureMap k
  letI (U : X.Opens) : Algebra k Γ(X,U) := (sectionCoefficients p U).toAlgebra
  let u := restrict p S.f₁₂.le
  let v := restrict p S.f₁₃.le
  exact overlapCup u v z x

/-- On a smooth finite cover of the projective line, the degree-one cochain
functional used in the cylinder is the proper curve's derived trace applied
to the class of its degree-two overlap representative. -/
theorem traceAgainst_eq_proper_trace [SmoothOfRelativeDimension 1 (q ≫ structureMap k)]
    (z x : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0) :
    (((traceAgainst k q z hz).f 1 ≫
      (singleObjXSelf (ComplexShape.up ℕ) 1 (ModuleCat.of k k)).hom) x) =
    CycleQ2ProperCurveTrace.trace k q
      (CycleQ2CurveTraceComparison.toDerived k q (cupRepresentative k q z x)) := by
  rw [CycleQ2CurveTraceComparison.trace_toDerived,CycleQ2NativeCurveTraceComplex.degreeTwo]
  rfl

end CycleQ2CurveOnePairing

namespace CycleQ2CurveOnePairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open CategoryTheory.MonoidalCategory
open CycleQ2CurveTensorTrace (C)
variable (k : Type) [Field k]
private abbrev F := curriedTensor (ModuleCat.{0} k)

private theorem shift_left_natural (K L M : C k) (r : L ⟶ M) (d : ℤ) :
    tensorHom (𝟙 (K⟦d⟧)) r ≫ (CochainComplex.mapBifunctorShift₁Iso K M (F k) d).hom =
    (CochainComplex.mapBifunctorShift₁Iso K L (F k) d).hom ≫ (tensorHom (𝟙 K) r)⟦d⟧' := by
  have h := NatTrans.shift_app_comm ((F k).map₂CochainComplex.flip.map r) d K
  rw [CategoryTheory.Functor.commShiftIso_map₂CochainComplex_flip_hom_app,
    CategoryTheory.Functor.commShiftIso_map₂CochainComplex_flip_hom_app] at h
  exact h.symm

private theorem scalar_natural (d : ℤ) (L M : C k) (r : L ⟶ M) :
    tensorHom (𝟙 ((single (ModuleCat.{0} k) (.up ℤ) d).obj (ModuleCat.of k k))) r ≫
      (scalarTensorInDegree k d M).hom =
    (scalarTensorInDegree k d L).hom ≫ r⟦-d⟧' := by
  let A := tensorUnit (ModuleCat.{0} k) (ComplexShape.up ℤ)
  let e := (((CochainComplex.singleFunctors (ModuleCat.{0} k)).shiftIso (-d) d 0 (by omega)).app
    (ModuleCat.of k k)).symm
  let η := ((F k).map₂CochainComplex).map e.hom
  have h₁ := η.naturality r
  have h₂ := shift_left_natural k A L M r (-d)
  have h₃ : tensorHom (𝟙 A) r ≫ (HomologicalComplex.leftUnitor M).hom =
      (HomologicalComplex.leftUnitor L).hom ≫ r := by
    suffices h : (HomologicalComplex.leftUnitor L).inv ≫ tensorHom (𝟙 A) r =
        r ≫ (HomologicalComplex.leftUnitor M).inv by
      rw [← cancel_epi (HomologicalComplex.leftUnitor L).inv,← Category.assoc,h]
      simp
    ext n : 1
    change (leftUnitor' L).inv n ≫ (tensorHom (𝟙 A) r).f n =
      r.f n ≫ (leftUnitor' M).inv n
    rw [leftUnitor'_inv,leftUnitor'_inv]
    simp [HomologicalComplex.ιTensorObj, HomologicalComplex.tensorHom,Category.assoc,A]
    rw [← whisker_exchange_assoc,← leftUnitor_inv_naturality_assoc]
  have unitor := congrArg (fun f => (shiftFunctor (C k) (-d)).map f) h₃
  erw [CategoryTheory.Functor.map_comp,CategoryTheory.Functor.map_comp] at unitor
  exact ((CommSq.mk h₁).vert_comp ((CommSq.mk h₂).vert_comp ⟨unitor⟩)).w

open CycleQ2NativeCurveTraceComplex (complex)
open CycleQ2CurveTensorTrace (curve)
open CycleQ2LaurentProjectiveLine (line)
variable [CharZero k] {X : Scheme.{0}} [IsIntegral X] (q : X ⟶ line k) [IsFinite q] [IsDominant q]

/-- The curve action commutes with horizontal restrictions. -/
theorem cylinder_natural (z : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0)
    (L M : C k) (r : L ⟶ M) :
    tensorHom (𝟙 (curve k q)) r ≫ cylinderInto k q z hz M =
      cylinderInto k q z hz L ≫ r⟦(-1:ℤ)⟧' := by
  let e := extendSingleIso ComplexShape.embeddingUpNat (ModuleCat.of k k) 1 1 rfl
  let t := extendMap (traceAgainst k q z hz) ComplexShape.embeddingUpNat ≫ e.hom
  let η := ((F k).map₂CochainComplex).map t
  exact ((CommSq.mk (η.naturality r)).vert_comp ⟨scalar_natural k 1 L M r⟩).w

theorem cylinder_restricts_zero (z : (complex k q).X 1) (hz : (complex k q).d 1 2 z = 0)
    (L M : C k) (r : L ⟶ M) (n : ℤ) (x : (tensorObj (curve k q) L).homology n)
    (hx : homologyMap (tensorHom (𝟙 (curve k q)) r) n x = 0) :
    homologyMap (r⟦(-1:ℤ)⟧') n (homologyMap (cylinderInto k q z hz L) n x) = 0 := by
  have h := congrArg (fun f => homologyMap f n) (cylinder_natural k q z hz L M r)
  rw [homologyMap_comp,homologyMap_comp] at h
  have hh := congrArg (fun f : (tensorObj (curve k q) L).homology n ⟶ (M⟦(-1:ℤ)⟧).homology n => f x) h
  change homologyMap (cylinderInto k q z hz M) n (homologyMap (tensorHom (𝟙 (curve k q)) r) n x) = _ at hh
  rw [hx] at hh
  exact hh.symm.trans (map_zero _)

end CycleQ2CurveOnePairing
#print axioms CycleQ2CurveOnePairing.cylinder_restricts_zero
#print axioms CycleQ2CurveOnePairing.traceAgainst_eq_proper_trace
#print axioms CycleQ2CurveTraceComparison.trace_tensor_factor
#print axioms CycleQ2CurveOnePairing.cylinder_cohomologous
