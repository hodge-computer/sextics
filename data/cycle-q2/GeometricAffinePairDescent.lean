import Proposal.GeometricUnframedTensorAssembly
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! Descent on framed curve opens for arbitrary tensor coefficients.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
noncomputable section

namespace CycleQ2AffinePairDescent
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Module TensorProduct
open CycleQ2RectangleBasisGluing (Index)
open scoped TensorProduct KaehlerDifferential

variable {k : Type} [Field k] {C : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 p]

private theorem cover (U : C.Opens) : U ≤ ⨆ i : Index p U, i.1.1 := by
  intro x hx
  obtain ⟨W,hW,hxW,hWU⟩ := (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis p 1)) hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨W,hW⟩,hWU⟩,hxW⟩

private theorem finite_cover {U : C.Opens} (hU : IsAffineOpen U) :
    ∃ L : Finset (Index p U), U ≤ ⨆ i : (L : Set (Index p U)), i.1.1.1 := by
  classical
  obtain ⟨L,hL⟩ := hU.isCompact.elim_finite_subcover (fun i : Index p U => (i.1.1 : Set C))
    (fun i => i.1.1.isOpen) (by intro x hx; exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp (cover p U hx)))
  refine ⟨L,?_⟩
  intro x hx
  obtain ⟨i,hi,hm⟩ := Set.mem_iUnion₂.mp (hL hx)
  exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hm⟩

variable (D : TopCat.Sheaf AddCommGrpCat.{0} C)
private abbrev restriction {U V : C.Opens} (h : V ≤ U) := D.obj.map (homOfLE h).op
private theorem restriction_comp {U V W : C.Opens} (h : W ≤ V) (g : V ≤ U) (x : D.obj.obj (op U)) :
    restriction D h (restriction D g x) = restriction D (h.trans g) x := by
  rw [restriction,restriction,← ConcreteCategory.comp_apply,← D.obj.map_comp]
  rfl

private theorem glue {U : C.Opens} (y : (i : Index p U) → D.obj.obj (op i.1.1))
    (hy : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1), restriction D h (y j) = y i) :
    ∃! s : D.obj.obj (op U), ∀ i : Index p U, restriction D i.2 s = y i := by
  apply D.existsUnique_gluing' (fun i : Index p U => i.1.1) U _ (cover p U) y
  intro i j
  let O := i.1.1 ⊓ j.1.1
  apply D.eq_of_locally_eq' (fun t : Index p O => t.1.1) O (fun t => homOfLE t.2) (cover p O)
  intro t
  let a : Index p U := ⟨t.1,(t.2.trans inf_le_left).trans i.2⟩
  change restriction D t.2 (restriction D (inf_le_left : O ≤ _) (y i)) =
    restriction D t.2 (restriction D (inf_le_right : O ≤ _) (y j))
  rw [restriction_comp,restriction_comp]
  exact (hy a i (t.2.trans inf_le_left)).trans (hy a j (t.2.trans inf_le_right)).symm

private theorem coordinate_res {P Q T : Type} [AddCommGroup P] [Module k P] [AddCommGroup Q]
    [Module k Q] [AddCommGroup T] [Module k T] {ι : Type} [DecidableEq ι]
    (b : Basis ι k T) (f : P →ₗ[k] Q) (t : P ⊗[k] T) (i : ι) :
    equivFinsuppOfBasisRight b (TensorProduct.map f LinearMap.id t) i =
      f (equivFinsuppOfBasisRight b t i) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp only [map_tmul,LinearMap.id_apply,equivFinsuppOfBasisRight_apply_tmul_apply,map_smul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

variable (M : C.Opens → ModuleCat.{0} k)
  (r : ∀ {W Z : C.Opens}, W ≤ Z → M Z →ₗ[k] M W)
  (e : ∀ W : C.Opens, IsAffineOpen W → M W ≃+ D.obj.obj (op W))
  (natural : ∀ {W Z : C.Opens} (h : W ≤ Z) (hW : IsAffineOpen W) (hZ : IsAffineOpen Z) (s : M Z),
    restriction D h (e Z hZ s) = e W hW (r h s))
  {T : Type} [AddCommGroup T] [Module k T]

set_option maxHeartbeats 1600000 in
include natural in
private theorem tensor_glue {U : C.Opens} (hU : IsAffineOpen U)
    (x : (i : Index p U) → (M i.1.1 ⊗[k] T))
    (hx : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1),
      TensorProduct.map (r h) LinearMap.id (x j) = x i) :
    ∃! z : M U ⊗[k] T, ∀ i : Index p U, TensorProduct.map (r i.2) LinearMap.id z = x i := by
  classical
  let b := Basis.ofVectorSpace k T
  let coord (i : Index p U) := equivFinsuppOfBasisRight b (x i)
  let y (a : Basis.ofVectorSpaceIndex k T) (i : Index p U) := e i.1.1 i.1.2.1 (coord i a)
  have hy (a) (i j : Index p U) (h : i.1.1 ≤ j.1.1) : restriction D h (y a j) = y a i := by
    unfold y coord
    rw [natural, ← coordinate_res, hx i j h]
  choose u hu hu_unique using fun a => glue p D (y a) (hy a)
  obtain ⟨L,hL⟩ := finite_cover p hU
  let S := L.biUnion fun i => (coord i).support
  have hbound (a) (ha : a ∉ S) : u a = 0 := by
    apply D.eq_of_locally_eq' (fun i : (L : Set (Index p U)) => i.1.1.1) U (fun i => homOfLE i.1.2) hL
    intro i
    change restriction D i.1.2 (u a) = restriction D i.1.2 0
    rw [map_zero,hu]
    have h : a ∉ (coord i.1).support := fun hm => ha (Finset.mem_biUnion.mpr ⟨i.1,i.2,hm⟩)
    exact (congrArg (e i.1.1.1 i.1.1.2.1) (Finsupp.notMem_support_iff.mp h)).trans (map_zero _)
  let s := Finsupp.onFinset S (fun a => (e U hU).symm (u a))
    (fun a ha => by_contra fun h => ha (by rw [hbound a h,map_zero]))
  let z := (equivFinsuppOfBasisRight b).symm s
  have hzcoord : equivFinsuppOfBasisRight b z = s := (equivFinsuppOfBasisRight b).apply_symm_apply s
  refine ⟨z,?_,?_⟩
  · intro i
    apply (equivFinsuppOfBasisRight b).injective
    ext a
    rw [coordinate_res]
    rw [hzcoord]
    change r i.2 ((e U hU).symm (u a)) = coord i a
    apply (e i.1.1 i.1.2.1).injective
    rw [← natural i.2 i.1.2.1 hU,AddEquiv.apply_symm_apply]
    exact hu a i
  · intro z' hz'
    apply (equivFinsuppOfBasisRight b).injective
    ext a
    rw [hzcoord]
    change equivFinsuppOfBasisRight b z' a = (e U hU).symm (u a)
    apply (e U hU).injective
    rw [AddEquiv.apply_symm_apply]
    apply hu_unique a
    intro i
    rw [natural,← coordinate_res,hz']

open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)

def functionsMod (W : C.Opens) : ModuleCat.{0} k :=
  letI := (sectionCoefficients p W).toAlgebra
  ModuleCat.of k Γ(C,W)

def formsMod (W : C.Opens) : ModuleCat.{0} k :=
  letI := (sectionCoefficients p W).toAlgebra
  ModuleCat.of k Ω[Γ(C,W)⁄k]

abbrev functionsMap {Z W : C.Opens} (h : W ≤ Z) : functionsMod p Z →ₗ[k] functionsMod p W :=
  letI := (sectionCoefficients p W).toAlgebra
  letI := (sectionCoefficients p Z).toAlgebra
  (restrict p h).toLinearMap

abbrev formsMap {Z W : C.Opens} (h : W ≤ Z) : formsMod p Z →ₗ[k] formsMod p W :=
  letI := (sectionCoefficients p W).toAlgebra
  letI := (sectionCoefficients p Z).toAlgebra
  CycleQ2NativeCurveTraceComplex.pullLinear (restrict p h)

theorem functions {U : C.Opens} (hU : IsAffineOpen U) (T : Type) [AddCommGroup T] [Module k T]
    (x : (i : Index p U) → (functionsMod p i.1.1 ⊗[k] T))
    (hx : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1),
      TensorProduct.map (functionsMap p h) LinearMap.id (x j) = x i) :
    ∃! z : functionsMod p U ⊗[k] T, ∀ i : Index p U, TensorProduct.map (functionsMap p i.2) LinearMap.id z = x i :=
  tensor_glue p (CycleQ2GeometricProjectiveHOne.structureAdditiveSheaf C) (functionsMod p) (functionsMap p)
    (fun W _ => AddEquiv.refl (functionsMod p W)) (fun _ _ _ _ => rfl) hU x hx

theorem forms [CharZero k] {U : C.Opens} (hU : IsAffineOpen U) (T : Type) [AddCommGroup T] [Module k T]
    (x : (i : Index p U) → (formsMod p i.1.1 ⊗[k] T))
    (hx : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1),
      TensorProduct.map (formsMap p h) LinearMap.id (x j) = x i) :
    ∃! z : formsMod p U ⊗[k] T, ∀ i : Index p U, TensorProduct.map (formsMap p i.2) LinearMap.id z = x i :=
  tensor_glue p (CycleQ2RankOneDifferentialSheaf.oneForms p) (formsMod p) (formsMap p)
    (CycleQ2RankOneAffineForms.affineForms p) (fun h hW hZ ω =>
      CycleQ2RankOneAffineForms.restrict_affine p h hZ hW ω) hU x hx

end CycleQ2AffinePairDescent

namespace CycleQ2AffinePairDescent
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped TensorProduct KaehlerDifferential
open CycleQ2OrdinaryTensorRows (ordinary)
open CycleQ2RectangleBasisGluing (Index)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2NativeCurveTraceComplex (pullLinear)
open CycleQ2UnframedTensorNaturality (formLinear)
open CycleQ2WeightedCoordinateExterior (Form)

variable {k : Type} [Field k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k))
  {U W : C.Opens} (V : X.Opens)

private theorem fixed_target (d : ℕ) :
    letI := (sectionCoefficients q V).toAlgebra
    formLinear (restrict q (le_refl V)) d = LinearMap.id := by
  let := (sectionCoefficients q V).toAlgebra
  rw [CycleQ2FramedAffineSite.restrict_id q V]
  exact LinearMap.ext (CycleQ2AffineDeRhamFunctorial.exteriorPullback_id d)

set_option maxHeartbeats 1600000 in
private theorem row_zero (h : W ≤ U) (x : ordinary p q U V 0) :
    letI := (sectionCoefficients p U).toAlgebra
    letI := (sectionCoefficients p W).toAlgebra
    letI := (sectionCoefficients q V).toAlgebra
    CycleQ2OrdinaryTensorRows.map p q h (le_refl V) 0 x =
      TensorProduct.map (restrict p h).toLinearMap LinearMap.id x := by
  let := (sectionCoefficients p U).toAlgebra
  let := (sectionCoefficients p W).toAlgebra
  let := (sectionCoefficients q V).toAlgebra
  change TensorProduct.map _ (formLinear (restrict q (le_refl V)) 0) x = _
  rw [fixed_target q V 0]

set_option maxHeartbeats 1600000 in
private theorem row_succ (h : W ≤ U) (n : ℕ) (x : ordinary p q U V (n+1)) :
    letI := (sectionCoefficients p U).toAlgebra
    letI := (sectionCoefficients p W).toAlgebra
    letI := (sectionCoefficients q V).toAlgebra
    CycleQ2OrdinaryTensorRows.map p q h (le_refl V) (n+1) x =
      (TensorProduct.map (restrict p h).toLinearMap LinearMap.id x.1,
       TensorProduct.map (pullLinear (restrict p h)) LinearMap.id x.2) := by
  let := (sectionCoefficients p U).toAlgebra
  let := (sectionCoefficients p W).toAlgebra
  let := (sectionCoefficients q V).toAlgebra
  change (TensorProduct.map _ (formLinear (restrict q (le_refl V)) (n+1)) x.1,
    TensorProduct.map _ (formLinear (restrict q (le_refl V)) n) x.2) = _
  rw [fixed_target q V (n+1), fixed_target q V n]

/-- The ordinary affine product row is recovered from its restrictions to every
framed affine curve patch, using the same maps as the signed tensor complex. -/
theorem ordinary_glue [CharZero k] [SmoothOfRelativeDimension 1 p] (hU : IsAffineOpen U) (n : ℕ)
    (y : (i : Index p U) → ordinary p q i.1.1 V n)
    (hy : ∀ (i j : Index p U) (h : i.1.1 ≤ j.1.1),
      CycleQ2OrdinaryTensorRows.map p q h (le_refl V) n (y j) = y i) :
    ∃! x : ordinary p q U V n, ∀ i : Index p U,
      CycleQ2OrdinaryTensorRows.map p q i.2 (le_refl V) n x = y i := by
  let := (sectionCoefficients q V).toAlgebra
  cases n with
  | zero =>
    obtain ⟨s,hs,hu⟩ := functions p hU (Form k Γ(X,V) 0) y (fun i j h =>
      (row_zero p q V h (y j)).symm.trans (hy i j h))
    refine ⟨s, fun i => (row_zero p q V i.2 s).trans (hs i), ?_⟩
    intro a ha
    exact hu a (fun i => (row_zero p q V i.2 a).symm.trans (ha i))
  | succ n =>
    obtain ⟨a,ha,ua⟩ := functions p hU (Form k Γ(X,V) (n+1)) (fun i => (y i).1)
      (fun i j h => congrArg Prod.fst ((row_succ p q V h n (y j)).symm.trans (hy i j h)))
    obtain ⟨b,hb,ub⟩ := forms p hU (Form k Γ(X,V) n) (fun i => (y i).2)
      (fun i j h => congrArg Prod.snd ((row_succ p q V h n (y j)).symm.trans (hy i j h)))
    refine ⟨(a,b),fun i => (row_succ p q V i.2 n (a,b)).trans (Prod.ext (ha i) (hb i)),?_⟩
    rintro ⟨u,v⟩ h
    apply Prod.ext
    · exact ua u (fun i => congrArg Prod.fst ((row_succ p q V i.2 n (u,v)).symm.trans (h i)))
    · exact ub v (fun i => congrArg Prod.snd ((row_succ p q V i.2 n (u,v)).symm.trans (h i)))

end CycleQ2AffinePairDescent

namespace CycleQ2UnframedProductChain

open AlgebraicGeometry TopologicalSpace CategoryTheory
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
    (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
    [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]

/-- On an affine curve open the tensor rows give the actual relative de Rham complex
of its product with a framed target open. -/
def affineIso {U : C.Opens} (hU : IsAffineOpen U) (V : FramedOpen q m) :
    source p q m U V ≅ native p q m U V.1 :=
  isoOfDescent p q m U V (fun n => CycleQ2AffinePairDescent.ordinary_glue p q V.1 hU n)

@[simp] theorem affineIso_hom {U : C.Opens} (hU : IsAffineOpen U) (V : FramedOpen q m) :
    (affineIso p q m hU V).hom = chainMap p q m U V := by
  apply HomologicalComplex.hom_ext
  intro i
  rfl

end CycleQ2UnframedProductChain
#print axioms CycleQ2UnframedProductChain.affineIso
