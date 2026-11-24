import Proposal.GeometricLogarithmicNonvanishing
import Proposal.GeometricSmoothSurfaceGysin
import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-! A closed overlap form defines a nonzero supported degree-four derived class when its
coefficient survives the Čech and de Rham differentials. On a nonempty smooth codimension-two
surface this detects any class with the prescribed logarithmic restrictions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2LogDetection
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian CategoryTheory.Pretriangulated TopologicalSpace
universe w v u
section Triangle
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C] [HasExt.{w} C]
private abbrev E := DerivedCategory.singleFunctor C 0
private abbrev F := shiftFunctor (DerivedCategory C) (1:ℤ)

/-- Exactness at the connecting map for any derived target, including an arbitrary
shift of a de Rham complex. -/
theorem extension_of_connecting_zero {S : ShortComplex C} (hS : S.ShortExact)
    {T : DerivedCategory C} (a : E.obj S.X₁ ⟶ T)
    (hz : hS.extClass.hom ≫ F.map a = 0) :
    ∃ b : E.obj S.X₂ ⟶ T, a = E.map S.f ≫ b := by
  rw [hS.extClass_hom] at hz
  let Δ := hS.singleTriangle
  have hΔ := rot_of_distTriang _ (rot_of_distTriang _ hS.singleTriangle_distinguished)
  obtain ⟨c,hc⟩ := Δ.rotate.rotate.yoneda_exact₂ hΔ (F.map a) hz
  simp only [Δ,Triangle.rotate_mor₂,Triangle.rotate_mor₃,ShortComplex.ShortExact.singleTriangle_mor₁] at hc
  refine ⟨F.preimage (-c), F.map_injective ?_⟩
  calc
    F.map a = (-F.map (E.map S.f)) ≫ c := hc
    _ = -(F.map (E.map S.f) ≫ c) := Preadditive.neg_comp _ _
    _ = F.map (E.map S.f) ≫ (-c) := (Preadditive.comp_neg _ _).symm
    _ = F.map (E.map S.f) ≫ F.map (F.preimage (-c)) :=
      congrArg (fun d => F.map (E.map S.f) ≫ d) (F.map_preimage (-c)).symm
    _ = F.map (E.map S.f ≫ F.preimage (-c)) := (F.map_comp _ _).symm

variable (K : CochainComplex C ℤ) (n : ℤ)

abbrev cutoff := (K.restriction (ComplexShape.embeddingUpIntLE n)).extend (ComplexShape.embeddingUpIntLE n)

/-- The canonical projection to the brutal upper truncation. -/
def cutoffMap : K ⟶ cutoff K n :=
  (ComplexShape.embeddingUpIntLE n).liftExtend (𝟙 _)
    (fun _ hj _ _ => hj.false_of_isTruncLE.elim)

omit [HasDerivedCategory C] [HasExt C] in
theorem cutoff_iso (i : ℤ) (hi : i ≤ n) : IsIso ((cutoffMap K n).f i) := by
  have h : (ComplexShape.embeddingUpIntLE n).f (n-i).toNat = i := by
    simp only [ComplexShape.embeddingUpIntLE_f,Int.toNat_of_nonneg (sub_nonneg.mpr hi)]
    omega
  apply ((ComplexShape.embeddingUpIntLE n).isIso_liftExtend_f_iff _ _ h).mpr
  simp only [HomologicalComplex.id_f]
  infer_instance

end Triangle

section Double
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2RelativeOpenSupport (shortExact relativeClass)
open CycleQ2DerivedOverlapClass (overlapClass sectionClass)
variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _
private abbrev G := DerivedCategory.singleFunctor (AbSheaf X) 0
private abbrev Q := DerivedCategory.Q (C := AbSheaf X)
variable {K : CochainComplex (AbSheaf X) ℤ}
    (q : ℤ) (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    {W : Opens X} (h : S.X₄ ≤ W)
    (z : S.shortComplex.X₁ ⟶ (K⟦q⟧).X 0) (hz : z ≫ (K⟦q⟧).d 0 1 = 0)

/-- If the class on the overlap does not extend from the two single opens and
there is no ambient class in degree q+1, its double connecting class is nonzero. -/
theorem relative_nonzero
    (ha : ∀ b : G.obj (freeOpen W) ⟶ (Q.obj K)⟦q+1⟧, b = 0)
    (hn : ¬ ∃ b : G.obj S.shortComplex.X₂ ⟶ (Q.obj K)⟦q⟧,
      sectionClass q z hz = G.map S.shortComplex.f ≫ b) :
    relativeClass q S h z hz ≠ 0 := by
  intro H
  let b := overlapClass q S z hz
  let J := (shiftFunctorAdd (DerivedCategory (AbSheaf X)) (q+1) 1).inv.app (Q.obj K)
  have h₁ : (shortExact h).extClass.hom ≫ F.map b = 0 := by
    apply (cancel_mono J).mp
    change (shortExact h).extClass.hom ≫ F.map b ≫ J = 0 at H
    simpa only [Category.assoc,zero_comp] using H
  obtain ⟨c,hc⟩ := extension_of_connecting_zero (shortExact h) b h₁
  have hb : b = 0 := hc.trans
    ((congrArg (fun d => E.map (CycleQ2RelativeOpenSupport.sequence h).f ≫ d) (ha c)).trans
      comp_zero)
  let I := (shiftFunctorAdd (DerivedCategory (AbSheaf X)) q 1).inv.app (Q.obj K)
  have h₂ : S.shortComplex_shortExact.extClass.hom ≫ F.map (sectionClass q z hz) = 0 := by
    apply (cancel_mono I).mp
    change S.shortComplex_shortExact.extClass.hom ≫ F.map (sectionClass q z hz) ≫ I = 0 at hb
    simpa only [Category.assoc,zero_comp] using hb
  exact hn (extension_of_connecting_zero S.shortComplex_shortExact _ h₂)

open HomologicalComplex
open CycleQ2DerivedOverlapClass (sectionChainMap)

private theorem post_closed {L : CochainComplex (AbSheaf X) ℤ} (m : K ⟶ L)
    {P : AbSheaf X} (f : P ⟶ (K⟦q⟧).X 0) (hf : f ≫ (K⟦q⟧).d 0 1 = 0) :
    (f ≫ (m⟦q⟧').f 0) ≫ (L⟦q⟧).d 0 1 = 0 := by
  rw [Category.assoc,(m⟦q⟧').comm,← Category.assoc,hf,zero_comp]

theorem sectionClass_post {L : CochainComplex (AbSheaf X) ℤ} (m : K ⟶ L)
    {P : AbSheaf X} (f : P ⟶ (K⟦q⟧).X 0) (hf : f ≫ (K⟦q⟧).d 0 1 = 0) :
    sectionClass q f hf ≫ (Q.map m)⟦q⟧' =
      sectionClass q (f ≫ (m⟦q⟧').f 0) (post_closed q m f hf) := by
  have hc : sectionChainMap q f hf ≫ m⟦q⟧' =
      sectionChainMap q (f ≫ (m⟦q⟧').f 0) (post_closed q m f hf) := by
    apply from_single_hom_ext
    change (sectionChainMap q f hf).f 0 ≫ (m⟦q⟧').f 0 =
      (sectionChainMap q (f ≫ (m⟦q⟧').f 0) (post_closed q m f hf)).f 0
    simp only [sectionChainMap,mkHomFromSingle_f]
    exact Category.assoc (singleObjXSelf (ComplexShape.up ℤ) 0 P).hom f ((m⟦q⟧').f 0)
  let a := sectionChainMap q f hf
  let θ := ((Q (X := X)).commShiftIso q).hom
  calc
    _ = Q.map a ≫ θ.app K ≫ (Q.map m)⟦q⟧' := Category.assoc _ _ _
    _ = Q.map a ≫ Q.map (m⟦q⟧') ≫ θ.app L :=
      congrArg (fun g => Q.map a ≫ g) (Q.commShiftIso_hom_naturality m q).symm
    _ = (Q.map a ≫ Q.map (m⟦q⟧')) ≫ θ.app L := (Category.assoc _ _ _).symm
    _ = Q.map (a ≫ m⟦q⟧') ≫ θ.app L :=
      congrArg (fun g => g ≫ θ.app L) (Q.map_comp a (m⟦q⟧')).symm
    _ = _ := congrArg (fun k => Q.map k ≫ θ.app L) hc

/-- Both connecting morphisms commute with postcomposition in the derived target. -/
theorem relativeClass_post {L : CochainComplex (AbSheaf X) ℤ} (m : K ⟶ L) :
    relativeClass q S h z hz ≫ (Q.map m)⟦q+1+1⟧' =
      relativeClass q S h (z ≫ (m⟦q⟧').f 0) (post_closed q m z hz) := by
  let Y := DerivedCategory (AbSheaf X)
  have step {P : Y} {i : ℤ} (v : P ⟶ (Q.obj K)⟦i⟧) :
      ((F.map v) ≫ (shiftFunctorAdd Y i 1).inv.app (Q.obj K)) ≫ (Q.map m)⟦i+1⟧' =
        F.map (v ≫ (Q.map m)⟦i⟧') ≫ (shiftFunctorAdd Y i 1).inv.app (Q.obj L) := by
    rw [Functor.map_comp,Category.assoc,Category.assoc]
    exact congrArg (fun g => F.map v ≫ g) ((shiftFunctorAdd Y i 1).inv.naturality (Q.map m)).symm
  have mv : overlapClass q S z hz ≫ (Q.map m)⟦q+1⟧' =
      overlapClass q S (z ≫ (m⟦q⟧').f 0) (post_closed q m z hz) := by
    unfold overlapClass
    rw [Category.assoc,step,sectionClass_post]
  let δ := (shortExact h).extClass.hom
  let v := overlapClass q S z hz
  let J := (shiftFunctorAdd Y (q+1) 1).inv
  calc
    _ = δ ≫ (F.map v ≫ J.app (Q.obj K)) ≫ (Q.map m)⟦q+1+1⟧' := Category.assoc _ _ _
    _ = δ ≫ F.map (v ≫ (Q.map m)⟦q+1⟧') ≫ J.app (Q.obj L) :=
      congrArg (fun g => δ ≫ g) (step v)
    _ = _ := congrArg (fun y => δ ≫ F.map y ≫ J.app (Q.obj L)) mv

end Double
end CycleQ2LogDetection

section
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
universe u v w
namespace CycleQ2KInjectiveSections
variable {C : Type u} [Category.{v} C] [Abelian C] (P : C) (I : CochainComplex C ℤ)
variable [HasDerivedCategory.{w} C] [I.IsKInjective]
/-- The actual derived map represented by a closed element. -/
def closedClass (n : ℤ) (f : P ⟶ I.X n) (hf : f ≫ I.d n (n+1) = 0) :
    (DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧ :=
  DerivedCategory.Q.map (Cocycle.equivHomShift.symm
    (Cocycle.fromSingleMk f (zero_add n) (n+1) rfl hf)) ≫ (DerivedCategory.Q.commShiftIso n).hom.app I

private theorem classEquiv_mk (n : ℤ) (f : P ⟶ I.X n) (hf : f ≫ I.d n (n+1) = 0) :
    classEquiv P I n (CohomologyClass.mk (Cocycle.fromSingleMk f (zero_add n) (n+1) rfl hf)) =
      closedClass P I n f hf := by
  let z := Cocycle.fromSingleMk f (zero_add n) (n+1) rfl hf
  let k := Cocycle.equivHomShift.symm z
  change (DerivedCategory.quotientCompQhIso C).inv.app _ ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map k) ≫
    (DerivedCategory.quotientCompQhIso C).hom.app _ ≫ _ = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  rw [Iso.inv_hom_id_app_assoc]
  rfl

/-- Every shifted derived morphism admits a closed representative in the given
K-injective target. -/
theorem closedClass_surjective (n : ℤ)
    (x : (DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj I)⟦n⟧) :
    ∃ (f : P ⟶ I.X n) (hf : f ≫ I.d n (n+1) = 0), closedClass P I n f hf = x := by
  obtain ⟨a, ha⟩ := (classEquiv P I n).surjective x
  obtain ⟨z, rfl⟩ := a.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective z n (zero_add n) (n+1) rfl
  exact ⟨f, hf, (classEquiv_mk P I n f hf).symm.trans ha⟩

/-- The canonical derived class of a represented section vanishes exactly when
it is an ordinary boundary. -/
theorem closedClass_eq_zero_iff (n : ℤ) (f : P ⟶ I.X n) (hf : f ≫ I.d n (n+1) = 0) :
    closedClass P I n f hf = 0 ↔ ∃ g : P ⟶ I.X (n-1), g ≫ I.d (n-1) n = f := by
  rw [← classEquiv_mk, EmbeddingLike.map_eq_zero_iff, CohomologyClass.mk_eq_zero_iff]
  exact Cocycle.fromSingleMk_mem_coboundaries_iff f (zero_add n) _ rfl hf _ (by simp)

omit [I.IsKInjective] in
/-- Restricting a closed representative precomposes its actual derived morphism. -/
theorem closedClass_precomp {P' : C} (g : P' ⟶ P) (n : ℤ) (f : P ⟶ I.X n)
    (hf : f ≫ I.d n (n+1) = 0) :
    closedClass P' I n (g ≫ f) (by simp [hf]) =
      (DerivedCategory.singleFunctor C 0).map g ≫ closedClass P I n f hf := by
  let z := Cocycle.fromSingleMk f (zero_add n) (n+1) rfl hf
  let a := (CochainComplex.singleFunctor C 0).map g
  have hz := Cocycle.fromSingleMk_precomp g f (zero_add n) (n+1) rfl hf
  have hh := (congrArg (fun ξ => Cocycle.equivHomShift.symm ξ) hz).trans
    (Cocycle.equivHomShift_symm_precomp z a)
  refine (congrArg (fun m => DerivedCategory.Q.map m ≫ (DerivedCategory.Q.commShiftIso n).hom.app I) hh).trans ?_
  change DerivedCategory.Q.map (a ≫ Cocycle.equivHomShift.symm z) ≫ _ =
    DerivedCategory.Q.map a ≫ DerivedCategory.Q.map (Cocycle.equivHomShift.symm z) ≫ _
  rw [Functor.map_comp, Category.assoc]

end CycleQ2KInjectiveSections
end

namespace CycleQ2AcyclicSectionRepresentatives
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex Opposite
open CochainComplex CochainComplex.HomComplex
open CycleQ2AcyclicComplexSections CycleQ2AffineHypercohomologyComparison CycleQ2KInjectiveSections

universe w v u
section Groups
variable (S : ShortComplex AddCommGrpCat.{v})

private abbrev cls : S.g.hom.ker →+ S.homology :=
  S.abHomologyIso.inv.hom.comp (QuotientAddGroup.mk' _)

private theorem cls_apply (z : S.g.hom.ker) :
    cls S z = S.homologyπ (S.abCyclesIso.inv z) := by
  exact ConcreteCategory.congr_hom S.abLeftHomologyData.π_comp_homologyIso_inv z

private theorem cls_surj : Function.Surjective (cls S) := by
  intro z
  obtain ⟨y,hy⟩ := (ConcreteCategory.bijective_of_isIso S.abHomologyIso.inv).surjective z
  obtain ⟨x,rfl⟩ := QuotientAddGroup.mk_surjective y
  exact ⟨x,hy⟩

private theorem cls_zero (z : S.g.hom.ker) :
    cls S z = 0 ↔ ∃ y : S.X₁, S.f y = z.val := by
  have h : cls S z = 0 ↔ (QuotientAddGroup.mk z : S.g.hom.ker ⧸ S.abToCycles.range) = 0 := by
    change S.abHomologyIso.inv _ = 0 ↔ _
    rw [← map_zero S.abHomologyIso.inv.hom]
    exact (ConcreteCategory.bijective_of_isIso S.abHomologyIso.inv).injective.eq_iff
  rw [h, QuotientAddGroup.eq_zero_iff]
  exact exists_congr (fun y => Subtype.ext_iff)

variable {S} {T : ShortComplex AddCommGrpCat.{v}} (e : S ⟶ T)

private def push : S.g.hom.ker →+ T.g.hom.ker :=
  AddMonoidHom.mk' (fun z => ⟨e.τ₂ z.val, by
    change T.g (e.τ₂ z.val) = 0
    rw [← ConcreteCategory.comp_apply,e.comm₂₃,ConcreteCategory.comp_apply,z.property,map_zero]⟩)
    (fun x y => Subtype.ext (map_add e.τ₂.hom x.val y.val))

private theorem cls_naturality (z : S.g.hom.ker) :
    ShortComplex.homologyMap e (cls S z) = cls T (push e z) := by
  have hc : ShortComplex.cyclesMap e (S.abCyclesIso.inv z) = T.abCyclesIso.inv (push e z) := by
    apply (AddCommGrpCat.mono_iff_injective T.iCycles).mp inferInstance
    rw [← ConcreteCategory.comp_apply,ShortComplex.cyclesMap_i,ConcreteCategory.comp_apply,
      ShortComplex.abCyclesIso_inv_apply_iCycles,ShortComplex.abCyclesIso_inv_apply_iCycles]
    rfl
  rw [cls_apply,cls_apply,← ConcreteCategory.comp_apply,ShortComplex.homologyπ_naturality,
    ConcreteCategory.comp_apply,hc]

/-- A sectionwise quasi-isomorphism lifts cycles modulo boundaries. -/
private theorem lift_cycle [ShortComplex.QuasiIso e] (y : T.X₂) (hy : T.g y = 0) :
    ∃ x : S.X₂, S.g x = 0 ∧ ∃ p : T.X₁, T.f p = y - e.τ₂ x := by
  let yy : T.g.hom.ker := ⟨y,hy⟩
  obtain ⟨z,hz⟩ := (ConcreteCategory.bijective_of_isIso (ShortComplex.homologyMap e)).surjective (cls T yy)
  obtain ⟨x,rfl⟩ := cls_surj S z
  rw [cls_naturality] at hz
  exact ⟨x.val,x.property,(cls_zero T (yy-push e x)).mp (by rw [map_sub,hz,sub_self])⟩

/-- A sectionwise quasi-isomorphism reflects boundaries of cycles. -/
private theorem reflect_boundary [ShortComplex.QuasiIso e] (x : S.X₂) (hx : S.g x = 0)
    (y : T.X₁) (hy : T.f y = e.τ₂ x) : ∃ p : S.X₁, S.f p = x := by
  let xx : S.g.hom.ker := ⟨x,hx⟩
  apply (cls_zero S xx).mp
  apply (ConcreteCategory.bijective_of_isIso (ShortComplex.homologyMap e)).injective
  rw [map_zero,cls_naturality]
  exact (cls_zero T _).mpr ⟨y,hy⟩
end Groups

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  [HasDerivedCategory.{w} C] [EnoughInjectives C] (P : C) {K I : CochainComplex C ℤ}

omit [HasExt C] [EnoughInjectives C] in
theorem closedClass_postcomp (i : K ⟶ I) (n : ℤ) (a : P ⟶ K.X n)
    (ha : a ≫ K.d n (n+1) = 0) :
    closedClass P I n (a ≫ i.f n) (by simp [reassoc_of% ha]) =
      closedClass P K n a ha ≫ (DerivedCategory.Q.map i)⟦n⟧' := by
  let A := (CochainComplex.singleFunctor C 0).obj P
  let Q := DerivedCategory.Q (C := C)
  let z := Cocycle.fromSingleMk a (zero_add n) (n+1) rfl ha
  let l : A ⟶ K⟦n⟧ := Cocycle.equivHomShift.symm z
  let β (L : CochainComplex C ℤ) := (Q.commShiftIso n).hom.app L
  have h := Cocycle.fromSingleMk_postcomp a (zero_add n) (n+1) rfl ha i
  have hc := (congrArg (fun v : Cocycle A I n => Cocycle.equivHomShift.symm v) h).trans
    (Cocycle.equivHomShift_symm_postcomp z i)
  calc
    _ = Q.map (l ≫ i⟦n⟧') ≫ β I := congrArg (fun m : A ⟶ I⟦n⟧ => Q.map m ≫ β I) hc
    _ = (Q.map l ≫ Q.map (i⟦n⟧')) ≫ β I := congrArg (fun m => m ≫ β I) (Q.map_comp l _)
    _ = Q.map l ≫ (β K ≫ (Q.map i)⟦n⟧') :=
      (Category.assoc _ _ _).trans
        (congrArg (fun m => Q.map l ≫ m) (Q.commShiftIso_hom_naturality i n))
    _ = _ := (Category.assoc _ _ _).symm

omit [HasExt C] [EnoughInjectives C] in
theorem closedClass_sub (n : ℤ) (a a' : P ⟶ K.X n) (ha : a ≫ K.d n (n+1) = 0)
    (ha' : a' ≫ K.d n (n+1) = 0) :
    closedClass P K n (a-a') (by simp [ha,ha']) = closedClass P K n a ha - closedClass P K n a' ha' := by
  let A := (CochainComplex.singleFunctor C 0).obj P
  let Q := DerivedCategory.Q (C := C)
  let e : Cocycle A K n ≃+ (A ⟶ K⟦n⟧) := Cocycle.equivHomShift.symm
  let β := (Q.commShiftIso n).hom.app K
  let z := Cocycle.fromSingleMk a (zero_add n) (n+1) rfl ha
  let z' := Cocycle.fromSingleMk a' (zero_add n) (n+1) rfl ha'
  have hc := (congrArg (fun v : Cocycle A K n => e v)
    (Cocycle.fromSingleMk_sub a a' (zero_add n) (n+1) rfl ha ha')).trans (map_sub e z z')
  calc
    _ = Q.map (e z - e z') ≫ β := congrArg (fun m : A ⟶ K⟦n⟧ => Q.map m ≫ β) hc
    _ = (Q.map (e z) - Q.map (e z')) ≫ β := congrArg (fun m => m ≫ β) Q.map_sub
    _ = _ := Preadditive.sub_comp (Q.map (e z)) (Q.map (e z')) β

variable (K) (b : ℤ) [lower : K.IsStrictlyGE b] (terms : ∀ j, AcyclicFor P (K.X j))

include lower terms in
/-- For an acyclic-term bounded-below complex every derived class is represented
by a single closed ordinary section. -/
theorem surjective (n : ℤ)
    (z : (DerivedCategory.singleFunctor C 0).obj P ⟶ (DerivedCategory.Q.obj K)⟦n⟧) :
    ∃ (a : P ⟶ K.X n) (ha : a ≫ K.d n (n+1) = 0), closedClass P K n a ha = z := by
  obtain ⟨I,i,hm,hq,hi,hb,hsec⟩ := exists_injective_sections_resolution P K b terms
  let : I.IsKInjective := isKInjective_of_injective I (b-1)
  let fi := (sectionComplex P).map i
  let e := (shortComplexFunctor' AddCommGrpCat (.up ℤ) (n-1) n (n+1)).map fi
  let : ShortComplex.QuasiIso e := (quasiIsoAt_iff' fi (n-1) n (n+1) (by simp) (by simp)).mp inferInstance
  let t := (DerivedCategory.Q.map i)⟦n⟧'
  obtain ⟨y,hy,hyz⟩ := closedClass_surjective P I n (z ≫ t)
  obtain ⟨a,ha,p,hp⟩ := lift_cycle e y hy
  change P ⟶ K.X n at a
  change P ⟶ I.X (n-1) at p
  change a ≫ K.d n (n+1) = 0 at ha
  change p ≫ I.d (n-1) n = y - a ≫ i.f n at hp
  have hai : (a ≫ i.f n) ≫ I.d n (n+1) = 0 := by
    rw [Category.assoc,i.comm,← Category.assoc,ha,zero_comp]
  have hzero := (closedClass_eq_zero_iff P I n (y-a ≫ i.f n) (by simp [hy,hai])).mpr ⟨p,hp⟩
  rw [closedClass_sub _ _ _ _ hy hai,sub_eq_zero] at hzero
  refine ⟨a,ha,(cancel_mono t).mp ?_⟩
  calc
    closedClass P K n a ha ≫ t = closedClass P I n (a ≫ i.f n) hai := (closedClass_postcomp P i n a ha).symm
    _ = closedClass P I n y hy := hzero.symm
    _ = _ := hyz

include lower terms in
/-- A closed section maps to zero in the derived category precisely when it
is the exterior derivative of an ordinary section in the preceding degree. -/
theorem zero_iff (n : ℤ) (a : P ⟶ K.X n) (ha : a ≫ K.d n (n+1) = 0) :
    closedClass P K n a ha = 0 ↔ ∃ p : P ⟶ K.X (n-1), p ≫ K.d (n-1) n = a := by
  obtain ⟨I,i,hm,hq,hi,hb,hsec⟩ := exists_injective_sections_resolution P K b terms
  let : I.IsKInjective := isKInjective_of_injective I (b-1)
  let fi := (sectionComplex P).map i
  let e := (shortComplexFunctor' AddCommGrpCat (.up ℤ) (n-1) n (n+1)).map fi
  let : ShortComplex.QuasiIso e := (quasiIsoAt_iff' fi (n-1) n (n+1) (by simp) (by simp)).mp inferInstance
  let t := (DerivedCategory.Q.map i)⟦n⟧'
  have hai : (a ≫ i.f n) ≫ I.d n (n+1) = 0 := by simp [reassoc_of% ha]
  have hEq := closedClass_postcomp P i n a ha
  constructor
  · intro h
    obtain ⟨p,hp⟩ := (closedClass_eq_zero_iff P I n _ hai).mp (by rw [hEq,h,zero_comp])
    exact reflect_boundary e a ha p hp
  · rintro ⟨p,rfl⟩
    apply (cancel_mono t).mp
    rw [zero_comp,← hEq]
    apply (closedClass_eq_zero_iff P I n _ hai).mpr
    exact ⟨p ≫ i.f (n-1),by rw [Category.assoc,i.comm,Category.assoc]⟩

end CycleQ2AcyclicSectionRepresentatives

namespace CycleQ2AffineOverlapRepresentatives
open CategoryTheory HomologicalComplex CochainComplex CochainComplex.HomComplex TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2DerivedOverlapClass (sectionClass sectionChainMap)
open CycleQ2KInjectiveSections (closedClass)
variable {X : TopCat.{0}} {P : AbSheaf X} {K : CochainComplex (AbSheaf X) ℤ}
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _

theorem sectionClass_eq (n : ℤ) (f : P ⟶ K.X n) (hf : f ≫ K.d n (n+1) = 0)
    (hs : (f ≫ (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv) ≫ (K⟦n⟧).d 0 1 = 0) :
    sectionClass n (f ≫ (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv) hs =
      closedClass P K n f hf := by
  let A := (CochainComplex.singleFunctor (AbSheaf X) 0).obj P
  let a : P ⟶ (K⟦n⟧).X 0 := f ≫ (K.shiftFunctorObjXIso n 0 n (zero_add n).symm).inv
  have hc : sectionChainMap n a hs = (Cocycle.equivHomShift.symm
      (Cocycle.fromSingleMk f (zero_add n) (n+1) rfl hf) : A ⟶ K⟦n⟧) := by
    apply from_single_hom_ext
    erw [sectionChainMap,mkHomFromSingle_f,Cocycle.equivHomShift_symm_apply,Cocycle.homOf_f,
      Cocycle.rightShift_coe,Cochain.rightShift_v _ n 0 _ 0 0 _ n (zero_add n),
      Cocycle.fromSingleMk_coe,Cochain.fromSingleMk_v,Category.assoc]
  exact congrArg (fun m : A ⟶ K⟦n⟧ =>
    DerivedCategory.Q.map m ≫ (DerivedCategory.Q.commShiftIso n).hom.app K) hc

/-- For the double residue in degree two the original and shifted sections have
definitionally the same coefficient and the shift's differential sign is positive. -/
theorem sectionClass_two (f : P ⟶ K.X 2) (hf : f ≫ K.d 2 3 = 0) :
    sectionClass (2:ℤ) (show P ⟶ (K⟦(2:ℤ)⟧).X 0 from f) (by
      rw [shiftFunctor_obj_d',Int.negOnePow_even 2 ⟨1,rfl⟩,one_smul]
      exact hf) = closedClass P K 2 f hf := by
  have he : f ≫ (K.shiftFunctorObjXIso 2 0 2 (by decide)).inv =
      (show P ⟶ (K⟦(2:ℤ)⟧).X 0 from f) := by
    change f ≫ 𝟙 (K.X 2) = f
    exact Category.comp_id f
  have hs : (f ≫ (K.shiftFunctorObjXIso 2 0 2 (by decide)).inv) ≫ (K⟦(2:ℤ)⟧).d 0 1 = 0 := by
    rw [he,shiftFunctor_obj_d',Int.negOnePow_even 2 ⟨1,rfl⟩,one_smul]
    exact hf
  simpa only [he] using sectionClass_eq 2 f hf hs

end CycleQ2AffineOverlapRepresentatives

namespace CycleQ2LogDetection
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace HomologicalComplex
open CochainComplex
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2AcyclicComplexSections (AcyclicFor)
open CycleQ2DerivedOverlapClass (sectionClass)
open CycleQ2RelativeOpenSupport (relativeClass)
open CycleQ2KInjectiveSections (closedClass closedClass_precomp)
open CycleQ2AffineOverlapRepresentatives (sectionClass_two)

variable {X : TopCat.{0}}
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _
local instance : HasDerivedCategory.{1} (AbSheaf X) := HasDerivedCategory.standard _
variable (K : CochainComplex (AbSheaf X) ℤ)

private theorem cutoff_zero (j : ℤ) (hj : 2 < j) : IsZero ((cutoff K 2).X j) :=
  (K.restriction (ComplexShape.embeddingUpIntLE 2)).isZero_extend_X
    (ComplexShape.embeddingUpIntLE 2) j (fun i hi => by
      rw [ComplexShape.embeddingUpIntLE_f] at hi
      omega)

private theorem cutoff_bounded [K.IsStrictlyGE 0] : CochainComplex.IsStrictlyGE (cutoff K 2) 0 := by
  apply (CochainComplex.isStrictlyGE_iff (cutoff K 2) 0).mpr
  intro i hi
  let := cutoff_iso K 2 i (by omega)
  exact (K.isZero_of_isStrictlyGE 0 i hi).of_iso (asIso ((cutoffMap K 2).f i)).symm

private theorem cut_terms (P : AbSheaf X) (ht : ∀ j, AcyclicFor P (K.X j)) :
    ∀ j, AcyclicFor P ((cutoff K 2).X j) := by
  intro j n
  let F := extFunctorObj.{1} P (n+1)
  change Subsingleton (F.obj _)
  by_cases hj : j ≤ 2
  · let := cutoff_iso K 2 j hj
    let : Subsingleton (F.obj (K.X j)) := ht j n
    exact (F.mapIso (asIso ((cutoffMap K 2).f j)).symm).addCommGroupIsoToAddEquiv.injective.subsingleton
  · exact AddCommGrpCat.isZero_iff_subsingleton.mp (F.map_isZero (cutoff_zero K j (lt_of_not_ge hj)))

/-- A closed overlap two-form that cannot be written as a difference of
chart forms plus an exact form has a nonzero twice-connected derived class. -/
theorem relativeClass_ne_zero_of_no_decomposition [K.IsStrictlyGE 0]
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare) {W : Opens X} (h : S.X₄ ≤ W)
    (tW : ∀ j, AcyclicFor (freeOpen W) (K.X j))
    (t₁ : ∀ j, AcyclicFor (freeOpen S.X₁) (K.X j))
    (t₂ : ∀ j, AcyclicFor (freeOpen S.X₂) (K.X j))
    (t₃ : ∀ j, AcyclicFor (freeOpen S.X₃) (K.X j))
    (z : S.shortComplex.X₁ ⟶ K.X 2) (hz : z ≫ K.d 2 3 = 0)
    (bad : ¬ ∃ (b : S.shortComplex.X₂ ⟶ K.X 2) (a : S.shortComplex.X₁ ⟶ K.X 1),
      z = S.shortComplex.f ≫ b + a ≫ K.d 1 2) :
    relativeClass (2:ℤ) S h (show S.shortComplex.X₁ ⟶ (K⟦(2:ℤ)⟧).X 0 from z) (by
      rw [shiftFunctor_obj_d',Int.negOnePow_even 2 ⟨1,rfl⟩,one_smul]; exact hz) ≠ 0 := by
  let L : CochainComplex (AbSheaf X) ℤ := cutoff K 2
  let m : K ⟶ L := cutoffMap K 2
  let : L.IsStrictlyGE 0 := cutoff_bounded K
  let : IsIso (m.f 1) := cutoff_iso K 2 1 (by decide)
  let : IsIso (m.f 2) := cutoff_iso K 2 2 (by decide)
  have tmid (j : ℤ) : AcyclicFor S.shortComplex.X₂ (K.X j) := by
    intro n
    constructor
    intro a b
    exact Ext.biprod_ext ((t₂ j n).elim _ _) ((t₃ j n).elim _ _)
  let z' : S.shortComplex.X₁ ⟶ L.X 2 := z ≫ m.f 2
  have hz' : z' ≫ L.d 2 3 = 0 := (cutoff_zero K 3 (by decide)).eq_of_tgt _ _
  have ha (w : G.obj (freeOpen W) ⟶ (Q.obj L)⟦(2:ℤ)+1⟧) : w = 0 := by
    obtain ⟨v,hv,rfl⟩ := CycleQ2AcyclicSectionRepresentatives.surjective
      (freeOpen W) L 0 (cut_terms K _ tW) 3 w
    apply (CycleQ2AcyclicSectionRepresentatives.zero_iff
      (freeOpen W) L 0 (cut_terms K _ tW) 3 v hv).mpr
    exact ⟨0,(cutoff_zero K 3 (by decide)).eq_of_tgt _ _⟩
  have hn : ¬ ∃ b : G.obj S.shortComplex.X₂ ⟶ (Q.obj L)⟦(2:ℤ)⟧,
      closedClass S.shortComplex.X₁ L 2 z' hz' = G.map S.shortComplex.f ≫ b := by
    rintro ⟨B,hB⟩
    obtain ⟨b,hb,rfl⟩ := CycleQ2AcyclicSectionRepresentatives.surjective
      S.shortComplex.X₂ L 0 (cut_terms K _ tmid) 2 B
    rw [← closedClass_precomp] at hB
    have cl (v : S.shortComplex.X₁ ⟶ L.X 2) : v ≫ L.d 2 (2+1) = 0 :=
      (cutoff_zero K 3 (by decide)).eq_of_tgt _ _
    have H := (CycleQ2AcyclicSectionRepresentatives.zero_iff S.shortComplex.X₁ L 0
      (cut_terms K _ t₁) 2 (z' - S.shortComplex.f ≫ b) (cl _)).mp
      (by rw [CycleQ2AcyclicSectionRepresentatives.closedClass_sub _ _ _ _ hz' (cl _), hB, sub_self])
    obtain ⟨a,ha⟩ := H
    change S.shortComplex.X₁ ⟶ L.X 1 at a
    change a ≫ L.d 1 2 = z' - S.shortComplex.f ≫ b at ha
    apply bad
    refine ⟨b ≫ inv (m.f 2), a ≫ inv (m.f 1),(cancel_mono (m.f 2)).mp ?_⟩
    change z' = (_ + _) ≫ m.f 2
    simp only [Preadditive.add_comp,Category.assoc,IsIso.inv_hom_id,Category.comp_id,
      ← m.comm,IsIso.inv_hom_id_assoc]
    rw [ha]
    abel
  have hzS : (show S.shortComplex.X₁ ⟶ (K⟦(2:ℤ)⟧).X 0 from z) ≫ (K⟦(2:ℤ)⟧).d 0 1 = 0 := by
    rw [shiftFunctor_obj_d',Int.negOnePow_even 2 ⟨1,rfl⟩,one_smul]; exact hz
  intro H
  have hr := relativeClass_post (2:ℤ) S h z hzS m
  rw [H,zero_comp] at hr
  exact (relative_nonzero (K := L) (2:ℤ) S h _ _ ha (by
    change ¬ ∃ b, sectionClass (2:ℤ) (show S.shortComplex.X₁ ⟶ (L⟦(2:ℤ)⟧).X 0 from z') _ = _
    rw [sectionClass_two z' hz']; exact hn)) hr.symm

end CycleQ2LogDetection

namespace CycleQ2LogDetection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open CycleQ2FramedCechFormRow
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves
open CycleQ2LocalPrincipalGysin (cover union_le localClass)
open CycleQ2RelativeOpenSupport (relativeClass relativeOfSection)
open CycleQ2DerivedDoubleSupport (sectionMap sectionMap_closed)
open CycleQ2PrincipalLogSupportClass (restrictionUnit)
open CycleQ2IntrinsicLogSupportClass (logForm shiftedSection shiftedSection_closed logForm_closed)

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 4 p]
    (W : FramedOpen p 4) [IsNoetherianRing Γ(X,W.1)]
    (u : Fin 4 → Γ(X,W.1))
    (hu : letI := (CycleQ2SmoothRelativeFrames.sectionCoefficients p W.1).toAlgebra
      ∃ b : Module.Basis (Fin 4) Γ(X,W.1) (KaehlerDifferential k Γ(X,W.1)),
        ∀ i, b i = KaehlerDifferential.D k Γ(X,W.1) (u i))
include hu

/-- The actual codimension-two supported class on an adapted affine chart
is nonzero whenever the common zero locus contains a point. -/
theorem localClass_ne_zero (x : X) (hx : x ∈ W.1) (hz : x ∈ X.zeroLocus {u 0,u 1}) :
    localClass p 4 (u 0) (u 1) (intersection p 4 W (u 0) (u 1)).2 ≠ 0 := by
  let K : CochainComplex (AbSheaf (show TopCat from X)) ℤ := relativeDeRhamInt p 4
  let f := u 0
  let g := u 1
  let S : (Opens.grothendieckTopology (show TopCat from X)).MayerVietorisSquare := cover f g
  let Z := intersection p 4 W f g
  let a := restrictionUnit f (show Z.1 ≤ X.basicOpen f from inf_le_left)
  let b := restrictionUnit g (show Z.1 ≤ X.basicOpen g from inf_le_right)
  let z := logForm p 4 Z a b
  let s := shiftedSection p 4 Z z
  let v := sectionMap (2:ℤ) S s
  have hvs := sectionMap_closed (2:ℤ) S s (shiftedSection_closed p 4 Z z (logForm_closed p 4 Z a b))
  have hv : v ≫ K.d 2 3 = 0 := by
    rw [CochainComplex.shiftFunctor_obj_d',Int.negOnePow_even 2 ⟨1,rfl⟩,one_smul] at hvs
    exact hvs
  let _ : K.IsStrictlyGE 0 := by
    apply (K.isStrictlyGE_iff 0).2
    intro i hi
    exact (relativeDeRham p 4).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i (by
      intro n hh; change (0:ℤ)+n=i at hh; omega)
  exact relativeClass_ne_zero_of_no_decomposition K S (union_le f g)
    (CycleQ2FramedOpenFormCoefficients.term_acyclic p 4 W)
    (CycleQ2FramedOpenFormCoefficients.term_acyclic p 4 Z)
    (CycleQ2FramedOpenFormCoefficients.term_acyclic p 4 (singleOpen p 4 W f))
    (CycleQ2FramedOpenFormCoefficients.term_acyclic p 4 (singleOpen p 4 W g))
    v hv (fun ⟨m,n,h⟩ => native_section_nondecomposable p W u hu x hx hz ⟨n,m,h⟩)

end CycleQ2LogDetection

namespace CycleQ2LogDetection
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2SmoothSurfaceGysin
open CycleQ2ClosedGraphSupport (support complement)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2InjectiveCech (AbSheaf)
private theorem supportMap_isIso_of_eq {T : TopCat.{0}} {U V W : Opens T}
    (e : U = V) (h : U ≤ W) (j : V ≤ W) :
    IsIso (CycleQ2RelativeSupportRefinement.supportMap h j e.le le_rfl).τ₃ := by
  subst V
  have idMap : (CycleQ2RelativeSupportRefinement.supportMap h h le_rfl le_rfl).τ₃ = 𝟙 _ := by
    apply (cancel_epi (CycleQ2RelativeOpenSupport.sequence h).g).mp
    have hW : CycleQ2InjectiveCech.freeOpenMap (show W ≤ W from le_rfl) = 𝟙 _ :=
      (CycleQ2MayerVietorisRestriction.freeOpenSheaf (X := T)).map_id W
    change cokernel.π _ ≫ cokernel.desc _ (CycleQ2InjectiveCech.freeOpenMap
      (show W ≤ W from le_rfl) ≫ cokernel.π _) (by rw [hW,Category.id_comp,cokernel.condition]) =
        cokernel.π _ ≫ 𝟙 _
    rw [cokernel.π_desc,hW,Category.id_comp,Category.comp_id]
  change IsIso (CycleQ2RelativeSupportRefinement.supportMap h h le_rfl le_rfl).τ₃
  rw [idMap]
  infer_instance

variable {k : Type} [Field k] [CharZero k] [Algebra ℂ k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

set_option quotPrecheck false
local notation "Ω" => (DerivedCategory.Q.obj (relativeDeRhamInt q 4) : DerivedCategory.{1} (AbSheaf (show TopCat from Y)))
local notation "E" => DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
local notation "res" => CycleQ2NoetherianSupport.res
local instance derived (Z : TopCat.{0}) : HasDerivedCategory.{1} (AbSheaf Z) :=
  HasDerivedCategory.standard _

include hi in
/-- A global degree-four class whose restrictions are the logarithmic equation-chart
classes is nonzero whenever the embedded surface contains a point. -/
theorem normalized_ne_zero (x : X) (z : (E).obj (support i ⊤) ⟶ Ω⟦(4:ℤ)⟧)
    (hz : ∀ n, res (complement i) (show atlasOpen q i n ≤ ⊤ from le_top) z =
      atlasClass q i n) : z ≠ 0 := by
  obtain ⟨U,f,g,hxU,_,hfr,hspan⟩ := exists_chart p q i hi x ⊤ (by trivial)
  let A : Chart q i := ⟨U,f,g,hfr,hspan⟩
  obtain ⟨T,e,hxT,w,hw,hf,hg⟩ := adapted_chart p q i hi A x hxU
  let W : CycleQ2IntrinsicFramedAffineSite.FramedOpen q 4 := ⟨T.1,T.2,⟨w,hw⟩⟩
  let : Smooth q := SmoothOfRelativeDimension.smooth 4 q
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsNoetherianRing Γ(Y,T.1) := IsLocallyNoetherian.component_noetherian T
  let ℓ := CycleQ2SmoothTwoChartAgreement.locus_of_span i U A.f A.g A.equations
  have hl : CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) = (T.1 : Set Y) ∩ Set.range i := by
    rw [hf,hg]
    exact CycleQ2ClosedGraphRestriction.locus_restrict i e A.f A.g ℓ
  have hloc := localClass_ne_zero q W w hw (i x) hxT
    (show i x ∈ (Y).zeroLocus {w 0,w 1} from
      (show i x ∈ CycleQ2LocalPrincipalGysin.locus (w 0) (w 1) from hl ▸ ⟨hxT,⟨x,rfl⟩⟩).2)
  let hpair := (CycleQ2FramedCechFormRow.intersection q 4 W (w 0) (w 1)).2
  have ht : CycleQ2ClosedGraphSupport.classOf i (w 0) (w 1) q 4 hl hpair ≠ 0 := by
    unfold CycleQ2ClosedGraphSupport.classOf
    let he := CycleQ2ClosedGraphSupport.union_eq_complement i (w 0) (w 1) hl
    let m := (CycleQ2RelativeSupportRefinement.supportMap
      (show T.1 ⊓ complement i ≤ T.1 from inf_le_left)
      (CycleQ2LocalPrincipalGysin.union_le (w 0) (w 1)) he.ge le_rfl).τ₃
    let : IsIso m := supportMap_isIso_of_eq he.symm _ _
    intro h
    exact hloc ((cancel_epi ((E).map m)).mp (by simpa only [comp_zero] using h))
  have span : Ideal.span {w 0,w 1} = (i).ker.ideal T := by
    rw [hf,hg,← (i).ker.map_ideal (U := T) (V := A.U) e,← A.equations,Ideal.map_span]
    simp only [Set.image_insert_eq,Set.image_singleton]
    rfl
  let B : Chart q i := ⟨T,w 0,w 1,⟨w,hw⟩,span⟩
  intro hz0
  have hm := hz (some B)
  rw [hz0] at hm
  exact ht (hm.symm.trans (show _ ≫ 0 = (0 : (E).obj (support i B.U.1) ⟶ Ω⟦(4:ℤ)⟧) from comp_zero))

end CycleQ2LogDetection

#print axioms CycleQ2LogDetection.normalized_ne_zero
