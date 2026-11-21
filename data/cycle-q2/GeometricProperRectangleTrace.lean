import Proposal.GeometricMarkedGraphCharts
import Proposal.GeometricAffinePairDescent
import Proposal.GeometricCurveCupTrace
import Proposal.GeometricSignedRowComparison
import Proposal.GeometricRectangularHypercohomology

/-! The actual signed curve/target tensor complex computes de Rham classes
on the full proper product above a framed affine target open. The comparison
uses both geometric restrictions on the overlap of the two curve charts.
A closed curve cochain acts on those classes by cup and proper trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

noncomputable section
namespace CycleQ2EvaluationExtension
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (K : HomologicalComplex C c)

private abbrev mapped := (F.mapHomologicalComplex c).obj K
private def atOption : (a : Option ι) → extend.X (mapped F K) a ≅ F.obj (extend.X K a)
  | some _ => Iso.refl _
  | none => (isZero_zero D).iso (F.map_isZero (isZero_zero C))

private theorem with_d (a b : Option ι) :
    (atOption F K a).hom ≫ F.map (extend.d K a b) = extend.d (mapped F K) a b ≫ (atOption F K b).hom := by
  cases a with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some a => cases b with
    | none => exact (F.map_isZero (isZero_zero C)).eq_of_tgt _ _
    | some b => exact (Category.id_comp (F.map (K.d a b))).trans (Category.comp_id _).symm

/-- Applying a zero-preserving functor commutes with extension by zero of a complex. -/
def comparison (e : c.Embedding c') : (mapped F K).extend e ≅ (F.mapHomologicalComplex c').obj (K.extend e) :=
  HomologicalComplex.Hom.isoOfComponents (fun i => atOption F K (e.r i)) (fun i j _ => with_d F K (e.r i) (e.r j))

variable (G : C ⥤ D) [G.PreservesZeroMorphisms] (η : F ⟶ G)
private theorem with_nat (a : Option ι) :
    (atOption F K a).hom ≫ η.app (extend.X K a) =
      extend.mapX ((η.mapHomologicalComplex c).app K) a ≫ (atOption G K a).hom := by
  cases a with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i => exact (Category.id_comp (η.app (K.X i))).trans (Category.comp_id _).symm

theorem comparison_natural (e : c.Embedding c') :
    (comparison F K e).hom ≫ (η.mapHomologicalComplex c').app (K.extend e) =
      extendMap ((η.mapHomologicalComplex c).app K) e ≫ (comparison G K e).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  exact with_nat F K G η (e.r i)

private theorem with_map {L : HomologicalComplex C c} (f : K ⟶ L) (a : Option ι) :
    extend.mapX ((F.mapHomologicalComplex c).map f) a ≫ (atOption F L a).hom =
      (atOption F K a).hom ≫ F.map (extend.mapX f a) := by
  cases a with
  | none => exact (isZero_zero D).eq_of_src _ _
  | some i => exact (Category.comp_id (F.map (f.f i))).trans (Category.id_comp _).symm

theorem comparison_map {L : HomologicalComplex C c} (f : K ⟶ L) (e : c.Embedding c') :
    extendMap ((F.mapHomologicalComplex c).map f) e ≫ (comparison F L e).hom =
      (comparison F K e).hom ≫ (F.mapHomologicalComplex c').map (extendMap f e) := by
  apply HomologicalComplex.hom_ext
  intro i
  exact with_map F K f (e.r i)

end CycleQ2EvaluationExtension

namespace CycleQ2UnframedProductChain
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite HomologicalComplex
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2ProductFramedOpen (smooth_product)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)
open CycleQ2OrdinaryTensorRows (complex restrictComplex)
open CycleQ2EvaluationExtension (comparison comparison_natural comparison_map)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (m : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension m q]
local instance : SmoothOfRelativeDimension (1+m) (productBase p q) := smooth_product p q m
private abbrev E := ComplexShape.embeddingUpNat
private theorem embeddings : E = ComplexShape.embeddingUpIntGE 0  := by
  have h {a b : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℤ)} (h : a.f = b.f) : a = b := by
    cases a; cases b; cases h; rfl
  exact h (funext fun i => (Int.zero_add _).symm)

private abbrev evalSections (U : C.Opens) (V : X.Opens) :=
  sheafToPresheaf (Opens.grothendieckTopology (show Scheme from pullback p q)) AddCommGrpCat.{0} ⋙
    (evaluation (Opens (show Scheme from pullback p q))ᵒᵖ AddCommGrpCat.{0}).obj (op (productOpen p q U V))

local instance evaluationPreservesZero (U : C.Opens) (V : X.Opens) : (evalSections p q U V).PreservesZeroMorphisms :=
  ⟨fun _ _ => rfl⟩

abbrev intSource (U : C.Opens) (V : FramedOpen q m) :=
  ((forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).obj ((complex p q m V U).extend E)

abbrev intNative (U : C.Opens) (V : X.Opens) :=
  ((evalSections p q U V).mapHomologicalComplex (.up ℤ)).obj (relativeDeRhamInt (productBase p q) (1+m))

private abbrev DR := relativeDeRham (productBase p q) (1+m)
private def shiftIso : (DR p q m).extend E ≅ relativeDeRhamInt (productBase p q) (1+m) :=
  eqToIso (congrArg (DR p q m).extend embeddings)

private def nativeExtend (U : C.Opens) (V : X.Opens) : (native p q m U V).extend E ≅ intNative p q m U V := by
  letI : (evalSections p q U V).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  exact comparison (evalSections p q U V) (DR p q m) E ≪≫ ((evalSections p q U V).mapHomologicalComplex (.up ℤ)).mapIso (shiftIso p q m)

private abbrev sourceExtend (U : C.Opens) (V : FramedOpen q m) :=
  comparison (forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}) (complex p q m V U) E

/-- The signed assembly on the integer complex used in the actual rectangular hypercohomology class. -/
def intChainMap (U : C.Opens) (V : FramedOpen q m) : intSource p q m U V ⟶ intNative p q m U V.1 :=
  (sourceExtend p q m U V).inv ≫ extendMap (chainMap p q m U V) E ≫ (nativeExtend p q m U V.1).hom

private abbrev evNat {U U' : C.Opens} {V V' : X.Opens} (h : U' ≤ U) (g : V' ≤ V) : evalSections p q U V ⟶ evalSections p q U' V' :=
  Functor.whiskerLeft (sheafToPresheaf (Opens.grothendieckTopology (show Scheme from pullback p q)) AddCommGrpCat.{0})
    ((evaluation (Opens (show Scheme from pullback p q))ᵒᵖ AddCommGrpCat.{0}).map (homOfLE (productOpen_mono p q h g)).op)

abbrev intNativeRestriction {U U' : C.Opens} {V V' : X.Opens} (h : U' ≤ U) (g : V' ≤ V) : intNative p q m U V ⟶ intNative p q m U' V' :=
  ((evNat p q h g).mapHomologicalComplex (.up ℤ)).app _

abbrev intSourceRestriction {U U' : C.Opens} {V V' : FramedOpen q m} (h : U' ≤ U) (g : V'.1 ≤ V.1) : intSource p q m U V ⟶ intSource p q m U' V' :=
  ((forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℤ)).map (extendMap (restrictComplex p q m V h g) E)

private theorem nativeExtend_natural {U U' : C.Opens} {V V' : X.Opens} (h : U' ≤ U) (g : V' ≤ V) :
    (nativeExtend p q m U V).hom ≫ intNativeRestriction p q m h g =
      extendMap (nativeRestriction p q m h g) E ≫ (nativeExtend p q m U' V').hom := by
  let : (evalSections p q U V).PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let : (evalSections p q U' V').PreservesZeroMorphisms := ⟨fun _ _ => rfl⟩
  let η := evNat p q h g
  let cU := comparison (evalSections p q U V) (DR p q m) E
  let cV := comparison (evalSections p q U' V') (DR p q m) E
  let s := (shiftIso p q m).hom
  let τ := η.mapHomologicalComplex (.up ℤ)
  have x : CommSq cU.hom (extendMap (nativeRestriction p q m h g) E) (τ.app ((DR p q m).extend E)) cV.hom :=
    ⟨comparison_natural (evalSections p q U V) (DR p q m) (evalSections p q U' V') η E⟩
  have y : CommSq (((evalSections p q U V).mapHomologicalComplex (.up ℤ)).map s)
      (τ.app ((DR p q m).extend E)) (intNativeRestriction p q m h g)
      (((evalSections p q U' V').mapHomologicalComplex (.up ℤ)).map s) := ⟨τ.naturality s⟩
  exact (x.horiz_comp y).w

/-- Naturality on the same integer-indexed section and restriction complexes as rectangular hypercohomology. -/
theorem intChainMap_natural {U U' : C.Opens} {V V' : FramedOpen q m} (h : U' ≤ U) (g : V'.1 ≤ V.1) :
    intChainMap p q m U V ≫ intNativeRestriction p q m h g = intSourceRestriction p q m h g ≫ intChainMap p q m U' V' := by
  let a := sourceExtend p q m U V
  let a' := sourceExtend p q m U' V'
  let v := nativeExtend p q m U V.1
  let v' := nativeExtend p q m U' V'.1
  let F := E.extendFunctor AddCommGrpCat.{0}
  let j := chainMap p q m U V
  let j' := chainMap p q m U' V'
  let c := sourceRestriction p q m h g
  let d := nativeRestriction p q m h g
  have sa : CommSq a.hom (F.map c) (intSourceRestriction p q m h g) a'.hom :=
    ⟨(comparison_map (forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}) (complex p q m V U) (restrictComplex p q m V h g) E).symm⟩
  have sj : CommSq j c d j' := ⟨chainMap_natural p q m h g⟩
  have sv : CommSq v.hom (F.map d) (intNativeRestriction p q m h g) v'.hom := ⟨nativeExtend_natural p q m h g⟩
  exact (sa.horiz_inv.horiz_comp ((F.map_commSq sj).horiz_comp sv)).w

/-- The integer-indexed affine rectangle comparison, with source and target used by the proper-curve restriction cone. -/
def intAffineIso {U : C.Opens} (hU : IsAffineOpen U) (V : FramedOpen q m) :
    intSource p q m U V ≅ intNative p q m U V.1 :=
  (sourceExtend p q m U V).symm ≪≫ (E.extendFunctor AddCommGrpCat.{0}).mapIso (affineIso p q m hU V) ≪≫
    nativeExtend p q m U V.1

@[simp] theorem intAffineIso_hom {U : C.Opens} (hU : IsAffineOpen U) (V : FramedOpen q m) :
    (intAffineIso p q m hU V).hom = intChainMap p q m U V := by
  change (sourceExtend p q m U V).inv ≫ (E.extendFunctor AddCommGrpCat.{0}).map (affineIso p q m hU V).hom ≫ _ = _
  rw [affineIso_hom]
  rfl

/-- Restricting either affine rectangle gives a commutative square of actual signed integer complexes. -/
theorem intAffineIso_natural {U U' : C.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    {V V' : FramedOpen q m} (h : U' ≤ U) (g : V'.1 ≤ V.1) :
    (intAffineIso p q m hU V).hom ≫ intNativeRestriction p q m h g =
      intSourceRestriction p q m h g ≫ (intAffineIso p q m hU' V').hom := by
  rw [intAffineIso_hom,intAffineIso_hom]
  exact intChainMap_natural p q m h g

end CycleQ2UnframedProductChain

set_option autoImplicit false
namespace CycleQ2RectangularSections

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap freeOpenSections)
open CycleQ2RectangularTrace (secs res)

private abbrev Ab := AddCommGrpCat.{0}
private abbrev CC := CochainComplex Ab ℤ
variable {X : TopCat.{0}} (K : CochainComplex (AbSheaf X) ℤ)
  (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

abbrev row (U : Opens X) : CC :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) Ab ⋙
    (evaluation (Opens X)ᵒᵖ Ab).obj (op U)).mapHomologicalComplex (.up ℤ)).obj K

def restriction {U V : Opens X} (h : U ≤ V) : row K V ⟶ row K U where
  f n := (K.X n).obj.map (homOfLE h).op
  comm' i j _ := ((K.d i j).hom.naturality _)

def evaluate (U : Opens X) : secs K (freeOpen U) ≅ row K U := by
  refine Hom.isoOfComponents (fun n => (freeOpenSections (K.X n) U).toAddCommGrpIso) ?_
  intro i j _
  apply AddCommGrpCat.ext
  intro x
  exact (CycleQ2CechTwoToDerived.freeOpenSections_postcomp U x (K.d i j)).symm

private theorem evaluate_res {U V : Opens X} (h : U ≤ V) :
    (evaluate K V).hom ≫ restriction K h = res K (freeOpenMap h) ≫ (evaluate K U).hom := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact (CycleQ2InjectiveCech.freeOpenSections_naturality (K.X n) h x).symm

private theorem res_comp {P Q R : AbSheaf X} (a : P ⟶ Q) (b : Q ⟶ R) :
    res K b ≫ res K a = res K (a ≫ b) := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact (Category.assoc a b x).symm

private theorem res_add {P Q : AbSheaf X} (a b : P ⟶ Q) :
    res K a + res K b = res K (a+b) := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact (Preadditive.add_comp P Q (K.X n) a b (show Q ⟶ K.X n from x)).symm

private theorem res_id (P : AbSheaf X) : res K (𝟙 P) = 𝟙 _ := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact Category.id_comp x

private theorem res_zero {P Q : AbSheaf X} : res K (0 : P ⟶ Q) = 0 := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact CategoryTheory.Limits.zero_comp (f := (show Q ⟶ K.X n from x))

private theorem res_neg {P Q : AbSheaf X} (a : P ⟶ Q) : -res K a = res K (-a) := by
  apply Hom.ext
  funext n
  apply AddCommGrpCat.ext
  intro x
  exact (Preadditive.neg_comp a x).symm

private def sumIso (P Q : AbSheaf X) : secs K (P ⊞ Q) ≅ secs K P ⊞ secs K Q where
  hom := biprod.lift (res K biprod.inl) (res K biprod.inr)
  inv := biprod.desc (res K biprod.fst) (res K biprod.snd)
  hom_inv_id := by
    rw [biprod.lift_desc,res_comp,res_comp,res_add,biprod.total,res_id]
  inv_hom_id := by
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp only [biprod.inl_desc_assoc,Category.assoc,biprod.lift_fst,biprod.inl_fst,
          res_comp,res_id,Category.comp_id]
      · simp only [biprod.inl_desc_assoc,Category.assoc,biprod.lift_snd,biprod.inl_snd,
          biprod.inr_fst,res_comp,res_zero,Category.comp_id]
    · apply biprod.hom_ext
      · simp only [biprod.inr_desc_assoc,Category.assoc,biprod.lift_fst,biprod.inr_fst,
          biprod.inl_snd,res_comp,res_zero,Category.comp_id]
      · simp only [biprod.inr_desc_assoc,Category.assoc,biprod.lift_snd,biprod.inr_snd,
          res_comp,res_id,Category.comp_id]

def pairIso : secs K S.shortComplex.X₂ ≅ row K S.X₂ ⊞ row K S.X₃ :=
  sumIso K (freeOpen S.X₂) (freeOpen S.X₃) ≪≫ biprod.mapIso (evaluate K S.X₂) (evaluate K S.X₃)

def difference : row K S.X₂ ⊞ row K S.X₃ ⟶ row K S.X₁ :=
  biprod.desc (restriction K S.f₁₂.le) (-(restriction K S.f₁₃.le))

private theorem split_lift {A B M : AbSheaf X} (a : M ⟶ A) (b : M ⟶ B) :
    (sumIso K A B).hom ≫ biprod.desc (res K a) (-(res K b)) = res K (biprod.lift a (-b)) := by
  change biprod.lift _ _ ≫ _ = _
  rw [biprod.lift_desc,Preadditive.comp_neg,res_comp,res_comp,
    res_neg,res_add,biprod.lift_eq,Preadditive.neg_comp]

private theorem evaluated_sum {U V W : Opens X} (a : W ≤ U) (b : W ≤ V) :
    biprod.map (evaluate K U).hom (evaluate K V).hom ≫ biprod.desc (restriction K a) (-restriction K b) =
      biprod.desc (res K (freeOpenMap a)) (-(res K (freeOpenMap b))) ≫ (evaluate K W).hom := by
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc,biprod.inl_desc_assoc,biprod.inl_desc]
    exact evaluate_res K a
  · simp only [biprod.inr_map_assoc,biprod.inr_desc_assoc,biprod.inr_desc,
      Preadditive.comp_neg,Preadditive.neg_comp]
    exact congrArg Neg.neg (evaluate_res K b)

private theorem signed_square {U V W : Opens X} (a : W ≤ U) (b : W ≤ V) :
    ((sumIso K (freeOpen U) (freeOpen V)).hom ≫ biprod.map (evaluate K U).hom (evaluate K V).hom) ≫
      biprod.desc (restriction K a) (-restriction K b) =
      res K (biprod.lift (freeOpenMap a) (-(freeOpenMap b))) ≫ (evaluate K W).hom := by
  rw [Category.assoc,evaluated_sum,← Category.assoc,split_lift]

theorem difference_eq :
    (pairIso K S).hom ≫ difference K S =
      (CycleQ2RectangularTrace.pair S.shortComplex K).g ≫ (evaluate K S.X₁).hom :=
  signed_square K S.f₁₂.le S.f₁₃.le

/-- A change of coordinates of both rows induces an isomorphism of their ordinary cones. -/
private def coneCongr {A B C D : CC} (f : A ⟶ B) (g : C ⟶ D) (e : A ≅ C) (w : B ≅ D)
    (h : e.hom ≫ g = f ≫ w.hom) : mappingCone f ≅ mappingCone g := by
  have h' : g ≫ w.inv = e.inv ≫ f := by
    rw [← cancel_epi e.hom,← Category.assoc,h,Category.assoc,Iso.hom_inv_id,Category.comp_id,
      Iso.hom_inv_id_assoc]
  exact
    { hom := mappingCone.map _ _ e.hom w.hom h.symm
      inv := mappingCone.map _ _ e.inv w.inv h'
      hom_inv_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id]
      inv_hom_id := by rw [← mappingCone.map_comp]; simp [mappingCone.map_id] }

def sectionConeIso : CycleQ2RectangularTrace.rectangleCone S.shortComplex K ≅
    mappingCone (difference K S) :=
  coneCongr _ _ (pairIso K S) (evaluate K S.X₁) (difference_eq K S)

section Product
open CycleQ2LaurentProjectiveLine CycleQ2ProjectiveLineStructure CycleQ2RectangularTrace
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
attribute [local instance] HasDerivedCategory.standard HasExt.standard
variable {k : Type} [Field k] [CharZero k] {C X Y : Scheme.{0}} [AlgebraicGeometry.IsIntegral C]
  (f : C ⟶ line k) (t : X ⟶ Spec (CommRingCat.of k)) (U : X.Opens)
  (i : Y ⟶ pullback (f ≫ structureMap k) t) (p : Y ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [IsFinite f] [IsAffineHom i] [SmoothOfRelativeDimension r p]

/-- Ordinary de Rham hypercohomology of the actual open product, evaluated
on geometric sections, using its two affine curve rectangles and their overlap. -/
def geometricRectangleClasses (hU : IsAffineOpen U) (n : ℤ) :
    (mappingCone (difference (relativeDeRhamInt p r) (sourceRectangle f t U i))).homology (n-1) ≃+
    ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj
      (freeOpen (i ⁻¹ᵁ baseOpen f t U)) ⟶ (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦n⟧) :=
  (((homologyFunctor Ab (.up ℤ) (n-1)).mapIso
    (sectionConeIso (relativeDeRhamInt p r) (sourceRectangle f t U i))).symm.addCommGroupIsoToAddEquiv).trans
      (affineRectangleClasses f t U i p r hU n)
end Product

end CycleQ2RectangularSections

namespace CycleQ2NativeCurveFiber
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open CycleQ2LaurentProjectiveLine HomologicalComplex CochainComplex

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} [IsIntegral X]
  (q : X ⟶ line k) [IsFinite q] [IsDominant q]
local notation "S" => CycleQ2FiniteCurveCover.square k q
local notation "I" => ComplexShape.up ℤ
private abbrev Ab := AddCommGrpCat.{0}
private abbrev forgetModule := forget₂ (ModuleCat.{0} k) Ab
private abbrev forgetComplex := (forgetModule (k := k)).mapHomologicalComplex (ComplexShape.up ℤ)

variable (L : CochainComplex (ModuleCat.{0} k) ℤ)

def alternatingAb :
    (forgetComplex (k := k)).obj (tensorObj (affineRow k q (S).X₂) L) ⊞
    (forgetComplex (k := k)).obj (tensorObj (affineRow k q (S).X₃) L) ⟶
    (forgetComplex (k := k)).obj (tensorObj (affineRow k q (S).X₁) L) :=
  biprod.desc ((forgetComplex (k := k)).map (tensorHom (affineRestriction k q (S).f₁₂.le) (𝟙 L)))
    (-(forgetComplex (k := k)).map (tensorHom (affineRestriction k q (S).f₁₃.le) (𝟙 L)))

def abCohomology (n : ℤ) :
    (forgetModule (k := k)).obj ((tensorObj (CycleQ2CurveTensorTrace.curve k q) L).homology n) ≅
    (mappingCone (alternatingAb q L)).homology (n-1) := by
  let F := forgetModule (k := k)
  let G := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let a := tensorHom (affineRestriction k q (S).f₁₂.le) (𝟙 L)
  let b := tensorHom (affineRestriction k q (S).f₁₃.le) (𝟙 L)
  let f := biprod.desc a (-b)
  let H := homologyFunctor Ab (ComplexShape.up ℤ) (n-1)
  let : PreservesBinaryBiproducts G := preservesBinaryBiproducts_of_preservesBiproducts G
  let e := G.mapBiprod (tensorObj (affineRow k q (S).X₂) L) (tensorObj (affineRow k q (S).X₃) L)
  have h : e.hom ≫ alternatingAb q L = G.map f := by
    change (G.mapBiprod _ _).hom ≫ biprod.desc (G.map a) (-G.map b) = G.map _
    rw [← G.map_neg,biprod.mapBiprod_hom_desc]
  let coneIso := CycleQ2RectangularSections.coneCongr
    (G.map f) (alternatingAb q L) e (Iso.refl _) (by simpa using h)
  exact F.mapIso (rectangleCohomology k q L n) ≪≫
    ((((mappingCone f).sc (n-1)).mapHomologyIso F).symm) ≪≫
    H.mapIso (mappingCone.mapHomologicalComplexIso f F) ≪≫ H.mapIso coneIso
end CycleQ2NativeCurveFiber

namespace CycleQ2ProperRectangleTrace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4000
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry TopologicalSpace
open CochainComplex HomologicalComplex
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)
open CycleQ2UnframedProductChain
open CycleQ2NativeCurveFiber (affineRow affineRestriction alternatingAb abCohomology)
open CycleQ2RectangularTrace (sourceRectangle baseOpen)
open CycleQ2RectangularSections (difference geometricRectangleClasses)
open scoped KaehlerDifferential
attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (f : C ⟶ line k) [SmoothOfRelativeDimension 1 (f ≫ structureMap k)]
  (t : X ⟶ Spec (CommRingCat.of k)) (m : ℕ) [SmoothOfRelativeDimension m t]
  (V : FramedOpen t m)

private abbrev M := ModuleCat.{0} k
private abbrev Ab := AddCommGrpCat.{0}
private abbrev G := (forget₂ (M (k := k)) Ab).mapHomologicalComplex (.up ℤ)
local notation "p" => f ≫ structureMap k
local notation "S" => CycleQ2FiniteCurveCover.square k f
local notation "P" => productBase p t
local notation "E" => ComplexShape.embeddingUpNat
local instance : SmoothOfRelativeDimension (1+m) P := CycleQ2ProductFramedOpen.smooth_product p t m

abbrev horizontal : CochainComplex (M (k := k)) ℤ :=
  letI := (sectionCoefficients t V.1).toAlgebra
  (CycleQ2SignedRowComparison.horizontal (frame t m V) (functions t m V) (frame_apply t m V)).extend E

def affineIso (U : C.Opens) (hU : IsAffineOpen U) :
    (G (k := k)).obj (tensorObj (affineRow k f U) (horizontal t m V)) ≅ intNative p t m U V.1 := by
  letI := (sectionCoefficients p U).toAlgebra
  letI := (sectionCoefficients t V.1).toAlgebra
  exact (G (k := k)).mapIso (CycleQ2SignedRowComparison.signedIso (A := Γ(C,U))
    (frame t m V) (functions t m V) (frame_apply t m V)) ≪≫
    intAffineIso p t m hU V

/-- Restriction of the base de Rham cochain complex between framed affine target opens. -/
def horizontalRestriction {V' : FramedOpen t m} (g : V'.1 ≤ V.1) :
    horizontal t m V ⟶ horizontal t m V' := by
  letI (W : X.Opens) := (sectionCoefficients t W).toAlgebra
  exact extendMap (CycleQ2SignedRowComparison.hMap (frame t m V) (functions t m V) (frame_apply t m V)
    (frame t m V') (functions t m V') (frame_apply t m V') (restrict t g)) E

omit [SmoothOfRelativeDimension m t] in
@[simp] theorem horizontalRestriction_id :
    horizontalRestriction t m V (le_refl V.1) = 𝟙 (horizontal t m V) := by
  let := (sectionCoefficients t V.1).toAlgebra
  change extendMap (CycleQ2SignedRowComparison.hMap _ _ _ _ _ _ (restrict t (le_refl V.1))) E = _
  rw [CycleQ2FramedAffineSite.restrict_id t V.1,CycleQ2SignedRowComparison.hMap_id,extendMap_id]

/-- The row comparison respects restriction in both factors simultaneously. -/
theorem affineIso_natural {V' : FramedOpen t m} {U U' : C.Opens} (h : U' ≤ U) (g : V'.1 ≤ V.1)
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U') :
    (affineIso f t m V U hU).hom ≫ intNativeRestriction p t m h g =
    (G (k := k)).map (tensorHom (affineRestriction k f h) (horizontalRestriction t m V g)) ≫
      (affineIso f t m V' U' hU').hom := by
  let (W : C.Opens) := (sectionCoefficients p W).toAlgebra
  let (W : X.Opens) := (sectionCoefficients t W).toAlgebra
  let e := CycleQ2SignedRowComparison.signedIso (A := Γ(C,U)) (frame t m V) (functions t m V) (frame_apply t m V)
  let e' := CycleQ2SignedRowComparison.signedIso (A := Γ(C,U')) (frame t m V') (functions t m V') (frame_apply t m V')
  let J := G (k := k)
  let r := tensorHom (affineRestriction k f h) (horizontalRestriction t m V g)
  let a := CycleQ2OrdinaryTensorRows.restrictComplex p t m V h g
  have aSq : r ≫ e'.hom = e.hom ≫ extendMap a E :=
    CycleQ2SignedRowComparison.signedIso_restriction (frame t m V) (functions t m V) (frame_apply t m V)
      (frame t m V') (functions t m V') (frame_apply t m V') (restrict p h) (restrict t g)
  have x : CommSq (J.map e.hom) (J.map r) (J.map (extendMap a E)) (J.map e'.hom) :=
    ⟨by rw [← J.map_comp,← J.map_comp,aSq]⟩
  have y : CommSq (intAffineIso p t m hU V).hom (J.map (extendMap a E))
      (intNativeRestriction p t m h g) (intAffineIso p t m hU' V').hom :=
    ⟨intAffineIso_natural p t m hU hU' h g⟩
  exact (x.horiz_comp y).w

variable [IsIntegral C] [IsFinite f] [IsDominant f]

private abbrev square := sourceRectangle f t V.1 (𝟙 (pullback p t))

/-- The two actual restrictions of both coordinate algebras commute with the
row comparisons, so the signed ordinary cones agree on the literal product. -/
def properConeIso : mappingCone (alternatingAb f (horizontal t m V)) ≅
    mappingCone (difference (relativeDeRhamInt P (1+m)) (square f t m V)) := by
  let A := affineIso f t m V _ (CycleQ2FiniteCurveCover.zero_affine k f)
  let B := affineIso f t m V _ (CycleQ2FiniteCurveCover.infinity_affine k f)
  let W := affineIso f t m V _ (CycleQ2FiniteCurveCover.torus_affine k f)
  refine CycleQ2RectangularSections.coneCongr _ _ (biprod.mapIso A B) W ?_
  apply biprod.hom_ext'
  · change biprod.inl ≫ biprod.map A.hom B.hom ≫ biprod.desc _ _ = biprod.inl ≫ (biprod.desc _ _ ≫ W.hom)
    simp only [biprod.inl_map_assoc,biprod.inl_desc,biprod.inl_desc_assoc]
    have h := affineIso_natural f t m V (S).f₁₂.le (le_refl V.1)
      (CycleQ2FiniteCurveCover.zero_affine k f) (CycleQ2FiniteCurveCover.torus_affine k f)
    rw [horizontalRestriction_id] at h
    exact h
  · change biprod.inr ≫ biprod.map A.hom B.hom ≫ biprod.desc _ _ = biprod.inr ≫ (biprod.desc _ _ ≫ W.hom)
    simp only [biprod.inr_map_assoc,biprod.inr_desc,biprod.inr_desc_assoc,Preadditive.comp_neg,Preadditive.neg_comp]
    have h := affineIso_natural f t m V (S).f₁₃.le (le_refl V.1)
      (CycleQ2FiniteCurveCover.infinity_affine k f) (CycleQ2FiniteCurveCover.torus_affine k f)
    rw [horizontalRestriction_id] at h
    exact congrArg Neg.neg h

private abbrev site := CycleQ2InjectiveCech.AbSheaf (show TopCat from (pullback p t : Scheme))
abbrev ordinary (n : ℤ) :=
  (DerivedCategory.singleFunctor (site f t) 0).obj (CycleQ2InjectiveCech.freeOpen (baseOpen f t V.1)) ⟶
    (DerivedCategory.Q.obj (relativeDeRhamInt P (1+m)))⟦n⟧

/-- Genuine de Rham hypercohomology on the open full proper-curve product
is computed by the curve/affine tensor complex used in integration. -/
def properProductCohomology (n : ℤ) :
    (tensorObj (CycleQ2CurveTensorTrace.curve k f) (horizontal t m V)).homology n ≃+
      ordinary f t m V n :=
  ((abCohomology f (horizontal t m V) n ≪≫
    (homologyFunctor Ab (.up ℤ) (n-1)).mapIso (properConeIso f t m V)).addCommGroupIsoToAddEquiv).trans
      (geometricRectangleClasses f t V.1 (𝟙 (pullback p t)) P (1+m) V.2.1 n)

/-- On the actual full proper-curve product above the affine target, cup
with a closed curve cochain and apply its proper trace. -/
def cylinder (z : (CycleQ2NativeCurveTraceComplex.complex k f).X 1)
    (hz : (CycleQ2NativeCurveTraceComplex.complex k f).d 1 2 z = 0) (n : ℤ) :
    ordinary f t m V n →+ (horizontal t m V).homology (n-1) := by
  let L := horizontal t m V
  let α := CycleQ2CurveOnePairing.cylinderInto k f z hz L
  let e := ((homologyFunctor (ModuleCat k) (.up ℤ) 0).shiftIso (-1:ℤ) n (n-1) (by omega)).app L
  exact ((homologyMap α n ≫ e.hom).hom.toAddMonoidHom).comp
    (properProductCohomology f t m V n).symm.toAddMonoidHom

/-- Replacing the curve cocycle by a cohomologous one gives the same operation
on genuine de Rham classes of the proper product. -/
theorem cylinder_cohomologous (z y : (CycleQ2NativeCurveTraceComplex.complex k f).X 1)
    (hz : (CycleQ2NativeCurveTraceComplex.complex k f).d 1 2 z = 0)
    (hy : (CycleQ2NativeCurveTraceComplex.complex k f).d 1 2 y = 0)
    (a : (CycleQ2NativeCurveTraceComplex.complex k f).X 0)
    (ha : z-y = (CycleQ2NativeCurveTraceComplex.complex k f).d 0 1 a) (n : ℤ) :
    cylinder f t m V z hz n = cylinder f t m V y hy n := by
  let L := horizontal t m V
  let e := ((homologyFunctor (ModuleCat k) (.up ℤ) 0).shiftIso (-1:ℤ) n (n-1) (by omega)).app L
  exact congrArg (fun w : (tensorObj (CycleQ2CurveTensorTrace.curve k f) L).homology n ⟶ (L⟦(-1:ℤ)⟧).homology n =>
    ((w ≫ e.hom).hom.toAddMonoidHom).comp (properProductCohomology f t m V n).symm.toAddMonoidHom)
      (CycleQ2CurveOnePairing.cylinder_cohomologous k f z y hz hy a ha L n)

end CycleQ2ProperRectangleTrace

#print axioms CycleQ2ProperRectangleTrace.properProductCohomology
#print axioms CycleQ2ProperRectangleTrace.cylinder

namespace CycleQ2NativeWeightedTopGerm

open CategoryTheory AlgebraicGeometry
open CycleQ2MonicGenericAmbientChart (genericChartRing)
open CycleQ2NormalWeightedCotangent (A Cubic cubicIso inclusion)
open CycleQ2NativeNormalFunctionField (toField_native)
open CycleQ2NativeNormalResidue (Patch evaluatePatch evaluatePatch_algebraMap)
open CycleQ2NativeResidueOffGraph (patchInclusion)
open CycleQ2GenericProperGraphSupport (chart)
open CycleQ2NativeWeightedFieldAlgebra (fieldAlgEquiv)
open CycleQ2GenericGraphFunctionStalk (chartField)
open CycleQ2UniversalWeightedDeRham (W)

private theorem spec_triple {R S T B : CommRingCat.{0}} {Z : Scheme.{0}} (f : R ⟶ S) (g : S ⟶ T)
    (a : T ⟶ B) (i : Spec R ⟶ Z) :
    Spec.map a ≫ Spec.map g ≫ Spec.map f ≫ i = Spec.map (f ≫ g ≫ a) ≫ i := by
  rw [← Spec.map_comp_assoc,← Spec.map_comp_assoc]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
/-- Every nonzero weighted patch evaluates at the same native chart function
point after the coefficient-preserving identification of function fields. -/
theorem functionPoint_eq_native (s : A) (hs : s ≠ 0) :
    functionPoint s hs = Spec.map (CommRingCat.ofHom fieldAlgEquiv.toAlgHom.toRingHom) ≫
      CycleQ2GenericGraphFunctionStalk.functionPoint := by
  let α : genericChartRing →+* W := (evaluatePatch s hs).toRingHom.comp
    ((algebraMap A (Patch s)).comp ((algebraMap Cubic A).comp cubicIso.toRingHom))
  let β : genericChartRing →+* W :=
    fieldAlgEquiv.toAlgHom.toRingHom.comp (algebraMap genericChartRing chartField)
  have h : α = β := by
    apply RingHom.ext
    intro x
    change evaluatePatch s hs (algebraMap A (Patch s) (algebraMap Cubic A (cubicIso x))) =
      fieldAlgEquiv (algebraMap genericChartRing chartField x)
    exact (evaluatePatch_algebraMap s hs _).trans (toField_native x)
  calc
    functionPoint s hs = Spec.map (CommRingCat.ofHom α) ≫ chart := by
      exact spec_triple (CommRingCat.ofHom ((algebraMap Cubic A).comp cubicIso.toRingHom))
        (CommRingCat.ofHom (algebraMap A (Patch s))) (CommRingCat.ofHom (evaluatePatch s hs).toRingHom) chart
    _ = Spec.map (CommRingCat.ofHom β) ≫ chart := by rw [h]
    _ = _ := by
      exact Spec.map_comp_assoc (CommRingCat.ofHom (algebraMap genericChartRing chartField))
        (CommRingCat.ofHom fieldAlgEquiv.toAlgHom.toRingHom) chart

end CycleQ2NativeWeightedTopGerm

namespace CycleQ2ProperRectangleTrace
open CategoryTheory AlgebraicGeometry TopologicalSpace HomologicalComplex CochainComplex
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame functions frame_apply)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2ArbitraryFrameDifferential (d)
open scoped KaehlerDifferential

section Top
variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (t : X ⟶ Spec (CommRingCat.of k)) (V : FramedOpen t 3)
local instance : Algebra k Γ(X,V.1) := (sectionCoefficients t V.1).toAlgebra
private abbrev baseRow := CycleQ2SignedRowComparison.horizontal (frame t 3 V) (functions t 3 V) (frame_apply t 3 V)
private abbrev topSequence := (baseRow t V).sc 3
private theorem topOutgoing : (topSequence t V).g = 0 := by
  change (baseRow t V).d 3 ((ComplexShape.up ℕ).next 3) = 0
  rw [(ComplexShape.up ℕ).next_eq' (j := 4) (by rfl)]
  let : Subsingleton (Form k Γ(X,V.1) 4) := CycleQ2SurfaceDeRhamChart.exterior_subsingleton (frame t 3 V) (by decide)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact Subsingleton.elim (α := Form k Γ(X,V.1) 4) _ _

private def topQuotientIso :
    (topSequence t V).opcycles ≅ (horizontal t 3 V).homology 3 :=
  ((topSequence t V).asIsoHomologyι (topOutgoing t V)).symm ≪≫
    ((baseRow t V).extendHomologyIso ComplexShape.embeddingUpNat (j := 3) (j' := 3) rfl).symm

/-- The class of an ordinary three-form in the horizontal cohomology group
which is the target of the proper cylinder in degree four. -/
def topFormClass : Form k Γ(X,V.1) 3 →+ (horizontal t 3 V).homology 3 :=
  ((topSequence t V).pOpcycles ≫ (topQuotientIso t V).hom).hom.toAddMonoidHom

omit [CharZero k] in
private theorem mappedClass_zero_iff {D : ModuleCat.{0} k}
    (S : CategoryTheory.ShortComplex (ModuleCat.{0} k)) (e : S.opcycles ≅ D) (x : S.X₂) :
    (S.pOpcycles ≫ e.hom) x = 0 ↔ ∃ y, S.f y = x := by
  have hi := (ModuleCat.mono_iff_injective e.hom).mp inferInstance
  change e.hom (S.pOpcycles x) = 0 ↔ _
  rw [← map_zero e.hom.hom,hi.eq_iff,S.moduleCat_pOpcycles_eq_zero_iff]
  rfl

set_option maxHeartbeats 1600000 in
theorem topFormClass_zero_iff (ω : Form k Γ(X,V.1) 3) :
    topFormClass t V ω = 0 ↔ ∃ η : Form k Γ(X,V.1) 2, d (frame t 3 V) 2 η = ω := by
  refine (mappedClass_zero_iff (topSequence t V) (topQuotientIso t V) ω).trans ?_
  change (∃ η, (baseRow t V).d ((ComplexShape.up ℕ).prev 3) 3 η = ω) ↔ _
  erw [show (ComplexShape.up ℕ).prev 3 = 2 from (ComplexShape.up ℕ).prev_eq' (by rfl)]
  erw [show (baseRow t V).d 2 3 = ModuleCat.ofHom (d (frame t 3 V) 2) from
    CochainComplex.of_d (fun i => ModuleCat.of k (Form k Γ(X,V.1) i))
      (fun i => ModuleCat.ofHom (d (frame t 3 V) i)) 2]
  rfl
end Top

section Protected
open CycleQ2UniversalWeightedDeRham (K W sourceForm)
open CycleQ2RelativePointEvaluation (point value)
open CycleQ2WeightedRationalRestriction (evaluate ExactWedgeRule protected_exact_of_affine_boundary)
variable {X : Scheme.{0}} (t : X ⟶ Spec (CommRingCat.of K)) (V : FramedOpen t 3)
local instance : Algebra K Γ(X,V.1) := (sectionCoefficients t V.1).toAlgebra

/-- A vanishing cylinder value identified with the prescribed three-form at
the protected function point yields an actual primitive of the original four-form. -/
theorem protected_of_topFormClass_zero (x : Spec (CommRingCat.of W) ⟶ X)
    (hx : x ≫ t = Spec.map (CommRingCat.ofHom (algebraMap K W)))
    (hV : point x ∈ V.1) (ω : Form K Γ(X,V.1) 3)
    (hω : evaluate (value t x hx V.1 hV) 3 ω = sourceForm) (hz : topFormClass t V ω = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  obtain ⟨η,hη⟩ := (topFormClass_zero_iff t V ω).mp hz
  let δ := (d (frame t 3 V) 2).toAddMonoidHom
  have hδ : ExactWedgeRule δ := by
    intro a b c
    have h := CycleQ2FrameCanonicalDifferential.d_exact_symbol (frame t 3 V)
      (functions t 3 V) (frame_apply t 3 V) 2 a ![b,c]
    exact h.trans (congrArg (exteriorPower.ιMulti Γ(X,V.1) 3)
      (funext fun i => by fin_cases i <;> rfl))
  exact protected_exact_of_affine_boundary (value t x hx V.1 hV) δ hδ ω hω η hη
end Protected

section WeightedVertex
open Opposite
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2NativeWeightedDeRham (vertex VertexSections asOrdinaryForm)
open CycleQ2NativeWeightedTopGerm (functionPoint functionPoint_over x_mem_vertex)
open CycleQ2NormalWeightedCotangent (A)
open CycleQ2UniversalWeightedDeRham (K W sourceForm)
open CycleQ2RelativeDeRhamSheaves (onBasisIso)
open CycleQ2RelativeSectionPullback (sectionPull)
open CycleQ2RelativePointEvaluation (value point)
open CycleQ2ExactFrameThreeDeRham (exteriorPullback)

local instance : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
variable (s : A) {Y : Scheme.{0}} (j : Y ⟶ genericAmbient) (V : FramedOpen (j ≫ ambientToField) 3)
  (h : V.1 ≤ j ⁻¹ᵁ (vertex s).1)
local instance : Algebra K Γ(Y,V.1) := (sectionCoefficients (j ≫ ambientToField) V.1).toAlgebra
local instance : Algebra K Γ(genericAmbient,(vertex s).1) := (sectionCoefficients ambientToField (vertex s).1).toAlgebra
private abbrev pull := sectionPull ambientToField (j ≫ ambientToField) j rfl (vertex s).1 V.1 h

/-- The original weighted vertex section, pulled back to the framed affine
target of the proper cylinder. In particular the target may lie on the
surviving open subscheme of the generic threefold. -/
def restrictedVertexClass (ω : VertexSections s) : (horizontal (j ≫ ambientToField) 3 V).homology 3 :=
  topFormClass (j ≫ ambientToField) V (exteriorPullback (pull s j V h) 3
    ((onBasisIso ambientToField 3).hom.app (op (vertex s)) ω))

variable (hs : s ≠ 0) (y : Spec (CommRingCat.of W) ⟶ Y) (hy : y ≫ j = functionPoint s hs)
  (hV : point y ∈ V.1)

include hy in
private theorem lift_over : y ≫ j ≫ ambientToField = Spec.map (CommRingCat.ofHom (algebraMap K W)) := by
  rw [← Category.assoc,hy,functionPoint_over]

private theorem pull_value :
    (value (j ≫ ambientToField) y (lift_over s j hs y hy) V.1 hV).comp (pull s j V h) =
      value ambientToField (functionPoint s hs) (functionPoint_over s hs) (vertex s).1 (x_mem_vertex s hs) := by
  have topV : ⊤ ≤ y ⁻¹ᵁ V.1 := fun x _ => by
    change y x ∈ V.1
    rw [Subsingleton.elim x (IsLocalRing.closedPoint W)]
    exact hV
  have topU : ⊤ ≤ functionPoint s hs ⁻¹ᵁ (vertex s).1 := fun x _ => by
    change functionPoint s hs x ∈ (vertex s).1
    rw [Subsingleton.elim x (IsLocalRing.closedPoint W)]
    exact x_mem_vertex s hs
  have same (z z' : Spec (CommRingCat.of W) ⟶ genericAmbient) (eq : z = z')
      (u : ⊤ ≤ z ⁻¹ᵁ (vertex s).1) (u' : ⊤ ≤ z' ⁻¹ᵁ (vertex s).1) :
      z.appLE (vertex s).1 ⊤ u = z'.appLE (vertex s).1 ⊤ u' := by
    subst z'
    rfl
  have e : j.appLE (vertex s).1 V.1 h ≫ y.appLE V.1 ⊤ topV = (functionPoint s hs).appLE (vertex s).1 ⊤ topU := by
    rw [Scheme.Hom.appLE_comp_appLE]
    exact same _ _ hy _ _
  apply AlgHom.ext
  intro a
  exact congrArg (fun v : Γ(genericAmbient,(vertex s).1) ⟶ Γ(Spec (CommRingCat.of W),⊤) =>
    (v ≫ (Scheme.ΓSpecIso (CommRingCat.of W)).hom) a) e

/-- Vanishing of the genuine weighted vertex class on a framed restriction
containing its lifted function point gives an actual primitive of the protected
four-form. This applies to the literal surviving open and its inclusion. -/
theorem protected_of_restrictedVertexClass_zero
    (yc : Spec (CommRingCat.of CycleQ2GenericGraphFunctionStalk.chartField) ⟶ Y)
    (hc : yc ≫ j = CycleQ2GenericGraphFunctionStalk.functionPoint) (hVc : Set.range yc ⊆ (V.1 : Set Y))
    (ω : VertexSections s)
    (hω : CycleQ2WeightedRationalRestriction.evaluate (CycleQ2NativeNormalResidue.evaluatePatch s hs) 3
      (asOrdinaryForm s ω) = sourceForm) (hz : restrictedVertexClass s j V h ω = 0) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  let ψ := Spec.map (CommRingCat.ofHom CycleQ2NativeWeightedFieldAlgebra.fieldAlgEquiv.toAlgHom.toRingHom)
  let y := ψ ≫ yc
  have hy : y ≫ j = functionPoint s hs := by
    change (ψ ≫ yc) ≫ j = _
    rw [Category.assoc,hc]
    exact (CycleQ2NativeWeightedTopGerm.functionPoint_eq_native s hs).symm
  have hV : point y ∈ V.1 := hVc ⟨ψ (IsLocalRing.closedPoint W),rfl⟩
  let r := pull s j V h
  let e := value (j ≫ ambientToField) y (lift_over s j hs y hy) V.1 hV
  let α : Form K Γ(genericAmbient,(vertex s).1) 3 := (onBasisIso ambientToField 3).hom.app (op (vertex s)) ω
  apply protected_of_topFormClass_zero (j ≫ ambientToField) V y (lift_over s j hs y hy) hV
    (exteriorPullback r 3 α) _ hz
  change exteriorPullback e 3 (exteriorPullback r 3 α) = sourceForm
  exact (CycleQ2AffineDeRhamFunctorial.exteriorPullback_comp r e 3 α).symm.trans <|
    (congrArg (fun z : Γ(genericAmbient,(vertex s).1) →ₐ[K] W => exteriorPullback z 3 α)
      (pull_value s j V h hs y hy hV)).trans ((CycleQ2NativeWeightedTopGerm.eval_vertex s hs ω).trans hω)

end WeightedVertex

end CycleQ2ProperRectangleTrace

#print axioms CycleQ2ProperRectangleTrace.protected_of_restrictedVertexClass_zero

namespace CycleQ2NativeWeightedTopGerm
open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2NativeWeightedDeRham (vertex)
open CycleQ2LiteralIncidenceGenericCorrespondence (genericAmbient)
open CycleQ2GenericGraphFunctionStalk (chartField)
open CycleQ2NativeWeightedFieldAlgebra (fieldAlgEquiv)
open CycleQ2UniversalWeightedDeRham (W)

/-- An exact-framed affine subopen surrounding the entire image of a
field-valued point exists inside any neighborhood of its closed point. -/
theorem exists_framed_neighborhood
    {k L : Type} [Field k] [CharZero k] [Field L] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of k)) (n : ℕ) [SmoothOfRelativeDimension n p]
    (y : Spec (CommRingCat.of L) ⟶ Y) (B : Y.Opens)
    (hy : y (IsLocalRing.closedPoint L) ∈ B) :
    ∃ V : FramedOpen p n, Set.range y ⊆ (V.1 : Set Y) ∧ V.1 ≤ B := by
  obtain ⟨O,hO,hyO,hOB⟩ := Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis p n) hy
  refine ⟨⟨O,hO⟩,?_,hOB⟩
  rintro _ ⟨z,rfl⟩
  rw [Subsingleton.elim z (IsLocalRing.closedPoint L)]
  exact hyO

private theorem nativePoint_mem_vertex (s : CycleQ2NormalWeightedCotangent.A) (hs : s ≠ 0)
    (z : Spec (CommRingCat.of chartField)) :
    CycleQ2GenericGraphFunctionStalk.functionPoint z ∈ (vertex s).1 := by
  let w : Spec (CommRingCat.of W) := IsLocalRing.closedPoint W
  let e := Spec.map (CommRingCat.ofHom fieldAlgEquiv.toAlgHom.toRingHom)
  rw [Subsingleton.elim z (e w)]
  change (e ≫ CycleQ2GenericGraphFunctionStalk.functionPoint) w ∈ (vertex s).1
  rw [← functionPoint_eq_native s hs]
  exact x_mem_vertex s hs

/-- The open killing the graph class and any specified nonzero weighted
vertex admit one common framed affine refinement on the surviving target. -/
theorem exists_framed_target (U A : genericAmbient.Opens)
    (yc : Spec (CommRingCat.of chartField) ⟶ U.toScheme)
    (hyc : yc ≫ U.ι = CycleQ2GenericGraphFunctionStalk.functionPoint)
    (hpoint : Set.range CycleQ2GenericGraphFunctionStalk.functionPoint ⊆ (A : Set genericAmbient))
    (s : CycleQ2NormalWeightedCotangent.A) (hs : s ≠ 0) :
    ∃ V : FramedOpen (U.ι ≫ ambientToField) 3, Set.range yc ⊆ (V.1 : Set U.toScheme) ∧
      V.1 ≤ U.ι ⁻¹ᵁ A ∧ V.1 ≤ U.ι ⁻¹ᵁ (vertex s).1 := by
  let : SmoothOfRelativeDimension 3 ambientToField := CycleQ2NativeGenericSmooth.ambient_smooth
  let : SmoothOfRelativeDimension 3 (U.ι ≫ ambientToField) :=
    smoothOfRelativeDimension_comp 0 3 _ _
  let z : Spec (CommRingCat.of chartField) := IsLocalRing.closedPoint chartField
  have hp : U.ι (yc z) = CycleQ2GenericGraphFunctionStalk.functionPoint z :=
    congrArg (fun f : Spec (CommRingCat.of chartField) ⟶ genericAmbient => f z) hyc
  have hB : yc z ∈ (U.ι ⁻¹ᵁ A) ⊓ (U.ι ⁻¹ᵁ (vertex s).1) := by
    change U.ι (yc z) ∈ A ∧ U.ι (yc z) ∈ (vertex s).1
    rw [hp]
    exact ⟨hpoint ⟨z,rfl⟩,nativePoint_mem_vertex s hs z⟩
  obtain ⟨V,hV,hVB⟩ := exists_framed_neighborhood (U.ι ≫ ambientToField) 3 yc _ hB
  exact ⟨V,hV,hVB.trans inf_le_left,hVB.trans inf_le_right⟩

end CycleQ2NativeWeightedTopGerm

namespace CycleQ2MarkedCylinderRestriction
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralIncidenceRelativeSpread CycleQ2LiteralIncidenceNormalizedSlice
open CycleQ2LiteralIncidenceRelativeCompletion CycleQ2LiteralIncidenceRelativeCorrespondence
open CycleQ2LiteralIncidenceGenericCorrespondence CycleQ2GenericSmoothCurveGraph
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)
open CycleQ2NativeWeightedCover (ambientToField)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2InjectiveCech (AbSheaf freeOpenMap)
open CycleQ2ClosedGraphSupport (complement)
open CycleQ2SurvivingProductGysin (SupportedClass IsNormalized literalOpen literalIso)
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2NativeWeightedDeRham (vertex VertexSections asVertexSection asOrdinaryForm roundTrip)
open CycleQ2NormalWeightedCotangent (A)
open CycleQ2NativeNormalResidue (evaluatePatch)
open CycleQ2WeightedRationalRestriction (evaluate)
open CycleQ2UniversalWeightedDeRham (sourceForm)
open CycleQ2GenericGraphFunctionStalk (chartField functionPoint)
open CycleQ2ProperRectangleTrace (ordinary cylinder)
attribute [local instance] HasDerivedCategory.standard HasExt.standard
set_option maxRecDepth 6000

local notation "T" => ambientToField
local instance targetSmooth (U : genericAmbient.Opens) : SmoothOfRelativeDimension 3 (U.ι ≫ T) := by
  let : SmoothOfRelativeDimension 3 T := CycleQ2NativeGenericSmooth.ambient_smooth
  exact smoothOfRelativeDimension_comp 0 3 _ _

/-- The surface is the literal base change of the original marked incidence,
and its normalized class has the original cubic and row as its ordered
equations arbitrarily near each surface point. -/
def SeedGraph {C S : Scheme.{0}} (c : C ⟶ Spec (CommRingCat.of genericField))
    (U : genericAmbient.Opens) (i : S ⟶ pullback c (U.ι ≫ T))
    [IsClosedImmersion i] [SmoothOfRelativeDimension 4 (productBase c (U.ι ≫ T))]
    (z : SupportedClass (productBase c (U.ι ≫ T)) i) : Prop :=
  ∃ (t : Fin 3 → ℂ), AlgebraicIndependent ℚ t ∧ ∃ (P : parameterScheme.Opens) (hP : seedBasePoint ∈ P)
    (r : C ⟶ Completion P) (hc : r ≫ structureMap P = c ≫ genericPoint)
    (D : Scheme.{0}) (j : D ⟶ C) (a : D ⟶ Time toRaw P)
    (ha : j ≫ r = a ≫ CycleQ2LiteralIncidenceRelativeCompletion.inclusion P) (v : S ⟶ TestSurface P t a),
    let m := fromTest P t r j a ha
    CycleQ2MarkedGenericSurvives.SeedCompatible t P hP c r j a ∧ IsOpenImmersion v ∧
      IsPullback i (v ≫ m.toImage) (literalOpen c U) (m.imageι ≫ embeddingGeneric P t r c hc) ∧
      ∃ (hj : IsOpenImmersion j), let _ := hj
      CycleQ2MarkedGraphChartApplication.HasMarkedCharts t r c hc j a ha (literalOpen c U)
        (productBase c (U.ι ≫ T)) i v z

private abbrev curveBase {C : Scheme.{0}} (f : C ⟶ line genericField) :=
  f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField

private abbrev productStructure {C : Scheme.{0}} (f : C ⟶ line genericField) (U : genericAmbient.Opens) :=
  productBase (curveBase f) (U.ι ≫ T)

section
variable {C S : Scheme.{0}} [IsIntegral C] (f : C ⟶ line genericField)
  [IsFinite f] [IsDominant f] [SmoothOfRelativeDimension 1 (curveBase f)]
  (U : genericAmbient.Opens)
variable (i : S ⟶ pullback (curveBase f) (U.ι ≫ T)) [IsClosedImmersion i]
local instance : SmoothOfRelativeDimension 4 (productStructure f U) := CycleQ2ProductFramedOpen.smooth_product (curveBase f) (U.ι ≫ T) 3

/-- Forget support of the marked class and restrict it to the proper curve
over the chosen framed affine target open. -/
def restrictClass (z : SupportedClass (productStructure f U) i) (V : FramedOpen (U.ι ≫ T) 3) :
    ordinary f (U.ι ≫ T) 3 V 4 :=
  let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from (pullback (curveBase f) (U.ι ≫ T) : Scheme))) 0
  E.map (freeOpenMap (show (pullback.snd (curveBase f) (U.ι ≫ T)) ⁻¹ᵁ V.1 ≤ ⊤ from le_top)) ≫
    E.map (CycleQ2SupportMV.π (complement i) ⊤) ≫ z

/-- The span of the actual cylinder values of one supported graph class
on a specified framed open. -/
def cylinderSpan (z : SupportedClass (productStructure f U) i) (V : FramedOpen (U.ι ≫ T) 3) :
    Submodule genericField ((CycleQ2ProperRectangleTrace.horizontal (U.ι ≫ T) 3 V).homology 3) :=
  Submodule.span genericField {x | ∃ (w : (CycleQ2NativeCurveTraceComplex.complex genericField f).X 1)
    (hw : (CycleQ2NativeCurveTraceComplex.complex genericField f).d 1 2 w = 0),
    x = cylinder f (U.ι ≫ T) 3 V w hw 4 (restrictClass f U i z V)}

/-- Every curve cocycle acts by zero on the ordinary restriction of the
same normalized class. The framed open also carries the actual weighted
vertex form, with evaluation equal to the original protected source. -/
def VanishesOnWeightedFrame (z : SupportedClass (productStructure f U) i) : Prop :=
  ∃ (s : A) (hs : s ≠ 0) (ω : VertexSections s),
    evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) = sourceForm ∧
    ∃ (yc : Spec (CommRingCat.of chartField) ⟶ U.toScheme), yc ≫ U.ι = functionPoint ∧
    ∃ V : FramedOpen (U.ι ≫ T) 3, Set.range yc ⊆ (V.1 : Set U.toScheme) ∧
      ∃ hV : V.1 ≤ U.ι ⁻¹ᵁ (vertex s).1,
        (∀ (w : (CycleQ2NativeCurveTraceComplex.complex genericField f).X 1)
          (hw : (CycleQ2NativeCurveTraceComplex.complex genericField f).d 1 2 w = 0),
          cylinder f (U.ι ≫ T) 3 V w hw 4 (restrictClass f U i z V) = 0) ∧
        (CycleQ2ProperRectangleTrace.restrictedVertexClass s U.ι V hV ω ∈ cylinderSpan f U i z V →
          ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
            CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA)

set_option maxHeartbeats 800000 in
private theorem vanishes_of_avoids
    (z : SupportedClass (productStructure f U) i)
    (O : genericAmbient.Opens) (hOU : O ≤ U) (hpoint : Set.range functionPoint ⊆ (O : Set genericAmbient))
    (hoff : (pullback.snd (curveBase f) (U.ι ≫ T) ≫ U.ι) ⁻¹ᵁ O ≤ complement i) :
    VanishesOnWeightedFrame f U i z := by
  let c := f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField
  obtain ⟨b,hs,β,hβ⟩ := CycleQ2NativeNormalResidue.exists_regular_representative (1:A) one_ne_zero
  let s := 1*b
  let ω := asVertexSection s β
  have he : evaluate (evaluatePatch s hs) 3 (asOrdinaryForm s ω) = sourceForm := by
    unfold ω
    rw [roundTrip]
    exact hβ
  have hu : Set.range functionPoint ⊆ Set.range U.ι := by rw [U.range_ι]; exact hpoint.trans hOU
  let yc := IsOpenImmersion.lift U.ι functionPoint hu
  have hy : yc ≫ U.ι = functionPoint := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨V,hV,hVO,hVs⟩ := CycleQ2NativeWeightedTopGerm.exists_framed_target U O yc hy hpoint s hs
  have haway : (pullback.snd c (U.ι ≫ T)) ⁻¹ᵁ V.1 ≤ complement i := fun _ hx => hoff (hVO hx)
  have zero : restrictClass f U i z V = 0 := CycleQ2MarkedFunctionPoint.forget_off i _ haway z
  have vanishes (w : (CycleQ2NativeCurveTraceComplex.complex genericField f).X 1)
      (hw : (CycleQ2NativeCurveTraceComplex.complex genericField f).d 1 2 w = 0) :
      cylinder f (U.ι ≫ T) 3 V w hw 4 (restrictClass f U i z V) = 0 := by rw [zero,map_zero]
  refine ⟨s,hs,ω,he,yc,hy,V,hV,hVs,vanishes,?_⟩
  intro hmem
  have hb : cylinderSpan f U i z V ≤ ⊥ := Submodule.span_le.mpr (by
    rintro _ ⟨w,hw,rfl⟩
    exact (Submodule.mem_bot _).mpr (vanishes w hw))
  exact CycleQ2ProperRectangleTrace.protected_of_restrictedVertexClass_zero s U.ι V hVs hs yc hy hV ω he
    ((Submodule.mem_bot _).mp (hb hmem))

end

set_option maxHeartbeats 3000000 in
/-- On the actual surviving seed-compatible surface, every closed proper-curve
cochain has zero cylinder on an affine neighborhood of the function point
where the protected source is represented by the original weighted vertex. -/
theorem exists_marked_zero_cylinders :
    ∃ (C : Scheme.{0}) (f : C ⟶ line genericField)
      (hC : IsIntegral C) (hf : IsFinite f) (hd : IsDominant f),
      let c := f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField
      ∃ (hs : SmoothOfRelativeDimension 1 c),
        let := hC
        let := hf
        let := hd
        let := hs
        IsProper c ∧ ∃ (U : genericAmbient.Opens) (S : Scheme.{0}) (i : S ⟶ pullback c (U.ι ≫ T)),
          IsProper (i ≫ pullback.snd c (U.ι ≫ T)) ∧
          SmoothOfRelativeDimension 2 (i ≫ productBase c (U.ι ≫ T)) ∧
          ∃ (hi : IsClosedImmersion i),
            let := hi
            let _ : SmoothOfRelativeDimension 4 (productBase c (U.ι ≫ T)) := CycleQ2ProductFramedOpen.smooth_product c (U.ι ≫ T) 3
            ∃ z : SupportedClass (productBase c (U.ι ≫ T)) i, z ≠ 0 ∧
              IsNormalized (productBase c (U.ι ≫ T)) i z ∧ SeedGraph c U i z ∧ VanishesOnWeightedFrame f U i z := by
  obtain ⟨t,ht,P,hP,C,c,r,hc,D,j,a,ha,hC,hproper,hsm,hproj,_,_,U,_,_,S,i,v,_,hv,_,_,hseed,
    ⟨hj,_⟩,⟨square,hclass⟩,_⟩ := CycleQ2SurvivingProductGysin.exists_seed_compatible_literal_product
  obtain ⟨f,hf,hd,hfc⟩ := hproj
  subst c
  let : IsIntegral C := hC
  let : IsFinite f := hf
  let : IsDominant f := hd
  let : SmoothOfRelativeDimension 1 (f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField) := hsm
  obtain ⟨hp,hsource,hi,h₄,z,hzne,hnorm,O,hOU,hpoint,hoff,_⟩ := hclass
  obtain ⟨hP',hseed⟩ := hseed
  let c := f ≫ CycleQ2ProjectiveLineStructure.structureMap genericField
  let i' := i ≫ (literalIso c U).hom
  let : IsClosedImmersion i' := hi
  let _ := hj
  let _ := hproper
  let _ : SmoothOfRelativeDimension 2 (i' ≫ productBase c (U.ι ≫ T)) := hsource
  have hG : SeedGraph c U i' z :=
    ⟨t,ht,P,hP',r,hc,D,j,a,ha,v,hseed,hv,square,hj,
      CycleQ2MarkedGraphChartApplication.has_marked_charts t r c hc j a ha
        (literalOpen c U) (productBase c (U.ι ≫ T)) i' v square z hnorm⟩
  refine ⟨C,f,hC,hf,hd,hsm,hproper,U,S,i',hp,hsource,hi,z,hzne,hnorm,hG,?_⟩
  exact vanishes_of_avoids f U i' z O hOU hpoint hoff
end CycleQ2MarkedCylinderRestriction

#print axioms CycleQ2MarkedCylinderRestriction.exists_marked_zero_cylinders
