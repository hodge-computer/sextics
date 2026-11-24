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

/-! Affine target descent does not require a global cotangent frame on a
coordinate open. A finite subcover of the exact-frame basis bounds the
tensor coordinates, so the actual ordinary exterior modules glue before
any differential or cohomology comparison is made. -/

namespace CycleQ2AffineTargetTensorDescent

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Module TensorProduct
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2IntrinsicDeRhamSheaves (sheafForms)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2WeightedCoordinateExterior (Form)
open CycleQ2UnframedTensorNaturality (formLinear)
open scoped TensorProduct KaehlerDifferential

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}}
  (q : X ⟶ Spec (CommRingCat.of k)) (r : ℕ) [SmoothOfRelativeDimension r q]

abbrev Index (V : X.Opens) := {W : FramedOpen q r // W.1 ≤ V}

theorem cover (V : X.Opens) : V ≤ ⨆ i : Index q r V, i.1.1 := by
  intro x hx
  obtain ⟨W,hW,hxW,hWV⟩ := (Opens.isBasis_iff_nbhd.mp
    (CycleQ2FiniteExactAffineAtlas.isBasis q r)) hx
  exact Opens.mem_iSup.mpr ⟨⟨⟨W,hW⟩,hWV⟩,hxW⟩

private theorem finite_cover {V : X.Opens} (hV : IsAffineOpen V) :
    ∃ L : Finset (Index q r V), V ≤ ⨆ i : (L : Set (Index q r V)), i.1.1.1 := by
  classical
  obtain ⟨L,hL⟩ := hV.isCompact.elim_finite_subcover
    (fun i : Index q r V => (i.1.1 : Set X)) (fun i => i.1.1.isOpen)
    (by intro x hx; exact Set.mem_iUnion.mpr (Opens.mem_iSup.mp (cover q r V hx)))
  refine ⟨L,?_⟩
  intro x hx
  obtain ⟨i,hi,hm⟩ := Set.mem_iUnion₂.mp (hL hx)
  exact Opens.mem_iSup.mpr ⟨⟨i,hi⟩,hm⟩

variable (D : TopCat.Sheaf AddCommGrpCat.{0} X)
private abbrev res {U V : X.Opens} (h : U ≤ V) := D.obj.map (homOfLE h).op

private theorem res_comp {U V W : X.Opens} (h : U ≤ V) (g : V ≤ W)
    (s : D.obj.obj (op W)) : res D h (res D g s) = res D (h.trans g) s := by
  rw [res,res,← ConcreteCategory.comp_apply,← D.obj.map_comp]
  rfl

private theorem glue {V : X.Opens}
    (y : (i : Index q r V) → D.obj.obj (op i.1.1))
    (hy : ∀ (i j : Index q r V) (h : i.1.1 ≤ j.1.1), res D h (y j) = y i) :
    ∃! s : D.obj.obj (op V), ∀ i : Index q r V, res D i.2 s = y i := by
  apply D.existsUnique_gluing' (fun i : Index q r V => i.1.1) V _ (cover q r V) y
  intro i j
  let O := i.1.1 ⊓ j.1.1
  apply D.eq_of_locally_eq' (fun t : Index q r O => t.1.1) O
    (fun t => homOfLE t.2) (cover q r O)
  intro t
  let a : Index q r V := ⟨t.1,(t.2.trans inf_le_left).trans i.2⟩
  change res D t.2 (res D (inf_le_left : O ≤ _) (y i)) =
    res D t.2 (res D (inf_le_right : O ≤ _) (y j))
  rw [res_comp,res_comp]
  exact (hy a i (t.2.trans inf_le_left)).trans (hy a j (t.2.trans inf_le_right)).symm

private theorem coordinate_res {P Q T : Type} [AddCommGroup P] [Module k P]
    [AddCommGroup Q] [Module k Q] [AddCommGroup T] [Module k T]
    {ι : Type} [DecidableEq ι] (b : Basis ι k T) (f : P →ₗ[k] Q)
    (z : T ⊗[k] P) (i : ι) :
    equivFinsuppOfBasisLeft b (TensorProduct.map LinearMap.id f z) i =
      f (equivFinsuppOfBasisLeft b z i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    simp only [map_tmul,LinearMap.id_apply,equivFinsuppOfBasisLeft_apply_tmul_apply,map_smul]
  | add x y hx hy => simp only [map_add,Finsupp.add_apply,hx,hy]

variable (M : X.Opens → ModuleCat.{0} k)
  (ρ : ∀ {U V : X.Opens}, U ≤ V → M V →ₗ[k] M U)
  (e : ∀ V : X.Opens, IsAffineOpen V → M V ≃+ D.obj.obj (op V))
  (natural : ∀ {U V : X.Opens} (h : U ≤ V) (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (s : M V), res D h (e V hV s) = e U hU (ρ h s))
  {T : Type} [AddCommGroup T] [Module k T]

set_option maxHeartbeats 1600000 in
include natural in
private theorem tensor_glue {V : X.Opens} (hV : IsAffineOpen V)
    (x : (i : Index q r V) → T ⊗[k] M i.1.1)
    (hx : ∀ (i j : Index q r V) (h : i.1.1 ≤ j.1.1),
      TensorProduct.map LinearMap.id (ρ h) (x j) = x i) :
    ∃! z : T ⊗[k] M V, ∀ i : Index q r V,
      TensorProduct.map LinearMap.id (ρ i.2) z = x i := by
  classical
  let b := Basis.ofVectorSpace k T
  let coord (i : Index q r V) := equivFinsuppOfBasisLeft b (x i)
  let y (a : Basis.ofVectorSpaceIndex k T) (i : Index q r V) :=
    e i.1.1 i.1.2.1 (coord i a)
  have hy (a) (i j : Index q r V) (h : i.1.1 ≤ j.1.1) :
      res D h (y a j) = y a i := by
    unfold y coord
    rw [natural,← coordinate_res,hx i j h]
  choose u hu hu_unique using fun a => glue q r D (y a) (hy a)
  obtain ⟨L,hL⟩ := finite_cover q r hV
  let S := L.biUnion fun i => (coord i).support
  have hbound (a) (ha : a ∉ S) : u a = 0 := by
    apply D.eq_of_locally_eq' (fun i : (L : Set (Index q r V)) => i.1.1.1) V
      (fun i => homOfLE i.1.2) hL
    intro i
    change res D i.1.2 (u a) = res D i.1.2 0
    rw [map_zero,hu]
    have h : a ∉ (coord i.1).support := fun hm => ha (Finset.mem_biUnion.mpr ⟨i.1,i.2,hm⟩)
    exact (congrArg (e i.1.1.1 i.1.1.2.1) (Finsupp.notMem_support_iff.mp h)).trans (map_zero _)
  let s := Finsupp.onFinset S (fun a => (e V hV).symm (u a))
    (fun a ha => by_contra fun h => ha (by rw [hbound a h,map_zero]))
  let z := (equivFinsuppOfBasisLeft b).symm s
  have hzcoord : equivFinsuppOfBasisLeft b z = s :=
    (equivFinsuppOfBasisLeft b).apply_symm_apply s
  refine ⟨z,?_,?_⟩
  · intro i
    apply (equivFinsuppOfBasisLeft b).injective
    ext a
    rw [coordinate_res,hzcoord]
    change ρ i.2 ((e V hV).symm (u a)) = coord i a
    apply (e i.1.1 i.1.2.1).injective
    rw [← natural i.2 i.1.2.1 hV,AddEquiv.apply_symm_apply]
    exact hu a i
  · intro z' hz'
    apply (equivFinsuppOfBasisLeft b).injective
    ext a
    rw [hzcoord]
    change equivFinsuppOfBasisLeft b z' a = (e V hV).symm (u a)
    apply (e V hV).injective
    rw [AddEquiv.apply_symm_apply]
    apply hu_unique a
    intro i
    rw [natural,← coordinate_res,hz']

abbrev formsModule (n : ℕ) (V : X.Opens) : ModuleCat.{0} k :=
  letI : Algebra k Γ(X,V) := (sectionCoefficients q V).toAlgebra
  ModuleCat.of k (Form k Γ(X,V) n)

def formsRestriction (n : ℕ) {U V : X.Opens} (h : U ≤ V) :
    formsModule q n V →ₗ[k] formsModule q n U :=
  letI : Algebra k Γ(X,U) := (sectionCoefficients q U).toAlgebra
  letI : Algebra k Γ(X,V) := (sectionCoefficients q V).toAlgebra
  formLinear (restrict q h) n

/-- The canonical affine comparison, with no chosen cotangent basis. -/
def formsEquiv (n : ℕ) (V : X.Opens) (hV : IsAffineOpen V) :
    formsModule q n V ≃+ (sheafForms q r n).obj.obj (op V) :=
  AddEquiv.ofBijective ((CycleQ2IntrinsicOrdinaryExterior.toSheaf q r n).app (op V)).hom
    (CycleQ2IntrinsicOrdinaryExterior.toSheaf_bijective q r n hV)

theorem formsEquiv_natural (n : ℕ) {U V : X.Opens} (h : U ≤ V)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (ω : formsModule q n V) :
    (sheafForms q r n).obj.map (homOfLE h).op (formsEquiv q r n V hV ω) =
      formsEquiv q r n U hU (formsRestriction q n h ω) :=
  (ConcreteCategory.congr_hom
    ((CycleQ2IntrinsicOrdinaryExterior.toSheaf q r n).naturality (homOfLE h).op) ω).symm

/-- Arbitrary constant tensor coefficients descend over an affine target
open through its exact-frame basis, in every exterior degree. -/
theorem tensor_forms (n : ℕ) {V : X.Opens} (hV : IsAffineOpen V)
    (T : Type) [AddCommGroup T] [Module k T]
    (x : (i : Index q r V) → T ⊗[k] formsModule q n i.1.1)
    (hx : ∀ (i j : Index q r V) (h : i.1.1 ≤ j.1.1),
      TensorProduct.map LinearMap.id (formsRestriction q n h) (x j) = x i) :
    ∃! z : T ⊗[k] formsModule q n V, ∀ i : Index q r V,
      TensorProduct.map LinearMap.id (formsRestriction q n i.2) z = x i :=
  tensor_glue q r (sheafForms q r n) (formsModule q n) (formsRestriction q n)
    (formsEquiv q r n) (fun h hU hV ω => formsEquiv_natural q r n h hU hV ω) hV x hx

end CycleQ2AffineTargetTensorDescent

namespace CycleQ2AffineTargetTensorDescent

open CategoryTheory AlgebraicGeometry TopologicalSpace TensorProduct
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2OrdinaryTensorRows (ordinary)
open CycleQ2NativeCurveTraceComplex (pullLinear)
open CycleQ2UnframedTensorNaturality (formLinear)
open scoped TensorProduct KaehlerDifferential

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r q] (U : C.Opens)

private theorem fixed_functions :
    letI := (sectionCoefficients p U).toAlgebra
    (restrict p (le_refl U)).toLinearMap = LinearMap.id := by
  letI := (sectionCoefficients p U).toAlgebra
  rw [CycleQ2FramedAffineSite.restrict_id]
  rfl

private theorem fixed_forms :
    letI := (sectionCoefficients p U).toAlgebra
    pullLinear (restrict p (le_refl U)) = LinearMap.id := by
  letI := (sectionCoefficients p U).toAlgebra
  rw [CycleQ2FramedAffineSite.restrict_id]
  exact LinearMap.ext CycleQ2AffineDeRhamFunctorial.onePullback_id

private theorem row_zero {V W : X.Opens} (h : W ≤ V) (x : ordinary p q U V 0) :
    letI := (sectionCoefficients p U).toAlgebra
    CycleQ2OrdinaryTensorRows.map p q (le_refl U) h 0 x =
      TensorProduct.map LinearMap.id (formsRestriction q 0 h) x := by
  letI := (sectionCoefficients p U).toAlgebra
  letI := (sectionCoefficients q V).toAlgebra
  letI := (sectionCoefficients q W).toAlgebra
  change TensorProduct.map (restrict p (le_refl U)).toLinearMap (formLinear (restrict q h) 0) x = _
  rw [fixed_functions]
  rfl

private theorem row_succ {V W : X.Opens} (h : W ≤ V) (n : ℕ)
    (x : ordinary p q U V (n+1)) :
    letI := (sectionCoefficients p U).toAlgebra
    CycleQ2OrdinaryTensorRows.map p q (le_refl U) h (n+1) x =
      (TensorProduct.map LinearMap.id (formsRestriction q (n+1) h) x.1,
        TensorProduct.map LinearMap.id (formsRestriction q n h) x.2) := by
  letI := (sectionCoefficients p U).toAlgebra
  letI := (sectionCoefficients q V).toAlgebra
  letI := (sectionCoefficients q W).toAlgebra
  change (TensorProduct.map (restrict p (le_refl U)).toLinearMap (formLinear (restrict q h) (n+1)) x.1,
    TensorProduct.map (pullLinear (restrict p (le_refl U))) (formLinear (restrict q h) n) x.2) = _
  rw [fixed_functions,fixed_forms]
  rfl

/-- The actual two tensor summands descend on the target, with exactly
the restriction maps of the original signed product rows. -/
theorem ordinary_glue {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    (y : (i : Index q r V) → ordinary p q U i.1.1 n)
    (hy : ∀ (i j : Index q r V) (h : i.1.1 ≤ j.1.1),
      CycleQ2OrdinaryTensorRows.map p q (le_refl U) h n (y j) = y i) :
    ∃! x : ordinary p q U V n, ∀ i : Index q r V,
      CycleQ2OrdinaryTensorRows.map p q (le_refl U) i.2 n x = y i := by
  letI := (sectionCoefficients p U).toAlgebra
  cases n with
  | zero =>
    obtain ⟨s,hs,hu⟩ := tensor_forms q r 0 hV Γ(C,U) y (fun i j h =>
      (row_zero p q U h (y j)).symm.trans (hy i j h))
    refine ⟨s,fun i => (row_zero p q U i.2 s).trans (hs i),?_⟩
    intro a ha
    exact hu a (fun i => (row_zero p q U i.2 a).symm.trans (ha i))
  | succ n =>
    obtain ⟨a,ha,ua⟩ := tensor_forms q r (n+1) hV Γ(C,U) (fun i => (y i).1)
      (fun i j h => congrArg Prod.fst ((row_succ p q U h n (y j)).symm.trans (hy i j h)))
    obtain ⟨b,hb,ub⟩ := tensor_forms q r n hV Ω[Γ(C,U)⁄k] (fun i => (y i).2)
      (fun i j h => congrArg Prod.snd ((row_succ p q U h n (y j)).symm.trans (hy i j h)))
    refine ⟨(a,b),fun i => (row_succ p q U i.2 n (a,b)).trans (Prod.ext (ha i) (hb i)),?_⟩
    rintro ⟨u,v⟩ h
    apply Prod.ext
    · exact ua u (fun i => congrArg Prod.fst ((row_succ p q U i.2 n (u,v)).symm.trans (h i)))
    · exact ub v (fun i => congrArg Prod.snd ((row_succ p q U i.2 n (u,v)).symm.trans (h i)))

theorem ordinary_ext {V : X.Opens} (hV : IsAffineOpen V) (n : ℕ)
    {x y : ordinary p q U V n}
    (h : ∀ i : Index q r V,
      CycleQ2OrdinaryTensorRows.map p q (le_refl U) i.2 n x =
        CycleQ2OrdinaryTensorRows.map p q (le_refl U) i.2 n y) : x = y := by
  have hglue := ordinary_glue p q r U hV n
    (fun i => CycleQ2OrdinaryTensorRows.map p q (le_refl U) i.2 n y)
    (fun i j h => CycleQ2OrdinaryTensorRows.map_comp p q (le_refl U) (le_refl U) j.2 h n y)
  exact hglue.unique h (fun _ => rfl)

end CycleQ2AffineTargetTensorDescent

namespace CycleQ2TargetRectangleBasisGluing

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2AffineTargetTensorDescent (Index)
open CycleQ2ProductAffineOpen (productOpen)
open CycleQ2ProductOpenRestrictions (productOpen_mono)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r q]

abbrev part (U : C.Opens) {V : X.Opens} (i : Index q r V) := productOpen p q U i.1.1

theorem covers (U : C.Opens) (V : X.Opens) :
    productOpen p q U V ≤ ⨆ i : Index q r V, part p q r U i := by
  intro x hx
  change pullback.fst p q x ∈ U ∧ pullback.snd p q x ∈ V at hx
  obtain ⟨W,hW,hxW,hWV⟩ := (Opens.isBasis_iff_nbhd.mp
    (CycleQ2FiniteExactAffineAtlas.isBasis q r)) hx.2
  exact Opens.mem_iSup.mpr ⟨⟨⟨W,hW⟩,hWV⟩,hx.1,hxW⟩

variable (D : TopCat.Sheaf AddCommGrpCat.{0} (show Scheme from pullback p q))
abbrev res {U V : (pullback p q).Opens} (h : U ≤ V) := D.obj.map (homOfLE h).op

private theorem res_comp {U V W : (pullback p q).Opens} (h : U ≤ V) (g : V ≤ W)
    (s : D.obj.obj (op W)) : res p q D h (res p q D g s) = res p q D (h.trans g) s := by
  rw [res,res,← ConcreteCategory.comp_apply,← D.obj.map_comp]
  rfl

theorem ext {U : C.Opens} {V : X.Opens}
    {s t : D.obj.obj (op (productOpen p q U V))}
    (h : ∀ i : Index q r V,
      res p q D (productOpen_mono p q (le_refl U) i.2) s =
        res p q D (productOpen_mono p q (le_refl U) i.2) t) : s = t :=
  D.eq_of_locally_eq' (part p q r U) (productOpen p q U V)
    (fun i : Index q r V => homOfLE (productOpen_mono p q (le_refl U) i.2))
    (covers p q r U V) s t h

theorem existsUnique {U : C.Opens} {V : X.Opens}
    (y : (i : Index q r V) → D.obj.obj (op (part p q r U i)))
    (hy : ∀ (i j : Index q r V) (h : i.1.1 ≤ j.1.1),
      res p q D (productOpen_mono p q (le_refl U) h) (y j) = y i) :
    ∃! s : D.obj.obj (op (productOpen p q U V)), ∀ i : Index q r V,
      res p q D (productOpen_mono p q (le_refl U) i.2) s = y i := by
  apply D.existsUnique_gluing' (part p q r U) (productOpen p q U V) _ (covers p q r U V) y
  intro i j
  let L := part p q r U i ⊓ part p q r U j
  let O := i.1.1 ⊓ j.1.1
  let ks (a : Index q r O) : part p q r U a ≤ L := le_inf
    (productOpen_mono p q (le_refl U) (a.2.trans inf_le_left))
    (productOpen_mono p q (le_refl U) (a.2.trans inf_le_right))
  have cov : L ≤ ⨆ a : Index q r O, part p q r U a := by
    apply le_trans _ (covers p q r U O)
    intro x hx
    exact ⟨hx.1.1,hx.1.2,hx.2.2⟩
  apply D.eq_of_locally_eq' (fun a : Index q r O => part p q r U a) L
    (fun a => homOfLE (ks a)) cov
  intro a
  let o : Index q r V := ⟨a.1,(a.2.trans inf_le_left).trans i.2⟩
  change res p q D (ks a) (res p q D (inf_le_left : L ≤ part p q r U i) (y i)) =
    res p q D (ks a) (res p q D (inf_le_right : L ≤ part p q r U j) (y j))
  rw [res_comp,res_comp]
  exact (hy o i (a.2.trans inf_le_left)).trans (hy o j (a.2.trans inf_le_right)).symm

end CycleQ2TargetRectangleBasisGluing

namespace CycleQ2UnframedAffineRectangle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2AffineTargetTensorDescent (Index)
open CycleQ2OrdinaryTensorRows (ordinary map map_comp)
open CycleQ2UnframedProductChain (Section sheaf geoRes)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension r q]

private theorem geo_comp {U U' U'' : C.Opens} {V V' V'' : X.Opens}
    (h : U' ≤ U) (h' : U'' ≤ U') (g : V' ≤ V) (g' : V'' ≤ V') (n : ℕ)
    (s : Section p q r U V n) :
    geoRes p q r h' g' n (geoRes p q r h g n s) =
      geoRes p q r (h'.trans h) (g'.trans g) n s := by
  change (sheaf p q r n).obj.map _ ((sheaf p q r n).obj.map _ s) = _
  rw [← ConcreteCategory.comp_apply,← Functor.map_comp]
  rfl

variable (U : C.Opens) (V : X.Opens) (n : ℕ)

private def patch (i : Index q r V) : ordinary p q U V n →+ Section p q r U i.1.1 n :=
  (CycleQ2UnframedProductChain.assemble p q r U i.1 n).comp
    (map p q (le_refl U) i.2 n).hom.toAddMonoidHom

private theorem patch_compatible (x : ordinary p q U V n)
    (i j : Index q r V) (h : i.1.1 ≤ j.1.1) :
    geoRes p q r (le_refl U) h n (patch p q r U V n j x) = patch p q r U V n i x :=
  (CycleQ2UnframedProductChain.assemble_natural p q r n (le_refl U) h
    (map p q (le_refl U) j.2 n x)).trans
    (congrArg (CycleQ2UnframedProductChain.assemble p q r U i.1 n)
      (map_comp p q (le_refl U) (le_refl U) j.2 h n x))

private theorem unique (x : ordinary p q U V n) :
    ∃! s : Section p q r U V n, ∀ i : Index q r V,
      geoRes p q r (le_refl U) i.2 n s = patch p q r U V n i x :=
  CycleQ2TargetRectangleBasisGluing.existsUnique p q r (sheaf p q r n)
    (fun i => patch p q r U V n i x) (patch_compatible p q r U V n x)

private def glued (x : ordinary p q U V n) := (unique p q r U V n x).choose

private theorem glued_spec (x : ordinary p q U V n) (i : Index q r V) :
    geoRes p q r (le_refl U) i.2 n (glued p q r U V n x) = patch p q r U V n i x :=
  (unique p q r U V n x).choose_spec.1 i

/-- Ordinary curve/target tensors assemble on the original rectangle,
without a global target frame. The map is defined even before affineness
is used to prove that it is an isomorphism. -/
def assemble : ordinary p q U V n →+ Section p q r U V n :=
  AddMonoidHom.mk' (glued p q r U V n) (by
    intro x y
    apply CycleQ2TargetRectangleBasisGluing.ext p q r (sheaf p q r n)
    intro i
    change geoRes p q r (le_refl U) i.2 n (glued p q r U V n (x+y)) =
      geoRes p q r (le_refl U) i.2 n (glued p q r U V n x + glued p q r U V n y)
    rw [map_add,glued_spec,glued_spec,glued_spec,map_add])

theorem on_patch (x : ordinary p q U V n) (W : FramedOpen q r) (h : W.1 ≤ V) :
    geoRes p q r (le_refl U) h n (assemble p q r U V n x) =
      CycleQ2UnframedProductChain.assemble p q r U W n (map p q (le_refl U) h n x) :=
  glued_spec p q r U V n x ⟨W,h⟩

variable {U U' : C.Opens} {V V' : X.Opens}

/-- Both original geometric restrictions commute with the unframed
assembly. In particular this applies to every inclusion of coordinate
faces in the original finite target cover. -/
theorem assemble_natural (h : U' ≤ U) (g : V' ≤ V) (x : ordinary p q U V n) :
    geoRes p q r h g n (assemble p q r U V n x) =
      assemble p q r U' V' n (map p q h g n x) := by
  apply CycleQ2TargetRectangleBasisGluing.ext p q r (sheaf p q r n)
  intro i
  let W := i.1
  have hw := i.2.trans g
  change geoRes p q r (le_refl U') i.2 n (geoRes p q r h g n _) =
    geoRes p q r (le_refl U') i.2 n _
  rw [geo_comp,on_patch p q r U' V' n _ W i.2]
  have he := geo_comp p q r (le_refl U) h hw (le_refl W.1) n (assemble p q r U V n x)
  refine he.symm.trans ?_
  rw [on_patch p q r U V n x W hw]
  refine (CycleQ2UnframedProductChain.assemble_natural p q r n h (le_refl W.1) _).trans ?_
  apply congrArg (CycleQ2UnframedProductChain.assemble p q r U' W n)
  exact (map_comp p q (le_refl U) h hw (le_refl W.1) n x).trans
    (map_comp p q h (le_refl U') g i.2 n x).symm

private def localEquiv (hU : IsAffineOpen U) (W : FramedOpen q r) :
    ordinary p q U W.1 n ≃+ Section p q r U W.1 n :=
  AddEquiv.ofBijective (CycleQ2UnframedProductChain.assemble p q r U W n)
    (CycleQ2UnframedProductChain.assemble_bijective p q r U W n
      (CycleQ2AffinePairDescent.ordinary_glue p q W.1 hU n))

/-- Both factors may be arbitrary affine opens. Only their local
smooth exact frames enter the proof of this actual section equivalence. -/
theorem assemble_bijective (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    Function.Bijective (assemble p q r U V n) := by
  constructor
  · intro x y hxy
    apply CycleQ2AffineTargetTensorDescent.ordinary_ext p q r U hV n
    intro i
    apply (localEquiv p q r n hU i.1).injective
    exact (on_patch p q r U V n x i.1 i.2).symm.trans
      ((congrArg (geoRes p q r (le_refl U) i.2 n) hxy).trans
        (on_patch p q r U V n y i.1 i.2))
  · intro s
    let w (i : Index q r V) := (localEquiv p q r n hU i.1).symm
      (geoRes p q r (le_refl U) i.2 n s)
    have norm (i : Index q r V) :
        localEquiv p q r n hU i.1 (w i) = geoRes p q r (le_refl U) i.2 n s :=
      (localEquiv p q r n hU i.1).apply_symm_apply _
    have compat (i j : Index q r V) (h : i.1.1 ≤ j.1.1) :
        map p q (le_refl U) h n (w j) = w i := by
      apply (localEquiv p q r n hU i.1).injective
      refine (CycleQ2UnframedProductChain.assemble_natural p q r n
        (le_refl U) h (w j)).symm.trans ?_
      refine (congrArg (geoRes p q r (le_refl U) h n) (norm j)).trans ?_
      exact (geo_comp p q r (le_refl U) (le_refl U) j.2 h n s).trans (norm i).symm
    obtain ⟨x,hx,_⟩ := CycleQ2AffineTargetTensorDescent.ordinary_glue p q r U hV n w compat
    refine ⟨x,?_⟩
    apply CycleQ2TargetRectangleBasisGluing.ext p q r (sheaf p q r n)
    intro i
    exact (on_patch p q r U V n x i.1 i.2).trans
      ((congrArg (localEquiv p q r n hU i.1) (hx i)).trans (norm i))

def sectionEquiv (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    ordinary p q U V n ≃+ Section p q r U V n :=
  AddEquiv.ofBijective (assemble p q r U V n) (assemble_bijective p q r n hU hV)

theorem sectionEquiv_natural (h : U' ≤ U) (g : V' ≤ V)
    (hU : IsAffineOpen U) (hU' : IsAffineOpen U')
    (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (x : ordinary p q U V n) :
    geoRes p q r h g n (sectionEquiv p q r n hU hV x) =
      sectionEquiv p q r n hU' hV' (map p q h g n x) :=
  assemble_natural p q r n h g x

end CycleQ2UnframedAffineRectangle

#print axioms CycleQ2UnframedAffineRectangle.sectionEquiv
#print axioms CycleQ2UnframedAffineRectangle.sectionEquiv_natural

namespace CycleQ2UnframedAffineRectangle

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open HomologicalComplex CochainComplex
open CycleQ2IntrinsicFramedAffineSite (FramedOpen)
open CycleQ2AffineTargetTensorDescent (Index)
open CycleQ2OrdinaryTensorRows (ordinary map)
open CycleQ2UnframedProductChain (Section geoRes native nativeRestriction)

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}}
  (p : C ⟶ Spec (CommRingCat.of k)) (q : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension 1 p] [SmoothOfRelativeDimension r q]
  {U : C.Opens} {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/-- The actual intrinsic differential transported through the affine
rectangle equivalence. Its target linearity is proved on exact frames
below, rather than assumed on an unframed affine coordinate chart. -/
def differential (i j : ℕ) : ordinary p q U V i →+ ordinary p q U V j :=
  (sectionEquiv p q r j hU hV).symm.toAddMonoidHom.comp
    (((native p q r U V).d i j).hom.comp
      (sectionEquiv p q r i hU hV).toAddMonoidHom)

theorem sectionEquiv_differential (i j : ℕ) (x : ordinary p q U V i) :
    sectionEquiv p q r j hU hV (differential p q r hU hV i j x) =
      (native p q r U V).d i j (sectionEquiv p q r i hU hV x) :=
  (sectionEquiv p q r j hU hV).apply_symm_apply _

/-- On every exact-framed target subopen the new differential is the
original signed curve/target differential, with the same geometric
restriction maps. This fixes its signs and its coefficient action. -/
theorem differential_on_patch (i j : ℕ) (x : ordinary p q U V i)
    (W : FramedOpen q r) (h : W.1 ≤ V) :
    map p q (le_refl U) h j (differential p q r hU hV i j x) =
      (CycleQ2OrdinaryTensorRows.complex p q r W U).d i j
        (map p q (le_refl U) h i x) := by
  apply (localEquiv p q r j hU W).injective
  calc
    _ = geoRes p q r (le_refl U) h j
        (sectionEquiv p q r j hU hV (differential p q r hU hV i j x)) :=
      (on_patch p q r U V j _ W h).symm
    _ = geoRes p q r (le_refl U) h j
        ((native p q r U V).d i j (sectionEquiv p q r i hU hV x)) := by
      rw [sectionEquiv_differential]
    _ = (native p q r U W.1).d i j
        (geoRes p q r (le_refl U) h i (sectionEquiv p q r i hU hV x)) :=
      (ConcreteCategory.congr_hom
        ((nativeRestriction p q r (le_refl U) h).comm i j)
        (sectionEquiv p q r i hU hV x)).symm
    _ = (native p q r U W.1).d i j
        (CycleQ2UnframedProductChain.assemble p q r U W i
          (map p q (le_refl U) h i x)) := by
      rw [show geoRes p q r (le_refl U) h i (sectionEquiv p q r i hU hV x) = _ from
        on_patch p q r U V i x W h]
    _ = _ := CycleQ2UnframedProductChain.assemble_d p q r U W i j _

theorem differential_smul (i j : ℕ) (a : k) (x : ordinary p q U V i) :
    differential p q r hU hV i j (a • x) = a • differential p q r hU hV i j x := by
  apply CycleQ2AffineTargetTensorDescent.ordinary_ext p q r U hV j
  intro W
  calc
    _ = (CycleQ2OrdinaryTensorRows.complex p q r W.1 U).d i j
        (map p q (le_refl U) W.2 i (a • x)) :=
      differential_on_patch p q r hU hV i j (a • x) W.1 W.2
    _ = a • (CycleQ2OrdinaryTensorRows.complex p q r W.1 U).d i j
        (map p q (le_refl U) W.2 i x) := by simp only [map_smul]
    _ = _ := by
      rw [map_smul,differential_on_patch p q r hU hV i j x W.1 W.2]

def differentialLinear (i j : ℕ) : ordinary p q U V i →ₗ[k] ordinary p q U V j where
  __ := differential p q r hU hV i j
  map_smul' := differential_smul p q r hU hV i j

private theorem differential_square (i j l : ℕ) (x : ordinary p q U V i) :
    differential p q r hU hV j l (differential p q r hU hV i j x) = 0 := by
  apply (sectionEquiv p q r l hU hV).injective
  rw [sectionEquiv_differential,sectionEquiv_differential,map_zero]
  change ((native p q r U V).d i j ≫ (native p q r U V).d j l)
    (sectionEquiv p q r i hU hV x) = 0
  rw [(native p q r U V).d_comp_d]
  rfl

/-- The ordinary two-row complex on an arbitrary pair of affine opens.
Its differential is k-linear and is the checked signed tensor
differential on every exact-framed target refinement. -/
def complex : CochainComplex (ModuleCat.{0} k) ℕ :=
  CochainComplex.of (ordinary p q U V)
    (fun n => ModuleCat.ofHom (differentialLinear p q r hU hV n (n+1))) (by
      intro n
      exact ModuleCat.hom_ext (LinearMap.ext
        (differential_square p q r hU hV n (n+1) (n+1+1))))

theorem complex_d (n : ℕ) :
    (complex p q r hU hV).d n (n+1) =
      ModuleCat.ofHom (differentialLinear p q r hU hV n (n+1)) :=
  CochainComplex.of_d _ _ n

private abbrev forgetComplex :=
  (forget₂ (ModuleCat.{0} k) AddCommGrpCat.{0}).mapHomologicalComplex (.up ℕ)

/-- Actual affine rectangle chain equivalence, in all degrees, without
a global frame on either affine factor. -/
def affineIso : (forgetComplex (k := k)).obj (complex p q r hU hV) ≅ native p q r U V := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun n => (sectionEquiv p q r n hU hV).toAddCommGrpIso) ?_
  intro i j hij
  have hj : i+1=j := hij
  subst j
  apply AddCommGrpCat.ext
  intro x
  change (native p q r U V).d i (i+1) (sectionEquiv p q r i hU hV x) =
    sectionEquiv p q r (i+1) hU hV ((complex p q r hU hV).d i (i+1) x)
  rw [complex_d]
  exact (sectionEquiv_differential p q r hU hV i (i+1) x).symm

variable {U' : C.Opens} {V' : X.Opens}
  (hU' : IsAffineOpen U') (hV' : IsAffineOpen V')

theorem differential_natural (h : U' ≤ U) (g : V' ≤ V) (i j : ℕ)
    (x : ordinary p q U V i) :
    map p q h g j (differential p q r hU hV i j x) =
      differential p q r hU' hV' i j (map p q h g i x) := by
  apply (sectionEquiv p q r j hU' hV').injective
  calc
    _ = geoRes p q r h g j
        (sectionEquiv p q r j hU hV (differential p q r hU hV i j x)) :=
      (sectionEquiv_natural p q r j h g hU hU' hV hV' _).symm
    _ = geoRes p q r h g j
        ((native p q r U V).d i j (sectionEquiv p q r i hU hV x)) := by
      rw [sectionEquiv_differential]
    _ = (native p q r U' V').d i j
        (geoRes p q r h g i (sectionEquiv p q r i hU hV x)) :=
      (ConcreteCategory.congr_hom ((nativeRestriction p q r h g).comm i j)
        (sectionEquiv p q r i hU hV x)).symm
    _ = (native p q r U' V').d i j
        (sectionEquiv p q r i hU' hV' (map p q h g i x)) := by
      rw [sectionEquiv_natural p q r i h g hU hU' hV hV']
    _ = _ := (sectionEquiv_differential p q r hU' hV' i j _).symm

def restriction (h : U' ≤ U) (g : V' ≤ V) :
    complex p q r hU hV ⟶ complex p q r hU' hV' :=
  CochainComplex.ofHom (fun n => map p q h g n) (by
    intro n
    rw [complex_d,complex_d]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (differential_natural p q r hU hV hU' hV' h g n (n+1) x).symm)

theorem affineIso_natural (h : U' ≤ U) (g : V' ≤ V) :
    (affineIso p q r hU hV).hom ≫ nativeRestriction p q r h g =
      (forgetComplex (k := k)).map (restriction p q r hU hV hU' hV' h g) ≫
        (affineIso p q r hU' hV').hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro x
  exact sectionEquiv_natural p q r n h g hU hU' hV hV' x

end CycleQ2UnframedAffineRectangle

#print axioms CycleQ2UnframedAffineRectangle.differential_on_patch
#print axioms CycleQ2UnframedAffineRectangle.affineIso
#print axioms CycleQ2UnframedAffineRectangle.affineIso_natural

/-! The positive augmentation used in finite-open descent. The map is
the actual inclusion of compatible sections into the mapping cocone;
its quasi-isomorphism is proved from the original short exact complex.
In particular, no inverse selected only in the derived category is used
as a chain-level augmentation. -/

namespace CycleQ2CechMappingCocone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex CategoryTheory.Pretriangulated

private abbrev CC := CochainComplex AddCommGrpCat.{0} ℤ

variable {A B C A' B' C' : CC}

/-- The map of actual mapping cocones induced by a commutative square. -/
def map (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ g) : mappingCocone f ⟶ mappingCocone g :=
  (mappingCone.map f g a b h)⟦(-1 : ℤ)⟧'

@[simp] theorem map_id (f : A ⟶ B) :
    map f f (𝟙 A) (𝟙 B) (by simp) = 𝟙 _ := by
  simp only [map, mappingCone.map_id, Functor.map_id]

theorem map_comp {A'' B'' : CC} (f : A ⟶ B) (g : A' ⟶ B') (l : A'' ⟶ B'')
    (a : A ⟶ A') (b : B ⟶ B') (a' : A' ⟶ A'') (b' : B' ⟶ B'')
    (h : f ≫ b = a ≫ g) (h' : g ≫ b' = a' ≫ l) :
    map f g a b h ≫ map g l a' b' h' =
      map f l (a ≫ a') (b ≫ b') (by rw [reassoc_of% h, h', Category.assoc]) := by
  simp only [map, ← Functor.map_comp, ← mappingCone.map_comp]

theorem ext_to (f : A ⟶ B) (n : ℤ) {D : AddCommGrpCat.{0}}
    {u v : D ⟶ (mappingCocone f).X n}
    (h₁ : u ≫ (mappingCocone.fst f).f n = v ≫ (mappingCocone.fst f).f n)
    (h₂ : u ≫ (mappingCocone.snd f).v n (n + -1) rfl =
      v ≫ (mappingCocone.snd f).v n (n + -1) rfl) : u = v := by
  calc
    u = u ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = u ≫ ((mappingCocone.fst f).f n ≫
        (mappingCocone.inl f).v n n (add_zero n) +
        (mappingCocone.snd f).v n (n + -1) rfl ≫
        (mappingCocone.inr f).1.v (n + -1) n (by omega)) := by
      rw [mappingCocone.id_X f n (n + -1) rfl]
    _ = v ≫ ((mappingCocone.fst f).f n ≫
        (mappingCocone.inl f).v n n (add_zero n) +
        (mappingCocone.snd f).v n (n + -1) rfl ≫
        (mappingCocone.inr f).1.v (n + -1) n (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, h₁, h₂]
    _ = v := by rw [mappingCocone.id_X, Category.comp_id]

@[reassoc] theorem inl_map (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ g) (n : ℤ) :
    (mappingCocone.inl f).v n n (add_zero n) ≫ (map f g a b h).f n =
      a.f n ≫ (mappingCocone.inl g).v n n (add_zero n) := by
  simp only [map, shiftFunctor_map_f', mappingCocone.inl,
    Cochain.rightShift_v (n := -1) _ (-1) 0 (zero_add _) n n (add_zero _)
      (n + -1) rfl,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
    Category.comp_id, mappingCone.map, mappingCone.inl_v_desc_f,
    Cochain.zero_cochain_comp_v, Cochain.ofHom_v]

/-- A genuine chain map with the given positive vertex part and zero
overlap primitive. -/
def zeroLift (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) :
    A ⟶ mappingCocone g :=
  mappingCocone.lift g f 0 (by simp only [δ_zero, h, Cochain.ofHom_zero, add_zero])

@[reassoc (attr := simp)] theorem zeroLift_fst
    (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) :
    zeroLift f g h ≫ mappingCocone.fst g = f :=
  mappingCocone.lift_fst _ _ _ _

theorem zeroLift_f (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0) (n : ℤ) :
    (zeroLift f g h).f n = f.f n ≫ (mappingCocone.inl g).v n n (add_zero n) := by
  apply ext_to g n
  · simp only [zeroLift, mappingCocone.lift_f_fst_f, Category.assoc,
      mappingCocone.inl_v_fst_f, Category.comp_id]
  · simp only [zeroLift, mappingCocone.lift_f_snd_v, Cochain.zero_v,
      Category.assoc, mappingCocone.inl_v_snd_v, comp_zero]

theorem zeroLift_natural (f : A ⟶ B) (g : B ⟶ C) (h : f ≫ g = 0)
    (f' : A' ⟶ B') (g' : B' ⟶ C') (h' : f' ≫ g' = 0)
    (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C')
    (h₁ : f ≫ b = a ≫ f') (h₂ : g ≫ c = b ≫ g') :
    zeroLift f g h ≫ map g g' b c h₂ = a ≫ zeroLift f' g' h' := by
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, zeroLift_f, Category.assoc, inl_map]
  rw [← Category.assoc, ← HomologicalComplex.comp_f, h₁,
    HomologicalComplex.comp_f, Category.assoc]

/-- A quasi-isomorphism on both entries gives a quasi-isomorphism on
their actual mapping cone. -/
theorem coneMap_quasiIso (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] : QuasiIso (mappingCone.map f g a b h) := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{0}
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _).mp
  let D := DerivedCategory.Q (C := AddCommGrpCat.{0})
  let t := D.mapTriangle.map (mappingCone.triangleMap f g a b h)
  have hdist {M N : CC} (d : M ⟶ N) :
      D.mapTriangle.obj (mappingCone.triangle d) ∈ distTriang _ :=
    (DerivedCategory.mem_distTriang_iff _).2 ⟨_, _, _, ⟨Iso.refl _⟩⟩
  exact isIso₃_of_isIso₁₂ t (hdist f) (hdist g)
    (inferInstanceAs (IsIso (D.map a))) (inferInstanceAs (IsIso (D.map b)))

theorem map_quasiIso (f : A ⟶ B) (g : A' ⟶ B')
    (a : A ⟶ A') (b : B ⟶ B') (h : f ≫ b = a ≫ g)
    [QuasiIso a] [QuasiIso b] : QuasiIso (map f g a b h) :=
  (quasiIso_shift_iff _ (-1)).mpr (coneMap_quasiIso f g a b h)

private def rotated (S : ShortComplex CC) : S.X₁⟦(1 : ℤ)⟧ ⟶ mappingCone S.g :=
  (mappingCone.rotateHomotopyEquiv S.f).hom ≫
    mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)

private theorem rotated_f (S : ShortComplex CC) (n : ℤ) :
    (rotated S).f n =
      S.f.f (n + 1) ≫ (mappingCone.inl S.g).v (n + 1) n (by omega) := by
  have hr : (mappingCone.rotateHomotopyEquiv S.f).hom.f n =
      S.f.f (n + 1) ≫ (mappingCone.inl (mappingCone.inr S.f)).v (n + 1) n (by omega) -
        (mappingCone.inl S.f).v (n + 1) n (by omega) ≫
          (mappingCone.inr (mappingCone.inr S.f)).f n := by
    change (mappingCone.lift _ _ _ _).f n = _
    rw [mappingCone.lift_f _ _ _ _ n (n + 1) rfl]
    simp only [Cocycle.coe_neg, Cocycle.leftShift_coe, Cocycle.ofHom_coe, Cochain.neg_v,
      (Cochain.ofHom S.f).leftShift_v 1 1 (zero_add 1) n (n + 1) rfl
        (n + 1) (add_zero _),
      (mappingCone.inl S.f).leftShift_v 1 0 (neg_add_cancel 1) n n (add_zero _)
        (n + 1) (by omega),
      mul_one, mul_zero, sub_self, Int.zero_ediv, add_zero,
      Int.negOnePow_one, Int.negOnePow_zero, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
      Cochain.ofHom_v, Units.neg_smul, one_smul, neg_neg,
      Preadditive.neg_comp, sub_eq_add_neg]
  simp only [rotated, HomologicalComplex.comp_f, hr, Preadditive.sub_comp,
    Category.assoc, mappingCone.map, mappingCone.inl_v_desc_f,
    mappingCone.inr_f_desc_f, Cochain.zero_cochain_comp_v, Cochain.ofHom_v,
    HomologicalComplex.id_f, Category.id_comp]
  simp only [← Category.assoc, mappingCone.inl_v_descShortComplex_f, zero_comp, sub_zero]

/-- Shifting the positive augmentation once gives the standard rotation
followed by the quotient of the original short exact complex. This
component calculation fixes the sign before passing to cohomology. -/
theorem augmentation_shift (S : ShortComplex CC) :
    (zeroLift S.f S.g S.zero)⟦(1 : ℤ)⟧' ≫
        (shiftFunctorCompIsoId CC (-1 : ℤ) 1 (by omega)).hom.app (mappingCone S.g) =
      rotated S := by
  apply HomologicalComplex.hom_ext
  intro n
  rw [HomologicalComplex.comp_f, shiftFunctor_map_f', zeroLift_f, rotated_f]
  have hc :
      ((shiftFunctorCompIsoId CC (-1 : ℤ) 1 (by omega)).hom.app
        (mappingCone S.g)).f n =
      ((mappingCone S.g).shiftFunctorObjXIso (-1) (n + 1) n (by omega)).hom := by
    simp [shiftFunctorCompIsoId, shiftFunctorAdd'_inv_app_f',
      shiftFunctorZero_hom_app_f, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq]
  dsimp only [mappingCocone.inl]
  rw [(mappingCone.inl S.g).rightShift_v (-1) 0 (zero_add _) (n + 1) (n + 1)
    (add_zero _) n (by omega), hc]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The positive compatible-section augmentation is a quasi-isomorphism
for every genuine short exact sequence of complexes. -/
theorem augmentation_quasiIso (S : ShortComplex CC) (hS : S.ShortExact) :
    QuasiIso (zeroLift S.f S.g S.zero) := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{0}
  letI : QuasiIso (mappingCone.descShortComplex S) := mappingCone.quasiIso_descShortComplex hS
  letI : QuasiIso (mappingCone.map (mappingCone.inr S.f) S.g (𝟙 _)
      (mappingCone.descShortComplex S) (by simp)) :=
    coneMap_quasiIso _ _ _ _ _
  have hr : QuasiIso (rotated S) := by unfold rotated; infer_instance
  letI : QuasiIso (rotated S) := hr
  let D := DerivedCategory.Q (C := AddCommGrpCat.{0})
  let a := zeroLift S.f S.g S.zero
  let e := (shiftFunctorCompIsoId CC (-1 : ℤ) 1 (by omega)).app (mappingCone S.g)
  haveI : IsIso (D.map (a⟦(1 : ℤ)⟧') ≫ D.map e.hom) := by
    rw [← D.map_comp]
    change IsIso (D.map ((zeroLift S.f S.g S.zero)⟦(1 : ℤ)⟧' ≫ _))
    rw [augmentation_shift]
    infer_instance
  haveI : IsIso (D.map (a⟦(1 : ℤ)⟧')) := IsIso.of_isIso_comp_right _ (D.map e.hom)
  exact (quasiIso_shift_iff a 1).mp
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _).mp inferInstance)

end CycleQ2CechMappingCocone

#print axioms CycleQ2CechMappingCocone.zeroLift_natural
#print axioms CycleQ2CechMappingCocone.augmentation_quasiIso

namespace CycleQ2CechMappingCocone

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex

theorem biprodMap_quasiIso {A B A' B' : CochainComplex AddCommGrpCat.{0} ℤ}
    (a : A ⟶ A') (b : B ⟶ B') [QuasiIso a] [QuasiIso b] :
    QuasiIso (biprod.map a b) := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{0}
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _).mp
  let F := DerivedCategory.Q (C := AddCommGrpCat.{0})
  letI : PreservesBinaryBiproducts F := preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapBiprod A B
  let e' := F.mapBiprod A' B'
  let m := biprod.map (F.map a) (F.map b)
  have he : F.map (biprod.map a b) ≫ e'.hom = e.hom ≫ m := by
    apply biprod.hom_ext
    · simp only [Category.assoc, e', e, m, Functor.mapBiprod_hom,
        biprod.lift_fst, biprod.map_fst, biprod.lift_fst_assoc, ← F.map_comp]
    · simp only [Category.assoc, e', e, m, Functor.mapBiprod_hom,
        biprod.lift_snd, biprod.map_snd, biprod.lift_snd_assoc, ← F.map_comp]
  haveI : IsIso m := (biprod.mapIso (asIso (F.map a)) (asIso (F.map b))).isIso_hom
  haveI : IsIso (F.map (biprod.map a b) ≫ e'.hom) := by rw [he]; infer_instance
  exact IsIso.of_isIso_comp_right _ e'.hom

end CycleQ2CechMappingCocone

namespace CycleQ2RectangularSections

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2RectangularTrace (secs res)

variable {X : TopCat.{0}} (K : CochainComplex (AbSheaf X) ℤ)

@[simp] theorem restriction_id (U : Opens X) : restriction K (le_refl U) = 𝟙 _ := by
  apply HomologicalComplex.hom_ext
  intro n
  exact (K.X n).obj.map_id (op U)

theorem restriction_comp {U V W : Opens X} (h : U ≤ V) (g : V ≤ W) :
    restriction K g ≫ restriction K h = restriction K (h.trans g) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ((K.X n).obj.map_comp (homOfLE g).op (homOfLE h).op).symm

def coefficient {L : CochainComplex (AbSheaf X) ℤ} (ρ : K ⟶ L) (U : Opens X) :
    row K U ⟶ row L U :=
  ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
    (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj (op U)).mapHomologicalComplex (.up ℤ)).map ρ

theorem coefficient_natural {L : CochainComplex (AbSheaf X) ℤ} (ρ : K ⟶ L)
    {U V : Opens X} (h : U ≤ V) :
    coefficient K ρ V ≫ restriction L h = restriction K h ≫ coefficient K ρ U := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ((ρ.f n).hom.naturality (homOfLE h).op).symm

variable (S : (Opens.grothendieckTopology X).MayerVietorisSquare)

def compatible : row K S.X₄ ⟶ row K S.X₂ ⊞ row K S.X₃ :=
  biprod.lift (restriction K S.f₂₄.le) (restriction K S.f₃₄.le)

theorem compatible_difference : compatible K S ≫ difference K S = 0 := by
  simp only [compatible, difference, biprod.lift_desc, Preadditive.comp_neg,
    restriction_comp]
  exact add_neg_cancel _

def sectionShortComplex : ShortComplex (CochainComplex AddCommGrpCat.{0} ℤ) :=
  ShortComplex.mk (compatible K S) (difference K S) (compatible_difference K S)

private theorem compatible_eq :
    (evaluate K S.X₄).hom ≫ compatible K S =
      (CycleQ2RectangularTrace.pair S.shortComplex K).f ≫ (pairIso K S).hom := by
  apply biprod.hom_ext
  · simp only [compatible, pairIso, Iso.trans_hom, Category.assoc,
      biprod.lift_fst, biprod.map_fst, sumIso, biprod.lift_fst_assoc]
    change (evaluate K S.X₄).hom ≫ restriction K S.f₂₄.le =
      res K S.shortComplex.g ≫ res K biprod.inl ≫ (evaluate K S.X₂).hom
    rw [← Category.assoc, res_comp]
    change _ = res K (biprod.inl ≫ biprod.desc _ _) ≫ _
    rw [biprod.inl_desc]
    exact evaluate_res K S.f₂₄.le
  · simp only [compatible, pairIso, Iso.trans_hom, Category.assoc,
      biprod.lift_snd, biprod.map_snd, sumIso, biprod.lift_snd_assoc]
    change (evaluate K S.X₄).hom ≫ restriction K S.f₃₄.le =
      res K S.shortComplex.g ≫ res K biprod.inr ≫ (evaluate K S.X₃).hom
    rw [← Category.assoc, res_comp]
    change _ = res K (biprod.inr ≫ biprod.desc _ _) ≫ _
    rw [biprod.inr_desc]
    exact evaluate_res K S.f₃₄.le

def sectionShortComplexIso : CycleQ2RectangularTrace.pair S.shortComplex K ≅
    sectionShortComplex K S :=
  ShortComplex.isoMk (evaluate K S.X₄) (pairIso K S) (evaluate K S.X₁)
    (compatible_eq K S) (difference_eq K S)

theorem sectionShortComplex_exact [∀ n, Injective (K.X n)] :
    (sectionShortComplex K S).ShortExact :=
  ShortComplex.shortExact_of_iso (sectionShortComplexIso K S)
    (CycleQ2RectangularTrace.pair_exact S.shortComplex K S.shortComplex_shortExact)

/-- Sections on the actual union enter the actual signed two-open total
complex by their positive restrictions and zero overlap component. -/
def augmentation : row K S.X₄ ⟶ mappingCocone (difference K S) :=
  CycleQ2CechMappingCocone.zeroLift (compatible K S) (difference K S)
    (compatible_difference K S)

theorem augmentation_quasiIso [∀ n, Injective (K.X n)] :
    QuasiIso (augmentation K S) :=
  CycleQ2CechMappingCocone.augmentation_quasiIso (sectionShortComplex K S)
    (sectionShortComplex_exact K S)

end CycleQ2RectangularSections

#print axioms CycleQ2RectangularSections.augmentation_quasiIso

/-! Finite target covers are assembled before taking cohomology. The
following construction keeps the sections on every nonempty face and
the actual restrictions. It applies on an arbitrary ambient open, so
the two curve charts and their overlap can use the same target complex. -/

namespace CycleQ2FiniteOpenComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)

private abbrev CC := CochainComplex AddCommGrpCat.{0} ℤ

variable {X : TopCat.{0}}

/-- Complexes with the actual restriction direction on opens. -/
structure System (X : TopCat.{0}) where
  obj : Opens X → CC
  res {U V : Opens X} : U ≤ V → (obj V ⟶ obj U)
  res_id (U : Opens X) : res (le_refl U) = 𝟙 _
  res_comp {U V W : Opens X} (h : U ≤ V) (g : V ≤ W) :
    res g ≫ res h = res (h.trans g)

namespace System

def on (F : System X) (W : Opens X) : System X where
  obj U := F.obj (U ⊓ W)
  res h := F.res (inf_le_inf h (le_refl W))
  res_id U := F.res_id (U ⊓ W)
  res_comp h g := F.res_comp _ _

structure Morphism (F G : System X) where
  app (U : Opens X) : F.obj U ⟶ G.obj U
  natural {U V : Opens X} (h : U ≤ V) :
    app V ≫ G.res h = F.res h ≫ app U

def identity (F : System X) : Morphism F F where
  app _ := 𝟙 _
  natural _ := by simp

def restrictMorphism {F G : System X} (ρ : Morphism F G) (W : Opens X) :
    Morphism (F.on W) (G.on W) where
  app U := ρ.app (U ⊓ W)
  natural h := ρ.natural (inf_le_inf h (le_refl W))

end System

def sections (K : CochainComplex (AbSheaf X) ℤ) : System X where
  obj := CycleQ2RectangularSections.row K
  res := CycleQ2RectangularSections.restriction K
  res_id := CycleQ2RectangularSections.restriction_id K
  res_comp := CycleQ2RectangularSections.restriction_comp K

def sectionMap {K L : CochainComplex (AbSheaf X) ℤ} (ρ : K ⟶ L) :
    System.Morphism (sections K) (sections L) where
  app := CycleQ2RectangularSections.coefficient K ρ
  natural := CycleQ2RectangularSections.coefficient_natural K ρ

/-- An actual finite-cover complex, augmented from sections on its
union. The ambient open is still a variable of the construction. -/
structure Augmented (F : System X) (W : Opens X) where
  system : System X
  inclusion : System.Morphism (F.on W) system

def single (F : System X) (W : Opens X) : Augmented F W where
  system := F.on W
  inclusion := System.identity _

namespace Augmented

variable {F : System X} {W : Opens X} (T : Augmented F W) (V : Opens X)

def overlap (U : Opens X) :
    T.system.obj U ⊞ F.obj (U ⊓ V) ⟶ T.system.obj (U ⊓ V) :=
  biprod.desc (T.system.res (show U ⊓ V ≤ U from inf_le_left))
    (-(F.res (show (U ⊓ V) ⊓ W ≤ U ⊓ V from inf_le_left) ≫
      T.inclusion.app (U ⊓ V)))

def vertices (U : Opens X) :
    F.obj (U ⊓ (W ⊔ V)) ⟶ T.system.obj U ⊞ F.obj (U ⊓ V) :=
  biprod.lift
    (F.res (inf_le_inf (le_refl U) (show W ≤ W ⊔ V from le_sup_left)) ≫ T.inclusion.app U)
    (F.res (inf_le_inf (le_refl U) (show V ≤ W ⊔ V from le_sup_right)))

theorem vertices_overlap (U : Opens X) : vertices T V U ≫ overlap T V U = 0 := by
  simp only [vertices, overlap, biprod.lift_desc, Preadditive.comp_neg, Category.assoc]
  rw [T.inclusion.natural (show U ⊓ V ≤ U from inf_le_left)]
  change (F.res _ ≫ F.res _ ≫ T.inclusion.app (U ⊓ V)) +
    -(F.res _ ≫ F.res _ ≫ T.inclusion.app (U ⊓ V)) = 0
  simp only [← Category.assoc, F.res_comp, add_neg_cancel]

theorem overlap_natural {U U' : Opens X} (h : U' ≤ U) :
    overlap T V U ≫ T.system.res (inf_le_inf h (le_refl V)) =
      biprod.map (T.system.res h) (F.res (inf_le_inf h (le_refl V))) ≫ overlap T V U' := by
  apply biprod.hom_ext'
  · simp only [overlap, biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc,
      T.system.res_comp]
  · simp only [overlap, biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
    rw [T.inclusion.natural (inf_le_inf h (le_refl V))]
    change -(F.res _ ≫ F.res _ ≫ T.inclusion.app (U' ⊓ V)) =
      -(F.res _ ≫ F.res _ ≫ T.inclusion.app (U' ⊓ V))
    simp only [← Category.assoc, F.res_comp]

theorem vertices_natural {U U' : Opens X} (h : U' ≤ U) :
    vertices T V U ≫ biprod.map (T.system.res h) (F.res (inf_le_inf h (le_refl V))) =
      F.res (inf_le_inf h (le_refl (W ⊔ V))) ≫ vertices T V U' := by
  apply biprod.hom_ext
  · simp only [vertices, Category.assoc, biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
    rw [T.inclusion.natural h]
    change F.res _ ≫ F.res _ ≫ T.inclusion.app U' =
      F.res _ ≫ F.res _ ≫ T.inclusion.app U'
    simp only [← Category.assoc, F.res_comp]
  · simp only [vertices, Category.assoc, biprod.map_snd, biprod.lift_snd_assoc,
      biprod.lift_snd, F.res_comp]

def addSystem : System X where
  obj U := mappingCocone (overlap T V U)
  res h := CycleQ2CechMappingCocone.map _ _
    (biprod.map (T.system.res h) (F.res (inf_le_inf h (le_refl V))))
    (T.system.res (inf_le_inf h (le_refl V))) (overlap_natural T V h)
  res_id U := by
    have hpair : biprod.map (T.system.res (le_refl U))
        (F.res (inf_le_inf (le_refl U) (le_refl V))) = 𝟙 _ := by
      apply biprod.hom_ext <;> simp only [biprod.map_fst, biprod.map_snd,
        T.system.res_id, F.res_id, Category.comp_id, Category.id_comp]
    simp only [hpair, T.system.res_id, CycleQ2CechMappingCocone.map_id]
  res_comp h g := by
    rw [CycleQ2CechMappingCocone.map_comp]
    have hpair :
        biprod.map (T.system.res g) (F.res (inf_le_inf g (le_refl V))) ≫
          biprod.map (T.system.res h) (F.res (inf_le_inf h (le_refl V))) =
        biprod.map (T.system.res (h.trans g)) (F.res (inf_le_inf (h.trans g) (le_refl V))) := by
      apply biprod.hom_ext
      · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, T.system.res_comp]
      · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc, F.res_comp]
    rw [hpair, T.system.res_comp]

def add : Augmented F (W ⊔ V) where
  system := addSystem T V
  inclusion :=
    { app U := CycleQ2CechMappingCocone.zeroLift (vertices T V U) (overlap T V U)
        (vertices_overlap T V U)
      natural := by
        intro U U' h
        exact CycleQ2CechMappingCocone.zeroLift_natural
          (vertices T V U') (overlap T V U') (vertices_overlap T V U')
          (vertices T V U) (overlap T V U) (vertices_overlap T V U)
          _ _ _ (vertices_natural T V h) (overlap_natural T V h) }

end Augmented

/-- A coefficient comparison retains the positive augmentation, in
addition to every restriction map. -/
structure Comparison {F G : System X} {W : Opens X}
    (ρ : System.Morphism F G) (T : Augmented F W) (T' : Augmented G W) where
  hom : System.Morphism T.system T'.system
  square (U : Opens X) : T.inclusion.app U ≫ hom.app U =
    ρ.app (U ⊓ W) ≫ T'.inclusion.app U

def singleComparison {F G : System X} (ρ : System.Morphism F G) (W : Opens X) :
    Comparison ρ (single F W) (single G W) where
  hom := System.restrictMorphism ρ W
  square _ := by simp only [single, System.identity, Category.id_comp, Category.comp_id]

namespace Comparison

variable {F G : System X} {W : Opens X} {ρ : System.Morphism F G}
  {T : Augmented F W} {T' : Augmented G W} (c : Comparison ρ T T') (V : Opens X)

theorem overlap (U : Opens X) :
    Augmented.overlap T V U ≫ c.hom.app (U ⊓ V) =
      biprod.map (c.hom.app U) (ρ.app (U ⊓ V)) ≫ Augmented.overlap T' V U := by
  apply biprod.hom_ext'
  · simp only [Augmented.overlap, biprod.inl_desc_assoc, biprod.inl_map_assoc,
      biprod.inl_desc]
    exact (c.hom.natural (show U ⊓ V ≤ U from inf_le_left)).symm
  · simp only [Augmented.overlap, biprod.inr_desc_assoc, biprod.inr_map_assoc,
      biprod.inr_desc, Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc]
    rw [c.square (U ⊓ V)]
    simpa only [Category.assoc] using congrArg
      (fun a => -(a ≫ T'.inclusion.app (U ⊓ V)))
      (ρ.natural (show (U ⊓ V) ⊓ W ≤ U ⊓ V from inf_le_left)).symm

theorem vertices (U : Opens X) :
    Augmented.vertices T V U ≫ biprod.map (c.hom.app U) (ρ.app (U ⊓ V)) =
      ρ.app (U ⊓ (W ⊔ V)) ≫ Augmented.vertices T' V U := by
  apply biprod.hom_ext
  · simp only [Augmented.vertices, Category.assoc, biprod.map_fst,
      biprod.lift_fst_assoc, biprod.lift_fst]
    rw [c.square U]
    simpa only [Category.assoc] using congrArg (fun a => a ≫ T'.inclusion.app U)
      (ρ.natural (inf_le_inf (le_refl U) (show W ≤ W ⊔ V from le_sup_left))).symm
  · simp only [Augmented.vertices, Category.assoc, biprod.map_snd,
      biprod.lift_snd_assoc, biprod.lift_snd]
    exact (ρ.natural (inf_le_inf (le_refl U) (show V ≤ W ⊔ V from le_sup_right))).symm

def add : Comparison ρ (T.add V) (T'.add V) where
  hom :=
    { app U := CycleQ2CechMappingCocone.map _ _
        (biprod.map (c.hom.app U) (ρ.app (U ⊓ V))) (c.hom.app (U ⊓ V))
        (overlap c V U)
      natural := by
        intro U U' h
        dsimp only [Augmented.add, Augmented.addSystem]
        rw [CycleQ2CechMappingCocone.map_comp, CycleQ2CechMappingCocone.map_comp]
        have ha :
            biprod.map (c.hom.app U') (ρ.app (U' ⊓ V)) ≫
              biprod.map (T'.system.res h) (G.res (inf_le_inf h (le_refl V))) =
            biprod.map (T.system.res h) (F.res (inf_le_inf h (le_refl V))) ≫
              biprod.map (c.hom.app U) (ρ.app (U ⊓ V)) := by
          apply biprod.hom_ext
          · simp only [Category.assoc, biprod.map_fst, biprod.map_fst_assoc, c.hom.natural h]
          · simp only [Category.assoc, biprod.map_snd, biprod.map_snd_assoc,
              ρ.natural (inf_le_inf h (le_refl V))]
        rw [ha, c.hom.natural (inf_le_inf h (le_refl V))] }
  square U := CycleQ2CechMappingCocone.zeroLift_natural
    (Augmented.vertices T V U) (Augmented.overlap T V U) (Augmented.vertices_overlap T V U)
    (Augmented.vertices T' V U) (Augmented.overlap T' V U) (Augmented.vertices_overlap T' V U)
    _ _ _ (vertices c V U) (overlap c V U)

theorem add_quasiIso (U : Opens X) [QuasiIso (c.hom.app U)]
    [QuasiIso (ρ.app (U ⊓ V))] [QuasiIso (c.hom.app (U ⊓ V))] :
    QuasiIso ((add c V).hom.app U) := by
  letI : QuasiIso (biprod.map (c.hom.app U) (ρ.app (U ⊓ V))) :=
    CycleQ2CechMappingCocone.biprodMap_quasiIso _ _
  exact CycleQ2CechMappingCocone.map_quasiIso _ _ _ _ _

end Comparison

/-- An ordered nonempty finite cover. Appending an open retains every
old face and every face intersected with the new open. -/
inductive Cover (X : TopCat.{0}) where
  | one (U : Opens X)
  | snoc (c : Cover X) (U : Opens X)

namespace Cover

def union : Cover X → Opens X
  | .one U => U
  | .snoc c U => union c ⊔ U

def assemble (F : System X) : (c : Cover X) → Augmented F c.union
  | .one U => single F U
  | .snoc c U => (assemble F c).add U

def compare {F G : System X} (ρ : System.Morphism F G) :
    (c : Cover X) → Comparison ρ (c.assemble F) (c.assemble G)
  | .one U => singleComparison ρ U
  | .snoc c U => (compare ρ c).add U

local instance : DecidableEq (Opens X) := Classical.decEq _

def faces : Cover X → Opens X → Finset (Opens X)
  | .one V, U => {U ⊓ V}
  | .snoc c V, U => (c.faces U ∪ {U ⊓ V}) ∪ c.faces (U ⊓ V)

/-- The map on a finite total complex is a quasi-isomorphism whenever
the actual maps on its nonempty faces are quasi-isomorphisms. -/
theorem compare_quasiIso {F G : System X} (ρ : System.Morphism F G) (c : Cover X)
    (U : Opens X) (h : ∀ V ∈ c.faces U, QuasiIso (ρ.app V)) :
    QuasiIso ((c.compare ρ).hom.app U) := by
  induction c generalizing U with
  | one V => exact h (U ⊓ V) (by simp [faces])
  | snoc c V ih =>
      haveI : QuasiIso ((c.compare ρ).hom.app U) := ih U (fun Z hZ => h Z (by simp [faces, hZ]))
      haveI : QuasiIso (ρ.app (U ⊓ V)) := h (U ⊓ V) (by simp [faces])
      haveI : QuasiIso ((c.compare ρ).hom.app (U ⊓ V)) :=
        ih (U ⊓ V) (fun Z hZ => h Z (by simp [faces, hZ]))
      exact Comparison.add_quasiIso _ V U

def four (U V W T : Opens X) : Cover X := .snoc (.snoc (.snoc (.one U) V) W) T

@[simp] theorem four_union (U V W T : Opens X) : (four U V W T).union = ((U ⊔ V) ⊔ W) ⊔ T := rfl

end Cover

end CycleQ2FiniteOpenComplex

#print axioms CycleQ2FiniteOpenComplex.Cover.compare_quasiIso

namespace CycleQ2FiniteOpenComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)

variable {X : TopCat.{0}}

/-- The actual Mayer–Vietoris square used when a new target open is
added to the existing union. -/
def addSquare (W V U : Opens X) : (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := (U ⊓ V) ⊓ W
      X₂ := U ⊓ W
      X₃ := U ⊓ V
      X₄ := U ⊓ (W ⊔ V)
      f₁₂ := homOfLE (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) (le_refl W))
      f₁₃ := homOfLE inf_le_left
      f₂₄ := homOfLE (inf_le_inf (le_refl U) (show W ≤ W ⊔ V from le_sup_left))
      f₃₄ := homOfLE (inf_le_inf (le_refl U) (show V ≤ W ⊔ V from le_sup_right))
      fac := Subsingleton.elim _ _ }
    (by ext x; change (_ ∧ (_ ∨ _)) ↔ ((_ ∧ _) ∨ (_ ∧ _)); tauto)
    (by ext x; change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ (_ ∧ _)); tauto)

namespace Augmented

variable {K : CochainComplex (AbSheaf X) ℤ} {W : Opens X}
  (T : Augmented (sections K) W) (V U : Opens X)

private theorem add_overlap_square :
    CycleQ2RectangularSections.difference K (addSquare W V U) ≫ T.inclusion.app (U ⊓ V) =
      biprod.map (T.inclusion.app U) (𝟙 _) ≫ overlap T V U := by
  apply biprod.hom_ext'
  · simp only [CycleQ2RectangularSections.difference, overlap,
      biprod.inl_desc_assoc, biprod.inl_map_assoc, biprod.inl_desc]
    exact (T.inclusion.natural (show U ⊓ V ≤ U from inf_le_left)).symm
  · simp only [CycleQ2RectangularSections.difference, overlap,
      biprod.inr_desc_assoc, biprod.inr_map_assoc, biprod.inr_desc,
      Preadditive.neg_comp, Category.id_comp]

private theorem add_vertices_square :
    CycleQ2RectangularSections.compatible K (addSquare W V U) ≫
      biprod.map (T.inclusion.app U) (𝟙 _) = vertices T V U := by
  apply biprod.hom_ext
  · simp only [CycleQ2RectangularSections.compatible, vertices, Category.assoc,
      biprod.map_fst, biprod.lift_fst_assoc, biprod.lift_fst]
  · simp only [CycleQ2RectangularSections.compatible, vertices, Category.assoc,
      biprod.map_snd, biprod.lift_snd_assoc, biprod.lift_snd, Category.comp_id]

theorem add_inclusion_eq :
    CycleQ2RectangularSections.augmentation K (addSquare W V U) ≫
      CycleQ2CechMappingCocone.map _ _
        (biprod.map (T.inclusion.app U) (𝟙 _)) (T.inclusion.app (U ⊓ V))
        (add_overlap_square T V U) = (T.add V).inclusion.app U := by
  simpa only [Category.id_comp] using
    CycleQ2CechMappingCocone.zeroLift_natural
      (CycleQ2RectangularSections.compatible K (addSquare W V U))
      (CycleQ2RectangularSections.difference K (addSquare W V U))
      (CycleQ2RectangularSections.compatible_difference K (addSquare W V U))
      (vertices T V U) (overlap T V U) (vertices_overlap T V U) (𝟙 _) _ _
      (by simpa only [Category.id_comp] using add_vertices_square T V U)
      (add_overlap_square T V U)

theorem add_inclusion_quasiIso [∀ n, Injective (K.X n)]
    [QuasiIso (T.inclusion.app U)] [QuasiIso (T.inclusion.app (U ⊓ V))] :
    QuasiIso ((T.add V).inclusion.app U) := by
  letI : QuasiIso (biprod.map (T.inclusion.app U) (𝟙 (CycleQ2RectangularSections.row K (U ⊓ V)))) :=
    CycleQ2CechMappingCocone.biprodMap_quasiIso _ _
  letI : QuasiIso (CycleQ2CechMappingCocone.map _ _
      (biprod.map (T.inclusion.app U) (𝟙 _)) (T.inclusion.app (U ⊓ V))
      (add_overlap_square T V U)) := CycleQ2CechMappingCocone.map_quasiIso _ _ _ _ _
  letI : QuasiIso (CycleQ2RectangularSections.augmentation K (addSquare W V U)) :=
    CycleQ2RectangularSections.augmentation_quasiIso K _
  rw [← add_inclusion_eq T V U]
  infer_instance

end Augmented

namespace Cover

/-- For a termwise injective sheaf complex, the positive finite-cover
augmentation computes sections on the actual union in every degree. -/
theorem inclusion_quasiIso (K : CochainComplex (AbSheaf X) ℤ)
    [∀ n, Injective (K.X n)] (c : Cover X) (U : Opens X) :
    QuasiIso ((c.assemble (sections K)).inclusion.app U) := by
  induction c generalizing U with
  | one V => exact inferInstanceAs (QuasiIso (𝟙 _))
  | snoc c V ih =>
      letI := ih U
      letI := ih (U ⊓ V)
      exact Augmented.add_inclusion_quasiIso _ V U

end Cover

end CycleQ2FiniteOpenComplex

#print axioms CycleQ2FiniteOpenComplex.Cover.inclusion_quasiIso

namespace CycleQ2RectangularSections

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2AffineHypercohomologyComparison (sectionComplex)

variable {X : TopCat.{0}} {K I : CochainComplex (AbSheaf X) ℤ}

theorem evaluate_coefficient (ρ : K ⟶ I) (U : Opens X) :
    (evaluate K U).hom ≫ coefficient K ρ U =
      (sectionComplex (freeOpen U)).map ρ ≫ (evaluate I U).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro x
  exact CycleQ2CechTwoToDerived.freeOpenSections_postcomp U x (ρ.f n)

theorem coefficient_quasiIso (ρ : K ⟶ I) (U : Opens X)
    [QuasiIso ((sectionComplex (freeOpen U)).map ρ)] : QuasiIso (coefficient K ρ U) := by
  letI := HasDerivedCategory.standard AddCommGrpCat.{0}
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _).mp
  let D := DerivedCategory.Q (C := AddCommGrpCat.{0})
  haveI : IsIso (D.map (evaluate K U).hom ≫ D.map (coefficient K ρ U)) := by
    rw [← D.map_comp, evaluate_coefficient]
    infer_instance
  exact IsIso.of_isIso_comp_left (D.map (evaluate K U).hom) _

attribute [local instance] HasDerivedCategory.standard

/-- Actual section cohomology of a K-injective complex, evaluated on
an open, is the corresponding ordinary derived morphism group. -/
def rowDerivedEquiv (I : CochainComplex (AbSheaf X) ℤ) [I.IsKInjective]
    (U : Opens X) (n : ℤ) :
    (row I U).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen U) ⟶
        (DerivedCategory.Q.obj I)⟦n⟧) :=
  (((homologyFunctor AddCommGrpCat.{0} (.up ℤ) n).mapIso (evaluate I U).symm).addCommGroupIsoToAddEquiv).trans
      (CycleQ2KInjectiveSections.derivedSectionsEquiv (freeOpen U) I n)

theorem rowDerivedEquiv_natural [I.IsKInjective] {U V : Opens X} (h : U ≤ V)
    (n : ℤ) (x : (row I V).homology n) :
    rowDerivedEquiv I U n (homologyMap (restriction I h) n x) =
      (DerivedCategory.singleFunctor (AbSheaf X) 0).map (freeOpenMap h) ≫
        rowDerivedEquiv I V n x := by
  have he : restriction I h ≫ (evaluate I U).inv =
      (evaluate I V).inv ≫ CycleQ2RectangularTrace.res I (freeOpenMap h) := by
    apply (cancel_mono (evaluate I U).hom).mp
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
      ← evaluate_res I h, Iso.inv_hom_id_assoc]
  have hh := congrArg (fun f => homologyMap f n) he
  simp only [homologyMap_comp] at hh
  have hx := ConcreteCategory.congr_hom hh x
  change CycleQ2KInjectiveSections.derivedSectionsEquiv (freeOpen U) I n
      (homologyMap (evaluate I U).inv n (homologyMap (restriction I h) n x)) = _
  rw [show homologyMap (evaluate I U).inv n (homologyMap (restriction I h) n x) = _ from hx]
  exact CycleQ2KInjectiveSections.derivedSectionsEquiv_precomp I (freeOpenMap h) n
    (homologyMap (evaluate I V).inv n x)

end CycleQ2RectangularSections

namespace CycleQ2FiniteOpenComplex

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2RectangularSections (row rowDerivedEquiv)

attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {X : TopCat.{0}} (K : CochainComplex (AbSheaf X) ℤ)
  {I : CochainComplex (AbSheaf X) ℤ} (ρ : K ⟶ I)
  [∀ n, Injective (I.X n)] (c : Cover X)

/-- The actual finite Čech complex is compared with sections of one
fixed injective resolution on the actual covered open. -/
def homologyIso (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ c.faces U, QuasiIso ((sectionMap ρ).app V)) :
    ((c.assemble (sections K)).system.obj U).homology n ≅
      (row I (U ⊓ c.union)).homology n := by
  letI := c.compare_quasiIso (sectionMap ρ) U h
  letI := c.inclusion_quasiIso I U
  exact asIso (homologyMap ((c.compare (sectionMap ρ)).hom.app U) n) ≪≫
    (asIso (homologyMap ((c.assemble (sections I)).inclusion.app U) n)).symm

theorem homologyIso_comp_inclusion (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ c.faces U, QuasiIso ((sectionMap ρ).app V)) :
    (homologyIso K ρ c U n h).hom ≫
        homologyMap ((c.assemble (sections I)).inclusion.app U) n =
      homologyMap ((c.compare (sectionMap ρ)).hom.app U) n := by
  letI := c.compare_quasiIso (sectionMap ρ) U h
  letI := c.inclusion_quasiIso I U
  simp only [homologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem homologyIso_natural {U V : Opens X} (g : U ≤ V) (n : ℤ)
    (hU : ∀ Z ∈ c.faces U, QuasiIso ((sectionMap ρ).app Z))
    (hV : ∀ Z ∈ c.faces V, QuasiIso ((sectionMap ρ).app Z)) :
    homologyMap ((c.assemble (sections K)).system.res g) n ≫
        (homologyIso K ρ c U n hU).hom =
      (homologyIso K ρ c V n hV).hom ≫
        homologyMap (CycleQ2RectangularSections.restriction I
          (inf_le_inf g (le_refl c.union))) n := by
  letI := c.inclusion_quasiIso I U
  have hc := congrArg (fun f => homologyMap f n) ((c.compare (sectionMap ρ)).hom.natural g)
  have hi := congrArg (fun f => homologyMap f n) ((c.assemble (sections I)).inclusion.natural g)
  simp only [homologyMap_comp] at hc hi
  apply (cancel_mono (homologyMap ((c.assemble (sections I)).inclusion.app U) n)).mp
  calc
    _ = homologyMap ((c.assemble (sections K)).system.res g) n ≫
        homologyMap ((c.compare (sectionMap ρ)).hom.app U) n := by
      rw [Category.assoc, homologyIso_comp_inclusion]
    _ = homologyMap ((c.compare (sectionMap ρ)).hom.app V) n ≫
        homologyMap ((c.assemble (sections I)).system.res g) n := hc.symm
    _ = ((homologyIso K ρ c V n hV).hom ≫
        homologyMap ((c.assemble (sections I)).inclusion.app V) n) ≫
        homologyMap ((c.assemble (sections I)).system.res g) n := by
      rw [homologyIso_comp_inclusion]
    _ = _ := by rw [Category.assoc, hi, ← Category.assoc]

variable [QuasiIso ρ] [I.IsKInjective]

/-- Every ordinary derived class on the covered open is represented by
the genuine finite-face section total complex. The chosen resolution
is the same at every ambient open. -/
def classesOfResolution (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ c.faces U, QuasiIso ((sectionMap ρ).app V)) :
    ((c.assemble (sections K)).system.obj U).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen (U ⊓ c.union)) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) := by
  let z := (CategoryTheory.shiftFunctor (DerivedCategory (AbSheaf X)) n).mapIso
    ((asIso (DerivedCategory.Q.map ρ)).symm)
  let e : ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen (U ⊓ c.union)) ⟶
      (DerivedCategory.Q.obj I)⟦n⟧) ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen (U ⊓ c.union)) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) :=
    { Iso.homCongr (Iso.refl _) z with map_add' x y := by simp [Iso.homCongr] }
  exact ((homologyIso K ρ c U n h).addCommGroupIsoToAddEquiv.trans
    (rowDerivedEquiv I (U ⊓ c.union) n)).trans e

theorem classesOfResolution_apply (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ c.faces U, QuasiIso ((sectionMap ρ).app V))
    (x : ((c.assemble (sections K)).system.obj U).homology n) :
    classesOfResolution K ρ c U n h x =
      rowDerivedEquiv I (U ⊓ c.union) n ((homologyIso K ρ c U n h).hom x) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (AbSheaf X)) n).map
          (asIso (DerivedCategory.Q.map ρ)).inv := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

theorem classesOfResolution_natural {U V : Opens X} (g : U ≤ V) (n : ℤ)
    (hU : ∀ Z ∈ c.faces U, QuasiIso ((sectionMap ρ).app Z))
    (hV : ∀ Z ∈ c.faces V, QuasiIso ((sectionMap ρ).app Z))
    (x : ((c.assemble (sections K)).system.obj V).homology n) :
    classesOfResolution K ρ c U n hU
        (homologyMap ((c.assemble (sections K)).system.res g) n x) =
      (DerivedCategory.singleFunctor (AbSheaf X) 0).map
        (freeOpenMap (inf_le_inf g (le_refl c.union))) ≫
          classesOfResolution K ρ c V n hV x := by
  rw [classesOfResolution_apply, classesOfResolution_apply]
  have h := ConcreteCategory.congr_hom (homologyIso_natural K ρ c g n hU hV) x
  change (homologyIso K ρ c U n hU).hom
      (homologyMap ((c.assemble (sections K)).system.res g) n x) =
    homologyMap (CycleQ2RectangularSections.restriction I
      (inf_le_inf g (le_refl c.union))) n ((homologyIso K ρ c V n hV).hom x) at h
  rw [h, CycleQ2RectangularSections.rowDerivedEquiv_natural, Category.assoc]

end CycleQ2FiniteOpenComplex

#print axioms CycleQ2FiniteOpenComplex.classesOfResolution
#print axioms CycleQ2FiniteOpenComplex.classesOfResolution_natural

namespace CycleQ2FiniteOpenComplex

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2RectangularSections (row rowDerivedEquiv)

attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {X : TopCat.{0}}

namespace System

def compose {F G H : System X} (a : Morphism F G) (b : Morphism G H) : Morphism F H where
  app U := a.app U ≫ b.app U
  natural h := by rw [Category.assoc, b.natural, ← Category.assoc, a.natural, Category.assoc]

theorem res_isIso (F : System X) {U V : Opens X} (h : U ≤ V) (e : U = V) : IsIso (F.res h) := by
  subst V
  rw [show h = le_refl U from Subsingleton.elim _ _, F.res_id]
  infer_instance

end System

namespace Augmented

variable {F : System X} {W : Opens X} (T : Augmented F W)

/-- The augmentation from all sections first restricts to the actual
covered union. It is defined even when the cover is not global. -/
def fromAll : System.Morphism F T.system where
  app U := F.res (show U ⊓ W ≤ U from inf_le_left) ≫ T.inclusion.app U
  natural h := by
    rw [Category.assoc, T.inclusion.natural]
    change F.res _ ≫ F.res _ ≫ T.inclusion.app _ = F.res _ ≫ (F.res _ ≫ T.inclusion.app _)
    simp only [← Category.assoc, F.res_comp]

theorem fromAll_quasiIso (hW : W = ⊤) (U : Opens X) [QuasiIso (T.inclusion.app U)] :
    QuasiIso (T.fromAll.app U) := by
  letI : IsIso (F.res (show U ⊓ W ≤ U from inf_le_left)) :=
    F.res_isIso _ (by rw [hW, inf_top_eq])
  change QuasiIso (_ ≫ _)
  infer_instance

end Augmented

/-- The inner finite cover is the original target cover; the outer one
is the original curve cover. Thus no product open with a whole proper
factor is declared affine. -/
def doubleSystem (F : System X) (outer inner : Cover X) : System X :=
  (outer.assemble (inner.assemble F).system).system

def doubleMap {F G : System X} (ρ : System.Morphism F G) (outer inner : Cover X) :
    System.Morphism (doubleSystem F outer inner) (doubleSystem G outer inner) :=
  (outer.compare (inner.compare ρ).hom).hom

def doubleAugmentation (F : System X) (outer inner : Cover X) :
    System.Morphism F (doubleSystem F outer inner) :=
  System.compose (outer.assemble F).fromAll
    (outer.compare (inner.assemble F).fromAll).hom

theorem doubleMap_quasiIso {F G : System X} (ρ : System.Morphism F G)
    (outer inner : Cover X) (U : Opens X)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, QuasiIso (ρ.app W)) :
    QuasiIso ((doubleMap ρ outer inner).app U) :=
  outer.compare_quasiIso (inner.compare ρ).hom U
    (fun V hV => inner.compare_quasiIso ρ V (h V hV))

theorem doubleAugmentation_quasiIso (I : CochainComplex (AbSheaf X) ℤ)
    [∀ n, Injective (I.X n)] (outer inner : Cover X)
    (ho : outer.union = ⊤) (hi : inner.union = ⊤) (U : Opens X) :
    QuasiIso ((doubleAugmentation (sections I) outer inner).app U) := by
  have hf (c : Cover X) (hc : c.union = ⊤) (V : Opens X) :
      QuasiIso ((c.assemble (sections I)).fromAll.app V) := by
    letI := c.inclusion_quasiIso I V
    exact Augmented.fromAll_quasiIso _ hc V
  letI := hf outer ho U
  letI : QuasiIso ((outer.compare (inner.assemble (sections I)).fromAll).hom.app U) :=
    outer.compare_quasiIso _ U (fun V _ => hf inner hi V)
  change QuasiIso (_ ≫ _)
  infer_instance

private instance sheafEnoughInjectives : EnoughInjectives (AbSheaf X) := by
  change EnoughInjectives (TopCat.Sheaf AddCommGrpCat.{0} X)
  infer_instance

private structure Resolution (K : CochainComplex (AbSheaf X) ℤ) where
  obj : CochainComplex (AbSheaf X) ℤ
  ι : K ⟶ obj
  quasiIso : QuasiIso ι
  injective : ∀ n, Injective (obj.X n)
  kInjective : obj.IsKInjective
  row (U : Opens X) :
    (∀ n, CycleQ2AcyclicComplexSections.AcyclicFor (freeOpen U) (K.X n)) →
      QuasiIso ((sectionMap ι).app U)

/-- One bounded-below injective resolution supplies the same coefficient
map on every curve rectangle and every target face. -/
private def resolution (K : CochainComplex (AbSheaf X) ℤ) (b : ℤ) [K.IsStrictlyGE b] :
    Resolution K := by
  let hr := CochainComplex.Plus.modelCategoryQuillen.exists_mono_quasiIso_injective K (b - 1) b
  let I := hr.choose
  let ρ : K ⟶ I := hr.choose_spec.choose
  have hI := hr.choose_spec.choose_spec
  letI : Mono ρ := hI.1
  letI : QuasiIso ρ := hI.2.1
  letI : ∀ n, Injective (I.X n) := hI.2.2.1
  letI : I.IsStrictlyGE (b - 1) := hI.2.2.2
  refine ⟨I, ρ, inferInstance, inferInstance, CochainComplex.isKInjective_of_injective I (b - 1), ?_⟩
  intro U hU
  letI : QuasiIso ((CycleQ2AffineHypercohomologyComparison.sectionComplex (freeOpen U)).map ρ) :=
    CycleQ2AffineHypercohomologyComparison.sections_quasiIso (freeOpen U) ρ (b - 1) hU
      (fun n m => Ext.subsingleton_of_injective (freeOpen U) (I.X n) m)
  exact CycleQ2RectangularSections.coefficient_quasiIso ρ U

variable (K : CochainComplex (AbSheaf X) ℤ) {I : CochainComplex (AbSheaf X) ℤ}
  (ρ : K ⟶ I) [∀ n, Injective (I.X n)] (outer inner : Cover X)
  (ho : outer.union = ⊤) (hi : inner.union = ⊤)

def doubleHomologyIso (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, QuasiIso ((sectionMap ρ).app W)) :
    ((doubleSystem (sections K) outer inner).obj U).homology n ≅ (row I U).homology n := by
  letI := doubleMap_quasiIso (sectionMap ρ) outer inner U h
  letI := doubleAugmentation_quasiIso I outer inner ho hi U
  exact asIso (homologyMap ((doubleMap (sectionMap ρ) outer inner).app U) n) ≪≫
    (asIso (homologyMap ((doubleAugmentation (sections I) outer inner).app U) n)).symm

theorem doubleHomologyIso_comp_augmentation (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, QuasiIso ((sectionMap ρ).app W)) :
    (doubleHomologyIso K ρ outer inner ho hi U n h).hom ≫
        homologyMap ((doubleAugmentation (sections I) outer inner).app U) n =
      homologyMap ((doubleMap (sectionMap ρ) outer inner).app U) n := by
  letI := doubleMap_quasiIso (sectionMap ρ) outer inner U h
  letI := doubleAugmentation_quasiIso I outer inner ho hi U
  simp only [doubleHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem doubleHomologyIso_natural {U V : Opens X} (g : U ≤ V) (n : ℤ)
    (hU : ∀ Z ∈ outer.faces U, ∀ W ∈ inner.faces Z, QuasiIso ((sectionMap ρ).app W))
    (hV : ∀ Z ∈ outer.faces V, ∀ W ∈ inner.faces Z, QuasiIso ((sectionMap ρ).app W)) :
    homologyMap ((doubleSystem (sections K) outer inner).res g) n ≫
        (doubleHomologyIso K ρ outer inner ho hi U n hU).hom =
      (doubleHomologyIso K ρ outer inner ho hi V n hV).hom ≫
        homologyMap (CycleQ2RectangularSections.restriction I g) n := by
  letI := doubleAugmentation_quasiIso I outer inner ho hi U
  have hc := congrArg (fun f => homologyMap f n) ((doubleMap (sectionMap ρ) outer inner).natural g)
  have ha := congrArg (fun f => homologyMap f n) ((doubleAugmentation (sections I) outer inner).natural g)
  simp only [homologyMap_comp] at hc ha
  apply (cancel_mono (homologyMap ((doubleAugmentation (sections I) outer inner).app U) n)).mp
  calc
    _ = homologyMap ((doubleSystem (sections K) outer inner).res g) n ≫
        homologyMap ((doubleMap (sectionMap ρ) outer inner).app U) n := by
      rw [Category.assoc, doubleHomologyIso_comp_augmentation]
    _ = homologyMap ((doubleMap (sectionMap ρ) outer inner).app V) n ≫
        homologyMap ((doubleSystem (sections I) outer inner).res g) n := hc.symm
    _ = ((doubleHomologyIso K ρ outer inner ho hi V n hV).hom ≫
        homologyMap ((doubleAugmentation (sections I) outer inner).app V) n) ≫
        homologyMap ((doubleSystem (sections I) outer inner).res g) n := by
      rw [doubleHomologyIso_comp_augmentation]
    _ = _ := by rw [Category.assoc, ha, ← Category.assoc]

variable [QuasiIso ρ] [I.IsKInjective]

def doubleClassesOfResolution (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, QuasiIso ((sectionMap ρ).app W)) :
    ((doubleSystem (sections K) outer inner).obj U).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen U) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) := by
  let z := (CategoryTheory.shiftFunctor (DerivedCategory (AbSheaf X)) n).mapIso
    ((asIso (DerivedCategory.Q.map ρ)).symm)
  let e : ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen U) ⟶
      (DerivedCategory.Q.obj I)⟦n⟧) ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen U) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) :=
    { Iso.homCongr (Iso.refl _) z with map_add' x y := by simp [Iso.homCongr] }
  exact ((doubleHomologyIso K ρ outer inner ho hi U n h).addCommGroupIsoToAddEquiv.trans
    (rowDerivedEquiv I U n)).trans e

theorem doubleClassesOfResolution_apply (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, QuasiIso ((sectionMap ρ).app W))
    (x : ((doubleSystem (sections K) outer inner).obj U).homology n) :
    doubleClassesOfResolution K ρ outer inner ho hi U n h x =
      rowDerivedEquiv I U n ((doubleHomologyIso K ρ outer inner ho hi U n h).hom x) ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (AbSheaf X)) n).map
          (asIso (DerivedCategory.Q.map ρ)).inv := by
  change 𝟙 _ ≫ _ ≫ _ = _
  exact Category.id_comp _

theorem doubleClassesOfResolution_natural {U V : Opens X} (g : U ≤ V) (n : ℤ)
    (hU : ∀ Z ∈ outer.faces U, ∀ W ∈ inner.faces Z, QuasiIso ((sectionMap ρ).app W))
    (hV : ∀ Z ∈ outer.faces V, ∀ W ∈ inner.faces Z, QuasiIso ((sectionMap ρ).app W))
    (x : ((doubleSystem (sections K) outer inner).obj V).homology n) :
    doubleClassesOfResolution K ρ outer inner ho hi U n hU
        (homologyMap ((doubleSystem (sections K) outer inner).res g) n x) =
      (DerivedCategory.singleFunctor (AbSheaf X) 0).map (freeOpenMap g) ≫
        doubleClassesOfResolution K ρ outer inner ho hi V n hV x := by
  rw [doubleClassesOfResolution_apply, doubleClassesOfResolution_apply]
  have h := ConcreteCategory.congr_hom
    (doubleHomologyIso_natural K ρ outer inner ho hi g n hU hV) x
  change (doubleHomologyIso K ρ outer inner ho hi U n hU).hom
      (homologyMap ((doubleSystem (sections K) outer inner).res g) n x) =
    homologyMap (CycleQ2RectangularSections.restriction I g) n
      ((doubleHomologyIso K ρ outer inner ho hi V n hV).hom x) at h
  rw [h, CycleQ2RectangularSections.rowDerivedEquiv_natural, Category.assoc]

omit ρ [∀ n, Injective (I.X n)] [QuasiIso ρ] [I.IsKInjective] in
/-- The finite double-cover comparison has no chosen-resolution premise:
ordinary acyclicity of the actual face terms supplies one common
injective resolution and all the required face quasi-isomorphisms. -/
def doubleClasses (b : ℤ) [K.IsStrictlyGE b] (U : Opens X) (n : ℤ)
    (h : ∀ V ∈ outer.faces U, ∀ W ∈ inner.faces V, ∀ j,
      CycleQ2AcyclicComplexSections.AcyclicFor (freeOpen W) (K.X j)) :
    ((doubleSystem (sections K) outer inner).obj U).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf X) 0).obj (freeOpen U) ⟶
        (DerivedCategory.Q.obj K)⟦n⟧) := by
  let R := resolution K b
  letI := R.quasiIso
  letI := R.injective
  letI := R.kInjective
  exact doubleClassesOfResolution K R.ι outer inner ho hi U n
    (fun V hV W hW => R.row W (h V hV W hW))

omit ρ [∀ n, Injective (I.X n)] [QuasiIso ρ] [I.IsKInjective] in
theorem doubleClasses_natural (b : ℤ) [K.IsStrictlyGE b] {U V : Opens X} (g : U ≤ V) (n : ℤ)
    (hU : ∀ Z ∈ outer.faces U, ∀ W ∈ inner.faces Z, ∀ j,
      CycleQ2AcyclicComplexSections.AcyclicFor (freeOpen W) (K.X j))
    (hV : ∀ Z ∈ outer.faces V, ∀ W ∈ inner.faces Z, ∀ j,
      CycleQ2AcyclicComplexSections.AcyclicFor (freeOpen W) (K.X j))
    (x : ((doubleSystem (sections K) outer inner).obj V).homology n) :
    doubleClasses K outer inner ho hi b U n hU
        (homologyMap ((doubleSystem (sections K) outer inner).res g) n x) =
      (DerivedCategory.singleFunctor (AbSheaf X) 0).map (freeOpenMap g) ≫
        doubleClasses K outer inner ho hi b V n hV x := by
  let R := resolution K b
  letI := R.quasiIso
  letI := R.injective
  letI := R.kInjective
  exact doubleClassesOfResolution_natural K R.ι outer inner ho hi g n
    (fun Z hZ W hW => R.row W (hU Z hZ W hW))
    (fun Z hZ W hW => R.row W (hV Z hZ W hW)) x

end CycleQ2FiniteOpenComplex

#print axioms CycleQ2FiniteOpenComplex.doubleClasses
#print axioms CycleQ2FiniteOpenComplex.doubleClasses_natural

namespace CycleQ2FiniteOpenComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex TopologicalSpace

variable {X : TopCat.{0}}

theorem Comparison.fromAll {F G : System X} {W : Opens X} {ρ : System.Morphism F G}
    {T : Augmented F W} {T' : Augmented G W} (c : Comparison ρ T T') (U : Opens X) :
    T.fromAll.app U ≫ c.hom.app U = ρ.app U ≫ T'.fromAll.app U := by
  change (F.res _ ≫ T.inclusion.app U) ≫ c.hom.app U =
    ρ.app U ≫ (G.res _ ≫ T'.inclusion.app U)
  rw [Category.assoc, c.square, ← Category.assoc,
    ← ρ.natural (show U ⊓ W ≤ U from inf_le_left), Category.assoc]

theorem doubleAugmentation_factored (F : System X) (outer inner : Cover X) (U : Opens X) :
    (doubleAugmentation F outer inner).app U =
      (inner.assemble F).fromAll.app U ≫
        (outer.assemble (inner.assemble F).system).fromAll.app U :=
  (outer.compare (inner.assemble F).fromAll).fromAll U

/-- The finite global augmentation uses the original coefficient map,
not only abstract isomorphisms of its face cohomology groups. -/
theorem doubleAugmentation_coefficient {F G : System X} (ρ : System.Morphism F G)
    (outer inner : Cover X) (U : Opens X) :
    (doubleAugmentation F outer inner).app U ≫ (doubleMap ρ outer inner).app U =
      ρ.app U ≫ (doubleAugmentation G outer inner).app U := by
  rw [doubleAugmentation_factored, doubleAugmentation_factored, Category.assoc,
    (outer.compare (inner.compare ρ).hom).fromAll U,
    ← Category.assoc, (inner.compare ρ).fromAll U, Category.assoc]

namespace Cover

variable {ι : Type} [DecidableEq ι]

def fromFamily (v : ι → Opens X) : Cover X → Prop
  | .one U => ∃ i, U = v i
  | .snoc c U => fromFamily v c ∧ ∃ i, U = v i

/-- Every retained face is the intersection with an actual nonempty
finite subset of the original opens. -/
theorem face_shape (v : ι → Opens X) (c : Cover X) (hc : c.fromFamily v)
    (U Z : Opens X) (hZ : Z ∈ c.faces U) :
    ∃ S : Finset ι, S.Nonempty ∧ Z = U ⊓ S.inf v := by
  induction c generalizing U Z with
  | one V =>
      obtain ⟨i, rfl⟩ := hc
      refine ⟨{i}, Finset.singleton_nonempty i, ?_⟩
      simpa only [faces, Finset.mem_singleton, Finset.inf_singleton] using hZ
  | snoc c V ih =>
      obtain ⟨hc, i, rfl⟩ := hc
      simp only [faces, Finset.mem_union, Finset.mem_singleton] at hZ
      rcases hZ with (hZ | hZ) | hZ
      · exact ih hc U Z hZ
      · exact ⟨{i}, Finset.singleton_nonempty i, by simpa only [Finset.inf_singleton] using hZ⟩
      · obtain ⟨S, hS, hZ⟩ := ih hc (U ⊓ v i) Z hZ
        exact ⟨insert i S, ⟨i, Finset.mem_insert_self i S⟩,
          hZ.trans (by rw [Finset.inf_insert, inf_assoc])⟩

theorem four_face_shape (v : Fin 4 → Opens X) (U Z : Opens X)
    (hZ : Z ∈ (four (v 0) (v 1) (v 2) (v 3)).faces U) :
    ∃ S : Finset (Fin 4), S.Nonempty ∧ Z = U ⊓ S.inf v :=
  face_shape v _ ⟨⟨⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩, ⟨2, rfl⟩⟩, ⟨3, rfl⟩⟩ U Z hZ

end Cover

end CycleQ2FiniteOpenComplex

namespace CycleQ2FourTargetRectangleCohomology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
open AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenMap)
open CycleQ2LaurentProjectiveLine (line)
open CycleQ2ProjectiveLineStructure (structureMap)
open CycleQ2ProductCoefficients (productBase)
open CycleQ2ProductAffineOpen (productOpen isAffineOpen_product)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRham relativeDeRhamInt)
open CycleQ2FiniteOpenComplex

attribute [local instance] HasDerivedCategory.standard HasExt.standard

variable {k : Type} [Field k] [CharZero k] {C X : Scheme.{0}} [IsIntegral C]
  (f : C ⟶ line k) (q : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [IsFinite f] [SmoothOfRelativeDimension 1 (f ≫ structureMap k)]
  [SmoothOfRelativeDimension r q]

local notation "p" => f ≫ structureMap k
local notation "Y" => (pullback p q : Scheme)
local notation "P" => productBase p q

local instance : SmoothOfRelativeDimension (1 + r) P :=
  CycleQ2ProductFramedOpen.smooth_product p q r

private abbrev DR := relativeDeRhamInt P (1 + r)

private instance bounded : (DR f q r).IsStrictlyGE 0 := by
  apply ((DR f q r).isStrictlyGE_iff 0).2
  intro i hi
  exact (relativeDeRham P (1 + r)).isZero_extend_X (ComplexShape.embeddingUpIntGE 0) i
    (by intro a ha; change (0 : ℤ) + a = i at ha; omega)

def curveCover : Cover (show TopCat from Y) :=
  .snoc (.one ((pullback.fst p q) ⁻¹ᵁ CycleQ2FiniteCurveCover.zero k f))
    ((pullback.fst p q) ⁻¹ᵁ CycleQ2FiniteCurveCover.infinity k f)

def targetCover (v : Fin 4 → X.Opens) : Cover (show TopCat from Y) :=
  Cover.four ((pullback.snd p q) ⁻¹ᵁ v 0) ((pullback.snd p q) ⁻¹ᵁ v 1)
    ((pullback.snd p q) ⁻¹ᵁ v 2) ((pullback.snd p q) ⁻¹ᵁ v 3)

theorem curveCover_top : (curveCover f q).union = ⊤ := by
  change (pullback.fst p q) ⁻¹ᵁ
    (CycleQ2FiniteCurveCover.zero k f ⊔ CycleQ2FiniteCurveCover.infinity k f) = ⊤
  rw [CycleQ2FiniteCurveCover.cover_eq]
  rfl

theorem targetCover_top (v : Fin 4 → X.Opens) (hv : (⨆ i, v i) = ⊤) :
    (targetCover f q v).union = ⊤ := by
  apply le_antisymm le_top
  intro x _
  have hx : pullback.snd p q x ∈ ⨆ i, v i := by rw [hv]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  change (((pullback.snd p q x ∈ v 0 ∨ pullback.snd p q x ∈ v 1) ∨
    pullback.snd p q x ∈ v 2) ∨ pullback.snd p q x ∈ v 3)
  fin_cases i <;> tauto

private theorem product_inf_target (A : C.Opens) (B V : X.Opens) :
    productOpen p q A B ⊓ (pullback.snd p q) ⁻¹ᵁ V = productOpen p q A (B ⊓ V) := by
  ext x
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ (_ ∧ _))
  tauto

private theorem preimage_finset_inf (v : Fin 4 → X.Opens) (S : Finset (Fin 4)) :
    S.inf (fun i => (pullback.snd p q) ⁻¹ᵁ v i) = (pullback.snd p q) ⁻¹ᵁ S.inf v := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.inf_empty]; rfl
  | @insert i S hi ih => simp only [Finset.inf_insert, ih]; rfl

/-- The three outer faces are exactly the two original affine curve
charts and their original affine overlap, with the whole target open
retained. -/
theorem curve_face (B : X.Opens) (Z : Y.Opens)
    (hZ : Z ∈ (curveCover f q).faces (CycleQ2RectangularTrace.baseOpen f q B)) :
    ∃ A : C.Opens, IsAffineOpen A ∧ Z = productOpen p q A B := by
  simp only [curveCover, Cover.faces, Finset.mem_union, Finset.mem_singleton] at hZ
  rcases hZ with (rfl | rfl) | rfl
  · refine ⟨CycleQ2FiniteCurveCover.zero k f, CycleQ2FiniteCurveCover.zero_affine k f, ?_⟩
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    tauto
  · refine ⟨CycleQ2FiniteCurveCover.infinity k f, CycleQ2FiniteCurveCover.infinity_affine k f, ?_⟩
    ext x
    change (_ ∧ _) ↔ (_ ∧ _)
    tauto
  · refine ⟨CycleQ2FiniteCurveCover.torus k f, CycleQ2FiniteCurveCover.torus_affine k f, ?_⟩
    rw [CycleQ2FiniteCurveCover.overlap_eq]
    ext x
    change ((_ ∧ _) ∧ _) ↔ ((_ ∧ _) ∧ _)
    tauto

/-- Every inner face is an actual one of the fifteen nonempty target
intersections, times the same original affine curve chart. -/
theorem target_face (v : Fin 4 → X.Opens) (A : C.Opens) (B : X.Opens) (Z : Y.Opens)
    (hZ : Z ∈ (targetCover f q v).faces (productOpen p q A B)) :
    ∃ S : Finset (Fin 4), S.Nonempty ∧ Z = productOpen p q A (B ⊓ S.inf v) := by
  obtain ⟨S, hS, hZ⟩ := Cover.four_face_shape
    (fun i => (pullback.snd p q) ⁻¹ᵁ v i) (productOpen p q A B) Z hZ
  exact ⟨S, hS, hZ.trans (by rw [preimage_finset_inf, product_inf_target])⟩

theorem faces_acyclic (v : Fin 4 → X.Opens) (B : X.Opens)
    (hB : ∀ S : Finset (Fin 4), S.Nonempty → IsAffineOpen (B ⊓ S.inf v)) :
    ∀ Z ∈ (curveCover f q).faces (CycleQ2RectangularTrace.baseOpen f q B),
      ∀ W ∈ (targetCover f q v).faces Z, ∀ n,
        CycleQ2AcyclicComplexSections.AcyclicFor (freeOpen W) ((DR f q r).X n) := by
  intro Z hZ W hW n
  obtain ⟨A, hA, rfl⟩ := curve_face f q B Z hZ
  obtain ⟨S, hS, rfl⟩ := target_face f q v A B W hW
  exact CycleQ2AffineExteriorComparison.term_acyclic P (1 + r)
    (isAffineOpen_product p q hA (hB S hS)) n

/-- The full finite curve/target complex, with its actual restrictions
on an arbitrary ambient open of the original product. -/
def complex (v : Fin 4 → X.Opens) : System (show TopCat from Y) :=
  doubleSystem (sections (DR f q r)) (curveCover f q) (targetCover f q v)

/-- The actual original two-curve/four-target Čech complex computes
ordinary de Rham cohomology on the full product above B. All local
inputs are the ordinary affine exterior forms on the original faces. -/
def classes (v : Fin 4 → X.Opens) (hv : (⨆ i, v i) = ⊤) (B : X.Opens)
    (hB : ∀ S : Finset (Fin 4), S.Nonempty → IsAffineOpen (B ⊓ S.inf v)) (n : ℤ) :
    ((complex f q r v).obj (CycleQ2RectangularTrace.baseOpen f q B)).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj
        (freeOpen (CycleQ2RectangularTrace.baseOpen f q B)) ⟶
          (DerivedCategory.Q.obj (DR f q r))⟦n⟧) :=
  doubleClasses (DR f q r) (curveCover f q) (targetCover f q v)
    (curveCover_top f q) (targetCover_top f q v hv) 0
    (CycleQ2RectangularTrace.baseOpen f q B) n (faces_acyclic f q r v B hB)

theorem classes_natural (v : Fin 4 → X.Opens) (hv : (⨆ i, v i) = ⊤)
    {B B' : X.Opens} (h : B' ≤ B)
    (hB : ∀ S : Finset (Fin 4), S.Nonempty → IsAffineOpen (B ⊓ S.inf v))
    (hB' : ∀ S : Finset (Fin 4), S.Nonempty → IsAffineOpen (B' ⊓ S.inf v))
    (n : ℤ) (x : ((complex f q r v).obj (CycleQ2RectangularTrace.baseOpen f q B)).homology n) :
    classes f q r v hv B' hB' n
        (homologyMap ((complex f q r v).res (show CycleQ2RectangularTrace.baseOpen f q B' ≤
          CycleQ2RectangularTrace.baseOpen f q B from fun _ hx => h hx)) n x) =
      (DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).map
        (freeOpenMap (show CycleQ2RectangularTrace.baseOpen f q B' ≤
          CycleQ2RectangularTrace.baseOpen f q B from fun _ hx => h hx)) ≫
        classes f q r v hv B hB n x :=
  doubleClasses_natural (DR f q r) (curveCover f q) (targetCover f q v)
    (curveCover_top f q) (targetCover_top f q v hv) 0 _ n
    (faces_acyclic f q r v B' hB') (faces_acyclic f q r v B hB) x

/-- In particular the full original proper product is computed without
removing a target divisor or choosing a global cotangent frame. -/
def globalClasses (v : Fin 4 → X.Opens) (hv : (⨆ i, v i) = ⊤)
    (hface : ∀ S : Finset (Fin 4), S.Nonempty → IsAffineOpen (S.inf v)) (n : ℤ) :
    ((complex f q r v).obj ⊤).homology n ≃+
      ((DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0).obj (freeOpen ⊤) ⟶
        (DerivedCategory.Q.obj (DR f q r))⟦n⟧) :=
  classes f q r v hv ⊤ (fun S hS => by simpa only [top_inf_eq] using hface S hS) n

end CycleQ2FourTargetRectangleCohomology

#print axioms CycleQ2FourTargetRectangleCohomology.classes
#print axioms CycleQ2FourTargetRectangleCohomology.classes_natural
#print axioms CycleQ2FourTargetRectangleCohomology.globalClasses
