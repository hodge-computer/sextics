import Proposal.GeometricMonicGenericSupport
import Proposal.GeometricLogarithmicGraphRestriction
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Tactic.Ring
import Proposal.GeometricNormalCoordinateFrames

/-! Shears and local changes of generators preserve the supported logarithmic class on a common affine neighborhood.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section

namespace CycleQ2RelativeNativeShearCorrection

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2IntrinsicFramedAffineSite (FramedOpen frame frame_apply functions)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2SmoothRelativeFrames (sectionCoefficients)
open CycleQ2RelativeAffineOverlap (restrict)
open CycleQ2IntrinsicLogSupportClass (OrdinaryTwo ordinaryDerivative ordinaryRestrict logForm)
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val)
open CycleQ2IntrinsicPrincipalScale (log_restrict)
open CycleQ2PrincipalLogRestriction (unit_restrict)

private theorem unit_algRestrict {k : Type} [Field k] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) {Z O W : X.Opens} (t : Γ(X,Z))
    (h : O ≤ X.basicOpen t) (j : W ≤ O) :
    letI : Algebra k Γ(X,O) := (sectionCoefficients p O).toAlgebra
    letI : Algebra k Γ(X,W) := (sectionCoefficients p W).toAlgebra
    Units.map (restrict p j).toRingHom (restrictionUnit t h) = restrictionUnit t (j.trans h) :=
  unit_restrict t h j

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension r p] {W : X.Opens} (f g a : Γ(X,W))

abbrev changed := g + a*f
abbrev left := X.basicOpen f
abbrev right := X.basicOpen g
abbrev newRight := X.basicOpen (changed f g a)
abbrev commonRight := right g ⊓ newRight f g a
abbrev commonOverlap := left f ⊓ commonRight f g a
abbrev oldOverlap := left f ⊓ right g
abbrev newOverlap := left f ⊓ newRight f g a

abbrev allowed (U : X.Opens) := IsAffineOpen U ∧ HasFrame p r U

variable (hOld : allowed p r (oldOverlap f g)) (hNew : allowed p r (newOverlap f g a))
  (hRight : allowed p r (commonRight f g a)) (hOverlap : allowed p r (commonOverlap f g a))

abbrev oldFrame : FramedOpen p r := ⟨oldOverlap f g,hOld⟩
abbrev newFrame : FramedOpen p r := ⟨newOverlap f g a,hNew⟩
abbrev rightFrame : FramedOpen p r := ⟨commonRight f g a,hRight⟩
abbrev overlapFrame : FramedOpen p r := ⟨commonOverlap f g a,hOverlap⟩

abbrev left_old : commonOverlap f g a ≤ oldOverlap f g := inf_le_inf le_rfl inf_le_left
abbrev left_new : commonOverlap f g a ≤ newOverlap f g a := inf_le_inf le_rfl inf_le_right

def oldLog : OrdinaryTwo p r (oldFrame p r f g hOld) :=
  logForm p r (oldFrame p r f g hOld) (restrictionUnit f inf_le_left) (restrictionUnit g inf_le_right)

def newLog : OrdinaryTwo p r (newFrame p r f g a hNew) :=
  logForm p r (newFrame p r f g a hNew) (restrictionUnit f inf_le_left)
    (restrictionUnit (changed f g a) inf_le_right)

theorem exists_correction :
    ∃ η : OrdinaryTwo p r (rightFrame p r f g a hRight),
      ordinaryDerivative p r (rightFrame p r f g a hRight) η = 0 ∧
      ordinaryRestrict p r (rightFrame p r f g a hRight) (B' := overlapFrame p r f g a hOverlap)
        (homOfLE (show commonOverlap f g a ≤ commonRight f g a from inf_le_right)) η =
        ordinaryRestrict p r (newFrame p r f g a hNew) (B' := overlapFrame p r f g a hOverlap)
          (homOfLE (left_new f g a)) (newLog p r f g a hNew) -
        ordinaryRestrict p r (oldFrame p r f g hOld) (B' := overlapFrame p r f g a hOverlap)
          (homOfLE (left_old f g a)) (oldLog p r f g hOld) := by
  let C := commonRight f g a
  let E := commonOverlap f g a
  letI : Algebra k Γ(X,C) := (sectionCoefficients p C).toAlgebra
  letI : Algebra k Γ(X,E) := (sectionCoefficients p E).toAlgebra
  let φ := restrict p (show E ≤ C from inf_le_right)
  let ρ := X.presheaf.map (homOfLE (show C ≤ W from inf_le_left.trans (X.basicOpen_le g))).op
  let fC := ρ f
  let aC := ρ a
  let gC : Γ(X,C)ˣ := restrictionUnit g inf_le_left
  let hC : Γ(X,C)ˣ := restrictionUnit (changed f g a) inf_le_right
  let fE : Γ(X,E)ˣ := restrictionUnit f inf_le_left
  have hf : φ fC = ↑fE := by
    change (X.presheaf.map (homOfLE (show E ≤ C from inf_le_right)).op) (ρ f) =
      (restrictionUnit f (show E ≤ left f from inf_le_left) : Γ(X,E))
    rw [restrictionUnit_val, ← CommRingCat.comp_apply, ← Functor.map_comp]
    exact congrArg (fun i => X.presheaf.map i f) (Subsingleton.elim _ _)
  have he : (hC : Γ(X,C)) = (gC : Γ(X,C)) + aC*fC := by
    change (restrictionUnit (changed f g a) (show C ≤ newRight f g a from inf_le_right) : Γ(X,C)) =
      (restrictionUnit g (show C ≤ right g from inf_le_left) : Γ(X,C)) + ρ a * ρ f
    rw [restrictionUnit_val,restrictionUnit_val]
    change ρ.hom (g+a*f) = ρ.hom g + ρ.hom a * ρ.hom f
    rw [map_add,map_mul]
  let B := rightFrame p r f g a hRight
  obtain ⟨η,hη,hφ⟩ := CycleQ2IntrinsicClosedGeneratorWitness.exists_closed_correction φ
    (frame p r B) (functions p r B) (frame_apply p r B) fC aC gC hC fE hf he
  refine ⟨η,hη,?_⟩
  rw [newLog,oldLog,log_restrict,log_restrict,
    unit_algRestrict,unit_algRestrict,unit_algRestrict,unit_algRestrict]
  change _ = CycleQ2DoubleLogarithmicClass.twoLog (K := k) fE
      (restrictionUnit (changed f g a) (show E ≤ newRight f g a from inf_le_right.trans inf_le_right)) -
    CycleQ2DoubleLogarithmicClass.twoLog (K := k) fE
      (restrictionUnit g (show E ≤ right g from inf_le_right.trans inf_le_left))
  have hg := unit_algRestrict p g (show C ≤ right g from inf_le_left) (show E ≤ C from inf_le_right)
  have hh := unit_algRestrict p (changed f g a) (show C ≤ newRight f g a from inf_le_right)
    (show E ≤ C from inf_le_right)
  rw [← hg,← hh]
  exact hφ

end CycleQ2RelativeNativeShearCorrection

namespace CycleQ2LocalPrincipalShearInvariant

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2RelativeNativeShearCorrection
open CycleQ2IntrinsicLogSupportClass (shiftedSection shiftedSection_restrict shiftedSection_closed shiftedSection_add logForm_closed)
open CycleQ2PrincipalLogSupportClass (square restrictionUnit shear_refined_cover shear_refined_cover_new)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComparison (pullback_class eq_of_second_restriction)
open CycleQ2LocalPrincipalGysin (localClass union_le)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)

variable {k : Type} [Field k] [CharZero k] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of k)) (r : ℕ)
  [SmoothOfRelativeDimension r p] {W : X.Opens} (f g a : Γ(X,W))
  (hOld : allowed p r (oldOverlap f g)) (hNew : allowed p r (newOverlap f g a))
  (hRight : allowed p r (commonRight f g a)) (hOverlap : allowed p r (commonOverlap f g a))

private abbrev A := AbSheaf (show TopCat from X)
private abbrev K : CochainComplex (A (X := X)) ℤ := relativeDeRhamInt p r
local instance : HasDerivedCategory.{1} (A (X := X)) := HasDerivedCategory.standard _

private abbrev E := DerivedCategory.singleFunctor (A (X := X)) 0
private abbrev S := Opens.mayerVietorisSquare (left f) (commonRight f g a)

private abbrev newSection := shiftedSection p r (newFrame p r f g a hNew) (newLog p r f g a hNew)
private abbrev oldSection := shiftedSection p r (oldFrame p r f g hOld) (oldLog p r f g hOld)

private theorem newClosed :
    (((K p r)⟦(2:ℤ)⟧).d 0 1).hom.app (op (newOverlap f g a)) (newSection p r f g a hNew) = 0 :=
  shiftedSection_closed p r (newFrame p r f g a hNew) _ (logForm_closed p r (newFrame p r f g a hNew) _ _)

private theorem oldClosed :
    (((K p r)⟦(2:ℤ)⟧).d 0 1).hom.app (op (oldOverlap f g)) (oldSection p r f g hOld) = 0 :=
  shiftedSection_closed p r (oldFrame p r f g hOld) _ (logForm_closed p r (oldFrame p r f g hOld) _ _)

private abbrev P := (((K p r)⟦(2:ℤ)⟧).X 0).obj

private abbrev common_le : (S f g a).X₄ ≤ W :=
  sup_le (X.basicOpen_le f) (inf_le_left.trans (X.basicOpen_le g))

include hRight hOverlap in
/-- Equality of the two genuine derived classes on the common cover.
The common cover has the same union as each original cover by
`shear_refined_cover` and `shear_refined_cover_new`. -/
theorem shear_invariant :
    (E (X := X)).map (supportMap (common_le f g a) (union_le f (changed f g a))
        (sup_le_sup le_rfl inf_le_right) le_rfl).τ₃ ≫
      localClass p r f (changed f g a) hNew =
    (E (X := X)).map (supportMap (common_le f g a) (union_le f g)
        (sup_le_sup le_rfl inf_le_left) le_rfl).τ₃ ≫
      localClass p r f g hOld := by
  let U := left f
  let V := right g
  let V' := newRight f g a
  let R := commonRight f g a
  let hU : U ≤ U := le_rfl
  let hV : R ≤ V := inf_le_left
  let hV' : R ≤ V' := inf_le_right
  let n := newSection p r f g a hNew
  let m := oldSection p r f g hOld
  have hn := newClosed p r f g a hNew
  have hm := oldClosed p r f g hOld
  have eNew := pullback_class (K := K p r) 2 hU hV' (common_le f g a)
    (union_le f (changed f g a)) le_rfl n hn
  have eOld := pullback_class (K := K p r) 2 hU hV (common_le f g a)
    (union_le f g) le_rfl m hm
  refine eNew.trans (Eq.trans ?_ eOld.symm)
  obtain ⟨η,hη,hcorr⟩ := exists_correction p r f g a hOld hNew hRight hOverlap
  let w := shiftedSection p r (rightFrame p r f g a hRight) η
  have hw := shiftedSection_closed p r (rightFrame p r f g a hRight) η hη
  apply eq_of_second_restriction (K := K p r) 2 (S f g a) (common_le f g a)
    _ _ _ _ w hw
  change (P p r).map (homOfLE (left_new f g a)).op n =
    (P p r).map (homOfLE (left_old f g a)).op m +
      (P p r).map (homOfLE (show commonOverlap f g a ≤ R from inf_le_right)).op w
  dsimp only [n,m,w,P,newSection,oldSection]
  rw [shiftedSection_restrict p r (newFrame p r f g a hNew)
        (B' := overlapFrame p r f g a hOverlap) (homOfLE (left_new f g a)),
      shiftedSection_restrict p r (oldFrame p r f g hOld)
        (B' := overlapFrame p r f g a hOverlap) (homOfLE (left_old f g a)),
      shiftedSection_restrict p r (rightFrame p r f g a hRight)
        (B' := overlapFrame p r f g a hOverlap)
          (homOfLE (show commonOverlap f g a ≤ commonRight f g a from inf_le_right)),
      ← shiftedSection_add]
  apply congrArg (shiftedSection p r (overlapFrame p r f g a hOverlap))
  rw [hcorr]
  abel

end CycleQ2LocalPrincipalShearInvariant

namespace CycleQ2ClosedGraphShear

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf union_eq_complement)
open CycleQ2LocalPrincipalGysin (cover locus union_le localClass)
open CycleQ2PrincipalLogSupportClass (support_eq_zeroLocus shear_refined_cover shear_refined_cover_new)
open CycleQ2RelativeNativeShearCorrection (allowed oldOverlap newOverlap commonRight commonOverlap)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComposition (supportMap_comp)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  {W : X.Opens} (f g a : Γ(X,W))
  (he : locus f g = (W : Set X) ∩ Set.range i)

include he in

theorem shear_locus : locus f (g + a*f) = (W : Set X) ∩ Set.range i := by
  have h := (shear_refined_cover_new f g a).symm.trans (shear_refined_cover f g a)
  unfold locus at *
  rw [← support_eq_zeroLocus f (g+a*f), h, support_eq_zeroLocus]
  exact he

variable {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p]

theorem classOf_shear
    (hOld : allowed p r (oldOverlap f g))
    (hNew : allowed p r (newOverlap f g a))
    (hRight : allowed p r (commonRight f g a))
    (hOverlap : allowed p r (commonOverlap f g a)) :
    classOf i f (g + a*f) p r (shear_locus i f g a he) hNew = classOf i f g p r he hOld := by
  letI : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
  let T := X.basicOpen f ⊔ commonRight f g a
  let hT : T ≤ W := sup_le (X.basicOpen_le f) (inf_le_left.trans (X.basicOpen_le g))
  let hZ : W ⊓ complement i ≤ W := inf_le_left
  have ht : W ⊓ complement i ≤ T :=
    ((shear_refined_cover f g a).trans (union_eq_complement i f g he)).ge
  let m := (supportMap hZ hT ht (show W ≤ W from le_rfl)).τ₃
  let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
  let v := CycleQ2RelativeNativeShearCorrection.changed f g a
  let hO := union_le f g
  let hN := union_le f v
  let toOld : T ≤ (cover f g).X₄ := sup_le_sup le_rfl inf_le_left
  let toNew : T ≤ (cover f v).X₄ := sup_le_sup le_rfl inf_le_right
  let mO := (supportMap hT hO toOld (show W ≤ W from le_rfl)).τ₃
  let mN := (supportMap hT hN toNew (show W ≤ W from le_rfl)).τ₃
  let lO := localClass p r f g hOld
  let lN := localClass p r f v hNew
  have hn : E.map mN ≫ lN = E.map mO ≫ lO :=
    CycleQ2LocalPrincipalShearInvariant.shear_invariant p r f g a hOld hNew hRight hOverlap
  have hcO : E.map m ≫ E.map mO =
      E.map (supportMap hZ hO (ht.trans toOld) (show W ≤ W from le_rfl)).τ₃ :=
    (E.map_comp m mO).symm.trans (congrArg E.map (supportMap_comp hZ hT hO ht toOld le_rfl le_rfl))
  have hcN : E.map m ≫ E.map mN =
      E.map (supportMap hZ hN (ht.trans toNew) (show W ≤ W from le_rfl)).τ₃ :=
    (E.map_comp m mN).symm.trans (congrArg E.map (supportMap_comp hZ hT hN ht toNew le_rfl le_rfl))
  have hLeft := (Category.assoc (E.map m) (E.map mN) lN).symm.trans (congrArg (fun u ↦ u ≫ lN) hcN)
  have hRight' := (Category.assoc (E.map m) (E.map mO) lO).symm.trans (congrArg (fun u ↦ u ≫ lO) hcO)
  exact hLeft.symm.trans ((congrArg (fun u ↦ E.map m ≫ u) hn).trans hRight')

end CycleQ2ClosedGraphShear

section
namespace CycleQ2LocalPairChange

variable {R M : Type*} [CommRing R] (v : R → R → M)
  (scale : ∀ (x y : R) (u : Rˣ), v ((u : R)*x) y = v x y)
  (shear : ∀ (x y t : R), v x (y + t*x) = v x y)
  (swap : ∀ x y, v y x = v x y)

include scale shear swap in
private theorem unit_pivot (x y b c d : R) (a : Rˣ) (hdet : IsUnit ((a : R)*d - b*c)) :
    v ((a : R)*x + b*y) (c*x + d*y) = v x y := by
  let u := (↑(a⁻¹) : R)
  let t := d - c*u*b
  let z := (a : R)*x + b*y
  have ha : (a : R)*u = 1 := by simp [u]
  have hdet' : (a : R)*t = (a : R)*d - b*c := by
    calc
      _ = (a : R)*d - c*b*((a : R)*u) := by dsimp only [t]; ring
      _ = _ := by rw [ha]; ring
  have ht : IsUnit t := isUnit_of_mul_isUnit_right (hdet' ▸ hdet)
  obtain ⟨w,hw⟩ := ht
  have hsecond : c*x + d*y = (w : R)*y + (c*u)*z := by
    rw [hw]
    calc
      _ = (c*x)*((a : R)*u) + d*y := by rw [ha,mul_one]
      _ = _ := by dsimp only [t,z]; ring
  have hscale' (f g : R) (a' : Rˣ) : v f ((a' : R)*g) = v f g :=
    (swap _ _).symm.trans ((scale _ _ _).trans (swap _ _))
  have hshear' (f g q : R) : v (f + q*g) g = v f g :=
    (swap _ _).symm.trans ((shear _ _ _).trans (swap _ _))
  change v z (c*x+d*y) = v x y
  rw [hsecond,shear,hscale' z y w]
  exact (hshear' ((a : R)*x) y b).trans (scale x y a)

include scale shear swap in
/-- With a unit pivot, the comparison holds over the original ring. -/
theorem invariant_of_pivot (x y a b c d : R) (hdet : IsUnit (a*d - b*c))
    (hp : IsUnit a ∨ IsUnit c) : v (a*x + b*y) (c*x + d*y) = v x y := by
  rcases hp with ha | hc
  · obtain ⟨u,hu⟩ := ha
    rw [← hu] at hdet ⊢
    exact unit_pivot v scale shear swap x y b c d u hdet
  · obtain ⟨u,hu⟩ := hc
    have hd : c*b - d*a = -(a*d - b*c) := by ring
    have hu' : IsUnit ((u : R)*b - d*a) := hu.symm ▸ (hd.symm ▸ hdet.neg)
    refine (swap _ _).symm.trans ?_
    rw [← hu]
    exact unit_pivot v scale shear swap x y d a b u hu'

end CycleQ2LocalPairChange
end

namespace CycleQ2ClosedGraphUnitPivot

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (support classOf)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2LocalPrincipalGysin (cover locus)
open CycleQ2ClosedGraphGeneratorChanges (classOf_swap classOf_scale swap_locus scale_locus)
open CycleQ2ClosedGraphShear (classOf_shear)
open CycleQ2IntrinsicDeRhamSheaves (relativeDeRhamInt)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p] (W : X.affineOpens) (hW : HasFrame p r W.1)

include hW in
private theorem principalFrame (f : Γ(X,W.1)) : IsAffineOpen (X.basicOpen f) ∧ HasFrame p r (X.basicOpen f) :=
  ⟨W.2.basicOpen f,hasFrame_of_affine_le p r (X.basicOpen_le f) W.2 (W.2.basicOpen f) hW⟩

include hW in
private theorem pairFrame (f g : Γ(X,W.1)) : IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁ := by
  change IsAffineOpen (X.basicOpen f ⊓ X.basicOpen g) ∧ HasFrame p r (X.basicOpen f ⊓ X.basicOpen g)
  rw [← X.basicOpen_mul]
  exact principalFrame p r W hW (f*g)

include hW in
private theorem threeFrame (f g h : Γ(X,W.1)) :
    IsAffineOpen (X.basicOpen f ⊓ (X.basicOpen g ⊓ X.basicOpen h)) ∧
    HasFrame p r (X.basicOpen f ⊓ (X.basicOpen g ⊓ X.basicOpen h)) := by
  rw [← X.basicOpen_mul,← X.basicOpen_mul]
  exact principalFrame p r W hW (f*(g*h))

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _

private abbrev represents (f g : Γ(X,W.1)) := locus f g = (W.1 : Set X) ∩ Set.range i

private def value (f g : Γ(X,W.1)) :
    (DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj (support i W.1) ⟶
      (DerivedCategory.Q.obj (relativeDeRhamInt p r))⟦(4:ℤ)⟧ := by
  classical
  exact if h : represents i W f g then classOf i f g p r h (pairFrame p r W hW f g) else 0

private theorem value_swap (f g : Γ(X,W.1)) :
    value i p r W hW g f = value i p r W hW f g := by
  by_cases h : represents i W f g
  · have h' : represents i W g f := (swap_locus f g).trans h
    simp only [value,dif_pos h,dif_pos h']
    exact (classOf_swap i p r f g h (pairFrame p r W hW f g) (pairFrame p r W hW g f)).symm
  · have h' : ¬ represents i W g f := fun hs ↦ h ((swap_locus f g).symm.trans hs)
    simp only [value,dif_neg h,dif_neg h']

private theorem value_scale (f g : Γ(X,W.1)) (u : Γ(X,W.1)ˣ) :
    value i p r W hW ((u : Γ(X,W.1))*f) g = value i p r W hW f g := by
  by_cases h : represents i W f g
  · have h' : represents i W ((u : Γ(X,W.1))*f) g := (scale_locus f g u).trans h
    simp only [value,dif_pos h,dif_pos h']
    exact (classOf_scale i p r f g u h (pairFrame p r W hW f g) (pairFrame p r W hW _ g)
      (principalFrame p r W hW g)).symm
  · have h' : ¬ represents i W ((u : Γ(X,W.1))*f) g := fun hs ↦ h ((scale_locus f g u).symm.trans hs)
    simp only [value,dif_neg h,dif_neg h']

private theorem value_shear (f g t : Γ(X,W.1)) :
    value i p r W hW f (g+t*f) = value i p r W hW f g := by
  have hl : locus f (g+t*f) = locus f g := by
    apply CycleQ2ClosedGraphGeneratorChanges.locus_eq_of_union_eq
    exact (CycleQ2PrincipalLogSupportClass.shear_refined_cover_new f g t).symm.trans
      (CycleQ2PrincipalLogSupportClass.shear_refined_cover f g t)
  by_cases h : represents i W f g
  · have h' : represents i W f (g+t*f) := hl.trans h
    simp only [value,dif_pos h,dif_pos h']
    exact classOf_shear i f g t h p r (pairFrame p r W hW f g) (pairFrame p r W hW f _)
      (pairFrame p r W hW g (g+t*f)) (threeFrame p r W hW f g (g+t*f))
  · have h' : ¬ represents i W f (g+t*f) := fun hs ↦ h (hl.symm.trans hs)
    simp only [value,dif_neg h,dif_neg h']

theorem classOf_change (f g a b c d : Γ(X,W.1)) (hd : IsUnit (a*d-b*c))
    (hp : IsUnit a ∨ IsUnit c) (he : represents i W f g)
    (he' : represents i W (a*f+b*g) (c*f+d*g)) :
    classOf i (a*f+b*g) (c*f+d*g) p r he' (pairFrame p r W hW _ _) =
      classOf i f g p r he (pairFrame p r W hW f g) := by
  have h := CycleQ2LocalPairChange.invariant_of_pivot (value i p r W hW)
    (value_scale i p r W hW) (value_shear i p r W hW) (value_swap i p r W hW) f g a b c d hd hp
  simpa only [value,dif_pos he,dif_pos he'] using h

end CycleQ2ClosedGraphUnitPivot

namespace CycleQ2LocalPairPivotChart

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2PrincipalLogSupportClass (restrictionUnit restrictionUnit_val)

variable {X : Scheme.{0}} (U : X.affineOpens) (x : X)
  (a b c d : Γ(X,U.1))

abbrev determinant := a*d - b*c

private theorem isUnit_res {V : X.Opens} {s : Γ(X,U.1)} (h : V ≤ X.basicOpen s) :
    IsUnit ((X.presheaf.map (homOfLE (h.trans (X.basicOpen_le s))).op) s) := by
  rw [← restrictionUnit_val s h]
  exact (restrictionUnit s h).isUnit

theorem exists_pivot_chart (hdet : x ∈ X.basicOpen (determinant U a b c d)) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ U.1), x ∈ V.1 ∧
      let ρ := (X.presheaf.map (homOfLE h).op).hom
      IsUnit (ρ (determinant U a b c d)) ∧ (IsUnit (ρ a) ∨ IsUnit (ρ c)) := by
  have hx : x ∈ U.1 := X.basicOpen_le _ hdet
  let germ := (X.presheaf.germ U.1 x hx).hom
  let δ := determinant U a b c d
  have hδ : IsUnit (germ a * germ d - germ b * germ c) := by
    have h := (X.mem_basicOpen δ x hx).mp hdet
    change IsUnit (germ (a*d - b*c)) at h
    simpa only [map_sub,map_mul] using h
  have hp := IsLocalRing.isUnit_or_isUnit_of_isUnit_add
    (sub_eq_add_neg (germ a * germ d) (germ b * germ c) ▸ hδ)
  have hcol : x ∈ X.basicOpen a ∨ x ∈ X.basicOpen c := by
    rcases hp with h | h
    · exact Or.inl ((X.mem_basicOpen a x hx).mpr (isUnit_of_mul_isUnit_left h))
    · exact Or.inr ((X.mem_basicOpen c x hx).mpr
        (isUnit_of_mul_isUnit_right (show IsUnit (germ b * germ c) by simpa only [neg_neg] using h.neg)))
  have hchart (s : Γ(X,U.1)) (hs : x ∈ X.basicOpen s) :
      ∃ (V : X.affineOpens) (h : V.1 ≤ U.1), x ∈ V.1 ∧
        let ρ := (X.presheaf.map (homOfLE h).op).hom
        IsUnit (ρ δ) ∧ IsUnit (ρ s) := by
    let V := X.affineBasicOpen (s*δ)
    have hl : V.1 ≤ X.basicOpen s := (X.basicOpen_mul s δ).le.trans inf_le_left
    have hr : V.1 ≤ X.basicOpen δ := (X.basicOpen_mul s δ).le.trans inf_le_right
    have hxV : x ∈ V.1 := (X.basicOpen_mul s δ).ge ⟨hs,hdet⟩
    exact ⟨V,X.basicOpen_le _,hxV,isUnit_res U hr,isUnit_res U hl⟩
  rcases hcol with ha | hc
  · obtain ⟨V,h,hxV,hd',ha'⟩ := hchart a ha
    exact ⟨V,h,hxV,hd',Or.inl ha'⟩
  · obtain ⟨V,h,hxV,hd',hc'⟩ := hchart c hc
    exact ⟨V,h,hxV,hd',Or.inr hc'⟩

end CycleQ2LocalPairPivotChart

namespace CycleQ2ClosedGraphPivotRestriction

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2LocalPrincipalGysin (cover locus)
open CycleQ2LocalPrincipalRestriction (res)
open CycleQ2ClosedGraphRestriction (locus_restrict classOf_restrict)
open CycleQ2RelativeSupportRefinement (supportMap)

variable {Z X : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  {k : Type} [Field k] [CharZero k] (p : X ⟶ Spec (CommRingCat.of k))
  (r : ℕ) [SmoothOfRelativeDimension r p] (W : X.affineOpens) (hW : HasFrame p r W.1)

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from X)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev cle (i : Z ⟶ X) [IsClosedImmersion i] (U : X.Opens) : U ⊓ complement i ≤ U := inf_le_left

private theorem frame_of_pair (U : X.affineOpens) (h : HasFrame p r U.1) (f g : Γ(X,U.1)) :
    IsAffineOpen (cover f g).X₁ ∧ HasFrame p r (cover f g).X₁ := by
  change IsAffineOpen (X.basicOpen f ⊓ X.basicOpen g) ∧ HasFrame p r (X.basicOpen f ⊓ X.basicOpen g)
  rw [← X.basicOpen_mul]
  have ha := U.2.basicOpen (f*g)
  exact ⟨ha,hasFrame_of_affine_le p r (X.basicOpen_le _) U.2 ha h⟩

include hW in
theorem exists_comparison (x : X) (f g a b c d : Γ(X,W.1)) (hd : x ∈ X.basicOpen (a*d-b*c))
    (ho : locus f g = (W.1 : Set X) ∩ Set.range i)
    (hn : locus (a*f+b*g) (c*f+d*g) = (W.1 : Set X) ∩ Set.range i) :
    ∃ (V : X.affineOpens) (h : V.1 ≤ W.1), x ∈ V.1 ∧
      let m := E.map (supportMap (cle i V.1) (cle i W.1) (inf_le_inf h le_rfl) h).τ₃
      m ≫ classOf i f g p r ho (frame_of_pair p r W hW f g) =
        m ≫ classOf i (a*f+b*g) (c*f+d*g) p r hn (frame_of_pair p r W hW _ _) := by
  obtain ⟨V,h,hx,hu,hp⟩ := CycleQ2LocalPairPivotChart.exists_pivot_chart W x a b c d hd
  let ρ := (X.presheaf.map (homOfLE h).op).hom
  let f' := a*f+b*g
  let g' := c*f+d*g
  let q := ρ a * ρ f + ρ b * ρ g
  let t := ρ c * ρ f + ρ d * ρ g
  have hr : ρ f' = q := by simp only [f',q,map_add,map_mul]
  have hs : ρ g' = t := by simp only [g',t,map_add,map_mul]
  have hV := hasFrame_of_affine_le p r h W.2 V.2 hW
  have ho' : locus (ρ f) (ρ g) = (V.1 : Set X) ∩ Set.range i := locus_restrict i h f g ho
  have hn' : locus (ρ f') (ρ g') = (V.1 : Set X) ∩ Set.range i := locus_restrict i h f' g' hn
  have hqt : locus q t = (V.1 : Set X) ∩ Set.range i := by
    rw [← hr,← hs]
    exact hn'
  have hd' : IsUnit (ρ a * ρ d - ρ b * ρ c) := by
    change IsUnit (ρ (a*d-b*c)) at hu
    simpa only [map_sub,map_mul] using hu
  have hchange : classOf i q t p r hqt (frame_of_pair p r V hV q t) =
      classOf i (ρ f) (ρ g) p r ho' (frame_of_pair p r V hV _ _) :=
    CycleQ2ClosedGraphUnitPivot.classOf_change i p r V hV (ρ f) (ρ g) (ρ a) (ρ b) (ρ c) (ρ d) hd' hp ho' hqt
  have hcongr (u v s' t' : Γ(X,V.1)) (hu' : u = s') (hv' : v = t')
      (e : locus u v = (V.1 : Set X) ∩ Set.range i) (e' : locus s' t' = (V.1 : Set X) ∩ Set.range i) :
      classOf i u v p r e (frame_of_pair p r V hV u v) =
      classOf i s' t' p r e' (frame_of_pair p r V hV s' t') := by
    subst s'; subst t'; rfl
  refine ⟨V,h,hx,?_⟩
  have left := classOf_restrict i h f g ho p r (frame_of_pair p r W hW f g) (frame_of_pair p r V hV _ _)
  have right := classOf_restrict i h f' g' hn p r (frame_of_pair p r W hW f' g') (frame_of_pair p r V hV _ _)
  exact left.trans (hchange.symm.trans ((hcongr q t (ρ f') (ρ g') hr.symm hs.symm hqt hn').trans right.symm))

end CycleQ2ClosedGraphPivotRestriction

namespace CycleQ2SmoothAffineGraphOverlap

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf)
open CycleQ2LocalPrincipalGysin (cover locus)
open CycleQ2FiniteExactAffineAtlas (HasFrame)
open CycleQ2RelativeSupportRefinement (supportMap)

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev cle (i : X ⟶ Y) [IsClosedImmersion i] (U : Y.Opens) : U ⊓ complement i ≤ U := inf_le_left

private theorem locus_of_span (U : Y.affineOpens) (f g : Γ(Y,U.1))
    (he : Ideal.span {f,g} = i.ker.ideal U) : locus f g = (U.1 : Set Y) ∩ Set.range i := by
  unfold locus
  rw [← Y.zeroLocus_span,he,Set.inter_comm (U.1 : Set Y),← i.ker.coe_support_inter U,
    i.support_ker,i.isClosedEmbedding.isClosed_range.closure_eq,Set.inter_comm]

include hi in
theorem exists_agreement (U : Y.affineOpens) (hU : HasFrame q 4 U.1) (x : X) (hx : i x ∈ U.1)
    (f g f' g' : Γ(Y,U.1)) (hf : Ideal.span {f,g} = i.ker.ideal U) (hg : Ideal.span {f',g'} = i.ker.ideal U)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame q 4 (cover f g).X₁)
    (hn : IsAffineOpen (cover f' g').X₁ ∧ HasFrame q 4 (cover f' g').X₁) :
    ∃ (V : Y.affineOpens) (h : V.1 ≤ U.1), i x ∈ V.1 ∧
      let m := E.map (supportMap (cle i V.1) (cle i U.1) (inf_le_inf h le_rfl) h).τ₃
      m ≫ classOf i f g q 4 (locus_of_span i U f g hf) ho =
        m ≫ classOf i f' g' q 4 (locus_of_span i U f' g' hg) hn := by
  obtain ⟨a,b,c,d,he,he',hd⟩ := CycleQ2SmoothAffineGeneratorChange.exists_matrix p q i hi U x hx f g f' g' hf hg
  subst f'
  subst g'
  exact CycleQ2ClosedGraphPivotRestriction.exists_comparison i q 4 U hU (i x) f g a b c d hd
    (locus_of_span i U f g hf) (locus_of_span i U _ _ hg)

end CycleQ2SmoothAffineGraphOverlap

namespace CycleQ2SmoothTwoChartAgreement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2InjectiveCech (AbSheaf)
open CycleQ2ClosedGraphSupport (complement classOf)
open CycleQ2LocalPrincipalGysin (cover locus)
open CycleQ2LocalPrincipalRestriction (res)
open CycleQ2FiniteExactAffineAtlas (HasFrame hasFrame_of_affine_le)
open CycleQ2RelativeSupportRefinement (supportMap)
open CycleQ2RelativeSupportComposition (supportMap_comp)

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}}
  (p : X ⟶ Spec (CommRingCat.of k)) (q : Y ⟶ Spec (CommRingCat.of k))
  (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q = p)
  [SmoothOfRelativeDimension 2 p] [SmoothOfRelativeDimension 4 q]

local instance : HasDerivedCategory.{1} (AbSheaf (show TopCat from Y)) := HasDerivedCategory.standard _
private abbrev E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from Y)) 0
private abbrev cle (i : X ⟶ Y) [IsClosedImmersion i] (U : Y.Opens) : U ⊓ complement i ≤ U := inf_le_left

abbrev restriction {V U : Y.Opens} (e : V ≤ U) :=
  E.map (supportMap (cle i V) (cle i U) (inf_le_inf e le_rfl) e).τ₃

private theorem restriction_comp {T V U : Y.Opens} (e : T ≤ V) (h : V ≤ U) :
    restriction i e ≫ restriction i h = restriction i (e.trans h) := by
  unfold restriction
  rw [← Functor.map_comp, supportMap_comp]

theorem locus_of_span (U : Y.affineOpens) (f g : Γ(Y,U.1))
    (h : Ideal.span {f,g} = i.ker.ideal U) : locus f g = (U.1 : Set Y) ∩ Set.range i := by
  unfold locus
  rw [← Y.zeroLocus_span,h,Set.inter_comm (U.1 : Set Y),← i.ker.coe_support_inter U,
    i.support_ker,i.isClosedEmbedding.isClosed_range.closure_eq,Set.inter_comm]

private theorem span_of_restriction {T U : Y.affineOpens} (a : T.1 ≤ U.1) (f g : Γ(Y,U.1))
    (h : Ideal.span {f,g} = i.ker.ideal U) :
    Ideal.span {res a f, res a g} = i.ker.ideal T := by
  rw [← i.ker.map_ideal (U := T) (V := U) a, ← h, Ideal.map_span]
  simp only [Set.image_insert_eq, Set.image_singleton]
  rfl

theorem pairFrame (U : Y.affineOpens) (hU : HasFrame q 4 U.1) (f g : Γ(Y,U.1)) :
    IsAffineOpen (cover f g).X₁ ∧ HasFrame q 4 (cover f g).X₁ := by
  change IsAffineOpen (Y.basicOpen f ⊓ Y.basicOpen g) ∧ HasFrame q 4 (Y.basicOpen f ⊓ Y.basicOpen g)
  rw [← Y.basicOpen_mul]
  have ha := U.2.basicOpen (f*g)
  exact ⟨ha,hasFrame_of_affine_le q 4 (Y.basicOpen_le _) U.2 ha hU⟩

include hi in
theorem exists_agreement (U W : Y.affineOpens) (x : X) (hxU : i x ∈ U.1) (hxW : i x ∈ W.1)
    (f g : Γ(Y,U.1)) (f' g' : Γ(Y,W.1))
    (hf : Ideal.span {f,g} = i.ker.ideal U) (hg : Ideal.span {f',g'} = i.ker.ideal W)
    (ho : IsAffineOpen (cover f g).X₁ ∧ HasFrame q 4 (cover f g).X₁)
    (hn : IsAffineOpen (cover f' g').X₁ ∧ HasFrame q 4 (cover f' g').X₁) :
    ∃ (T : Y.affineOpens) (a : T.1 ≤ U.1) (b : T.1 ≤ W.1), i x ∈ T.1 ∧
      restriction i a ≫ classOf i f g q 4 (locus_of_span i U f g hf) ho =
      restriction i b ≫ classOf i f' g' q 4 (locus_of_span i W f' g' hg) hn := by
  have hx : i x ∈ U.1 ⊓ W.1 := ⟨hxU,hxW⟩
  obtain ⟨V',⟨hV,hfr⟩,hxV,hVW⟩ :=
    (Opens.isBasis_iff_nbhd.mp (CycleQ2FiniteExactAffineAtlas.isBasis q 4)) hx
  let V : Y.affineOpens := ⟨V',hV⟩
  have a : V.1 ≤ U.1 := hVW.trans inf_le_left
  have b : V.1 ≤ W.1 := hVW.trans inf_le_right
  have af := pairFrame q V hfr (res a f) (res a g)
  have bf := pairFrame q V hfr (res b f') (res b g')
  obtain ⟨T,m,hxT,hcomp⟩ := CycleQ2SmoothAffineGraphOverlap.exists_agreement p q i hi V hfr x hxV
    (res a f) (res a g) (res b f') (res b g')
    (span_of_restriction i a f g hf) (span_of_restriction i b f' g' hg) af bf
  have hrU := CycleQ2ClosedGraphRestriction.classOf_restrict i a f g (locus_of_span i U f g hf) q 4 ho af
  have hrW := CycleQ2ClosedGraphRestriction.classOf_restrict i b f' g' (locus_of_span i W f' g' hg) q 4 hn bf
  refine ⟨T,m.trans a,m.trans b,hxT,?_⟩
  rw [← restriction_comp i m a,← restriction_comp i m b, Category.assoc,Category.assoc]
  exact (congrArg (fun d ↦ restriction i m ≫ d) hrU).trans
    (hcomp.trans (congrArg (fun d ↦ restriction i m ≫ d) hrW).symm)

end CycleQ2SmoothTwoChartAgreement
