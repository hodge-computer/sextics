import Proposal.GeometricAffineHTwo
import Proposal.GeometricLiteralNegativeTwistDescent
import Proposal.GeometricThreeOpenH2Surjectivity
import Proposal.GeometricCartierCechConnecting

/-!
# Derived vanishing from explicit finite-cover Čech primitives

Injective presentations reduce the first two derived cohomology groups to
finite-cover Čech boundary equations. In degree two only degree-two
vanishing at the vertices and degree-one vanishing on their pairwise
intersections are needed. This applies to the four-open cover used by
the weighted threefold twists.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistDerived

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
open CycleQ2FiniteCechDescent (Zero)
open CycleQ2CechTwoToDerived (presentation presentation_shortExact sections_surjective_of_H_one_subsingleton
  connecting_one_zero app)
open CycleQ2GeometricSheafCohomologyRestriction (terminalCohomologyEquiv)

variable {X : TopCat.{0}} {ι : Type} [Fintype ι] (F : AbSheaf X) (U : ι → Opens X)
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

/-- First cohomology of a finite cover with explicit primitives for every edge cocycle. -/
theorem hOne_of_primitives (hcover : (⨆ i, U i) = ⊤)
    (hvertex : ∀ i, Subsingleton (F.H' 1 (U i)))
    (hprimitive : ∀ c : One F U, IsOneCocycle F U c → ∃ p : Zero F U,
      ∀ i j W hi hj, res F hj (p j) - res F hi (p i) = edgeValue F U c i j W hi hj) :
    Subsingleton (F.H 1) := by
  haveI : Subsingleton (F.H' 1 ⊤) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨c,hc,rfl⟩ := CycleQ2LiteralNegativeTwistDescent.cechOneClass_surjective_of_local_vanishing
      F U hcover hvertex x
    obtain ⟨p,hp⟩ := hprimitive c hc
    exact CycleQ2FiniteCechHOne.cechOneClass_eq_zero_of_primitive U hcover c hc p hp
  exact (terminalCohomologyEquiv (Opens.grothendieckTopology X) F ⊤ isTerminalTop 1).surjective.subsingleton

/-- Degree-two primitives on this cover imply vanishing in ordinary derived cohomology. -/
theorem hTwo_of_primitives (hcover : (⨆ i, U i) = ⊤)
    (hvertex : ∀ i, Subsingleton (F.H' 2 (U i)))
    (hedge : ∀ i j, Subsingleton (F.H' 1 (U i ⊓ U j)))
    (hprimitive : ∀ c : Two F U, IsTwoCocycle F U c → ∃ b : One F U,
      ∀ i j k W hi hj hk, boundaryValue F U b i j k W hi hj hk =
        faceValue F U c i j k W hi hj hk) : Subsingleton (F.H 2) := by
  let S := presentation F
  let T := presentation S.X₃
  apply CycleQ2GeometricAffineHTwo.hTwo_subsingleton_of_global_lift F
  intro z
  have hlocal (i : ι) : Subsingleton (S.X₃.H' 1 (U i)) := by
    apply subsingleton_of_forall_eq 0
    intro y
    apply connecting_one_zero (presentation_shortExact F) (U i) y
    exact @Subsingleton.elim (F.H' 2 (U i)) (hvertex i) _ _
  choose u hu using fun i => sections_surjective_of_H_one_subsingleton
    (presentation_shortExact S.X₃) (U i) (hlocal i) (res T.X₃ le_top z)
  exact CycleQ2GeometricAffineHTwo.lift_of_two_cocycle_primitives F U hcover
    (fun i j => sections_surjective_of_H_one_subsingleton (presentation_shortExact F) _ (hedge i j))
    hprimitive z u hu

end CycleQ2HodgeTwistDerived
end

#print axioms CycleQ2HodgeTwistDerived.hOne_of_primitives
#print axioms CycleQ2HodgeTwistDerived.hTwo_of_primitives

/-!
## The actual four-open comparison in degree three

Three successive Mayer--Vietoris connecting maps give the comparison from
a section on the fourfold intersection to derived cohomology. Naturality
with respect to inclusions of opens identifies its kernel with the four
alternating triple restrictions. No cohomology base-change map is an input.
-/

noncomputable section
namespace CycleQ2FourOpenH3

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  TopologicalSpace Opposite
open CycleQ2InjectiveCech (AbSheaf Sections)
open CycleQ2GeometricSheafLocalIso (res)
open CycleQ2GeometricConeCech.HZero (sectionsEquiv sectionsEquiv_naturality)
open CycleQ2MayerVietorisRestriction (freeOpenSheaf delta_restriction)
open CycleQ2ThreeOpenCechH2 (TripleOpen delta_pair_zero delta_left_zero
  delta_eq_zero_iff)

variable {X : TopCat.{0}}

/-- Any four compatible inclusions of the corners induce the actual map
of Mayer--Vietoris short complexes. Compatibility is automatic for opens. -/
def squareMap (S T : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h₁ : S.X₁ ≤ T.X₁) (h₂ : S.X₂ ≤ T.X₂)
    (h₃ : S.X₃ ≤ T.X₃) (h₄ : S.X₄ ≤ T.X₄) :
    S.shortComplex ⟶ T.shortComplex where
  τ₁ := (freeOpenSheaf (X := X)).map (homOfLE h₁)
  τ₂ := biprod.map ((freeOpenSheaf (X := X)).map (homOfLE h₂))
    ((freeOpenSheaf (X := X)).map (homOfLE h₃))
  τ₃ := (freeOpenSheaf (X := X)).map (homOfLE h₄)
  comm₁₂ := by
    let K := freeOpenSheaf (X := X)
    change K.map _ ≫ biprod.lift (K.map _) (-(K.map _)) =
      biprod.lift (K.map _) (-(K.map _)) ≫ biprod.map (K.map _) (K.map _)
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst, biprod.map_fst,
        biprod.lift_fst_assoc, ← Functor.map_comp]
      congr 1
    · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
        biprod.lift_snd_assoc, Preadditive.comp_neg,
        Preadditive.neg_comp, ← Functor.map_comp]
      congr 2
  comm₂₃ := by
    let K := freeOpenSheaf (X := X)
    change biprod.map (K.map _) (K.map _) ≫ biprod.desc (K.map _) (K.map _) =
      biprod.desc (K.map _) (K.map _) ≫ K.map _
    apply biprod.hom_ext'
    · simp only [Category.assoc, biprod.inl_map_assoc, biprod.inl_desc,
        biprod.inl_desc_assoc, ← Functor.map_comp]
      congr 1
    · simp only [Category.assoc, biprod.inr_map_assoc, biprod.inr_desc,
        biprod.inr_desc_assoc, ← Functor.map_comp]
      congr 1

variable [HasExt.{1} (AbSheaf X)] (F : AbSheaf X)

/-- Restriction naturality for the genuine connecting maps of arbitrary
Mayer--Vietoris squares of opens. -/
theorem delta_square_restriction
    (S T : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (h₁ : S.X₁ ≤ T.X₁) (h₂ : S.X₂ ≤ T.X₂)
    (h₃ : S.X₃ ≤ T.X₃) (h₄ : S.X₄ ≤ T.X₄)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) (x : F.H' n₀ T.X₁) :
    (F.cohomologyPresheaf n₁).map (homOfLE h₄).op (T.δ F n₀ n₁ h x) =
      S.δ F n₀ n₁ h ((F.cohomologyPresheaf n₀).map (homOfLE h₁).op x) := by
  let f := squareMap S T h₁ h₂ h₃ h₄
  let h' : 1 + n₀ = n₁ := (Nat.add_comm 1 n₀).trans h
  change (Ext.mk₀ f.τ₃).comp (T.shortComplex_shortExact.extClass.comp x h')
      (zero_add n₁) =
    S.shortComplex_shortExact.extClass.comp
      ((Ext.mk₀ f.τ₁).comp x (zero_add n₀)) h'
  rw [← Ext.comp_assoc_of_second_deg_zero]
  rw [ShortComplex.ShortExact.extClass_naturality S.shortComplex_shortExact
    T.shortComplex_shortExact f]
  exact (Ext.comp_assoc (Ext.mk₀ f.τ₃) T.shortComplex_shortExact.extClass x
    (zero_add 1) h' (by omega)).symm

/-- Restricting all three opens commutes with the original two connecting
maps, including the canonical comparison of sections with H⁰. -/
theorem three_connecting_restriction {U' V' W' U V W : Opens X}
    (hU : U' ≤ U) (hV : V' ≤ V) (hW : W' ≤ W)
    (s : Sections F (TripleOpen U V W)) :
    (F.cohomologyPresheaf 2).map
        (homOfLE (sup_le_sup (sup_le_sup hU hV) hW)).op
        (CycleQ2ThreeOpenSectionH2.connecting F U V W s) =
      CycleQ2ThreeOpenSectionH2.connecting F U' V' W'
        (res F (inf_le_inf (inf_le_inf hU hW) (inf_le_inf hV hW)) s) := by
  let S := CycleQ2ThreeOpenCechH2.outerSquare U V W
  let S' := CycleQ2ThreeOpenCechH2.outerSquare U' V' W'
  let T := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)
  let T' := Opens.mayerVietorisSquare (U' ⊓ W') (V' ⊓ W')
  let x := (sectionsEquiv F (TripleOpen U V W)).symm s
  let hI := inf_le_inf (inf_le_inf hU hW) (inf_le_inf hV hW)
  have h₀ : (F.cohomologyPresheaf 0).map (homOfLE hI).op x =
      (sectionsEquiv F (TripleOpen U' V' W')).symm (res F hI s) := by
    apply (sectionsEquiv F (TripleOpen U' V' W')).injective
    rw [sectionsEquiv_naturality, AddEquiv.apply_symm_apply,
      show sectionsEquiv F (TripleOpen U V W) x = s from
        (sectionsEquiv F (TripleOpen U V W)).apply_symm_apply s]
    rfl
  change (F.cohomologyPresheaf 2).map
      (homOfLE (sup_le_sup (sup_le_sup hU hV) hW)).op
      (S.δ F 1 2 rfl (T.δ F 0 1 rfl x)) =
    S'.δ F 1 2 rfl (T'.δ F 0 1 rfl
      ((sectionsEquiv F (TripleOpen U' V' W')).symm (res F hI s)))
  rw [delta_square_restriction F S' S
    (sup_le_sup (inf_le_inf hU hW) (inf_le_inf hV hW))
    (sup_le_sup hU hV) hW (sup_le_sup (sup_le_sup hU hV) hW)]
  rw [delta_restriction F (inf_le_inf hU hW) (inf_le_inf hV hW), h₀]

/-- The last union square retains the union of the three pair intersections
as its literal intersection object. -/
def outerSquare (U V W T : Opens X) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := ((U ⊓ T) ⊔ (V ⊓ T)) ⊔ (W ⊓ T)
      X₂ := (U ⊔ V) ⊔ W
      X₃ := T
      X₄ := ((U ⊔ V) ⊔ W) ⊔ T
      f₁₂ := homOfLE (sup_le_sup (sup_le_sup inf_le_left inf_le_left) inf_le_left)
      f₁₃ := homOfLE (sup_le (sup_le inf_le_right inf_le_right) inf_le_right)
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ }
    rfl (by rw [inf_sup_right, inf_sup_right])

abbrev QuadOpen (U V W T : Opens X) :=
  TripleOpen (U ⊓ T) (V ⊓ T) (W ⊓ T)

/-- The four increasing triple intersections, in the order 012,013,023,123. -/
abbrev TripleSections (U V W T : Opens X) :=
  Sections F (TripleOpen U V W) ×
    Sections F ((U ⊓ T) ⊓ (V ⊓ T)) ×
      Sections F ((U ⊓ T) ⊓ (W ⊓ T)) ×
        Sections F ((V ⊓ T) ⊓ (W ⊓ T))

private theorem quad_le_triple (U V W T : Opens X) :
    QuadOpen U V W T ≤ TripleOpen U V W :=
  inf_le_inf (inf_le_inf inf_le_left inf_le_left)
    (inf_le_inf inf_le_left inf_le_left)

/-- The actual alternating four-open restriction, with signs +,-,+,-
when indexed by the omitted vertex. -/
def boundary (U V W T : Opens X) : TripleSections F U V W T →+
    Sections F (QuadOpen U V W T) where
  toFun p := CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ T) (V ⊓ T) (W ⊓ T)
    (p.2.1, p.2.2.1, p.2.2.2) - res F (quad_le_triple U V W T) p.1
  map_zero' := by simp
  map_add' p q := by
    change CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ T) (V ⊓ T) (W ⊓ T)
        ((p.2.1, p.2.2.1, p.2.2.2) + (q.2.1, q.2.2.1, q.2.2.2)) -
        res F (quad_le_triple U V W T) (p.1 + q.1) = _
    rw [map_add, map_add]
    abel

/-- Three actual Mayer--Vietoris connecting maps, applied to the original
section on the fourfold intersection. -/
def connecting (U V W T : Opens X) : Sections F (QuadOpen U V W T) →+
    F.H' 3 (((U ⊔ V) ⊔ W) ⊔ T) :=
  ((outerSquare U V W T).δ F 2 3 rfl).hom.comp
    (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T))

/-- The same three genuine boundaries commute with every additive-sheaf
morphism on this space. -/
theorem connecting_naturality {G : AbSheaf X} (f : F ⟶ G) (U V W T : Opens X)
    (s : Sections F (QuadOpen U V W T)) :
    CycleQ2ThreeOpenH2Naturality.cohomologyMap f 3 (((U ⊔ V) ⊔ W) ⊔ T)
        (connecting F U V W T s) =
      connecting G U V W T (f.hom.app (op (QuadOpen U V W T)) s) := by
  let S := outerSquare U V W T
  change (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 3).map f).app
      (op S.X₄))
      (S.δ F 2 3 rfl
        (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T) s)) =
    S.δ G 2 3 rfl
      (CycleQ2ThreeOpenSectionH2.connecting G (U ⊓ T) (V ⊓ T) (W ⊓ T)
        (f.hom.app (op (QuadOpen U V W T)) s))
  exact (CycleQ2GeometricCanonicalCechBoundary.mayerVietoris_delta_naturality
    f S 2 3 rfl _).trans (congrArg (S.δ G 2 3 rfl)
      (CycleQ2ThreeOpenH2Naturality.connecting_naturality f (U ⊓ T) (V ⊓ T) (W ⊓ T) s))

theorem connecting_restrict012 (U V W T : Opens X)
    (s : Sections F (TripleOpen U V W)) :
    connecting F U V W T (res F (quad_le_triple U V W T) s) = 0 := by
  let S := outerSquare U V W T
  have hn := three_connecting_restriction F (inf_le_left : U ⊓ T ≤ U)
    (inf_le_left : V ⊓ T ≤ V) (inf_le_left : W ⊓ T ≤ W) s
  change S.δ F 2 3 rfl
    (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T)
      (res F (quad_le_triple U V W T) s)) = 0
  rw [← hn]
  exact delta_left_zero F S 2 3 rfl
    (CycleQ2ThreeOpenSectionH2.connecting F U V W s)

theorem connecting_boundary (U V W T : Opens X) (p : TripleSections F U V W T) :
    connecting F U V W T (boundary F U V W T p) = 0 := by
  change connecting F U V W T
    (CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ T) (V ⊓ T) (W ⊓ T)
      (p.2.1, p.2.2.1, p.2.2.2) - res F (quad_le_triple U V W T) p.1) = 0
  rw [map_sub, connecting_restrict012, sub_zero]
  change (outerSquare U V W T).δ F 2 3 rfl
    (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T)
      (CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ T) (V ⊓ T) (W ⊓ T)
        (p.2.1, p.2.2.1, p.2.2.2))) = 0
  rw [CycleQ2ThreeOpenSectionH2.connecting_boundary, map_zero]

/-- Local H² on the vertices and local H¹ on the six pairs identify the
complete kernel with actual alternating restrictions from the triples. -/
theorem connecting_eq_zero_iff (U V W T : Opens X)
    [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)]
    [Subsingleton (F.H' 2 W)] [Subsingleton (F.H' 2 T)]
    [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
    [Subsingleton (F.H' 1 (V ⊓ W))] [Subsingleton (F.H' 1 (U ⊓ T))]
    [Subsingleton (F.H' 1 (V ⊓ T))] [Subsingleton (F.H' 1 (W ⊓ T))]
    (s : Sections F (QuadOpen U V W T)) :
    connecting F U V W T s = 0 ↔
      ∃ p : TripleSections F U V W T, boundary F U V W T p = s := by
  constructor
  · intro hs
    let S := outerSquare U V W T
    let g := CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T)
    change S.δ F 2 3 rfl (g s) = 0 at hs
    obtain ⟨a, b, hab⟩ := (delta_eq_zero_iff F S 2 3 rfl (g s)).mp hs
    have hb : b = 0 := Subsingleton.elim _ _
    have ha : (F.cohomologyPresheaf 2).map S.f₁₂.op a = g s := by
      simpa only [hb, map_zero, sub_zero] using hab
    obtain ⟨v, hv⟩ := CycleQ2ThreeOpenH2Surjectivity.connecting_surjective F U V W a
    have he : g (res F (quad_le_triple U V W T) v) = g s := by
      exact (three_connecting_restriction F (inf_le_left : U ⊓ T ≤ U)
        (inf_le_left : V ⊓ T ≤ V) (inf_le_left : W ⊓ T ≤ W) v).symm.trans
          ((congrArg ((F.cohomologyPresheaf 2).map S.f₁₂.op) hv).trans ha)
    have hz : g (s - res F (quad_le_triple U V W T) v) = 0 := by
      rw [map_sub, he, sub_self]
    obtain ⟨a₀, b₀, c₀, h₀⟩ :=
      (CycleQ2ThreeOpenSectionH2.connecting_eq_zero_iff F
        (U ⊓ T) (V ⊓ T) (W ⊓ T) _).mp hz
    refine ⟨(-v, a₀, b₀, c₀), ?_⟩
    change CycleQ2ThreeOpenSectionH2.boundary F (U ⊓ T) (V ⊓ T) (W ⊓ T)
      (a₀, b₀, c₀) - res F (quad_le_triple U V W T) (-v) = s
    rw [h₀, map_neg]
    abel
  · rintro ⟨p, rfl⟩
    exact connecting_boundary F U V W T p

theorem connecting_ker (U V W T : Opens X)
    [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)]
    [Subsingleton (F.H' 2 W)] [Subsingleton (F.H' 2 T)]
    [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
    [Subsingleton (F.H' 1 (V ⊓ W))] [Subsingleton (F.H' 1 (U ⊓ T))]
    [Subsingleton (F.H' 1 (V ⊓ T))] [Subsingleton (F.H' 1 (W ⊓ T))] :
    (connecting F U V W T).ker = (boundary F U V W T).range := by
  ext s
  exact connecting_eq_zero_iff F U V W T s

private theorem delta_surjective (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Function.Surjective (S.δ F n₀ n₁ h) := by
  intro y
  have hy : S.toBiprod F n₁ y = 0 := by
    rw [S.toBiprod_apply]
    have hz : ((F.cohomologyPresheaf n₁).map S.f₂₄.op y,
        (F.cohomologyPresheaf n₁).map S.f₃₄.op y) = (0,0) :=
      Prod.ext (h₂.elim _ _) (h₃.elim _ _)
    rw [hz]
    exact map_zero _
  exact (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F n₀ n₁ h).exact 2) y hy

private theorem square_union_vanishing
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁)
    (h₁ : Subsingleton (F.H' n₀ S.X₁))
    (h₂ : Subsingleton (F.H' n₁ S.X₂)) (h₃ : Subsingleton (F.H' n₁ S.X₃)) :
    Subsingleton (F.H' n₁ S.X₄) := by
  apply subsingleton_of_forall_eq 0
  intro y
  obtain ⟨x,rfl⟩ := delta_surjective F S n₀ n₁ h h₂ h₃ y
  rw [h₁.elim x 0, map_zero]

/-- Local H³ on vertices, H² on pairs, and H¹ on triples make every actual
derived H³ class an image of a section on the fourfold intersection. -/
theorem connecting_surjective (U V W T : Opens X)
    [hU : Subsingleton (F.H' 3 U)] [hV : Subsingleton (F.H' 3 V)]
    [hW : Subsingleton (F.H' 3 W)] [hT : Subsingleton (F.H' 3 T)]
    [hUV : Subsingleton (F.H' 2 (U ⊓ V))]
    [hUW : Subsingleton (F.H' 2 (U ⊓ W))]
    [hVW : Subsingleton (F.H' 2 (V ⊓ W))]
    [Subsingleton (F.H' 2 (U ⊓ T))] [Subsingleton (F.H' 2 (V ⊓ T))]
    [Subsingleton (F.H' 2 (W ⊓ T))]
    [hUVW : Subsingleton (F.H' 1 (TripleOpen U V W))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (V ⊓ T)))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (W ⊓ T)))]
    [Subsingleton (F.H' 1 ((V ⊓ T) ⊓ (W ⊓ T)))] :
    Function.Surjective (connecting F U V W T) := by
  have hUV₃ : Subsingleton (F.H' 3 (U ⊔ V)) :=
    square_union_vanishing F (Opens.mayerVietorisSquare U V) 2 3 rfl hUV hU hV
  have hUVW₂ : Subsingleton (F.H' 2 ((U ⊓ W) ⊔ (V ⊓ W))) :=
    square_union_vanishing F (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W))
      1 2 rfl hUVW hUW hVW
  have hUVW₃ : Subsingleton (F.H' 3 ((U ⊔ V) ⊔ W)) :=
    square_union_vanishing F (CycleQ2ThreeOpenCechH2.outerSquare U V W)
      2 3 rfl hUVW₂ hUV₃ hW
  intro y
  obtain ⟨z,hz⟩ := delta_surjective F (outerSquare U V W T) 2 3 rfl hUVW₃ hT y
  obtain ⟨s,hs⟩ := CycleQ2ThreeOpenH2Surjectivity.connecting_surjective F
    (U ⊓ T) (V ⊓ T) (W ⊓ T) z
  refine ⟨s, ?_⟩
  change (outerSquare U V W T).δ F 2 3 rfl
    (CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ T) (V ⊓ T) (W ⊓ T) s) = y
  rw [hs, hz]

abbrev SectionQuotient (U V W T : Opens X) :=
  Sections F (QuadOpen U V W T) ⧸ (boundary F U V W T).range

/-- The comparison descends through the actual section-boundary range,
even before imposing any local cohomology vanishing. -/
def toSheafH3 (U V W T : Opens X) : SectionQuotient F U V W T →+
    F.H' 3 (((U ⊔ V) ⊔ W) ⊔ T) :=
  QuotientAddGroup.lift (boundary F U V W T).range (connecting F U V W T)
    (by rintro _ ⟨p,rfl⟩; exact connecting_boundary F U V W T p)

theorem toSheafH3_injective (U V W T : Opens X)
    [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)]
    [Subsingleton (F.H' 2 W)] [Subsingleton (F.H' 2 T)]
    [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
    [Subsingleton (F.H' 1 (V ⊓ W))] [Subsingleton (F.H' 1 (U ⊓ T))]
    [Subsingleton (F.H' 1 (V ⊓ T))] [Subsingleton (F.H' 1 (W ⊓ T))] :
    Function.Injective (toSheafH3 F U V W T) :=
  (QuotientAddGroup.injective_lift_iff _ _ _).2 (connecting_ker F U V W T).symm

theorem toSheafH3_surjective (U V W T : Opens X)
    [Subsingleton (F.H' 3 U)] [Subsingleton (F.H' 3 V)]
    [Subsingleton (F.H' 3 W)] [Subsingleton (F.H' 3 T)]
    [Subsingleton (F.H' 2 (U ⊓ V))] [Subsingleton (F.H' 2 (U ⊓ W))]
    [Subsingleton (F.H' 2 (V ⊓ W))] [Subsingleton (F.H' 2 (U ⊓ T))]
    [Subsingleton (F.H' 2 (V ⊓ T))] [Subsingleton (F.H' 2 (W ⊓ T))]
    [Subsingleton (F.H' 1 (TripleOpen U V W))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (V ⊓ T)))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (W ⊓ T)))]
    [Subsingleton (F.H' 1 ((V ⊓ T) ⊓ (W ⊓ T)))] :
    Function.Surjective (toSheafH3 F U V W T) := by
  intro y
  obtain ⟨s,hs⟩ := connecting_surjective F U V W T y
  exact ⟨QuotientAddGroup.mk s,hs⟩

/-- Under the explicit local vanishing groups the native section quotient
is actual derived H³ of the union, through the original connecting maps. -/
def toSheafH3Equiv (U V W T : Opens X)
    [Subsingleton (F.H' 2 U)] [Subsingleton (F.H' 2 V)]
    [Subsingleton (F.H' 2 W)] [Subsingleton (F.H' 2 T)]
    [Subsingleton (F.H' 1 (U ⊓ V))] [Subsingleton (F.H' 1 (U ⊓ W))]
    [Subsingleton (F.H' 1 (V ⊓ W))] [Subsingleton (F.H' 1 (U ⊓ T))]
    [Subsingleton (F.H' 1 (V ⊓ T))] [Subsingleton (F.H' 1 (W ⊓ T))]
    [Subsingleton (F.H' 3 U)] [Subsingleton (F.H' 3 V)]
    [Subsingleton (F.H' 3 W)] [Subsingleton (F.H' 3 T)]
    [Subsingleton (F.H' 2 (U ⊓ V))] [Subsingleton (F.H' 2 (U ⊓ W))]
    [Subsingleton (F.H' 2 (V ⊓ W))] [Subsingleton (F.H' 2 (U ⊓ T))]
    [Subsingleton (F.H' 2 (V ⊓ T))] [Subsingleton (F.H' 2 (W ⊓ T))]
    [Subsingleton (F.H' 1 (TripleOpen U V W))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (V ⊓ T)))]
    [Subsingleton (F.H' 1 ((U ⊓ T) ⊓ (W ⊓ T)))]
    [Subsingleton (F.H' 1 ((V ⊓ T) ⊓ (W ⊓ T)))] :
    SectionQuotient F U V W T ≃+ F.H' 3 (((U ⊔ V) ⊔ W) ⊔ T) :=
  AddEquiv.ofBijective (toSheafH3 F U V W T)
    ⟨toSheafH3_injective F U V W T,toSheafH3_surjective F U V W T⟩

end CycleQ2FourOpenH3
end

#print axioms CycleQ2FourOpenH3.connecting_eq_zero_iff
#print axioms CycleQ2FourOpenH3.connecting_surjective
#print axioms CycleQ2FourOpenH3.toSheafH3_injective
#print axioms CycleQ2FourOpenH3.toSheafH3_surjective
#print axioms CycleQ2FourOpenH3.toSheafH3Equiv

/-!
## The coefficient boundary of an actual four-face lift

The degree-two Čech comparison used by the divisor sequence is defined by
injective descent.  One further injective presentation gives its degree-three
continuation and identifies the coefficient boundary with the literal
alternating restriction of the given four-face lift.  No local vanishing is
needed for this identity.
-/

noncomputable section
namespace CycleQ2FourOpenTopCoefficientBoundary

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2CechTwoToDerived CycleQ2CechTwoComparison CycleQ2CechTwoNaturality
open CycleQ2CechOneConnecting
  (coefficientPresentationMap coefficientPresentationMap_left)

variable {X : TopCat.{0}}
local instance topBoundaryHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X} (U : Fin 4 → Opens X)

/-- A top cochain in an injective sheaf extends from the fourfold
intersection to the last triple intersection. -/
theorem three_exact_of_injective [Injective F] (c : Three F U) :
    ∃ b : Two F U, d2 F U b = c := by
  obtain ⟨b, hb⟩ := injective_restriction_surjective F
    (show (((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3) ≤ ((U 1 ⊓ U 2) ⊓ U 3) from
      inf_le_inf (inf_le_inf inf_le_right le_rfl) le_rfl) c
  refine ⟨⟨0, 0, 0, b⟩, ?_⟩
  simpa only [d2, map_zero, sub_zero, add_zero] using hb

/-- The image of a four-face lift is a genuine two-cocycle whenever its
top coboundary lies in the first term of the coefficient sequence. -/
theorem reducedTwo_closed {S : ShortComplex (AbSheaf X)}
    (b : Two S.X₂ U) (c : Three S.X₁ U)
    (hb : d2 S.X₂ U b = app S.f _ c) :
    d2 S.X₃ U (mapTwo U S.g b) = 0 := by
  rw [← mapThree_d2, hb, app_comp, S.zero, app_zero]

/-- The retained top lift into the original injective presentation. -/
structure TopLift (c : Three F U) where
  primitive : Two (presentation F).X₂ U
  differential : d2 (presentation F).X₂ U primitive = app (presentation F).f _ c

theorem topLift_nonempty (c : Three F U) : Nonempty (TopLift U c) := by
  obtain ⟨b, hb⟩ := three_exact_of_injective U (app (presentation F).f _ c)
  exact ⟨⟨b, hb⟩⟩

/-- A third actual coefficient boundary, composed with the existing
two-stage Čech class of the quotient cocycle. -/
def topLiftClass (hcover : (⨆ i, U i) = ⊤) {c : Three F U}
    (b : TopLift U c) : F.H' 3 ⊤ :=
  (cechTwoClass U hcover (mapTwo U (presentation F).g b.primitive)
    (reducedTwo_closed U b.primitive c b.differential)).comp
      (presentation_shortExact F).extClass rfl

/-- The top class is independent of every choice of injective lift. -/
theorem topLiftClass_independent (hcover : (⨆ i, U i) = ⊤)
    {c : Three F U} (b b' : TopLift U c) :
    topLiftClass U hcover b = topLiftClass U hcover b' := by
  have hd : d2 (presentation F).X₂ U (b.primitive - b'.primitive) = 0 := by
    change twoDifferentialHom U (b.primitive - b'.primitive) = 0
    rw [map_sub]
    change d2 (presentation F).X₂ U b.primitive -
      d2 (presentation F).X₂ U b'.primitive = 0
    rw [b.differential, b'.differential, sub_self]
  have hmap : d2 (presentation F).X₃ U
      (mapTwo U (presentation F).g (b.primitive - b'.primitive)) = 0 := by
    rw [← mapThree_d2, hd, map_zero]
  have hz : cechTwoClass U hcover
      (mapTwo U (presentation F).g (b.primitive - b'.primitive)) hmap = 0 := by
    rw [← cechTwoClass_naturality U hcover (presentation F).g _ hd hmap,
      show cechTwoClass U hcover (b.primitive - b'.primitive) hd = 0 from
        Ext.eq_zero_of_injective _, map_zero]
  let z : twoCycles (F := (presentation F).X₃) U :=
    ⟨mapTwo U (presentation F).g b.primitive,
      reducedTwo_closed U b.primitive c b.differential⟩
  let z' : twoCycles (F := (presentation F).X₃) U :=
    ⟨mapTwo U (presentation F).g b'.primitive,
      reducedTwo_closed U b'.primitive c b'.differential⟩
  have hdiff :
      (⟨mapTwo U (presentation F).g (b.primitive - b'.primitive), hmap⟩ :
        twoCycles (F := (presentation F).X₃) U) = z - z' := by
    apply Subtype.ext
    exact mapTwo_sub U (presentation F).g _ _
  change cyclesClass U hcover
    ⟨mapTwo U (presentation F).g (b.primitive - b'.primitive), hmap⟩ = 0 at hz
  rw [hdiff, map_sub] at hz
  exact congrArg (fun x : (presentation F).X₃.H' 2 ⊤ =>
    x.comp (presentation_shortExact F).extClass rfl) (sub_eq_zero.mp hz)

/-- The continuation of the existing Čech-to-derived comparison in top
degree, still defined by actual injective presentations. -/
def cechThreeClass (hcover : (⨆ i, U i) = ⊤) (c : Three F U) : F.H' 3 ⊤ :=
  topLiftClass U hcover (Classical.choice (topLift_nonempty U c))

theorem cechThreeClass_eq_topLiftClass (hcover : (⨆ i, U i) = ⊤)
    (c : Three F U) (b : TopLift U c) :
    cechThreeClass U hcover c = topLiftClass U hcover b :=
  topLiftClass_independent U hcover _ b

/-- The genuine coefficient connecting map applied to the existing
degree-two Čech class is exactly the degree-three class of the scalar
coboundary of its retained lift. -/
theorem cechTwoClass_connecting {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hcover : (⨆ i, U i) = ⊤)
    (b : Two S.X₂ U) (c : Three S.X₁ U)
    (hb : d2 S.X₂ U b = app S.f _ c) :
    (cechTwoClass U hcover (mapTwo U S.g b) (reducedTwo_closed U b c hb)).comp
      hS.extClass rfl = cechThreeClass U hcover c := by
  let m := coefficientPresentationMap hS
  let a := mapTwo U m.τ₂ b
  have ha : d2 (presentation S.X₁).X₂ U a = app (presentation S.X₁).f _ c := by
    dsimp only [a]
    rw [← mapThree_d2, hb, app_comp, ← m.comm₁₂]
    change app ((𝟙 S.X₁) ≫ (presentation S.X₁).f) _ c = _
    rw [Category.id_comp]
  let u := mapTwo U S.g b
  have hu : d2 S.X₃ U u = 0 := reducedTwo_closed U b c hb
  have hv : mapTwo U m.τ₃ u = mapTwo U (presentation S.X₁).g a := by
    dsimp only [u, a]
    rw [mapTwo_comp, mapTwo_comp, m.comm₂₃]
  have hmap : d2 (presentation S.X₁).X₃ U (mapTwo U m.τ₃ u) = 0 := by
    rw [← mapThree_d2, hu, map_zero]
  let l : TopLift U c := ⟨a, ha⟩
  have hnat := connecting_naturality hS (presentation_shortExact S.X₁) m 2
    (cechTwoClass U hcover u hu)
  have hleft : (cechTwoClass U hcover u hu).comp hS.extClass rfl =
      (derivedMap m.τ₃ (cechTwoClass U hcover u hu)).comp
        (presentation_shortExact S.X₁).extClass rfl := by
    simpa only [m, coefficientPresentationMap_left, Ext.comp_mk₀_id,
      derivedMap_apply] using hnat
  change (cechTwoClass U hcover u hu).comp hS.extClass rfl = _
  rw [hleft, cechTwoClass_naturality U hcover m.τ₃ u hu hmap,
    cechThreeClass_eq_topLiftClass U hcover c l]
  simp only [hv, topLiftClass, l]

end CycleQ2FourOpenTopCoefficientBoundary
end

#print axioms CycleQ2FourOpenTopCoefficientBoundary.topLiftClass_independent
#print axioms CycleQ2FourOpenTopCoefficientBoundary.cechTwoClass_connecting

/-!
## The sign of the three Mayer--Vietoris boundaries

The source Mayer--Vietoris map is left minus right, whereas the ordered
Čech differential is second minus first.  We retain actual maps from the
source short exact sequences to injective presentations to compare the
two conventions.
-/

noncomputable section
namespace CycleQ2FourOpenTopMayerVietoris

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
  Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2CechTwoToDerived CycleQ2CechTwoComparison
  CycleQ2FourOpenTopCoefficientBoundary
open CycleQ2ThreeOpenInjectiveComparison
  (sectionHom sectionHom_section sectionHom_restrict sectionHom_postcomp
    sections_biprod_lift sectionExtZero_eq_hzero sectionExtZero_restrict
    NormalizedData)

variable {X : TopCat.{0}}
local instance topMVHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X}

/-- Extend an actual first-component map into the injective middle term
and descend its quotient through the original source cokernel. -/
private def sourcePresentationMap {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (a : S.X₁ ⟶ F) : S ⟶ presentation F := by
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  let m : S.X₂ ⟶ (presentation F).X₂ :=
    Injective.factorThru (a ≫ (presentation F).f) S.f
  have hm : S.f ≫ m = a ≫ (presentation F).f := Injective.comp_factorThru _ _
  have hz : S.f ≫ (m ≫ (presentation F).g) = 0 := by
    rw [← Category.assoc, hm, Category.assoc, (presentation F).zero, comp_zero]
  exact
    { τ₁ := a
      τ₂ := m
      τ₃ := hS.exact.desc (m ≫ (presentation F).g) hz
      comm₁₂ := hm.symm
      comm₂₃ := (hS.exact.g_desc (m ≫ (presentation F).g) hz).symm }

/-- The actual section data of one source Mayer--Vietoris comparison.
Its last field fixes the Ext normalization, including the sign. -/
structure MayerVietorisLift
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (c : Sections F S.X₁) where
  left : Sections (presentation F).X₂ S.X₂
  right : Sections (presentation F).X₂ S.X₃
  quotient : Sections (presentation F).X₃ S.X₄
  difference : res (presentation F).X₂ S.f₁₂.le left -
      res (presentation F).X₂ S.f₁₃.le right = app (presentation F).f S.X₁ c
  quotient_left : app (presentation F).g S.X₂ left =
    res (presentation F).X₃ S.f₂₄.le quotient
  quotient_right : app (presentation F).g S.X₃ right =
    res (presentation F).X₃ S.f₃₄.le quotient
  boundary : S.δ F 0 1 rfl
      ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F S.X₁).symm c) =
    (sectionExtZero S.X₄ quotient).comp (presentation_shortExact F).extClass rfl

theorem mayerVietorisLift_nonempty
    (S : (Opens.grothendieckTopology X).MayerVietorisSquare)
    (c : Sections F S.X₁) : Nonempty (MayerVietorisLift S c) := by
  let m := sourcePresentationMap S.shortComplex_shortExact (sectionHom S.X₁ c)
  let l := freeOpenSections (presentation F).X₂ S.X₂ (biprod.inl ≫ m.τ₂)
  let r := freeOpenSections (presentation F).X₂ S.X₃ (biprod.inr ≫ m.τ₂)
  let q := freeOpenSections (presentation F).X₃ S.X₄ m.τ₃
  have hm : m.τ₂ = biprod.desc (sectionHom S.X₂ l) (sectionHom S.X₃ r) := by
    apply biprod.hom_ext'
    · rw [biprod.inl_desc]
      exact ((freeOpenSections (presentation F).X₂ S.X₂).symm_apply_apply _).symm
    · rw [biprod.inr_desc]
      exact ((freeOpenSections (presentation F).X₂ S.X₃).symm_apply_apply _).symm
  refine ⟨{
    left := l
    right := r
    quotient := q
    difference := ?_
    quotient_left := ?_
    quotient_right := ?_
    boundary := ?_
  }⟩
  · have h := congrArg (freeOpenSections (presentation F).X₂ S.X₁) m.comm₁₂
    change freeOpenSections (presentation F).X₂ S.X₁
        (sectionHom S.X₁ c ≫ (presentation F).f) = _ at h
    rw [sectionHom_postcomp, sectionHom_section, hm] at h
    change app (presentation F).f S.X₁ c =
      freeOpenSections (presentation F).X₂ S.X₁
        (biprod.lift (freeOpenMap S.f₁₂.le) (-(freeOpenMap S.f₁₃.le)) ≫
          biprod.desc (sectionHom S.X₂ l) (sectionHom S.X₃ r)) at h
    rw [sections_biprod_lift] at h
    exact h.symm
  · have h : (biprod.inl ≫ m.τ₂) ≫ (presentation F).g =
        freeOpenMap S.f₂₄.le ≫ m.τ₃ := by
      simpa only [Category.assoc,
        GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inl_desc_assoc] using
        congrArg (fun k => biprod.inl ≫ k) m.comm₂₃
    have hh := congrArg (freeOpenSections (presentation F).X₃ S.X₂) h
    rw [← freeOpenSections_postcomp, freeOpenSections_naturality] at hh
    exact hh
  · have h : (biprod.inr ≫ m.τ₂) ≫ (presentation F).g =
        freeOpenMap S.f₃₄.le ≫ m.τ₃ := by
      simpa only [Category.assoc,
        GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inr_desc_assoc] using
        congrArg (fun k => biprod.inr ≫ k) m.comm₂₃
    have hh := congrArg (freeOpenSections (presentation F).X₃ S.X₃) h
    rw [← freeOpenSections_postcomp, freeOpenSections_naturality] at hh
    exact hh
  · have h := ShortComplex.ShortExact.extClass_naturality
      S.shortComplex_shortExact (presentation_shortExact F) m
    change S.shortComplex_shortExact.extClass.comp (sectionExtZero S.X₁ c)
        (add_zero 1) = (Ext.mk₀ m.τ₃).comp
          (presentation_shortExact F).extClass (zero_add 1) at h
    change S.shortComplex_shortExact.extClass.comp
      ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F S.X₁).symm c)
        (add_zero 1) = _
    rw [← sectionExtZero_eq_hzero, h]
    change (Ext.mk₀ m.τ₃).comp (presentation_shortExact F).extClass rfl =
      (Ext.mk₀ ((freeOpenSections (presentation F).X₃ S.X₄).symm
        (freeOpenSections (presentation F).X₃ S.X₄ m.τ₃))).comp
          (presentation_shortExact F).extClass rfl
    rw [AddEquiv.symm_apply_apply]

/-- Every triple section has normalized two-stage comparison data.  The
construction uses the actual two source sequences, so it also works when
their union is a proper open of the ambient space. -/
theorem normalizedData_nonempty (U V W : Opens X)
    (c : Sections F (CycleQ2ThreeOpenCechH2.TripleOpen U V W)) :
    Nonempty (NormalizedData F U V W c) := by
  obtain ⟨a⟩ := mayerVietorisLift_nonempty
    (Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)) c
  obtain ⟨b⟩ := mayerVietorisLift_nonempty
    (CycleQ2ThreeOpenCechH2.outerSquare U V W) a.quotient
  refine ⟨{
    b02 := -a.left
    b12 := -a.right
    first_boundary := ?_
    vUV := b.left
    vW := b.right
    second_left := ?_
    second_right := ?_
    t := b.quotient
    global_left := b.quotient_left
    global_right := b.quotient_right
  }⟩
  · rw [map_neg, map_neg]
    rw [← a.difference]
    abel
  · have h := congrArg (res (presentation (presentation F).X₃).X₂
      (show U ⊓ W ≤ (U ⊓ W) ⊔ (V ⊓ W) from le_sup_left)) b.difference
    simp only [map_sub, res_comp, ← app_res] at h
    rw [← a.quotient_left] at h
    rw [map_neg, map_neg]
    exact (by simpa only [neg_sub] using congrArg Neg.neg h)
  · have h := congrArg (res (presentation (presentation F).X₃).X₂
      (show V ⊓ W ≤ (U ⊓ W) ⊔ (V ⊓ W) from le_sup_right)) b.difference
    simp only [map_sub, res_comp, ← app_res] at h
    rw [← a.quotient_right] at h
    rw [map_neg, map_neg]
    exact (by simpa only [neg_sub] using congrArg Neg.neg h)

private theorem cross_pair_eq (U V T : Opens X) :
    (U ⊓ T) ⊓ (V ⊓ T) = (U ⊓ V) ⊓ T := by
  simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem]

variable (U : Fin 4 → Opens X)

private theorem ordered_quad_eq :
    (((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3) =
      CycleQ2FourOpenH3.QuadOpen (U 0) (U 1) (U 2) (U 3) := by
  simp only [CycleQ2FourOpenH3.QuadOpen, CycleQ2ThreeOpenCechH2.TripleOpen,
    inf_assoc, inf_left_comm, inf_comm, inf_idem]

/-- The same ordered fourfold section on the redundant intersection
used by the existing Mayer--Vietoris squares. -/
def quadSection (c : Three F U) :
    Sections F (CycleQ2FourOpenH3.QuadOpen (U 0) (U 1) (U 2) (U 3)) :=
  res F (ordered_quad_eq U).ge c

variable {c : Three F U}
  (d : NormalizedData F (U 0 ⊓ U 3) (U 1 ⊓ U 3) (U 2 ⊓ U 3)
    (quadSection U c))

/-- The first injective lift has exactly the two last triple-face
components retained by the inner two Mayer--Vietoris squares. -/
def normalizedTopLift : TopLift U c where
  primitive := ⟨0, 0,
    res (presentation F).X₂ (cross_pair_eq (U 0) (U 2) (U 3)).ge d.b02,
    res (presentation F).X₂ (cross_pair_eq (U 1) (U 2) (U 3)).ge d.b12⟩
  differential := by
    have h := congrArg (res (presentation F).X₂ (ordered_quad_eq U).le) d.first_boundary
    simpa only [d2, map_zero, sub_zero, add_zero, map_sub, res_comp,
      ← app_res, quadSection, res_self] using h

/-- The retained second primitive occupies precisely the three edges
meeting the last open. -/
def middlePrimitive : One (presentation (presentation F).X₃).X₂ U :=
  ⟨0, 0, res (presentation (presentation F).X₃).X₂ le_sup_left d.vUV,
    0, res (presentation (presentation F).X₃).X₂ le_sup_right d.vUV, d.vW⟩

theorem middlePrimitive_differential :
    d1 (presentation (presentation F).X₃).X₂ U (middlePrimitive U d) =
      mapTwo U (presentation (presentation F).X₃).f
        (mapTwo U (presentation F).g (normalizedTopLift U d).primitive) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · simp only [d1, middlePrimitive, mapTwo, normalizedTopLift, map_zero,
      sub_self, add_zero]
  · simp only [d1, middlePrimitive, mapTwo, normalizedTopLift, map_zero,
      res_comp, sub_self, add_zero]
  · have h := congrArg (res (presentation (presentation F).X₃).X₂
      (cross_pair_eq (U 0) (U 2) (U 3)).ge) d.second_left
    simpa only [d1, middlePrimitive, mapTwo, normalizedTopLift, map_zero,
      add_zero, map_sub, res_comp, ← app_res] using h
  · have h := congrArg (res (presentation (presentation F).X₃).X₂
      (cross_pair_eq (U 1) (U 2) (U 3)).ge) d.second_right
    simpa only [d1, middlePrimitive, mapTwo, normalizedTopLift, map_zero,
      add_zero, map_sub, res_comp, ← app_res] using h

variable (e : MayerVietorisLift
  (CycleQ2FourOpenH3.outerSquare (U 0) (U 1) (U 2) (U 3)) d.t)

/-- The last primitive is the negative of the actual outer source
comparison on both union components. -/
def lastPrimitive : Zero (presentation (presentation (presentation F).X₃).X₃).X₂ U :=
  Fin.cases (-res (presentation (presentation (presentation F).X₃).X₃).X₂
      (le_sup_left.trans le_sup_left) e.left)
    (Fin.cases (-res (presentation (presentation (presentation F).X₃).X₃).X₂
        (le_sup_right.trans le_sup_left) e.left)
      (Fin.cases (-res (presentation (presentation (presentation F).X₃).X₃).X₂
          le_sup_right e.left)
        (Fin.cases (-e.right) (fun i => Fin.elim0 i))))

theorem lastPrimitive_differential :
    d0 (presentation (presentation (presentation F).X₃).X₃).X₂ U
        (lastPrimitive U d e) =
      mapOne U (presentation (presentation (presentation F).X₃).X₃).f
        (mapOne U (presentation (presentation F).X₃).g (middlePrimitive U d)) := by
  let I := (presentation (presentation (presentation F).X₃).X₃).X₂
  let Q := (presentation (presentation F).X₃).X₃
  have h0 : app (presentation (presentation F).X₃).g (U 0 ⊓ U 3)
      (res (presentation (presentation F).X₃).X₂ le_sup_left d.vUV) =
      res Q (le_sup_left.trans le_sup_left) d.t := by
    rw [app_res, d.global_left, res_comp]
  have h1 : app (presentation (presentation F).X₃).g (U 1 ⊓ U 3)
      (res (presentation (presentation F).X₃).X₂ le_sup_right d.vUV) =
      res Q (le_sup_right.trans le_sup_left) d.t := by
    rw [app_res, d.global_left, res_comp]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))))
  · simp only [d0, lastPrimitive, middlePrimitive, mapOne, map_zero,
      map_neg, res_comp, sub_self]
  · simp only [d0, lastPrimitive, middlePrimitive, mapOne, map_zero,
      map_neg, res_comp, sub_self]
  · have h := congrArg (res I
      (show U 0 ⊓ U 3 ≤ ((U 0 ⊓ U 3) ⊔ (U 1 ⊓ U 3)) ⊔ (U 2 ⊓ U 3) from
        le_sup_left.trans le_sup_left)) e.difference
    simp only [map_sub, res_comp, ← app_res] at h
    change res I inf_le_right (-e.right) -
        res I inf_le_left (-res I (le_sup_left.trans le_sup_left) e.left) =
      app (presentation Q).f _ (app (presentation (presentation F).X₃).g _
        (res (presentation (presentation F).X₃).X₂ le_sup_left d.vUV))
    rw [map_neg, map_neg, res_comp, neg_sub_neg, h0]
    exact h
  · simp only [d0, lastPrimitive, middlePrimitive, mapOne, map_zero,
      map_neg, res_comp, sub_self]
  · have h := congrArg (res I
      (show U 1 ⊓ U 3 ≤ ((U 0 ⊓ U 3) ⊔ (U 1 ⊓ U 3)) ⊔ (U 2 ⊓ U 3) from
        le_sup_right.trans le_sup_left)) e.difference
    simp only [map_sub, res_comp, ← app_res] at h
    change res I inf_le_right (-e.right) -
        res I inf_le_left (-res I (le_sup_right.trans le_sup_left) e.left) =
      app (presentation Q).f _ (app (presentation (presentation F).X₃).g _
        (res (presentation (presentation F).X₃).X₂ le_sup_right d.vUV))
    rw [map_neg, map_neg, res_comp, neg_sub_neg, h1]
    exact h
  · have h := congrArg (res I
      (show U 2 ⊓ U 3 ≤ ((U 0 ⊓ U 3) ⊔ (U 1 ⊓ U 3)) ⊔ (U 2 ⊓ U 3) from
        le_sup_right)) e.difference
    simp only [map_sub, res_comp, ← app_res] at h
    change res I inf_le_right (-e.right) -
        res I inf_le_left (-res I le_sup_right e.left) =
      app (presentation Q).f _ (app (presentation (presentation F).X₃).g _ d.vW)
    rw [map_neg, map_neg, res_comp, neg_sub_neg, d.global_right]
    exact h

private theorem cover_union_eq (hcover : (⨆ i, U i) = ⊤) :
    ((U 0 ⊔ U 1) ⊔ U 2) ⊔ U 3 = ⊤ := by
  apply le_antisymm le_top
  rw [← hcover]
  apply iSup_le
  intro i
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

/-- The three source comparisons give exactly retained descent data for
the quotient of the first top lift. -/
def normalizedDescent (hcover : (⨆ i, U i) = ⊤) :
    TwoDescent U (mapTwo U (presentation F).g (normalizedTopLift U d).primitive) where
  first := middlePrimitive U d
  first_differential := middlePrimitive_differential U d
  second := lastPrimitive U d e
  second_differential := lastPrimitive_differential U d e
  globalSection := -res (presentation (presentation (presentation F).X₃).X₃).X₃
    (cover_union_eq U hcover).ge e.quotient
  global_restriction := by
    funext i
    fin_cases i
    · change res _ le_top (-res _ (cover_union_eq U hcover).ge e.quotient) =
        app _ _ (-res _ (le_sup_left.trans le_sup_left) e.left)
      rw [map_neg, map_neg, app_res, e.quotient_left, res_comp, res_comp]
    · change res _ le_top (-res _ (cover_union_eq U hcover).ge e.quotient) =
        app _ _ (-res _ (le_sup_right.trans le_sup_left) e.left)
      rw [map_neg, map_neg, app_res, e.quotient_left, res_comp, res_comp]
    · change res _ le_top (-res _ (cover_union_eq U hcover).ge e.quotient) =
        app _ _ (-res _ le_sup_right e.left)
      rw [map_neg, map_neg, app_res, e.quotient_left, res_comp, res_comp]
    · change res _ le_top (-res _ (cover_union_eq U hcover).ge e.quotient) = app _ _ (-e.right)
      rw [map_neg, map_neg, e.quotient_right, res_comp]

/-- The original three Mayer--Vietoris boundaries on an ordered top
section, transported from the proved covering union to the whole space. -/
def orderedConnecting (hcover : (⨆ i, U i) = ⊤) : Three F U →+ F.H' 3 ⊤ :=
  ((F.cohomologyPresheaf 3).map (homOfLE (cover_union_eq U hcover).ge).op).hom.comp
    ((CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)).comp
      (res F (ordered_quad_eq U).ge))

/-- Associativity of the actual three source extension classes gives
the unsigned triple injective boundary of the retained outer quotient. -/
theorem orderedConnecting_normalized (hcover : (⨆ i, U i) = ⊤) :
    orderedConnecting U hcover c =
      (((sectionExtZero ⊤
        (res (presentation (presentation (presentation F).X₃).X₃).X₃
          (cover_union_eq U hcover).ge e.quotient)).comp
        (presentation_shortExact (presentation (presentation F).X₃).X₃).extClass rfl).comp
          (presentation_shortExact (presentation F).X₃).extClass rfl).comp
            (presentation_shortExact F).extClass rfl := by
  let S := CycleQ2FourOpenH3.outerSquare (U 0) (U 1) (U 2) (U 3)
  let g := S.shortComplex_shortExact.extClass
  let p := sectionExtZero S.X₁ d.t
  let a := (presentation_shortExact (presentation F).X₃).extClass
  let b := (presentation_shortExact F).extClass
  have he : g.comp p (add_zero 1) =
      (sectionExtZero S.X₄ e.quotient).comp
        (presentation_shortExact (presentation (presentation F).X₃).X₃).extClass rfl := by
    change S.shortComplex_shortExact.extClass.comp (sectionExtZero S.X₁ d.t)
      (add_zero 1) = _
    rw [sectionExtZero_eq_hzero]
    exact e.boundary
  have hm : CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)
      (quadSection U c) =
      (((sectionExtZero S.X₄ e.quotient).comp
        (presentation_shortExact (presentation (presentation F).X₃).X₃).extClass rfl).comp
          a rfl).comp b rfl := by
    change g.comp
      (CycleQ2ThreeOpenSectionH2.connecting F (U 0 ⊓ U 3) (U 1 ⊓ U 3)
        (U 2 ⊓ U 3) (quadSection U c)) rfl = _
    rw [d.mv_eq]
    change g.comp ((p.comp a rfl).comp b rfl) rfl = _
    rw [← Ext.comp_assoc g (p.comp a rfl) b rfl rfl rfl,
      ← Ext.comp_assoc_of_second_deg_zero g p a rfl, he]
  change (Ext.mk₀ (freeOpenMap (cover_union_eq U hcover).ge)).comp
    (CycleQ2FourOpenH3.connecting F (U 0) (U 1) (U 2) (U 3)
      (quadSection U c)) (zero_add 3) = _
  rw [hm, sectionExtZero_restrict]
  symm
  rw [Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by decide),
    Ext.comp_assoc _ _ _ (zero_add 1) (by decide : 1 + 1 = 2) (by decide),
    Ext.comp_assoc _ _ _ (zero_add 2) (by decide : 2 + 1 = 3) (by decide)]

private theorem sectionExtZero_neg {G : AbSheaf X} (V : Opens X) (x : Sections G V) :
    sectionExtZero V (-x) = -sectionExtZero V x := by
  unfold sectionExtZero
  rw [map_neg, Ext.mk₀_neg]

/-- With the existing ordered Čech and source Mayer--Vietoris
conventions, the third comparison has a minus sign.  This follows from
three actual short-complex comparisons and retained injective descent. -/
theorem cechThreeClass_eq_neg_orderedConnecting (hcover : (⨆ i, U i) = ⊤)
    (c : Three F U) :
    cechThreeClass U hcover c = -orderedConnecting U hcover c := by
  obtain ⟨d⟩ := normalizedData_nonempty (U 0 ⊓ U 3) (U 1 ⊓ U 3) (U 2 ⊓ U 3)
    (quadSection U c)
  obtain ⟨e⟩ := mayerVietorisLift_nonempty
    (CycleQ2FourOpenH3.outerSquare (U 0) (U 1) (U 2) (U 3)) d.t
  rw [cechThreeClass_eq_topLiftClass U hcover c (normalizedTopLift U d)]
  unfold topLiftClass
  rw [cechTwoClass_eq_descentClass U hcover _ _ (normalizedDescent U d e hcover)]
  change (((sectionExtZero ⊤
      (-res (presentation (presentation (presentation F).X₃).X₃).X₃
        (cover_union_eq U hcover).ge e.quotient)).comp
        (presentation_shortExact (presentation (presentation F).X₃).X₃).extClass rfl).comp
          (presentation_shortExact (presentation F).X₃).extClass rfl).comp
            (presentation_shortExact F).extClass rfl = _
  rw [sectionExtZero_neg, Ext.neg_comp, Ext.neg_comp, Ext.neg_comp,
    orderedConnecting_normalized U d e hcover]

/-- The actual coefficient boundary of a four-face lift is the negative
of the original iterated Mayer--Vietoris map on its scalar coboundary. -/
theorem cechTwoClass_connecting_eq_neg_orderedConnecting
    {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (hcover : (⨆ i, U i) = ⊤) (b : Two S.X₂ U) (c : Three S.X₁ U)
    (hb : d2 S.X₂ U b = app S.f _ c) :
    (cechTwoClass U hcover (mapTwo U S.g b) (reducedTwo_closed U b c hb)).comp
      hS.extClass rfl = -orderedConnecting U hcover c :=
  (cechTwoClass_connecting U hS hcover b c hb).trans
    (cechThreeClass_eq_neg_orderedConnecting U hcover c)

end CycleQ2FourOpenTopMayerVietoris
end

#print axioms CycleQ2FourOpenTopMayerVietoris.mayerVietorisLift_nonempty
#print axioms CycleQ2FourOpenTopMayerVietoris.normalizedData_nonempty
#print axioms CycleQ2FourOpenTopMayerVietoris.cechThreeClass_eq_neg_orderedConnecting
#print axioms CycleQ2FourOpenTopMayerVietoris.cechTwoClass_connecting_eq_neg_orderedConnecting
