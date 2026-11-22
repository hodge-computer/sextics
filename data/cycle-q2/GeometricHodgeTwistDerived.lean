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
