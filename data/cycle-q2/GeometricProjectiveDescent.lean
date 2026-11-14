import Proposal.GeometricCechRefinement
import Proposal.GeometricGradedCechDescent
import Proposal.GeometricHomogeneousCartierDescent
import Proposal.GeometricCoordinateH2
import Proposal.GeometricThreeOpenH2

/-!
# The original Cartier class in the actual coordinate-derived cohomology

This file retains the original homogeneous second-descent witnesses and
realizes their mixed localizations as actual sections on common projective
opens. The diagonal coboundary compares the original Cartier cocycle with
the negative of the same coordinate descendant. A comparison of the two
actual Mayer--Vietoris extensions with the finite injective presentations
then identifies their maps to ordinary derived cohomology.

The final closed theorem identifies `literalDerivedClass` with the global
connecting image of that negative coordinate representative. It also
retains the fixed cubic coefficient and the separate nonvanishing of the
character-one projection. The latter is not asserted to equal the original
unprojected class. The moving-family, support and de Rham comparisons
needed for `Submission.missing_geometric_existence` remain separate.
-/

section SectionRealization

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2CechSectionRealization

open CategoryTheory Opposite TopologicalSpace CycleQ2InjectiveCech
  CycleQ2GeometricSheafLocalIso CycleQ2GeometricFourOpenCech

variable {X : TopCat.{0}} {F : AbSheaf X} {U : Fin 4 → Opens X}
variable {R : Type} [CommRing R] {V : Finset (Fin 4) → Type}
  [∀ s, AddCommGroup (V s)] [∀ s, Module R (V s)]

/-- A compatible family of actual sections on all common subopens. -/
structure Realization (U : Fin 4 → Opens X) (D : RestrictionSystem R V) where
  app (s : Finset (Fin 4)) (W : Opens X) (h : ∀ i ∈ s, W ≤ U i) :
    V s →+ Sections F W
  map_restrict (s : Finset (Fin 4)) (W W' : Opens X) (h : ∀ i ∈ s, W ≤ U i)
    (h' : W' ≤ W) (z : V s) :
    res F h' (app s W h z) = app s W' (fun i hi => h'.trans (h i hi)) z
  naturality {s t : Finset (Fin 4)} (hst : s ⊆ t)
    (W : Opens X) (h : ∀ i ∈ t, W ≤ U i) (z : V s) :
    app t W h (D.res hst z) = app s W (fun i hi => h i (hst hi)) z

variable {D : RestrictionSystem R V}

theorem tripleLE (U : Fin 4 → Opens X) (i j k : Fin 4) :
    ∀ l ∈ ({i,j,k} : Finset (Fin 4)), ((U i ⊓ U j) ⊓ U k) ≤ U l := by
  intro l hl
  simp only [Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl | rfl
  · exact inf_le_left.trans inf_le_left
  · exact inf_le_left.trans inf_le_right
  · exact inf_le_right

def fourSections (m : Realization (F := F) U D) (c : TwoCochain V) :
    CycleQ2CechTwoToDerived.Two F U :=
  ⟨m.app {0,1,2} ((U 0 ⊓ U 1) ⊓ U 2) (tripleLE U 0 1 2) c.1.1,
   m.app {0,1,3} ((U 0 ⊓ U 1) ⊓ U 3) (tripleLE U 0 1 3) c.1.2,
   m.app {0,2,3} ((U 0 ⊓ U 2) ⊓ U 3) (tripleLE U 0 2 3) c.2.1,
   m.app {1,2,3} ((U 1 ⊓ U 2) ⊓ U 3) (tripleLE U 1 2 3) c.2.2⟩

theorem fourSections_faceAt (m : Realization (F := F) U D) (c : TwoCochain V)
    (s : Finset (Fin 4)) (W : Opens X) (h : ∀ i ∈ s, W ≤ U i)
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    CycleQ2FourToFiniteCech.faceAt U (fourSections m c) i j k W (h i hi) (h j hj) (h k hk) =
      m.app s W h (CycleQ2CechStaircaseSign.evalTwo D s i j k hi hj hk c) := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp only [CycleQ2FourToFiniteCech.faceAt, CycleQ2FourToFiniteCech.fourCases_zero,
      CycleQ2FourToFiniteCech.fourCases_one, CycleQ2FourToFiniteCech.fourCases_two,
      CycleQ2FourToFiniteCech.fourCases_three, fourSections,
      CycleQ2CechStaircaseSign.evalTwo, CycleQ2CechStaircaseSign.fourCases_zero,
      CycleQ2CechStaircaseSign.fourCases_one, CycleQ2CechStaircaseSign.fourCases_two,
      CycleQ2CechStaircaseSign.fourCases_three, map_zero, map_neg,
      m.naturality, m.map_restrict]

theorem fourSections_d2_at (m : Realization (F := F) U D) (c : TwoCochain V)
    (W : Opens X) (h : ∀ i : Fin 4, W ≤ U i) :
    res F (le_inf (le_inf (le_inf (h 0) (h 1)) (h 2)) (h 3))
        (CycleQ2CechTwoToDerived.d2 F U (fourSections m c)) =
      m.app Finset.univ W (fun i _ => h i) (d2 D c) := by
  simp only [CycleQ2CechTwoToDerived.d2, fourSections, map_add, map_sub,
    CycleQ2GeometricFourOpenCech.d2, LinearMap.coe_mk, AddHom.coe_mk,
    m.map_restrict, m.naturality]

theorem fourSections_closed (m : Realization (F := F) U D) (c : TwoCocycles D) :
    CycleQ2CechTwoToDerived.d2 F U (fourSections m c.val) = 0 := by
  let W := ((U 0 ⊓ U 1) ⊓ U 2) ⊓ U 3
  have h (i : Fin 4) : W ≤ U i := by
    fin_cases i
    · exact inf_le_left.trans (inf_le_left.trans inf_le_left)
    · exact inf_le_left.trans (inf_le_left.trans inf_le_right)
    · exact inf_le_left.trans inf_le_right
    · exact inf_le_right
  have hm := fourSections_d2_at m c.val W h
  rw [c.property, map_zero] at hm
  exact (res_self F W _).symm.trans hm

end CycleQ2CechSectionRealization

#print axioms CycleQ2CechSectionRealization.fourSections_faceAt
#print axioms CycleQ2CechSectionRealization.fourSections_closed

end
end SectionRealization

section MixedProjectiveSections

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2ProjectiveMixedSections

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricHomogeneousPrincipal CycleQ2GeometricFourOpenCech
  CycleQ2CechStaircaseSign CycleQ2GeometricSheafLocalIso
  CycleQ2GeometricProjectiveHOne CycleQ2InjectiveCech

variable {A σ : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (a : Fin 4 → A) (da : Fin 4 → ℕ) (ha : ∀ i, a i ∈ 𝒜 (da i))
  (b : Fin 4 → A) (db : Fin 4 → ℕ) (hb : ∀ i, b i ∈ 𝒜 (db i))

def mixedOpen (s t : Finset (Fin 4)) : (Proj 𝒜).Opens :=
  Proj.basicOpen 𝒜 (mixedProduct a b s t)

theorem mixedOpen_mono {s s' t t' : Finset (Fin 4)}
    (hs : s ⊆ s') (ht : t ⊆ t') :
    mixedOpen 𝒜 a b s' t' ≤ mixedOpen 𝒜 a b s t :=
  Proj.basicOpen_mono 𝒜 _ _
    ⟨product b (t' \ t) * product a (s' \ s), mixedProduct_factor a b hs ht⟩

/-- The canonical map from each actual homogeneous localization to
the structure-sheaf sections of its actual projective basic open. -/
def mixedSection (s t : Finset (Fin 4)) :
    MixedRing 𝒜 a b s t →+* Γ(Proj 𝒜, mixedOpen 𝒜 a b s t) :=
  (Proj.awayToSection 𝒜 (mixedProduct a b s t)).hom

theorem mixedSection_restrict {s s' t t' : Finset (Fin 4)}
    (hs : s ⊆ s') (ht : t ⊆ t') (z : MixedRing 𝒜 a b s t) :
    res (structureAdditiveSheaf (Proj 𝒜)) (mixedOpen_mono 𝒜 a b hs ht)
        (mixedSection 𝒜 a b s t z) =
      mixedSection 𝒜 a b s' t' (restriction 𝒜 a da ha b db hb hs ht z) := by
  exact congrArg (fun k => k z)
    (Proj.awayMap_awayToSection 𝒜
      (SetLike.mul_mem_graded (product_homogeneous 𝒜 b db hb (t' \ t))
        (product_homogeneous 𝒜 a da ha (s' \ s)))
      (mixedProduct_factor a b hs ht)).symm

def mixedSectionAt (s t : Finset (Fin 4)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s t) :
    MixedRing 𝒜 a b s t →+ Sections (structureAdditiveSheaf (Proj 𝒜)) W :=
  (res (structureAdditiveSheaf (Proj 𝒜)) hW).comp
    (mixedSection 𝒜 a b s t).toAddMonoidHom

theorem res_mixedSectionAt (s t : Finset (Fin 4))
    (W V : (Proj 𝒜).Opens) (hW : W ≤ mixedOpen 𝒜 a b s t) (hV : V ≤ W)
    (z : MixedRing 𝒜 a b s t) :
    res (structureAdditiveSheaf (Proj 𝒜)) hV (mixedSectionAt 𝒜 a b s t W hW z) =
      mixedSectionAt 𝒜 a b s t V (hV.trans hW) z :=
  res_comp _ hW hV _

theorem mixedSectionAt_restrict {s s' t t' : Finset (Fin 4)}
    (hs : s ⊆ s') (ht : t ⊆ t') (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s' t') (z : MixedRing 𝒜 a b s t) :
    mixedSectionAt 𝒜 a b s' t' W hW (restriction 𝒜 a da ha b db hb hs ht z) =
      mixedSectionAt 𝒜 a b s t W (hW.trans (mixedOpen_mono 𝒜 a b hs ht)) z := by
  change res (structureAdditiveSheaf (Proj 𝒜)) hW (mixedSection 𝒜 a b s' t' _) = _
  rw [← mixedSection_restrict 𝒜 a da ha b db hb]
  exact res_comp _ _ _ _

theorem biRes_eq_restriction {s s' t t' : Finset (Fin 4)}
    (hs : s ⊆ s') (ht : t ⊆ t') (z : MixedRing 𝒜 a b s t) :
    biRes (homogeneousBiSystem 𝒜 a da ha b db hb) hs ht z =
      restriction 𝒜 a da ha b db hb hs ht z := by
  change restriction 𝒜 a da ha b db hb hs (by rfl)
      (restriction 𝒜 a da ha b db hb (by rfl) ht z) = _
  exact restriction_comp 𝒜 a da ha b db hb (by rfl) hs ht (by rfl) z

theorem mixedSectionAt_biRes {s s' t t' : Finset (Fin 4)}
    (hs : s ⊆ s') (ht : t ⊆ t') (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s' t') (z : MixedRing 𝒜 a b s t) :
    mixedSectionAt 𝒜 a b s' t' W hW
        (biRes (homogeneousBiSystem 𝒜 a da ha b db hb) hs ht z) =
      mixedSectionAt 𝒜 a b s t W (hW.trans (mixedOpen_mono 𝒜 a b hs ht)) z := by
  rw [biRes_eq_restriction]
  exact mixedSectionAt_restrict 𝒜 a da ha b db hb hs ht W hW z

def family (i : Fin 4) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (a i)

def commonFamily (ij : Fin 4 × Fin 4) : (Proj 𝒜).Opens :=
  family 𝒜 a ij.1 ⊓ family 𝒜 b ij.2

theorem productOpen_eq_inf (s : Finset (Fin 4)) :
    Proj.basicOpen 𝒜 (product a s) = s.inf (family 𝒜 a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [product]
  | @insert i s hi ih =>
      simp only [product, Finset.prod_insert hi, Proj.basicOpen_mul,
        Finset.inf_insert] at *
      exact congrArg (fun V => family 𝒜 a i ⊓ V) ih

theorem mixedOpen_eq_inf (s t : Finset (Fin 4)) :
    mixedOpen 𝒜 a b s t = s.inf (family 𝒜 a) ⊓ t.inf (family 𝒜 b) := by
  change Proj.basicOpen 𝒜 (product b t * product a s) = _
  rw [Proj.basicOpen_mul, productOpen_eq_inf, productOpen_eq_inf, inf_comm]

theorem mixedOpen_pair_eq (u v : Fin 4 × Fin 4) :
    mixedOpen 𝒜 a b {u.1,v.1} {u.2,v.2} =
      commonFamily 𝒜 a b u ⊓ commonFamily 𝒜 a b v := by
  simp only [mixedOpen_eq_inf, Finset.inf_insert, Finset.inf_singleton, commonFamily]
  ac_rfl

theorem mixedOpen_triple_eq (u v w : Fin 4 × Fin 4) :
    mixedOpen 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} =
      (commonFamily 𝒜 a b u ⊓ commonFamily 𝒜 a b v) ⊓ commonFamily 𝒜 a b w := by
  simp only [mixedOpen_eq_inf, Finset.inf_insert, Finset.inf_singleton, commonFamily]
  ac_rfl


/-- The original mixed staircase edge as an actual section on each
pairwise intersection of the sixteen-open common refinement. -/
def diagonalSection
    (x : OneCochain (fun s => ZeroCochain (MixedRing 𝒜 a b s)))
    (y : ZeroCochain (fun s => OneCochain (MixedRing 𝒜 a b s))) :
    CycleQ2FiniteInjectiveCech.One (structureAdditiveSheaf (Proj 𝒜))
      (commonFamily 𝒜 a b) := fun u v =>
  mixedSectionAt 𝒜 a b {u.1,v.1} {u.2,v.2}
    (commonFamily 𝒜 a b u ⊓ commonFamily 𝒜 a b v)
    (mixedOpen_pair_eq 𝒜 a b u v).ge
    (diagonalEdge (homogeneousBiSystem 𝒜 a da ha b db hb) x y u v)

/-- The actual structure-sheaf coboundary of the original diagonal
primitive equals the sum of the two actual restricted cocycles. The
ordinary Čech comparison therefore retains the negative sign. -/
theorem diagonalSection_boundary
    (x : OneCochain (fun s => ZeroCochain (MixedRing 𝒜 a b s)))
    (y : ZeroCochain (fun s => OneCochain (MixedRing 𝒜 a b s)))
    (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅))
    (d : TwoCochain (MixedRing 𝒜 a b ∅))
    (hx : d1 (homogeneousBiSystem 𝒜 a da ha b db hb).row0 x =
      (homogeneousBiSystem 𝒜 a da ha b db hb).horizontalAugmentation.map2 c)
    (hxy : d0 (homogeneousBiSystem 𝒜 a da ha b db hb).row1 y =
      (homogeneousBiSystem 𝒜 a da ha b db hb).vertical0.map1 x)
    (hy : augmentation (homogeneousBiSystem 𝒜 a da ha b db hb).row2 d =
      (homogeneousBiSystem 𝒜 a da ha b db hb).vertical1.map0 y)
    (u v w : Fin 4 × Fin 4) (W : (Proj 𝒜).Opens)
    (hu : W ≤ commonFamily 𝒜 a b u) (hv : W ≤ commonFamily 𝒜 a b v)
    (hw : W ≤ commonFamily 𝒜 a b w) :
    CycleQ2FiniteInjectiveCech.boundaryValue (structureAdditiveSheaf (Proj 𝒜))
      (commonFamily 𝒜 a b) (diagonalSection 𝒜 a da ha b db hb x y) u v w W hu hv hw =
    mixedSectionAt 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} W
      (by rw [mixedOpen_triple_eq]; exact le_inf (le_inf hu hv) hw)
      (horizontalValue (homogeneousBiSystem 𝒜 a da ha b db hb) c
          {u.1,v.1,w.1} {u.2,v.2,w.2} u.1 v.1 w.1 (by simp) (by simp) (by simp) +
        verticalValue (homogeneousBiSystem 𝒜 a da ha b db hb) d
          {u.1,v.1,w.1} {u.2,v.2,w.2} u.2 v.2 w.2 (by simp) (by simp) (by simp)) := by
  let hW : W ≤ mixedOpen 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} := by
    rw [mixedOpen_triple_eq]
    exact le_inf (le_inf hu hv) hw
  have h := congrArg (mixedSectionAt 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} W hW)
    (diagonal_boundary (homogeneousBiSystem 𝒜 a da ha b db hb) x y c d hx hxy hy
      {u.1,v.1,w.1} {u.2,v.2,w.2} u v w
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp))
  simp only [map_add, map_sub, mixedSectionAt_biRes] at h
  simpa only [CycleQ2FiniteInjectiveCech.boundaryValue,
    CycleQ2FiniteInjectiveCech.edgeValue, diagonalSection, res_mixedSectionAt,
    map_add, map_sub] using h


theorem mixedOpen_le_left {s t : Finset (Fin 4)} {i : Fin 4} (hi : i ∈ s) :
    mixedOpen 𝒜 a b s t ≤ family 𝒜 a i := by
  rw [mixedOpen_eq_inf]
  exact inf_le_left.trans (Finset.inf_le hi)

theorem mixedOpen_le_right {s t : Finset (Fin 4)} {i : Fin 4} (hi : i ∈ t) :
    mixedOpen 𝒜 a b s t ≤ family 𝒜 b i := by
  rw [mixedOpen_eq_inf]
  exact inf_le_right.trans (Finset.inf_le hi)

theorem mixedSectionAt_leftRes {s s' : Finset (Fin 4)}
    (hs : s ⊆ s') (W : (Proj 𝒜).Opens) (hW : W ≤ mixedOpen 𝒜 a b s' ∅)
    (z : MixedRing 𝒜 a b s ∅) :
    mixedSectionAt 𝒜 a b s' ∅ W hW
        (((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅).res hs z) =
      mixedSectionAt 𝒜 a b s ∅ W
        (hW.trans (mixedOpen_mono 𝒜 a b hs (by rfl))) z := by
  exact mixedSectionAt_restrict 𝒜 a da ha b db hb hs (by rfl) W hW z

def leftFourSections (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅)) :
    CycleQ2CechTwoToDerived.Two (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 a) :=
  ⟨mixedSectionAt 𝒜 a b {0,1,2} ∅
    ((family 𝒜 a 0 ⊓ family 𝒜 a 1) ⊓ family 𝒜 a 2)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.1.1,
   mixedSectionAt 𝒜 a b {0,1,3} ∅
    ((family 𝒜 a 0 ⊓ family 𝒜 a 1) ⊓ family 𝒜 a 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.1.2,
   mixedSectionAt 𝒜 a b {0,2,3} ∅
    ((family 𝒜 a 0 ⊓ family 𝒜 a 2) ⊓ family 𝒜 a 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.2.1,
   mixedSectionAt 𝒜 a b {1,2,3} ∅
    ((family 𝒜 a 1 ⊓ family 𝒜 a 2) ⊓ family 𝒜 a 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.2.2⟩

def leftRealization :
    CycleQ2CechSectionRealization.Realization (F := structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 a) ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅) where
  app s W h := mixedSectionAt 𝒜 a b s ∅ W (by
    rw [mixedOpen_eq_inf]
    simpa only [Finset.inf_empty, inf_top_eq] using Finset.le_inf h)
  map_restrict s W W' h h' z := by
    exact res_mixedSectionAt 𝒜 a b s ∅ W W' _ h' z
  naturality hst W h z := by
    exact mixedSectionAt_leftRes 𝒜 a da ha b db hb hst W _ z

theorem leftFourSections_faceAt (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅))
    (s : Finset (Fin 4)) (W : (Proj 𝒜).Opens) (hW : W ≤ mixedOpen 𝒜 a b s ∅)
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    CycleQ2FourToFiniteCech.faceAt (family 𝒜 a) (leftFourSections 𝒜 a b c)
        i j k W (hW.trans (mixedOpen_le_left 𝒜 a b hi))
          (hW.trans (mixedOpen_le_left 𝒜 a b hj)) (hW.trans (mixedOpen_le_left 𝒜 a b hk)) =
      mixedSectionAt 𝒜 a b s ∅ W hW
        (evalTwo ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅) s i j k hi hj hk c) := by
  let h : ∀ l ∈ s, W ≤ family 𝒜 a l :=
    fun l hl => hW.trans (mixedOpen_le_left 𝒜 a b hl)
  exact CycleQ2CechSectionRealization.fourSections_faceAt
    (leftRealization 𝒜 a da ha b db hb) c s W h i j k hi hj hk

theorem mixedSectionAt_rightRes {s s' : Finset (Fin 4)}
    (hs : s ⊆ s') (W : (Proj 𝒜).Opens) (hW : W ≤ mixedOpen 𝒜 a b ∅ s')
    (z : MixedRing 𝒜 a b ∅ s) :
    mixedSectionAt 𝒜 a b ∅ s' W hW
        (((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅).res hs z) =
      mixedSectionAt 𝒜 a b ∅ s W
        (hW.trans (mixedOpen_mono 𝒜 a b (by rfl) hs)) z := by
  exact mixedSectionAt_restrict 𝒜 a da ha b db hb (by rfl) hs W hW z

def rightFourSections (c : TwoCochain (MixedRing 𝒜 a b ∅)) :
    CycleQ2CechTwoToDerived.Two (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 b) :=
  ⟨mixedSectionAt 𝒜 a b ∅ {0,1,2}
    ((family 𝒜 b 0 ⊓ family 𝒜 b 1) ⊓ family 𝒜 b 2)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.1.1,
   mixedSectionAt 𝒜 a b ∅ {0,1,3}
    ((family 𝒜 b 0 ⊓ family 𝒜 b 1) ⊓ family 𝒜 b 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.1.2,
   mixedSectionAt 𝒜 a b ∅ {0,2,3}
    ((family 𝒜 b 0 ⊓ family 𝒜 b 2) ⊓ family 𝒜 b 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.2.1,
   mixedSectionAt 𝒜 a b ∅ {1,2,3}
    ((family 𝒜 b 1 ⊓ family 𝒜 b 2) ⊓ family 𝒜 b 3)
    (by simp [mixedOpen_eq_inf, inf_assoc]) c.2.2⟩

def rightRealization :
    CycleQ2CechSectionRealization.Realization (F := structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 b) ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅) where
  app s W h := mixedSectionAt 𝒜 a b ∅ s W (by
    rw [mixedOpen_eq_inf]
    simpa only [Finset.inf_empty, top_inf_eq] using Finset.le_inf h)
  map_restrict s W W' h h' z := by
    exact res_mixedSectionAt 𝒜 a b ∅ s W W' _ h' z
  naturality hst W h z := by
    exact mixedSectionAt_rightRes 𝒜 a da ha b db hb hst W _ z

theorem rightFourSections_faceAt (c : TwoCochain (MixedRing 𝒜 a b ∅))
    (s : Finset (Fin 4)) (W : (Proj 𝒜).Opens) (hW : W ≤ mixedOpen 𝒜 a b ∅ s)
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    CycleQ2FourToFiniteCech.faceAt (family 𝒜 b) (rightFourSections 𝒜 a b c)
        i j k W (hW.trans (mixedOpen_le_right 𝒜 a b hi))
          (hW.trans (mixedOpen_le_right 𝒜 a b hj)) (hW.trans (mixedOpen_le_right 𝒜 a b hk)) =
      mixedSectionAt 𝒜 a b ∅ s W hW
        (evalTwo ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅) s i j k hi hj hk c) := by
  let h : ∀ l ∈ s, W ≤ family 𝒜 b l :=
    fun l hl => hW.trans (mixedOpen_le_right 𝒜 a b hl)
  exact CycleQ2CechSectionRealization.fourSections_faceAt
    (rightRealization 𝒜 a da ha b db hb) c s W h i j k hi hj hk

theorem leftFourSections_closed
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅)) :
    CycleQ2CechTwoToDerived.d2 (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 a)
      (leftFourSections 𝒜 a b c.val) = 0 :=
  CycleQ2CechSectionRealization.fourSections_closed
    (leftRealization 𝒜 a da ha b db hb) c

def leftFinite (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅)) :
    CycleQ2FiniteInjectiveCech.Two (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 a) :=
  CycleQ2FourToFiniteCech.extendTwo (family 𝒜 a) (leftFourSections 𝒜 a b c)

theorem leftFinite_normalized (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅)) :
    CycleQ2FiniteInjectiveCech.NormalizedTwo (structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 a) (leftFinite 𝒜 a b c) :=
  CycleQ2FourToFiniteCech.extendTwo_normalized (family 𝒜 a) (leftFourSections 𝒜 a b c)

theorem leftFinite_closed (hcover : (⨆ i, family 𝒜 a i) = ⊤)
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅)) :
    CycleQ2FiniteInjectiveCech.IsTwoCocycle (structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 a) (leftFinite 𝒜 a b c.val) :=
  CycleQ2FourToFiniteCech.extendTwo_closed (family 𝒜 a) hcover
    (leftFourSections 𝒜 a b c.val) (leftFourSections_closed 𝒜 a da ha b db hb c)

theorem rightFourSections_closed
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅)) :
    CycleQ2CechTwoToDerived.d2 (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 b)
      (rightFourSections 𝒜 a b c.val) = 0 :=
  CycleQ2CechSectionRealization.fourSections_closed
    (rightRealization 𝒜 a da ha b db hb) c

def rightFinite (c : TwoCochain (MixedRing 𝒜 a b ∅)) :
    CycleQ2FiniteInjectiveCech.Two (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 b) :=
  CycleQ2FourToFiniteCech.extendTwo (family 𝒜 b) (rightFourSections 𝒜 a b c)

theorem rightFinite_normalized (c : TwoCochain (MixedRing 𝒜 a b ∅)) :
    CycleQ2FiniteInjectiveCech.NormalizedTwo (structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 b) (rightFinite 𝒜 a b c) :=
  CycleQ2FourToFiniteCech.extendTwo_normalized (family 𝒜 b) (rightFourSections 𝒜 a b c)

theorem rightFinite_closed (hcover : (⨆ i, family 𝒜 b i) = ⊤)
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅)) :
    CycleQ2FiniteInjectiveCech.IsTwoCocycle (structureAdditiveSheaf (Proj 𝒜))
      (family 𝒜 b) (rightFinite 𝒜 a b c.val) :=
  CycleQ2FourToFiniteCech.extendTwo_closed (family 𝒜 b) hcover
    (rightFourSections 𝒜 a b c.val) (rightFourSections_closed 𝒜 a da ha b db hb c)

theorem mixedSectionAt_horizontalValue
    (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅))
    (s t : Finset (Fin 4)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s t)
    (i j k : Fin 4) (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s) :
    mixedSectionAt 𝒜 a b s t W hW
        (horizontalValue (homogeneousBiSystem 𝒜 a da ha b db hb) c s t i j k hi hj hk) =
      CycleQ2FourToFiniteCech.faceAt (family 𝒜 a) (leftFourSections 𝒜 a b c) i j k W
        (hW.trans (mixedOpen_le_left 𝒜 a b hi))
        (hW.trans (mixedOpen_le_left 𝒜 a b hj)) (hW.trans (mixedOpen_le_left 𝒜 a b hk)) := by
  change mixedSectionAt 𝒜 a b s t W hW
    (restriction 𝒜 a da ha b db hb (show s ⊆ s by rfl) (Finset.empty_subset t)
      (evalTwo ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅) s i j k hi hj hk c)) = _
  rw [mixedSectionAt_restrict]
  exact (leftFourSections_faceAt 𝒜 a da ha b db hb c s W _ i j k hi hj hk).symm

theorem mixedSectionAt_verticalValue
    (d : TwoCochain (MixedRing 𝒜 a b ∅))
    (s t : Finset (Fin 4)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s t)
    (i j k : Fin 4) (hi : i ∈ t) (hj : j ∈ t) (hk : k ∈ t) :
    mixedSectionAt 𝒜 a b s t W hW
        (verticalValue (homogeneousBiSystem 𝒜 a da ha b db hb) d s t i j k hi hj hk) =
      CycleQ2FourToFiniteCech.faceAt (family 𝒜 b) (rightFourSections 𝒜 a b d) i j k W
        (hW.trans (mixedOpen_le_right 𝒜 a b hi))
        (hW.trans (mixedOpen_le_right 𝒜 a b hj)) (hW.trans (mixedOpen_le_right 𝒜 a b hk)) := by
  change mixedSectionAt 𝒜 a b s t W hW
    (restriction 𝒜 a da ha b db hb (Finset.empty_subset s) (show t ⊆ t by rfl)
      (evalTwo ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅) t i j k hi hj hk d)) = _
  rw [mixedSectionAt_restrict]
  exact (rightFourSections_faceAt 𝒜 a da ha b db hb d t W _ i j k hi hj hk).symm

def commonLeftFinite (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅)) :
    CycleQ2FiniteInjectiveCech.Two (structureAdditiveSheaf (Proj 𝒜)) (commonFamily 𝒜 a b) :=
  CycleQ2FiniteCechRefinement.restrictTwo (family 𝒜 a) (commonFamily 𝒜 a b)
    Prod.fst (fun _ => inf_le_left) (leftFinite 𝒜 a b c)

def commonRightFinite (d : TwoCochain (MixedRing 𝒜 a b ∅)) :
    CycleQ2FiniteInjectiveCech.Two (structureAdditiveSheaf (Proj 𝒜)) (commonFamily 𝒜 a b) :=
  CycleQ2FiniteCechRefinement.restrictTwo (family 𝒜 b) (commonFamily 𝒜 a b)
    Prod.snd (fun _ => inf_le_right) (rightFinite 𝒜 a b d)

theorem commonLeftFinite_face (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅))
    (u v w : Fin 4 × Fin 4) (W : (Proj 𝒜).Opens)
    (hu : W ≤ commonFamily 𝒜 a b u) (hv : W ≤ commonFamily 𝒜 a b v)
    (hw : W ≤ commonFamily 𝒜 a b w) :
    CycleQ2FiniteInjectiveCech.faceValue (structureAdditiveSheaf (Proj 𝒜)) (commonFamily 𝒜 a b)
      (commonLeftFinite 𝒜 a b c) u v w W hu hv hw =
    mixedSectionAt 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} W
      (by rw [mixedOpen_triple_eq]; exact le_inf (le_inf hu hv) hw)
      (horizontalValue (homogeneousBiSystem 𝒜 a da ha b db hb) c
        {u.1,v.1,w.1} {u.2,v.2,w.2} u.1 v.1 w.1 (by simp) (by simp) (by simp)) := by
  dsimp only [commonLeftFinite, leftFinite]
  rw [CycleQ2FiniteCechRefinement.faceValue_restrictTwo, CycleQ2FourToFiniteCech.faceValue_extendTwo]
  exact (mixedSectionAt_horizontalValue 𝒜 a da ha b db hb c
    {u.1,v.1,w.1} {u.2,v.2,w.2} W _ u.1 v.1 w.1 (by simp) (by simp) (by simp)).symm

theorem commonRightFinite_face (d : TwoCochain (MixedRing 𝒜 a b ∅))
    (u v w : Fin 4 × Fin 4) (W : (Proj 𝒜).Opens)
    (hu : W ≤ commonFamily 𝒜 a b u) (hv : W ≤ commonFamily 𝒜 a b v)
    (hw : W ≤ commonFamily 𝒜 a b w) :
    CycleQ2FiniteInjectiveCech.faceValue (structureAdditiveSheaf (Proj 𝒜)) (commonFamily 𝒜 a b)
      (commonRightFinite 𝒜 a b d) u v w W hu hv hw =
    mixedSectionAt 𝒜 a b {u.1,v.1,w.1} {u.2,v.2,w.2} W
      (by rw [mixedOpen_triple_eq]; exact le_inf (le_inf hu hv) hw)
      (verticalValue (homogeneousBiSystem 𝒜 a da ha b db hb) d
        {u.1,v.1,w.1} {u.2,v.2,w.2} u.2 v.2 w.2 (by simp) (by simp) (by simp)) := by
  dsimp only [commonRightFinite, rightFinite]
  rw [CycleQ2FiniteCechRefinement.faceValue_restrictTwo, CycleQ2FourToFiniteCech.faceValue_extendTwo]
  exact (mixedSectionAt_verticalValue 𝒜 a da ha b db hb d
    {u.1,v.1,w.1} {u.2,v.2,w.2} W _ u.2 v.2 w.2 (by simp) (by simp) (by simp)).symm

theorem diagonalSection_common_difference
    (x : OneCochain (fun s => ZeroCochain (MixedRing 𝒜 a b s)))
    (y : ZeroCochain (fun s => OneCochain (MixedRing 𝒜 a b s)))
    (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅))
    (d : TwoCochain (MixedRing 𝒜 a b ∅))
    (hx : d1 (homogeneousBiSystem 𝒜 a da ha b db hb).row0 x =
      (homogeneousBiSystem 𝒜 a da ha b db hb).horizontalAugmentation.map2 c)
    (hxy : d0 (homogeneousBiSystem 𝒜 a da ha b db hb).row1 y =
      (homogeneousBiSystem 𝒜 a da ha b db hb).vertical0.map1 x)
    (hy : augmentation (homogeneousBiSystem 𝒜 a da ha b db hb).row2 d =
      (homogeneousBiSystem 𝒜 a da ha b db hb).vertical1.map0 y)
    (u v w : Fin 4 × Fin 4) (W : (Proj 𝒜).Opens)
    (hu : W ≤ commonFamily 𝒜 a b u) (hv : W ≤ commonFamily 𝒜 a b v)
    (hw : W ≤ commonFamily 𝒜 a b w) :
    CycleQ2FiniteInjectiveCech.boundaryValue (structureAdditiveSheaf (Proj 𝒜))
      (commonFamily 𝒜 a b) (diagonalSection 𝒜 a da ha b db hb x y) u v w W hu hv hw =
    CycleQ2FiniteInjectiveCech.faceValue (structureAdditiveSheaf (Proj 𝒜)) (commonFamily 𝒜 a b)
      (commonLeftFinite 𝒜 a b c - commonRightFinite 𝒜 a b (-d)) u v w W hu hv hw := by
  rw [CycleQ2FiniteCechDescent.faceValue_sub, commonLeftFinite_face 𝒜 a da ha b db hb,
    commonRightFinite_face 𝒜 a da ha b db hb]
  rw [CycleQ2GradedCechProjection.verticalValue_neg, map_neg, sub_neg_eq_add]
  simpa only [map_add] using
    diagonalSection_boundary 𝒜 a da ha b db hb x y c d hx hxy hy u v w W hu hv hw

local instance projectiveMixedHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (Proj 𝒜)) AddCommGrpCat.{0}) :=
  HasExt.standard _

def leftFiniteClass (hcover : (⨆ i, family 𝒜 a i) = ⊤)
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅)) :
    (structureAdditiveSheaf (Proj 𝒜)).H' 2 ⊤ :=
  CycleQ2FiniteCechDescent.cechTwoClass (family 𝒜 a) hcover (leftFinite 𝒜 a b c.val)
    (leftFinite_normalized 𝒜 a b c.val) (leftFinite_closed 𝒜 a da ha b db hb hcover c)

def rightFiniteClass (hcover : (⨆ i, family 𝒜 b i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅)) :
    (structureAdditiveSheaf (Proj 𝒜)).H' 2 ⊤ :=
  CycleQ2FiniteCechDescent.cechTwoClass (family 𝒜 b) hcover (rightFinite 𝒜 a b d.val)
    (rightFinite_normalized 𝒜 a b d.val) (rightFinite_closed 𝒜 a da ha b db hb hcover d)

/-- An original homogeneous second descent identifies the actual derived
classes, with the negative on the coordinate descendant. Both classes
use the same injective presentations and genuine projective sections. -/
theorem secondDescent_finiteClass
    (hca : (⨆ i, family 𝒜 a i) = ⊤) (hcb : (⨆ i, family 𝒜 b i) = ⊤)
    (c : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).left ∅))
    (d : TwoCocycles ((homogeneousBiSystem 𝒜 a da ha b db hb).right ∅))
    (hcd : (homogeneousBiSystem 𝒜 a da ha b db hb).SecondDescent c.val d.val) :
    leftFiniteClass 𝒜 a da ha b db hb hca c = rightFiniteClass 𝒜 a da ha b db hb hcb (-d) := by
  obtain ⟨x,y,hx,hxy,hy⟩ := hcd
  have hcover : (⨆ ij, commonFamily 𝒜 a b ij) = ⊤ :=
    CycleQ2FiniteCechRefinement.commonRefinement_cover (family 𝒜 a) (family 𝒜 b) hca hcb
  have hnL := leftFinite_normalized 𝒜 a b c.val
  have hcL := leftFinite_closed 𝒜 a da ha b db hb hca c
  have hnR := rightFinite_normalized 𝒜 a b (-d).val
  have hcR := rightFinite_closed 𝒜 a da ha b db hb hcb (-d)
  have hnLC := CycleQ2FiniteCechRefinement.restrictTwo_normalized
    (family 𝒜 a) (commonFamily 𝒜 a b) Prod.fst (fun _ => inf_le_left) _ hnL
  have hcLC := CycleQ2FiniteCechRefinement.restrictTwo_closed
    (family 𝒜 a) (commonFamily 𝒜 a b) Prod.fst (fun _ => inf_le_left) _ hcL
  have hnRC := CycleQ2FiniteCechRefinement.restrictTwo_normalized
    (family 𝒜 b) (commonFamily 𝒜 a b) Prod.snd (fun _ => inf_le_right) _ hnR
  have hcRC := CycleQ2FiniteCechRefinement.restrictTwo_closed
    (family 𝒜 b) (commonFamily 𝒜 a b) Prod.snd (fun _ => inf_le_right) _ hcR
  have heq := CycleQ2FiniteCechDescent.cechTwoClass_eq_of_difference_boundary
    (commonFamily 𝒜 a b) hcover (commonLeftFinite 𝒜 a b c.val)
    (commonRightFinite 𝒜 a b (-d).val) hnLC hnRC hcLC hcRC
    (diagonalSection 𝒜 a da ha b db hb x y)
    (diagonalSection_common_difference 𝒜 a da ha b db hb x y c.val d.val hx hxy hy)
  exact (CycleQ2FiniteCechRefinement.cechTwoClass_refinement
    (family 𝒜 a) (commonFamily 𝒜 a b) Prod.fst (fun _ => inf_le_left)
    hca hcover _ hnL hcL).symm.trans
      (heq.trans (CycleQ2FiniteCechRefinement.cechTwoClass_refinement
        (family 𝒜 b) (commonFamily 𝒜 a b) Prod.snd (fun _ => inf_le_right)
        hcb hcover _ hnR hcR))

/-- The original Proj fraction-to-section map on any common subopen. -/
def basicSectionAt (f : A) (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 f) :
    HomogeneousLocalization.Away 𝒜 f →+ Sections (structureAdditiveSheaf (Proj 𝒜)) W :=
  (res (structureAdditiveSheaf (Proj 𝒜)) hW).comp
    (Proj.awayToSection 𝒜 f).hom.toAddMonoidHom

theorem basicSectionAt_congr {f g : A} (hfg : f = g) (W : (Proj 𝒜).Opens)
    (hf : W ≤ Proj.basicOpen 𝒜 f) (hg : W ≤ Proj.basicOpen 𝒜 g)
    (z : HomogeneousLocalization.Away 𝒜 f) :
    basicSectionAt 𝒜 f W hf z = basicSectionAt 𝒜 g W hg (awayCongr 𝒜 hfg z) := by
  subst g
  rfl

theorem mixedSectionAt_leftEmpty (s : Finset (Fin 4)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b s ∅) (hP : W ≤ Proj.basicOpen 𝒜 (product a s))
    (z : MixedRing 𝒜 a b s ∅) :
    mixedSectionAt 𝒜 a b s ∅ W hW z =
      basicSectionAt 𝒜 (product a s) W hP (leftEmptyEquiv 𝒜 a b s z) :=
  basicSectionAt_congr 𝒜 (by simp only [mixedProduct, product, Finset.prod_empty, one_mul])
    W hW hP z

theorem mixedSectionAt_rightEmpty (s : Finset (Fin 4)) (W : (Proj 𝒜).Opens)
    (hW : W ≤ mixedOpen 𝒜 a b ∅ s) (hP : W ≤ Proj.basicOpen 𝒜 (product b s))
    (z : MixedRing 𝒜 a b ∅ s) :
    mixedSectionAt 𝒜 a b ∅ s W hW z =
      basicSectionAt 𝒜 (product b s) W hP (rightEmptyEquiv 𝒜 a b s z) :=
  basicSectionAt_congr 𝒜 (by simp only [mixedProduct, product, Finset.prod_empty, mul_one])
    W hW hP z

def singleFourSections (c : TwoCochain (HomogeneousRing 𝒜 a)) :
    CycleQ2CechTwoToDerived.Two (structureAdditiveSheaf (Proj 𝒜)) (family 𝒜 a) :=
  ⟨basicSectionAt 𝒜 (product a {0,1,2}) ((family 𝒜 a 0 ⊓ family 𝒜 a 1) ⊓ family 𝒜 a 2)
      (by simp [productOpen_eq_inf, inf_assoc]) c.1.1,
   basicSectionAt 𝒜 (product a {0,1,3}) ((family 𝒜 a 0 ⊓ family 𝒜 a 1) ⊓ family 𝒜 a 3)
      (by simp [productOpen_eq_inf, inf_assoc]) c.1.2,
   basicSectionAt 𝒜 (product a {0,2,3}) ((family 𝒜 a 0 ⊓ family 𝒜 a 2) ⊓ family 𝒜 a 3)
      (by simp [productOpen_eq_inf, inf_assoc]) c.2.1,
   basicSectionAt 𝒜 (product a {1,2,3}) ((family 𝒜 a 1 ⊓ family 𝒜 a 2) ⊓ family 𝒜 a 3)
      (by simp [productOpen_eq_inf, inf_assoc]) c.2.2⟩

theorem leftFourSections_eq_single (c : TwoCochain (fun s => MixedRing 𝒜 a b s ∅)) :
    leftFourSections 𝒜 a b c = singleFourSections 𝒜 a
      ((homogeneousLeftEmpty 𝒜 a da ha b db hb).map2 c) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact mixedSectionAt_leftEmpty 𝒜 a b {0,1,2} _ _ _ c.1.1
  · exact mixedSectionAt_leftEmpty 𝒜 a b {0,1,3} _ _ _ c.1.2
  · exact mixedSectionAt_leftEmpty 𝒜 a b {0,2,3} _ _ _ c.2.1
  · exact mixedSectionAt_leftEmpty 𝒜 a b {1,2,3} _ _ _ c.2.2

theorem rightFourSections_eq_single (d : TwoCochain (MixedRing 𝒜 a b ∅)) :
    rightFourSections 𝒜 a b d = singleFourSections 𝒜 b
      ((homogeneousRightEmpty 𝒜 a da ha b db hb).map2 d) := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact mixedSectionAt_rightEmpty 𝒜 a b {0,1,2} _ _ _ d.1.1
  · exact mixedSectionAt_rightEmpty 𝒜 a b {0,1,3} _ _ _ d.1.2
  · exact mixedSectionAt_rightEmpty 𝒜 a b {0,2,3} _ _ _ d.2.1
  · exact mixedSectionAt_rightEmpty 𝒜 a b {1,2,3} _ _ _ d.2.2

end CycleQ2ProjectiveMixedSections

#print axioms CycleQ2ProjectiveMixedSections.mixedSection_restrict
#print axioms CycleQ2ProjectiveMixedSections.mixedSectionAt_biRes
#print axioms CycleQ2ProjectiveMixedSections.mixedOpen_triple_eq

#print axioms CycleQ2ProjectiveMixedSections.diagonalSection_boundary

#print axioms CycleQ2ProjectiveMixedSections.leftFourSections_faceAt
#print axioms CycleQ2ProjectiveMixedSections.rightFourSections_faceAt

#print axioms CycleQ2ProjectiveMixedSections.leftFinite_closed
#print axioms CycleQ2ProjectiveMixedSections.rightFinite_closed

#print axioms CycleQ2ProjectiveMixedSections.diagonalSection_common_difference
#print axioms CycleQ2ProjectiveMixedSections.secondDescent_finiteClass

#print axioms CycleQ2ProjectiveMixedSections.mixedSectionAt_rightEmpty
#print axioms CycleQ2ProjectiveMixedSections.rightFourSections_eq_single

end
end MixedProjectiveSections

section CanonicalCoordinate

/-!
# The canonical projected descendant in the actual coordinate charts

The homogeneous section below is the degree-zero projection of the
original first triple component. Its underlying fraction is exactly the
first component of the already checked projected cocycle. Thus the
incoming Laurent-weight, unchanged-cubic, and coordinate-derived proofs
apply to this same representative, without selecting another descendant.

The negative homogeneous section is recorded explicitly, as required by
the checked diagonal cochain identity. These nonvanishing statements
retain the same representative. The subsequent sections compare the
coordinate Mayer--Vietoris map with the injective-presentation map used
for the original Cartier derived class, including their map conventions.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2CanonicalProjectedCoordinate

open CycleQ2GeometricFourOpenCech CycleQ2GeometricLocalizedCech
  CycleQ2GeometricCartierCech CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2CartierSurfaceGrading CycleQ2NormalConnecting
  CycleQ2GradedLocalizationProjection CycleQ2GradedCechProjection
  CycleQ2GeometricHomogeneousWeight CycleQ2GeometricCoordinateCharacter
  CycleQ2GeometricLaurentTop CycleQ2SeedCechThreeOpen
  CycleQ2ProjectiveCoordinateH2 CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricHomogeneousPrincipal

/-- Retain a chosen homogeneous descendant and its actual staircase,
while forgetting only degree to the original scalar comparison. -/
theorem literal_homogeneous_descent_to_ordinary
    (d : TwoCocycles (homogeneousCoordinateSystem 57))
    (hd : HomogeneousSecondDescent (surfaceGrade 57 1)
      (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1)
      (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57)
      literalHomogeneousCartierCycle d) :
    CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0)
      (forgetCoordinateCycle 57 d) := by
  have ho := HomogeneousSecondDescent.to_scalar (surfaceGrade 57 1)
    (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1)
    (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57) hd
  obtain ⟨cT, dT, hcT, hmid, hdT⟩ :=
    ScalarProductSecondDescent.to_principal (coverElement 57 1) (coordinateCover 57) ho
  refine ⟨cT, dT, ?_, hmid, hdT⟩
  apply Subtype.ext
  have hc := congrArg Subtype.val hcT
  change (scalarTensorMorphism (coverElement 57 1)).map2 cT.val = _ at hc
  change (scalarTensorMorphism (coverElement 57 1)).map2 cT.val =
    (cartierCycle 57 1 derivativeA 0).val
  exact hc.trans literalHomogeneousCartierCycle_forget

/-- The actual homogeneous fraction above the canonical weight-zero part
of the original coordinate top component. -/
def projectedHomogeneousCoordinateTop (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) : HomogeneousCoordinateTop r :=
  degreeZero (surfaceGrade r 1) (coordinateProduct_univ_mem_grade r)
    (coordinateTopRepresentative r d)

@[simp] theorem projectedHomogeneousCoordinateTop_val (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) :
    (projectedHomogeneousCoordinateTop r d).val =
      coordinateTopRepresentative r (coordinateProjectedCocycle r d) := by
  rfl

/-- If the original descendant already carries its genuine homogeneous
fractions, the canonical projection retains exactly its first triple. -/
@[simp] theorem projectedHomogeneousCoordinateTop_forget (r : ℂ)
    (d : TwoCocycles (homogeneousCoordinateSystem r)) :
    projectedHomogeneousCoordinateTop r (forgetCoordinateCycle r d) =
      homogeneousCoordinateRepresentative r d := by
  change degreeZero (surfaceGrade r 1) (coordinateProduct_univ_mem_grade r)
    (homogeneousCoordinateRepresentative r d).val = homogeneousCoordinateRepresentative r d
  exact degreeZero_val (surfaceGrade r 1) (coordinateProduct_univ_mem_grade r) _

theorem projected_top_weight (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) (ab : ShiftIndex) (e : LaurentExponent)
    (he : (coordinateLaurent r Finset.univ
      (coordinateTopRepresentative r (coordinateProjectedCocycle r d)) ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = 0 := by
  apply homogeneous_coordinate_weight r (projectedHomogeneousCoordinateTop r d) ab e
  simpa only [projectedHomogeneousCoordinateTop_val] using he

theorem projected_top_cubic_weight (r : ℂ)
    (d : TwoCocycles (coordinateScalarSystem r)) (ab : ShiftIndex) (e : LaurentExponent)
    (he : (coordinateLaurent r Finset.univ
      (surfaceQuotient r 1 detectorCubic •
        coordinateTopRepresentative r (coordinateProjectedCocycle r d)) ab).coeff e ≠ 0) :
    (shiftedGrade ab e).1 = 3 := by
  apply homogeneous_coordinate_cubic_weight r (projectedHomogeneousCoordinateTop r d) ab e
  simpa only [projectedHomogeneousCoordinateTop_val] using he

theorem literal_projected_top_cubic_coefficient
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d) :
    (coordinateLaurent 57 Finset.univ
      (surfaceQuotient 57 1 detectorCubic •
        coordinateTopRepresentative 57 (coordinateProjectedCocycle 57 d)) (2,2)).coeff
          (fun _ => -1) ≠ 0 := by
  simpa only [projectedHomogeneousCoordinateTop_val] using
    literal_homogeneous_cubic_coefficient (coordinateProjectedCocycle 57 d)
      (literal_projected_descent d hcd) (projectedHomogeneousCoordinateTop 57 d)
      (projectedHomogeneousCoordinateTop_val 57 d)

theorem literal_projected_top_character_one_negative
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d) :
    ∃ ab e, (∀ i, e i < 0) ∧
      (coordinateLaurent 57 Finset.univ
        (coordinateProject 57 Finset.univ 1
          (coordinateTopRepresentative 57 (coordinateProjectedCocycle 57 d))) ab).coeff e ≠ 0 := by
  simpa only [projectedHomogeneousCoordinateTop_val] using
    literal_character_one_negative (coordinateProjectedCocycle 57 d)
      (literal_projected_descent d hcd) (projectedHomogeneousCoordinateTop 57 d)
      (projectedHomogeneousCoordinateTop_val 57 d)

theorem homogeneousProject_neg (r : ℂ) (χ : ZMod 3) (q : HomogeneousCoordinateTop r) :
    homogeneousProject r χ (-q) = -homogeneousProject r χ q := by
  apply HomogeneousLocalization.val_injective
  rw [homogeneousProject_val, HomogeneousLocalization.val_neg,
    HomogeneousLocalization.val_neg, homogeneousProject_val]
  exact map_neg (coordinateProjectHom r Finset.univ χ) q.val

theorem literal_projected_top_globalConnecting_ne_zero
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d) :
    globalConnecting 57 1 one_ne_zero
      (homogeneousProject 57 1 (projectedHomogeneousCoordinateTop 57 d)) ≠ 0 :=
  literal_projected_globalConnecting_ne_zero (coordinateProjectedCocycle 57 d)
    (literal_projected_descent d hcd) (projectedHomogeneousCoordinateTop 57 d)
    (projectedHomogeneousCoordinateTop_val 57 d)

/-- The signed homogeneous section, with the negative taken before the
actual character projection, also gives a nonzero genuine derived class. -/
theorem literal_signed_projected_top_globalConnecting_ne_zero
    (d : TwoCocycles (coordinateScalarSystem 57))
    (hcd : CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d) :
    globalConnecting 57 1 one_ne_zero
      (homogeneousProject 57 1 (-projectedHomogeneousCoordinateTop 57 d)) ≠ 0 := by
  rw [homogeneousProject_neg, map_neg, neg_ne_zero]
  exact literal_projected_top_globalConnecting_ne_zero d hcd

/-- The chosen homogeneous staircase may be used directly: its original
first triple is exactly the canonical projected section. -/
theorem literal_homogeneous_signed_globalConnecting_ne_zero
    (d : TwoCocycles (homogeneousCoordinateSystem 57))
    (hd : HomogeneousSecondDescent (surfaceGrade 57 1)
      (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1)
      (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57)
      literalHomogeneousCartierCycle d) :
    globalConnecting 57 1 one_ne_zero
      (homogeneousProject 57 1 (-homogeneousCoordinateRepresentative 57 d)) ≠ 0 := by
  have hcd := literal_homogeneous_descent_to_ordinary d hd
  simpa only [projectedHomogeneousCoordinateTop_forget] using
    literal_signed_projected_top_globalConnecting_ne_zero (forgetCoordinateCycle 57 d) hcd

/-- A closed result retaining one original descendant, its canonical
projection, the unchanged cubic coefficient, and the signed derived class. -/
theorem literal_canonical_coordinate_result :
    ∃ d : TwoCocycles (coordinateScalarSystem 57),
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0) d ∧
      (coordinateLaurent 57 Finset.univ
        (surfaceQuotient 57 1 detectorCubic •
          coordinateTopRepresentative 57 (coordinateProjectedCocycle 57 d)) (2,2)).coeff
            (fun _ => -1) ≠ 0 ∧
      globalConnecting 57 1 one_ne_zero
        (homogeneousProject 57 1 (-projectedHomogeneousCoordinateTop 57 d)) ≠ 0 := by
  obtain ⟨d, hcd, _⟩ := literal_cartier_coordinate_descent_nonzero
  exact ⟨d, hcd, literal_projected_top_cubic_coefficient d hcd,
    literal_signed_projected_top_globalConnecting_ne_zero d hcd⟩

end CycleQ2CanonicalProjectedCoordinate

#print axioms CycleQ2CanonicalProjectedCoordinate.projectedHomogeneousCoordinateTop_val
#print axioms CycleQ2CanonicalProjectedCoordinate.literal_homogeneous_descent_to_ordinary
#print axioms CycleQ2CanonicalProjectedCoordinate.projected_top_cubic_weight
#print axioms CycleQ2CanonicalProjectedCoordinate.literal_projected_top_cubic_coefficient
#print axioms CycleQ2CanonicalProjectedCoordinate.literal_signed_projected_top_globalConnecting_ne_zero
#print axioms CycleQ2CanonicalProjectedCoordinate.literal_canonical_coordinate_result
#print axioms CycleQ2CanonicalProjectedCoordinate.literal_homogeneous_signed_globalConnecting_ne_zero

end
end CanonicalCoordinate

section FiniteMayerVietoris

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ThreeOpenInjectiveComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_middle_injective
  app app_res app_comp app_zero freeOpenSections_postcomp sectionExtZero)
open CycleQ2ThreeOpenCechH2 (outerSquare TripleOpen)

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F G : AbSheaf X}

def sectionHom (U : Opens X) (x : Sections F U) : freeOpen U ⟶ F :=
  (freeOpenSections F U).symm x

@[simp] theorem sectionHom_section (U : Opens X) (x : Sections F U) :
    freeOpenSections F U (sectionHom U x) = x :=
  AddEquiv.apply_symm_apply _ _

theorem sectionHom_restrict {U V : Opens X} (h : U ≤ V) (x : Sections F V) :
    freeOpenMap h ≫ sectionHom V x = sectionHom U (res F h x) := by
  apply (freeOpenSections F U).injective
  rw [freeOpenSections_naturality, sectionHom_section, sectionHom_section]

theorem sectionHom_postcomp (f : F ⟶ G) (U : Opens X) (x : Sections F U) :
    sectionHom U x ≫ f = sectionHom U (app f U x) := by
  apply (freeOpenSections G U).injective
  rw [← freeOpenSections_postcomp, sectionHom_section, sectionHom_section]

theorem sections_biprod_lift {O U V : Opens X} (hU : O ≤ U) (hV : O ≤ V)
    (u : Sections F U) (v : Sections F V) :
    freeOpenSections F O
      (biprod.lift (freeOpenMap hU) (-(freeOpenMap hV)) ≫
        biprod.desc (sectionHom U u) (sectionHom V v)) =
      res F hU u - res F hV v := by
  rw [biprod.lift_desc, Preadditive.neg_comp, ← sub_eq_add_neg, map_sub,
    freeOpenSections_naturality, freeOpenSections_naturality,
    sectionHom_section, sectionHom_section]

theorem sectionExtZero_eq_hzero (U : Opens X) (x : Sections F U) :
    sectionExtZero U x = (CycleQ2GeometricConeCech.HZero.sectionsEquiv F U).symm x := by
  apply (CycleQ2GeometricConeCech.HZero.sectionsEquiv F U).injective
  rw [AddEquiv.apply_symm_apply]
  unfold sectionExtZero
  rw [CycleQ2GeometricConeCech.HZero.sectionsEquiv_mk₀]
  exact sectionHom_section U x

variable (F) (U V W : Opens X)

abbrev firstPresentation := presentation F
abbrev secondPresentation := presentation (presentation F).X₃
abbrev innerSquare := Opens.mayerVietorisSquare (U ⊓ W) (V ⊓ W)

/-- Explicit normalized lifts in the two actual injective presentations.
The negative signs used below arise from the actual Mayer--Vietoris
left-minus-right map, while the Cech differential is second-minus-first. -/
structure NormalizedData (c : Sections F (TripleOpen U V W)) where
  b02 : Sections (firstPresentation F).X₂ (U ⊓ W)
  b12 : Sections (firstPresentation F).X₂ (V ⊓ W)
  first_boundary :
    res (firstPresentation F).X₂ inf_le_right b12 -
      res (firstPresentation F).X₂ inf_le_left b02 =
        app (firstPresentation F).f (TripleOpen U V W) c
  vUV : Sections (secondPresentation F).X₂ (U ⊔ V)
  vW : Sections (secondPresentation F).X₂ W
  second_left :
    res (secondPresentation F).X₂ inf_le_right vW -
      res (secondPresentation F).X₂ (inf_le_left.trans le_sup_left) vUV =
        app (secondPresentation F).f (U ⊓ W)
          (app (firstPresentation F).g (U ⊓ W) b02)
  second_right :
    res (secondPresentation F).X₂ inf_le_right vW -
      res (secondPresentation F).X₂ (inf_le_left.trans le_sup_right) vUV =
        app (secondPresentation F).f (V ⊓ W)
          (app (firstPresentation F).g (V ⊓ W) b12)
  t : Sections (secondPresentation F).X₃ ((U ⊔ V) ⊔ W)
  global_left : app (secondPresentation F).g (U ⊔ V) vUV =
    res (secondPresentation F).X₃ le_sup_left t
  global_right : app (secondPresentation F).g W vW =
    res (secondPresentation F).X₃ le_sup_right t

variable {F U V W} {c : Sections F (TripleOpen U V W)}

namespace NormalizedData

variable (d : NormalizedData F U V W c)

def firstMap : (innerSquare U V W).shortComplex.X₂ ⟶ (firstPresentation F).X₂ :=
  biprod.desc (sectionHom (U ⊓ W) (-d.b02)) (sectionHom (V ⊓ W) (-d.b12))

theorem firstMap_comm :
    sectionHom (TripleOpen U V W) c ≫ (firstPresentation F).f =
      (innerSquare U V W).shortComplex.f ≫ d.firstMap := by
  apply (freeOpenSections (firstPresentation F).X₂ (TripleOpen U V W)).injective
  rw [sectionHom_postcomp, sectionHom_section]
  change _ = freeOpenSections (firstPresentation F).X₂ (TripleOpen U V W)
    (biprod.lift (freeOpenMap inf_le_left) (-(freeOpenMap inf_le_right)) ≫
      biprod.desc (sectionHom (U ⊓ W) (-d.b02)) (sectionHom (V ⊓ W) (-d.b12)))
  rw [sections_biprod_lift, map_neg, map_neg]
  rw [← d.first_boundary]
  abel

theorem firstMap_zero :
    (innerSquare U V W).shortComplex.f ≫
      (d.firstMap ≫ (firstPresentation F).g) = 0 := by
  rw [← Category.assoc, ← d.firstMap_comm, Category.assoc,
    (firstPresentation F).zero, comp_zero]

def middleMap : (innerSquare U V W).shortComplex.X₃ ⟶ (firstPresentation F).X₃ :=
  (innerSquare U V W).shortComplex_shortExact.gIsCokernel.desc
    (CokernelCofork.ofπ (d.firstMap ≫ (firstPresentation F).g) d.firstMap_zero)

@[reassoc] theorem middleMap_fac :
    (innerSquare U V W).shortComplex.g ≫ d.middleMap =
      d.firstMap ≫ (firstPresentation F).g :=
  (innerSquare U V W).shortComplex_shortExact.gIsCokernel.fac _ WalkingParallelPair.one

def firstComparison : (innerSquare U V W).shortComplex ⟶ firstPresentation F where
  τ₁ := sectionHom (TripleOpen U V W) c
  τ₂ := d.firstMap
  τ₃ := d.middleMap
  comm₁₂ := d.firstMap_comm
  comm₂₃ := d.middleMap_fac.symm

def secondMap : (outerSquare U V W).shortComplex.X₂ ⟶ (secondPresentation F).X₂ :=
  biprod.desc (sectionHom (U ⊔ V) d.vUV) (sectionHom W d.vW)

theorem secondMap_sections :
    freeOpenSections (secondPresentation F).X₂ ((U ⊓ W) ⊔ (V ⊓ W))
      ((outerSquare U V W).shortComplex.f ≫ d.secondMap) =
      res (secondPresentation F).X₂ (sup_le_sup inf_le_left inf_le_left) d.vUV -
        res (secondPresentation F).X₂ (sup_le inf_le_right inf_le_right) d.vW :=
  sections_biprod_lift _ _ _ _

theorem secondMap_comm :
    d.middleMap ≫ (secondPresentation F).f =
      (outerSquare U V W).shortComplex.f ≫ d.secondMap := by
  apply (cancel_epi (innerSquare U V W).shortComplex.g).mp
  rw [d.middleMap_fac_assoc]
  apply biprod.hom_ext'
  · simp only [firstMap, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
      biprod.inl_desc_assoc]
    change sectionHom (U ⊓ W) (-d.b02) ≫ (firstPresentation F).g ≫
        (secondPresentation F).f =
      freeOpenMap le_sup_left ≫ (outerSquare U V W).shortComplex.f ≫ d.secondMap
    apply (freeOpenSections (secondPresentation F).X₂ (U ⊓ W)).injective
    rw [← Category.assoc, sectionHom_postcomp, sectionHom_postcomp, sectionHom_section,
      freeOpenSections_naturality, d.secondMap_sections, map_sub, res_comp, res_comp,
      map_neg, map_neg]
    rw [← d.second_left]
    abel
  · simp only [firstMap, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
      biprod.inr_desc_assoc]
    change sectionHom (V ⊓ W) (-d.b12) ≫ (firstPresentation F).g ≫
        (secondPresentation F).f =
      freeOpenMap le_sup_right ≫ (outerSquare U V W).shortComplex.f ≫ d.secondMap
    apply (freeOpenSections (secondPresentation F).X₂ (V ⊓ W)).injective
    rw [← Category.assoc, sectionHom_postcomp, sectionHom_postcomp, sectionHom_section,
      freeOpenSections_naturality, d.secondMap_sections, map_sub, res_comp, res_comp,
      map_neg, map_neg]
    rw [← d.second_right]
    abel

def secondComparison : (outerSquare U V W).shortComplex ⟶ secondPresentation F where
  τ₁ := d.middleMap
  τ₂ := d.secondMap
  τ₃ := sectionHom ((U ⊔ V) ⊔ W) d.t
  comm₁₂ := d.secondMap_comm
  comm₂₃ := by
    apply biprod.hom_ext'
    · simp only [secondMap, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inl_desc_assoc]
      change sectionHom (U ⊔ V) d.vUV ≫ (secondPresentation F).g =
        freeOpenMap le_sup_left ≫ sectionHom ((U ⊔ V) ⊔ W) d.t
      rw [sectionHom_postcomp, sectionHom_restrict, d.global_left]
    · simp only [secondMap, GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
        biprod.inr_desc_assoc]
      change sectionHom W d.vW ≫ (secondPresentation F).g =
        freeOpenMap le_sup_right ≫ sectionHom ((U ⊔ V) ⊔ W) d.t
      rw [sectionHom_postcomp, sectionHom_restrict, d.global_right]

/-- Two actual short-complex morphisms identify the two Mayer--Vietoris
boundaries with the two injective boundaries, with positive normalization. -/
theorem mv_eq :
    CycleQ2ThreeOpenSectionH2.connecting F U V W c =
      ((sectionExtZero ((U ⊔ V) ⊔ W) d.t).comp
        (presentation_shortExact (presentation F).X₃).extClass rfl).comp
          (presentation_shortExact F).extClass rfl := by
  have h1 := ShortComplex.ShortExact.extClass_naturality
    (innerSquare U V W).shortComplex_shortExact (presentation_shortExact F) d.firstComparison
  have h2 := ShortComplex.ShortExact.extClass_naturality
    (outerSquare U V W).shortComplex_shortExact
    (presentation_shortExact (presentation F).X₃) d.secondComparison
  change (innerSquare U V W).shortComplex_shortExact.extClass.comp
      (sectionExtZero (TripleOpen U V W) c) (add_zero 1) =
    (Ext.mk₀ d.middleMap).comp (presentation_shortExact F).extClass (zero_add 1) at h1
  change (outerSquare U V W).shortComplex_shortExact.extClass.comp
      (Ext.mk₀ d.middleMap) (add_zero 1) =
    (sectionExtZero ((U ⊔ V) ⊔ W) d.t).comp
      (presentation_shortExact (presentation F).X₃).extClass (zero_add 1) at h2
  change (outerSquare U V W).shortComplex_shortExact.extClass.comp
    ((innerSquare U V W).shortComplex_shortExact.extClass.comp
      ((CycleQ2GeometricConeCech.HZero.sectionsEquiv F (TripleOpen U V W)).symm c)
        (add_zero 1)) rfl = _
  rw [← sectionExtZero_eq_hzero, h1, ← Ext.comp_assoc_of_second_deg_zero, h2]

end NormalizedData

end CycleQ2ThreeOpenInjectiveComparison

#print axioms CycleQ2ThreeOpenInjectiveComparison.NormalizedData.mv_eq


namespace CycleQ2ThreeOpenInjectiveComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2CechTwoToDerived (presentation presentation_shortExact presentation_middle_injective
  app app_res app_comp app_zero sectionExtZero)
open CycleQ2FiniteInjectiveCech
open CycleQ2ThreeOpenCechH2 (TripleOpen)

variable {X : TopCat.{0}} {ι : Type}
local instance sheafHasExt' : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X}

theorem sections_eq_of_pair_restrictions (U V : Opens X) (x y : Sections F (U ⊔ V))
    (hU : res F le_sup_left x = res F le_sup_left y)
    (hV : res F le_sup_right x = res F le_sup_right y) : x = y := by
  apply (freeOpenSections F (U ⊔ V)).symm.injective
  apply (cancel_epi (Opens.mayerVietorisSquare U V).shortComplex.g).mp
  apply biprod.hom_ext'
  · simp only [GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
      biprod.inl_desc_assoc]
    change freeOpenMap le_sup_left ≫ sectionHom (U ⊔ V) x =
      freeOpenMap le_sup_left ≫ sectionHom (U ⊔ V) y
    rw [sectionHom_restrict, sectionHom_restrict, hU]
  · simp only [GrothendieckTopology.MayerVietorisSquare.shortComplex_g,
      biprod.inr_desc_assoc]
    change freeOpenMap le_sup_right ≫ sectionHom (U ⊔ V) x =
      freeOpenMap le_sup_right ≫ sectionHom (U ⊔ V) y
    rw [sectionHom_restrict, sectionHom_restrict, hV]

variable (A : ι → Opens X)

def selectedTriple (c : Two F A) (i j k : ι) :
    Sections F (TripleOpen (A i) (A j) (A k)) :=
  faceValue F A c i j k _ (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right)

/-- Every retained finite injective descent supplies the normalized
two-Mayer--Vietoris comparison data. Its global second quotient section
is merely restricted to the selected union; it is not changed. -/
theorem normalizedData_of_descent {c : Two F A}
    (d : CycleQ2FiniteCechDescent.TwoDescent A c) (i j k : ι) :
    ∃ e : NormalizedData F (A i) (A j) (A k) (selectedTriple A c i j k),
      e.t = res (secondPresentation F).X₃ le_top d.globalSection := by
  let I := (firstPresentation F).X₂
  let J := (secondPresentation F).X₂
  let Q₂ := (secondPresentation F).X₃
  let O := ((A i ⊔ A j) ⊔ A k)
  let T := TripleOpen (A i) (A j) (A k)
  obtain ⟨a, ha⟩ := injective_restriction_surjective I
    (inf_le_right : A i ⊓ A j ≤ A j) (d.first i j)
  let vj : Sections J (A j) := d.second j -
    app (secondPresentation F).f (A j) (app (firstPresentation F).g (A j) a)
  have hij : res J inf_le_right vj = res J inf_le_left (d.second i) := by
    have h := d.second_differential i j (A i ⊓ A j) inf_le_left inf_le_right
    simp only [edgeValue, res_self] at h
    dsimp only [vj]
    rw [map_sub, ← app_res, ← app_res, ha]
    rw [sub_eq_iff_eq_add.mp h]
    abel
  obtain ⟨vUV, hvU, hvV⟩ := extend_pair J (A i ⊔ A j) (A i) (A j)
    le_sup_left le_sup_right (d.second i) vj (by
      intro Z hi hj
      have h := congrArg (res J (le_inf hi hj)) hij
      simpa only [res_comp] using h.symm)
  let b12 : Sections I (A j ⊓ A k) :=
    d.first j k + res I inf_le_left a
  have haT : res I (show T ≤ A j from inf_le_right.trans inf_le_left) a =
      res I (show T ≤ A i ⊓ A j from
        le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left))
          (d.first i j) := by
    rw [← ha, res_comp]
  have hfirst : res I inf_le_right b12 - res I inf_le_left (d.first i k) =
      app (firstPresentation F).f T (selectedTriple A c i j k) := by
    have h := d.first_differential i j k T (inf_le_left.trans inf_le_left)
      (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right)
    dsimp only [boundaryValue, edgeValue] at h
    dsimp only [b12]
    rw [map_add, res_comp, haT]
    convert h using 1 <;> abel
  have hleft : res J inf_le_right (d.second k) -
      res J (inf_le_left.trans le_sup_left) vUV =
        app (secondPresentation F).f (A i ⊓ A k)
          (app (firstPresentation F).g (A i ⊓ A k) (d.first i k)) := by
    rw [← res_comp J le_sup_left inf_le_left, hvU]
    simpa only [edgeValue, res_self] using
      d.second_differential i k (A i ⊓ A k) inf_le_left inf_le_right
  have hright : res J inf_le_right (d.second k) -
      res J (inf_le_left.trans le_sup_right) vUV =
        app (secondPresentation F).f (A j ⊓ A k)
          (app (firstPresentation F).g (A j ⊓ A k) b12) := by
    have h := d.second_differential j k (A j ⊓ A k) inf_le_left inf_le_right
    simp only [edgeValue, res_self] at h
    rw [← res_comp J le_sup_right inf_le_left, hvV]
    dsimp only [vj, b12]
    rw [map_sub, ← app_res, ← app_res, map_add, map_add]
    rw [← h]
    abel
  have hglobal (l : ι) :
      res Q₂ le_top d.globalSection = app (secondPresentation F).g (A l) (d.second l) :=
    congrFun d.global_restriction l
  have hgvj : app (secondPresentation F).g (A j) vj =
      app (secondPresentation F).g (A j) (d.second j) := by
    dsimp only [vj]
    rw [map_sub, app_comp, (secondPresentation F).zero, app_zero, sub_zero]
  have hgleft : app (secondPresentation F).g (A i ⊔ A j) vUV =
      res Q₂ le_sup_left (res Q₂ (show O ≤ ⊤ from le_top) d.globalSection) := by
    apply sections_eq_of_pair_restrictions (A i) (A j)
    · rw [← app_res, hvU, res_comp, res_comp]
      exact (hglobal i).symm
    · rw [← app_res, hvV, hgvj, res_comp, res_comp]
      exact (hglobal j).symm
  refine ⟨{
    b02 := d.first i k
    b12 := b12
    first_boundary := hfirst
    vUV := vUV
    vW := d.second k
    second_left := hleft
    second_right := hright
    t := res Q₂ le_top d.globalSection
    global_left := hgleft
    global_right := ?_
  }, rfl⟩
  rw [res_comp]
  exact (hglobal k).symm

theorem mv_eq_descent_section {c : Two F A}
    (d : CycleQ2FiniteCechDescent.TwoDescent A c) (i j k : ι) :
    CycleQ2ThreeOpenSectionH2.connecting F (A i) (A j) (A k) (selectedTriple A c i j k) =
      ((sectionExtZero ((A i ⊔ A j) ⊔ A k)
        (res (secondPresentation F).X₃ le_top d.globalSection)).comp
          (presentation_shortExact (presentation F).X₃).extClass rfl).comp
            (presentation_shortExact F).extClass rfl := by
  obtain ⟨e, he⟩ := normalizedData_of_descent A d i j k
  simpa only [he] using e.mv_eq

end CycleQ2ThreeOpenInjectiveComparison

#print axioms CycleQ2ThreeOpenInjectiveComparison.normalizedData_of_descent
#print axioms CycleQ2ThreeOpenInjectiveComparison.mv_eq_descent_section


namespace CycleQ2ThreeOpenInjectiveComparison

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
open CycleQ2CechTwoToDerived (presentation presentation_shortExact sectionExtZero)
open CycleQ2FiniteInjectiveCech

variable {X : TopCat.{0}} {ι : Type}
local instance sheafHasExt'' : HasExt.{1} (AbSheaf X) := HasExt.standard _
variable {F : AbSheaf X}

theorem sectionExtZero_restrict {U V : Opens X} (h : U ≤ V) (x : Sections F V) :
    sectionExtZero U (res F h x) =
      (Ext.mk₀ (freeOpenMap h)).comp (sectionExtZero V x) (zero_add 0) := by
  unfold sectionExtZero
  rw [Ext.mk₀_comp_mk₀]
  exact congrArg Ext.mk₀ (sectionHom_restrict h x).symm

variable (A : ι → Opens X)

/-- The genuine iterated Mayer--Vietoris map is the restriction of the
same injective-presentation Ext class. This is an equality of maps on
each retained descent, not merely equality of their kernels. -/
theorem mv_eq_descent_restriction {c : Two F A}
    (d : CycleQ2FiniteCechDescent.TwoDescent A c) (i j k : ι) :
    CycleQ2ThreeOpenSectionH2.connecting F (A i) (A j) (A k) (selectedTriple A c i j k) =
      (F.cohomologyPresheaf 2).map
        (homOfLE (show (A i ⊔ A j) ⊔ A k ≤ ⊤ from le_top)).op
          (CycleQ2FiniteCechDescent.descentClass A d) := by
  rw [mv_eq_descent_section, sectionExtZero_restrict]
  change (((Ext.mk₀ (freeOpenMap (show (A i ⊔ A j) ⊔ A k ≤ ⊤ from le_top))).comp
      (sectionExtZero ⊤ d.globalSection) (zero_add 0)).comp
        (presentation_shortExact (presentation F).X₃).extClass rfl).comp
          (presentation_shortExact F).extClass rfl =
    (Ext.mk₀ (freeOpenMap (show (A i ⊔ A j) ⊔ A k ≤ ⊤ from le_top))).comp
      (((sectionExtZero ⊤ d.globalSection).comp
        (presentation_shortExact (presentation F).X₃).extClass rfl).comp
          (presentation_shortExact F).extClass rfl) (zero_add 2)
  rw [Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (by decide),
    Ext.comp_assoc _ _ _ (zero_add 1) (by decide : 1 + 1 = 2) (by decide)]

theorem mv_eq_finiteClass_restriction [Fintype ι]
    (hcover : (⨆ i, A i) = ⊤) (c : Two F A)
    (hn : NormalizedTwo F A c) (hc : IsTwoCocycle F A c) (i j k : ι) :
    CycleQ2ThreeOpenSectionH2.connecting F (A i) (A j) (A k) (selectedTriple A c i j k) =
      (F.cohomologyPresheaf 2).map
        (homOfLE (show (A i ⊔ A j) ⊔ A k ≤ ⊤ from le_top)).op
          (CycleQ2FiniteCechDescent.cechTwoClass A hcover c hn hc) := by
  let d := Classical.choice (CycleQ2FiniteCechDescent.twoDescent_nonempty A hcover c hn hc)
  rw [CycleQ2FiniteCechDescent.cechTwoClass_eq_descentClass A hcover c hn hc d]
  exact mv_eq_descent_restriction A d i j k

end CycleQ2ThreeOpenInjectiveComparison

#print axioms CycleQ2ThreeOpenInjectiveComparison.mv_eq_finiteClass_restriction

end
end FiniteMayerVietoris

section CoordinateMayerVietoris

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2CoordinateMVBinding

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  AlgebraicGeometry
open CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso
  CycleQ2GeometricProjectiveHOne CycleQ2CartierProjectiveCover
  CycleQ2CartierSurfaceGrading CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricCartierCech CycleQ2GeometricHomogeneousWeight
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2GeometricSheafCohomologyRestriction CycleQ2ThreeOpenInjectiveComparison
  CycleQ2FiniteInjectiveCech

section General

variable {X : TopCat.{0}}
local instance sheafHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

theorem coverIso_restriction (F : AbSheaf X) (O : Opens X) (hO : O = ⊤)
    (x : F.H' 2 ⊤) :
    (((F.cohomologyPresheaf 2).mapIso (eqToIso hO.symm).op).addCommGroupIsoToAddEquiv)
      ((F.cohomologyPresheaf 2).map (homOfLE (show O ≤ ⊤ from le_top)).op x) = x := by
  change ((F.cohomologyPresheaf 2).map (homOfLE (show O ≤ ⊤ from le_top)).op ≫
    (F.cohomologyPresheaf 2).map (eqToIso hO.symm).op.hom) x = x
  rw [← Functor.map_comp,
    show (homOfLE (show O ≤ ⊤ from le_top)).op ≫ (eqToIso hO.symm).op.hom =
      𝟙 (op (⊤ : Opens X)) from Subsingleton.elim _ _,
    (F.cohomologyPresheaf 2).map_id]
  rfl

end General

local instance surfaceHasExt (r θ : ℂ) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface r θ)) AddCommGrpCat.{0}) :=
  HasExt.standard _

def coordinateFamily (r : ℂ) (i : Fin 4) : (projectiveSurface r 1).Opens :=
  Proj.basicOpen (surfaceGrade r 1) (coordinateCover r i)

theorem coordinateFamily_cover (r : ℂ) : (⨆ i, coordinateFamily r i) = ⊤ := by
  apply top_unique
  rw [← coordinate_three_cover r 1 one_ne_zero]
  exact sup_le (sup_le (le_iSup (coordinateFamily r) 0)
    (le_iSup (coordinateFamily r) 1)) (le_iSup (coordinateFamily r) 2)

theorem tripleSections_eq_awayToSection (r θ : ℂ)
    (q : HomogeneousCoordinateLocal r θ Finset.univ) :
    tripleSections r θ q =
      res (structureAdditiveSheaf (projectiveSurface r θ))
        (coordinateIntersection_univ r θ).ge
        ((Proj.awayToSection (surfaceGrade r θ) (coordinateProduct r θ Finset.univ)).hom q) := by
  rfl

theorem unionGlobalEquiv_restriction (r θ : ℂ) (hθ : θ ≠ 0)
    (x : (structureAdditiveSheaf (projectiveSurface r θ)).H' 2 ⊤) :
    unionGlobalEquiv r θ hθ
      (((structureAdditiveSheaf (projectiveSurface r θ)).cohomologyPresheaf 2).map
        (homOfLE (show (coordinateOpen r θ 0 ⊔ coordinateOpen r θ 1) ⊔
          coordinateOpen r θ 2 ≤ ⊤ from le_top)).op x) =
      terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r θ))
        (structureAdditiveSheaf (projectiveSurface r θ)) ⊤ isTerminalTop 2 x := by
  change terminalCohomologyEquiv _ _ _ _ _
    (((((structureAdditiveSheaf (projectiveSurface r θ)).cohomologyPresheaf 2).mapIso
      (eqToIso (coordinate_three_cover r θ hθ).symm).op).addCommGroupIsoToAddEquiv)
      (((structureAdditiveSheaf (projectiveSurface r θ)).cohomologyPresheaf 2).map
        (homOfLE (show (coordinateOpen r θ 0 ⊔ coordinateOpen r θ 1) ⊔
          coordinateOpen r θ 2 ≤ ⊤ from le_top)).op x)) = _
  rw [coverIso_restriction _ _ (coordinate_three_cover r θ hθ)]

/-- The exact finite injective class of a coordinate cocycle equals the
actual global Mayer--Vietoris image of its same homogeneous top section. -/
theorem finite_coordinate_global_eq (r : ℂ)
    (hcover : (⨆ i, coordinateFamily r i) = ⊤)
    (c : Two (structureAdditiveSheaf (projectiveSurface r 1)) (coordinateFamily r))
    (hn : NormalizedTwo _ _ c) (hc : IsTwoCocycle _ _ c)
    (q : HomogeneousCoordinateTop r)
    (hq : selectedTriple (coordinateFamily r) c 0 1 2 = tripleSections r 1 q) :
    terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r 1))
      (structureAdditiveSheaf (projectiveSurface r 1)) ⊤ isTerminalTop 2
        (CycleQ2FiniteCechDescent.cechTwoClass (coordinateFamily r) hcover c hn hc) =
      globalConnecting r 1 one_ne_zero q := by
  have h := mv_eq_finiteClass_restriction (coordinateFamily r) hcover c hn hc 0 1 2
  rw [hq] at h
  change coordinateConnecting r 1 q =
    ((structureAdditiveSheaf (projectiveSurface r 1)).cohomologyPresheaf 2).map
      (homOfLE (show (coordinateOpen r 1 0 ⊔ coordinateOpen r 1 1) ⊔
        coordinateOpen r 1 2 ≤ ⊤ from le_top)).op
          (CycleQ2FiniteCechDescent.cechTwoClass (coordinateFamily r) hcover c hn hc) at h
  change _ = unionGlobalEquiv r 1 one_ne_zero (coordinateConnecting r 1 q)
  rw [h, unionGlobalEquiv_restriction]


open CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricFourOpenCech CycleQ2GeometricHomogeneousPrincipal
  CycleQ2ProjectiveMixedSections

section SelectedFace

variable {X : TopCat.{0}} {F : AbSheaf X}
local instance selectedHasExt : HasExt.{1} (AbSheaf X) := HasExt.standard _

theorem selectedTriple_extendTwo_first (U : Fin 4 → Opens X)
    (c : CycleQ2CechTwoToDerived.Two F U) :
    selectedTriple U (CycleQ2FourToFiniteCech.extendTwo U c) 0 1 2 =
      res F (le_inf (le_inf (inf_le_left.trans inf_le_left)
        (inf_le_right.trans inf_le_left)) (inf_le_left.trans inf_le_right)) c.1 := by
  unfold selectedTriple
  rw [CycleQ2FourToFiniteCech.faceValue_extendTwo]
  rfl

end SelectedFace

/-- The selected finite coordinate face is the same homogeneous fraction
viewed through the actual Proj structure-sheaf section map. -/
theorem selectedTriple_singleCoordinate (r : ℂ)
    (d : TwoCocycles (homogeneousCoordinateSystem r)) :
    selectedTriple (coordinateFamily r)
      (CycleQ2FourToFiniteCech.extendTwo (coordinateFamily r)
        (singleFourSections (surfaceGrade r 1) (coordinateCover r) d.val)) 0 1 2 =
      tripleSections r 1 (homogeneousCoordinateRepresentative r d) := by
  rw [selectedTriple_extendTwo_first]
  change res (structureAdditiveSheaf (projectiveSurface r 1)) _
    (res (structureAdditiveSheaf (projectiveSurface r 1)) _
      ((Proj.awayToSection (surfaceGrade r 1)
        (coordinateProduct r 1 Finset.univ)).hom (homogeneousCoordinateRepresentative r d))) = _
  rw [res_comp, tripleSections_eq_awayToSection]
  rfl

/-- The empty horizontal index retains the chosen homogeneous coordinate
cocycle and its actual first face, including its sign. -/
theorem selectedTriple_rightFinite (r : ℂ)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    selectedTriple (coordinateFamily r)
      (rightFinite (surfaceGrade r 1) (coverElement r 1) (coordinateCover r) d.val) 0 1 2 =
      tripleSections r 1 (homogeneousCoordinateRepresentative r dH) := by
  have hv := congrArg Subtype.val hR
  change (homogeneousRightEmpty (surfaceGrade r 1)
    (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
    (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).map2 d.val = dH.val at hv
  change selectedTriple (coordinateFamily r)
    (CycleQ2FourToFiniteCech.extendTwo (coordinateFamily r)
      (rightFourSections (surfaceGrade r 1) (coverElement r 1) (coordinateCover r) d.val))
        0 1 2 = _
  rw [rightFourSections_eq_single (surfaceGrade r 1)
    (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
    (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r), hv]
  exact selectedTriple_singleCoordinate r dH

/-- On the actual weighted projective surface, the finite injective class
of the retained coordinate cocycle equals its genuine global
Mayer--Vietoris image. The comparison has positive normalization. -/
theorem rightFiniteClass_global_eq (r : ℂ)
    (hcover : (⨆ i, family (surfaceGrade r 1) (coordinateCover r) i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r 1))
      (structureAdditiveSheaf (projectiveSurface r 1)) ⊤ isTerminalTop 2
        (rightFiniteClass (surfaceGrade r 1)
          (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
          (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r) hcover d) =
      globalConnecting r 1 one_ne_zero (homogeneousCoordinateRepresentative r dH) := by
  exact finite_coordinate_global_eq r hcover _
    (rightFinite_normalized (surfaceGrade r 1) (coverElement r 1) (coordinateCover r) d.val)
    (rightFinite_closed (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r) hcover d)
    (homogeneousCoordinateRepresentative r dH) (selectedTriple_rightFinite r d dH hR)

/-- The minus sign comes from the original second-descent diagonal,
and is retained on the same chosen homogeneous coordinate representative. -/
theorem rightFiniteClass_neg_global_eq (r : ℂ)
    (hcover : (⨆ i, family (surfaceGrade r 1) (coordinateCover r) i) = ⊤)
    (d : TwoCocycles ((homogeneousBiSystem (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).right ∅))
    (dH : TwoCocycles (homogeneousCoordinateSystem r))
    (hR : (homogeneousRightEmpty (surfaceGrade r 1)
      (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
      (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle d = dH) :
    terminalCohomologyEquiv (Opens.grothendieckTopology (projectiveSurface r 1))
      (structureAdditiveSheaf (projectiveSurface r 1)) ⊤ isTerminalTop 2
        (rightFiniteClass (surfaceGrade r 1)
          (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
          (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r) hcover (-d)) =
      globalConnecting r 1 one_ne_zero (-homogeneousCoordinateRepresentative r dH) := by
  apply rightFiniteClass_global_eq r hcover (-d) (-dH)
  let f := (homogeneousRightEmpty (surfaceGrade r 1)
    (coverElement r 1) coverDegree (coverElement_mem_grade r 1)
    (coordinateCover r) (fun _ => 1) (coordinateCover_mem_grade r)).mapCycle
  have hf : f (-d) = -(f d) := _root_.map_neg f d
  have he : -(f d) = -dH :=
    congrArg (fun z : TwoCocycles (homogeneousCoordinateSystem r) => -z) hR
  exact hf.trans he


end CycleQ2CoordinateMVBinding

#print axioms CycleQ2CoordinateMVBinding.finite_coordinate_global_eq

#print axioms CycleQ2CoordinateMVBinding.rightFiniteClass_global_eq
#print axioms CycleQ2CoordinateMVBinding.rightFiniteClass_neg_global_eq

end
end CoordinateMayerVietoris

section LiteralDescent

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralProjectiveDescent

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricFourOpenCech CycleQ2GeometricHomogeneousPrincipal
  CycleQ2ProjectiveMixedSections CycleQ2CartierSurfaceGrading
  CycleQ2GeometricCartierNormalLift CycleQ2GeometricCartierCech
  CycleQ2CartierProjectiveCover CycleQ2ProjectiveCartierIntersections
  CycleQ2ProjectiveCartierDerived CycleQ2ProjectiveCoordinateCohomology

/-- Equality of the actual finite cocycles suffices; the normalization and
closedness witnesses are propositions and do not change the class. -/
theorem finiteClass_congr {X : TopCat.{0}} {ι : Type} [Fintype ι]
    {F : CycleQ2InjectiveCech.AbSheaf X} (U : ι → Opens X)
    (hcover : (⨆ i, U i) = ⊤)
    (c c' : CycleQ2FiniteInjectiveCech.Two F U)
    (hn : CycleQ2FiniteInjectiveCech.NormalizedTwo F U c)
    (hn' : CycleQ2FiniteInjectiveCech.NormalizedTwo F U c')
    (hc : CycleQ2FiniteInjectiveCech.IsTwoCocycle F U c)
    (hc' : CycleQ2FiniteInjectiveCech.IsTwoCocycle F U c')
    (h : c = c') :
    CycleQ2FiniteCechDescent.cechTwoClass U hcover c hn hc =
      CycleQ2FiniteCechDescent.cechTwoClass U hcover c' hn' hc' := by
  subst c'
  rfl

abbrev literalSystem :=
  homogeneousBiSystem (surfaceGrade 57 1) (coverElement 57 1) coverDegree
    (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57)

abbrev literalLeftEmpty :=
  homogeneousLeftEmpty (surfaceGrade 57 1) (coverElement 57 1) coverDegree
    (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57)

abbrev literalRightEmpty :=
  homogeneousRightEmpty (surfaceGrade 57 1) (coverElement 57 1) coverDegree
    (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57)

/-- The original three coordinate opens, with the empty fourth member,
cover the actual literal surface. -/
theorem literalCoordinateCover :
    (⨆ i, family (surfaceGrade 57 1) (coordinateCover 57) i) = ⊤ := by
  apply top_le_iff.mp
  rw [← coordinate_cover 57 1 (by norm_num)]
  apply iSup_le
  intro i
  apply le_iSup_of_le i.castSucc
  fin_cases i <;> exact le_rfl

/-- The four named Cartier sections retain their exact Proj normalization. -/
theorem singleFourSections_literal :
    singleFourSections (surfaceGrade 57 1) (coverElement 57 1)
      literalHomogeneousCartierCycle.val = literalCocycle := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · rfl
  · simp only [singleFourSections, literalHomogeneousCartierCycle, literalCocycle,
      toTwo, CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain, map_zero]
  · simp only [singleFourSections, literalHomogeneousCartierCycle, literalCocycle,
      toTwo, CycleQ2ProjectiveCartierCochain.literalProjectiveCartierCochain, map_zero]

local instance literalProjectiveHasExt :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology (projectiveSurface 57 1)) AddCommGrpCat.{0}) :=
  HasExt.standard _

abbrev literalLeftClass (c : TwoCocycles (literalSystem.left ∅)) :=
  leftFiniteClass (surfaceGrade 57 1) (coverElement 57 1) coverDegree
    (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57) literal_cover c

abbrev literalRightClass (d : TwoCocycles (literalSystem.right ∅)) :=
  rightFiniteClass (surfaceGrade 57 1) (coverElement 57 1) coverDegree
    (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57) literalCoordinateCover d

/-- The left endpoint is exactly the previously constructed derived
Cartier class. No scalar matching or choice of a substitute class occurs. -/
theorem literalLeftClass_eq (c : TwoCocycles (literalSystem.left ∅))
    (hc : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle) :
    literalLeftClass c = literalDerivedClassAtTop := by
  have hc' := congrArg Subtype.val hc
  change literalLeftEmpty.map2 c.val = literalHomogeneousCartierCycle.val at hc'
  have hsections := (leftFourSections_eq_single (surfaceGrade 57 1) (coverElement 57 1)
    coverDegree (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
    (coordinateCover_mem_grade 57) c.val).trans
      ((congrArg (singleFourSections (surfaceGrade 57 1) (coverElement 57 1)) hc').trans
        singleFourSections_literal)
  have hfinite :
      leftFinite (surfaceGrade 57 1) (coverElement 57 1) (coordinateCover 57) c.val =
        CycleQ2LiteralCechRefinement.literalFiniteCocycle :=
    congrArg (CycleQ2FourToFiniteCech.extendTwo
      (family (surfaceGrade 57 1) (coverElement 57 1))) hsections
  exact (finiteClass_congr (coverFamily 57 1) literal_cover _ _
    (leftFinite_normalized (surfaceGrade 57 1) (coverElement 57 1) (coordinateCover 57) c.val)
    CycleQ2LiteralCechRefinement.literalFiniteCocycle_normalized
    (leftFinite_closed (surfaceGrade 57 1) (coverElement 57 1) coverDegree
      (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
      (coordinateCover_mem_grade 57) literal_cover c)
    CycleQ2LiteralCechRefinement.literalFiniteCocycle_closed hfinite).trans
      CycleQ2LiteralCechRefinement.literalFiniteClass_eq

/-- The same homogeneous staircase preserves the literal derived class,
with its exact negative coordinate endpoint. -/
theorem literal_secondDescent_class
    (c : TwoCocycles (literalSystem.left ∅)) (d : TwoCocycles (literalSystem.right ∅))
    (hc : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    literalDerivedClassAtTop = literalRightClass (-d) :=
  (literalLeftClass_eq c hc).symm.trans
    (secondDescent_finiteClass (surfaceGrade 57 1) (coverElement 57 1) coverDegree
      (coverElement_mem_grade 57 1) (coordinateCover 57) (fun _ => 1)
      (coordinateCover_mem_grade 57) literal_cover literalCoordinateCover c d hcd)

/-- A closed retained descent: the original Cartier cocycle, its actual
homogeneous coordinate descendant, and both mixed endpoints are supplied
with their exact ordinary descent and their equality in derived cohomology. -/
theorem literal_retained_projective_descent :
    ∃ dH : TwoCocycles (homogeneousCoordinateSystem 57),
    ∃ c : TwoCocycles (literalSystem.left ∅),
    ∃ d : TwoCocycles (literalSystem.right ∅),
      literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle ∧
      literalRightEmpty.mapCycle d = dH ∧
      literalSystem.SecondDescent c.val d.val ∧
      literalDerivedClassAtTop = literalRightClass (-d) ∧
      CartierCoordinateDescent 57 (cartierCycle 57 1 CycleQ2NormalConnecting.derivativeA 0)
        (forgetCoordinateCycle 57 dH) := by
  obtain ⟨dH,hD⟩ := exists_homogeneous_second_descent (surfaceGrade 57 1)
    (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1) coverDegree_pos literal_cover
    (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57)
    (fun _ => by decide) literalHomogeneousCartierCycle
  have ho := CycleQ2CanonicalProjectedCoordinate.literal_homogeneous_descent_to_ordinary dH hD
  obtain ⟨c,d,hc,hd,hcd⟩ := hD
  exact ⟨dH,c,d,hc,hd,hcd,literal_secondDescent_class c d hc hcd,ho⟩

end CycleQ2LiteralProjectiveDescent

#print axioms CycleQ2LiteralProjectiveDescent.literalCoordinateCover
#print axioms CycleQ2LiteralProjectiveDescent.singleFourSections_literal
#print axioms CycleQ2LiteralProjectiveDescent.literalLeftClass_eq
#print axioms CycleQ2LiteralProjectiveDescent.literal_retained_projective_descent

end
end LiteralDescent

section LiteralGlobalEndpoint

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralProjectiveDescent

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricFourOpenCech CycleQ2GeometricHomogeneousPrincipal
  CycleQ2GeometricCartierCech CycleQ2CartierSurfaceGrading
  CycleQ2GeometricCartierNormalLift CycleQ2CartierProjectiveCover
  CycleQ2ProjectiveCartierDerived CycleQ2ProjectiveCoordinateH2
  CycleQ2CoordinateMVBinding CycleQ2GeometricHomogeneousWeight
  CycleQ2GeometricCoordinateCharacter CycleQ2GeometricSurfaceCoordinates
  CycleQ2GeometricLaurentTop
  CycleQ2GeometricSeedNormalIdeals CycleQ2NormalConnecting
  CycleQ2CanonicalProjectedCoordinate

/-- The original Cartier class in ordinary derived cohomology is the
genuine global connecting image of the negative of the same retained
homogeneous coordinate representative. -/
theorem literalDerivedClass_eq_signed_coordinate
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (c : TwoCocycles (literalSystem.left ∅))
    (d : TwoCocycles (literalSystem.right ∅))
    (hL : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hR : literalRightEmpty.mapCycle d = dH)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    literalDerivedClass = globalConnecting 57 1 one_ne_zero
      (-homogeneousCoordinateRepresentative 57 dH) := by
  have htop := literal_secondDescent_class c d hL hcd
  have hleft : literalDerivedClass = literalTerminalCohomologyEquiv (literalRightClass (-d)) :=
    congrArg literalTerminalCohomologyEquiv htop
  have hright : literalTerminalCohomologyEquiv (literalRightClass (-d)) =
      globalConnecting 57 1 one_ne_zero (-homogeneousCoordinateRepresentative 57 dH) :=
    rightFiniteClass_neg_global_eq 57 literalCoordinateCover d dH hR
  exact hleft.trans hright

/-- This nonvanishing statement concerns the unprojected representative
identified with the original Cartier class. -/
theorem literal_signed_coordinate_ne_zero
    (dH : TwoCocycles (homogeneousCoordinateSystem 57))
    (c : TwoCocycles (literalSystem.left ∅))
    (d : TwoCocycles (literalSystem.right ∅))
    (hL : literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle)
    (hR : literalRightEmpty.mapCycle d = dH)
    (hcd : literalSystem.SecondDescent c.val d.val) :
    globalConnecting 57 1 one_ne_zero (-homogeneousCoordinateRepresentative 57 dH) ≠ 0 := by
  rw [← literalDerivedClass_eq_signed_coordinate dH c d hL hR hcd]
  exact literalDerivedClass_ne_zero

/-- A closed result retaining the actual homogeneous staircase and its
ordinary coordinate descent. The equality refers to the unprojected
Cartier class; the final assertion is a separate nonvanishing statement
for its coordinate character-one projection. The fixed cubic coefficient
is evaluated on this same chosen representative. -/
theorem literal_retained_global_descent :
    ∃ dH : TwoCocycles (homogeneousCoordinateSystem 57),
    ∃ c : TwoCocycles (literalSystem.left ∅),
    ∃ d : TwoCocycles (literalSystem.right ∅),
      literalLeftEmpty.mapCycle c = literalHomogeneousCartierCycle ∧
      literalRightEmpty.mapCycle d = dH ∧
      literalSystem.SecondDescent c.val d.val ∧
      CartierCoordinateDescent 57 (cartierCycle 57 1 derivativeA 0)
        (forgetCoordinateCycle 57 dH) ∧
      literalDerivedClass = globalConnecting 57 1 one_ne_zero
        (-homogeneousCoordinateRepresentative 57 dH) ∧
      globalConnecting 57 1 one_ne_zero (-homogeneousCoordinateRepresentative 57 dH) ≠ 0 ∧
      (coordinateLaurent 57 Finset.univ
        (surfaceQuotient 57 1 detectorCubic •
          (homogeneousCoordinateRepresentative 57 dH).val) (2,2)).coeff
            (fun _ => -1) ≠ 0 ∧
      globalConnecting 57 1 one_ne_zero
        (homogeneousProject 57 1 (-homogeneousCoordinateRepresentative 57 dH)) ≠ 0 := by
  obtain ⟨dH,c,d,hL,hR,hcd,_htop,ho⟩ := literal_retained_projective_descent
  have hD : HomogeneousSecondDescent (surfaceGrade 57 1)
      (coverElement 57 1) coverDegree (coverElement_mem_grade 57 1)
      (coordinateCover 57) (fun _ => 1) (coordinateCover_mem_grade 57)
      literalHomogeneousCartierCycle dH := ⟨c,d,hL,hR,hcd⟩
  refine ⟨dH,c,d,hL,hR,hcd,ho,
    literalDerivedClass_eq_signed_coordinate dH c d hL hR hcd,
    literal_signed_coordinate_ne_zero dH c d hL hR hcd, ?_,
    literal_homogeneous_signed_globalConnecting_ne_zero dH hD⟩
  exact literal_homogeneous_cubic_coefficient (forgetCoordinateCycle 57 dH) ho
    (homogeneousCoordinateRepresentative 57 dH) (homogeneousCoordinateRepresentative_val 57 dH)

end CycleQ2LiteralProjectiveDescent

#print axioms CycleQ2LiteralProjectiveDescent.literalDerivedClass_eq_signed_coordinate
#print axioms CycleQ2LiteralProjectiveDescent.literal_signed_coordinate_ne_zero
#print axioms CycleQ2LiteralProjectiveDescent.literal_retained_global_descent

end
end LiteralGlobalEndpoint
