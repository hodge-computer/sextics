import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricLiteralAmbientProjFiberPolynomial
import Proposal.GeometricGradedAwaySpecialization
import Proposal.GeometricChartSectionPullback
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The sole Laurent coefficient of a global degree-zero section

With no poles and weighted degree zero, the cubic generator has exponent
zero and all four weight-one exponents vanish. Thus the actual global
structure-sheaf coordinates are determined by one original coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeTwistConstantSections

open CycleQ2HodgeTwistCech

private theorem allowed_zero_iff (j : Fin 3) (e : Exp) :
    Allowed 0 ∅ j e ↔ j = 0 ∧ e = 0 := by
  constructor
  · intro h
    have he (i : Vertex) : 0 ≤ e i := by
      by_contra hn
      have hm := h.2 i (lt_of_not_ge hn)
      simpa using hm
    have hs : 0 ≤ ∑ i : Vertex, e i := Finset.sum_nonneg (fun i _ => he i)
    have hw := h.1
    have hj : j = 0 := Fin.ext (by omega)
    have hsum : ∑ i : Vertex, e i = 0 := by
      have hw := h.1
      have hv : (j.val : ℤ) = 0 := by rw [hj]; rfl
      omega
    refine ⟨hj, funext fun i => ?_⟩
    have hi : e i ≤ ∑ k : Vertex, e k :=
      Finset.single_le_sum (fun k _ => he k) (Finset.mem_univ i)
    change e i = 0
    rw [hsum] at hi
    exact le_antisymm hi (he i)
  · rintro ⟨rfl,rfl⟩
    simp [Allowed]

variable {A : Type} [AddCommGroup A]

def constant (a : A) : sections A 0 ∅ := by
  classical
  refine ⟨fun j => if j = 0 then Finsupp.single 0 a else 0, ?_⟩
  intro j e hn
  by_cases hj : j = 0
  · subst j
    have he : e ≠ 0 := by
      intro h
      exact hn ((allowed_zero_iff 0 e).mpr ⟨rfl,h⟩)
    simp [he]
  · simp [hj]

def coefficient : sections A 0 ∅ →+ A where
  toFun p := p.val 0 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem coefficient_constant (a : A) : coefficient (constant a) = a := by
  change (constant a).val 0 0 = a
  simp [constant]

theorem constant_coefficient (p : sections A 0 ∅) : constant (coefficient p) = p := by
  classical
  apply Subtype.ext
  funext j
  apply Finsupp.ext
  intro e
  by_cases hj : j = 0
  · subst j
    by_cases he : e = 0
    · subst e
      exact (show (constant (coefficient p)).val 0 0 = coefficient p from
        coefficient_constant (coefficient p)).trans (by rfl)
    · have hp : p.val 0 e = 0 := p.property 0 e ((allowed_zero_iff 0 e).not.mpr (by simp [he]))
      simp [constant, he, hp]
  · have hp : p.val j e = 0 := p.property j e ((allowed_zero_iff j e).not.mpr (by simp [hj]))
    simp [constant, hj, hp]

/-- The actual polynomial normal forms in weighted degree zero have one coefficient. -/
def degreeZeroEquiv : sections A 0 ∅ ≃+ A :=
  AddEquiv.ofBijective coefficient ⟨fun p q h =>
    (constant_coefficient p).symm.trans ((congrArg constant h).trans (constant_coefficient q)),
      fun a => ⟨constant a, coefficient_constant a⟩⟩

open CategoryTheory AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen vertexCoefficient)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2HodgeTwistTorusChart (structureLaurentSections)

/-- The original structure-sheaf global sections are determined by this coefficient.
This assertion includes the actual Laurent/gluing comparison; it does not identify
an arbitrary additive equivalence with a ring or module structure. -/
def structureSections {R : Type} [CommRing R] [Nontrivial R]
    (φ : CoeffRing →+* R) (h : IsUnit (φ vertexCoefficient)) :
    CycleQ2InjectiveCech.Sections (structureAdditiveSheaf (threefold φ)) ⊤ ≃+ R :=
  (CycleQ2HodgeTwistGlobal.globalCoordinates (structureLaurentSections φ h)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)).trans degreeZeroEquiv

end CycleQ2HodgeTwistConstantSections
end

#print axioms CycleQ2HodgeTwistConstantSections.constant_coefficient
#print axioms CycleQ2HodgeTwistConstantSections.structureSections

/-!
## Actual coefficient change and the top Laurent trace

The morphism is induced by coefficient change on the original homogeneous
quotient. Its section map is the scheme's own `appLE`. The comparison with
Laurent coordinates is proved by mapping the original homogeneous fractions.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistCoefficientChange

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
  HomogeneousLocalization MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight PolynomialGrade)
open CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeTwistCech (Vertex Exp NormalForm sections)
open CycleQ2HodgeTwistAnchor (torus torus_le torus_le_face commonCoefficient)
open CycleQ2HodgeTwistRatios (normalized ratio transition)
open CycleQ2HodgeTwistMonomials (units weightTwo monomial evaluate)
open CycleQ2GradedAwaySpecialization (awayMapOfEq awayMapOfEq_mk)
open CycleQ2HodgeTwistTorusChart (structureLaurentSections structureTopSectionTrace)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)

variable {R S : Type} [CommRing R] [CommRing S]
  (φ : CoeffRing →+* R) (ρ : R →+* S)

theorem equation_map : MvPolynomial.map ρ (equation φ) = equation (ρ.comp φ) := by
  rw [equation, equation, MvPolynomial.map_map]

private theorem equation_ideal_map :
    (Ideal.span {equation φ}).map (MvPolynomial.map ρ) =
      Ideal.span {equation (ρ.comp φ)} := by
  rw [Ideal.map_span, Set.image_singleton, equation_map]

/-- Coefficient change on the unchanged weighted homogeneous quotient. -/
def gradedMap : grade φ →+*ᵍ grade (ρ.comp φ) :=
  CycleQ2LiteralAmbientProjFiberPolynomial.graded ρ
    (Ideal.span {equation φ}) (Ideal.span {equation (ρ.comp φ)})
    (equation_ideal_map φ ρ)

@[simp] theorem gradedMap_quotient (p : MvPolynomial (Fin 5) R) :
    gradedMap φ ρ (quotient φ p) = quotient (ρ.comp φ) (MvPolynomial.map ρ p) := rfl

@[simp] theorem gradedMap_coord (i : Fin 5) :
    gradedMap φ ρ (coord φ i) = coord (ρ.comp φ) i := by
  change quotient (ρ.comp φ) (MvPolynomial.map ρ (X i)) = quotient (ρ.comp φ) (X i)
  rw [MvPolynomial.map_X]

theorem gradedMap_irrelevant : HomogeneousIdeal.irrelevant (grade (ρ.comp φ)) ≤
    (HomogeneousIdeal.irrelevant (grade φ)).map (gradedMap φ ρ) := by
  apply toIdeal_le_toIdeal_iff.mp
  apply (HomogeneousIdeal.toIdeal_irrelevant_le (grade (ρ.comp φ))).mpr
  rintro n hn _ ⟨p,hp,rfl⟩
  let J := ((HomogeneousIdeal.irrelevant (grade φ)).map (gradedMap φ ρ)).toIdeal
  have hvars : Ideal.span (Set.range (X : Fin 5 → MvPolynomial (Fin 5) S)) ≤
      J.comap (quotient (ρ.comp φ)) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change coord (ρ.comp φ) i ∈ J
    rw [← gradedMap_coord φ ρ i]
    exact Ideal.mem_map_of_mem (gradedMap φ ρ)
      (HomogeneousIdeal.mem_irrelevant_of_mem (grade φ)
        (CycleQ2IncidenceFamilyContainment.geometricWeight_pos i) (coord_mem_grade φ i))
  exact hvars (CycleQ2IncidenceFamilyContainment.homogeneous_mem_variableIdeal hn hp)

/-- The actual projective morphism induced by the given coefficient map. -/
def morphism : threefold (ρ.comp φ) ⟶ threefold φ :=
  Proj.map (gradedMap φ ρ) (gradedMap_irrelevant φ ρ)

@[simp] theorem morphism_preimage_coordinate (i : Vertex) :
    morphism φ ρ ⁻¹ᵁ coordinateOpen φ i = coordinateOpen (ρ.comp φ) i := by
  change Proj.map (gradedMap φ ρ) (gradedMap_irrelevant φ ρ) ⁻¹ᵁ
      Proj.basicOpen (grade φ) (coord φ i.castSucc) = _
  rw [Proj.map_preimage_basicOpen, gradedMap_coord]
  rfl

theorem morphism_preimage_face (B : Finset Vertex) :
    morphism φ ρ ⁻¹ᵁ B.inf (coordinateOpen φ) = B.inf (coordinateOpen (ρ.comp φ)) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp
  | insert i B hi ih =>
    simp only [Finset.inf_insert, Scheme.Hom.preimage_inf, morphism_preimage_coordinate, ih]

theorem morphism_preimage_torus : morphism φ ρ ⁻¹ᵁ torus φ = torus (ρ.comp φ) :=
  morphism_preimage_face φ ρ Finset.univ

/-- Pullback on each original projective intersection, through the actual
scheme morphism rather than an assigned coordinate transformation. -/
def facePullback (B : Finset Vertex) :
    Γ(threefold φ, B.inf (coordinateOpen φ)) →+*
      Γ(threefold (ρ.comp φ), B.inf (coordinateOpen (ρ.comp φ))) :=
  ((morphism φ ρ).appLE _ _ (morphism_preimage_face φ ρ B).ge).hom

def pullback : Γ(threefold φ, torus φ) →+* Γ(threefold (ρ.comp φ), torus (ρ.comp φ)) :=
  facePullback φ ρ Finset.univ

def chartMap (i : Vertex) : ChartRing φ i →+* ChartRing (ρ.comp φ) i :=
  awayMapOfEq (gradedMap φ ρ) (coord φ i.castSucc) (coord (ρ.comp φ) i.castSucc)
    (gradedMap_coord φ ρ i.castSucc)

/-- The actual chart section square, including the proved coordinate equality. -/
theorem chart_section_square (i : Vertex) :
    Proj.awayToSection (grade φ) (coord φ i.castSucc) ≫
      (morphism φ ρ).appLE (coordinateOpen φ i) (coordinateOpen (ρ.comp φ) i)
        (morphism_preimage_coordinate φ ρ i).ge =
      CommRingCat.ofHom (chartMap φ ρ i) ≫
        Proj.awayToSection (grade (ρ.comp φ)) (coord (ρ.comp φ) i.castSucc) := by
  have h (b : cone (ρ.comp φ)) (hb : gradedMap φ ρ (coord φ i.castSucc) = b) :
      Proj.awayToSection (grade φ) (coord φ i.castSucc) ≫
        (morphism φ ρ).appLE (coordinateOpen φ i)
          (Proj.basicOpen (grade (ρ.comp φ)) b) (by
            change Proj.basicOpen (grade (ρ.comp φ)) b ≤
              Proj.map (gradedMap φ ρ) (gradedMap_irrelevant φ ρ) ⁻¹ᵁ
                Proj.basicOpen (grade φ) (coord φ i.castSucc)
            rw [Proj.map_preimage_basicOpen, hb]) =
        CommRingCat.ofHom (awayMapOfEq (gradedMap φ ρ) (coord φ i.castSucc) b hb) ≫
          Proj.awayToSection (grade (ρ.comp φ)) b := by
    subst b
    exact Proj.awayToSection_comp_appLE (gradedMap φ ρ) (gradedMap_irrelevant φ ρ)
      (weightOne_mem_grade φ i)
  exact h _ (gradedMap_coord φ ρ i.castSucc)

/-- Pullback of an original homogeneous fraction on the common torus. -/
theorem pullback_normalized (i : Vertex) {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) :
    pullback φ ρ (normalized φ i p hp (torus φ) (torus_le φ i)) =
      normalized (ρ.comp φ) i (gradedMap φ ρ p) ((gradedMap φ ρ).map_mem hp)
        (torus (ρ.comp φ)) (torus_le (ρ.comp φ) i) := by
  let a : ChartRing φ i := Away.mk (grade φ) (weightOne_mem_grade φ i) n p
    (by simpa using hp)
  have ht := ConcreteCategory.congr_hom (chart_section_square φ ρ i) a
  change (morphism φ ρ).appLE (coordinateOpen φ i) (coordinateOpen (ρ.comp φ) i)
      (morphism_preimage_coordinate φ ρ i).ge
      (Proj.awayToSection (grade φ) (coord φ i.castSucc) a) =
    Proj.awayToSection (grade (ρ.comp φ)) (coord (ρ.comp φ) i.castSucc)
      (chartMap φ ρ i a) at ht
  calc
    _ = (threefold (ρ.comp φ)).presheaf.map (homOfLE (torus_le (ρ.comp φ) i)).op
        ((morphism φ ρ).appLE (coordinateOpen φ i) (coordinateOpen (ρ.comp φ) i)
          (morphism_preimage_coordinate φ ρ i).ge
          (Proj.awayToSection (grade φ) (coord φ i.castSucc) a)) :=
      CycleQ2ChartSectionPullback.restriction_square (morphism φ ρ) (torus_le φ i)
        (morphism_preimage_coordinate φ ρ i).ge (torus_le (ρ.comp φ) i)
        (morphism_preimage_torus φ ρ).ge _
    _ = (threefold (ρ.comp φ)).presheaf.map (homOfLE (torus_le (ρ.comp φ) i)).op
        (Proj.awayToSection (grade (ρ.comp φ)) (coord (ρ.comp φ) i.castSucc)
          (chartMap φ ρ i a)) :=
      congrArg ((threefold (ρ.comp φ)).presheaf.map
        (homOfLE (torus_le (ρ.comp φ) i)).op) ht
    _ = _ := by
      apply congrArg ((threefold (ρ.comp φ)).presheaf.map
        (homOfLE (torus_le (ρ.comp φ) i)).op)
      apply congrArg (Proj.awayToSection (grade (ρ.comp φ)) (coord (ρ.comp φ) i.castSucc))
      exact awayMapOfEq_mk (gradedMap φ ρ) (coord φ i.castSucc)
        (coord (ρ.comp φ) i.castSucc) (gradedMap_coord φ ρ i.castSucc)
        (weightOne_mem_grade φ i) (weightOne_mem_grade (ρ.comp φ) i) n p
        (by simpa using hp)

theorem commonCoefficient_normalized (c : R) :
    commonCoefficient φ c = normalized φ 0 (coefficient φ c).val (coefficient φ c).property
      (torus φ) (torus_le φ 0) := by
  change CycleQ2GeometricProjectiveCurve.Twisted.res (threefold φ).sheaf (torus_le φ 0)
      ((Proj.awayToSection (grade φ) (coord φ 0)) (chartCoefficient φ 0 c)) = _
  rw [CycleQ2HodgeTwistAnchor.coefficient_fraction]
  rfl

theorem pullback_commonCoefficient (c : R) :
    pullback φ ρ (commonCoefficient φ c) = commonCoefficient (ρ.comp φ) (ρ c) := by
  rw [commonCoefficient_normalized, pullback_normalized, commonCoefficient_normalized]
  have hc : gradedMap φ ρ (coefficient φ c).val = (coefficient (ρ.comp φ) (ρ c)).val := by
    change gradedMap φ ρ (quotient φ (MvPolynomial.C c)) =
      quotient (ρ.comp φ) (MvPolynomial.C (ρ c))
    rw [gradedMap_quotient, MvPolynomial.map_C]
  simp only [hc]

theorem pullback_ratio (i j : Vertex) :
    pullback φ ρ (ratio φ i j (torus φ) (torus_le φ i)) =
      ratio (ρ.comp φ) i j (torus (ρ.comp φ)) (torus_le (ρ.comp φ) i) := by
  simpa only [ratio, CycleQ2HodgeTwistRatios.x, gradedMap_coord] using
    pullback_normalized φ ρ i (coord φ j.castSucc) (weightOne_mem_grade φ j)

theorem pullback_transition (i j : Vertex) :
    Units.map (pullback φ ρ).toMonoidHom
      (transition φ i j (torus φ) (torus_le φ i) (torus_le φ j)) =
      transition (ρ.comp φ) i j (torus (ρ.comp φ))
        (torus_le (ρ.comp φ) i) (torus_le (ρ.comp φ) j) :=
  Units.ext (pullback_ratio φ ρ i j)

theorem pullback_units (i : Vertex) (e : Exp) :
    Units.map (pullback φ ρ).toMonoidHom (units φ (torus φ) (torus_le φ) i e) =
      units (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ)) i e := by
  simp only [units, map_prod, map_zpow, pullback_transition]

theorem pullback_weightTwo (i : Vertex) :
    pullback φ ρ (weightTwo φ (torus φ) (torus_le φ) i) =
      weightTwo (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ)) i := by
  simpa only [weightTwo, gradedMap_coord] using
    pullback_normalized φ ρ i (coord φ (Fin.last 4)) (coord_mem_grade φ (Fin.last 4))

theorem pullback_monomial (i : Vertex) (j : Fin 3) (e : Exp) :
    pullback φ ρ (monomial φ (torus φ) (torus_le φ) i j e) =
      monomial (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ)) i j e := by
  unfold monomial
  rw [map_mul, map_pow, pullback_weightTwo]
  exact congrArg (fun u : Γ(threefold (ρ.comp φ),torus (ρ.comp φ))ˣ =>
    u.val * weightTwo (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ)) i ^ j.val)
      (pullback_units φ ρ i e)

/-- Change just the coefficients of a finite Laurent normal form. -/
def normalFormMap : NormalForm R →+ NormalForm S where
  toFun p j := Finsupp.mapRange ρ (map_zero ρ) (p j)
  map_zero' := by
    funext j
    exact Finsupp.mapRange_zero
  map_add' p q := by
    funext j
    apply Finsupp.ext
    intro e
    exact map_add ρ (p j e) (q j e)

/-- Allowed exponents and weighted degrees are unchanged by coefficient change. -/
def sectionsMap {t : ℤ} (B : Finset Vertex) : sections R t B →+ sections S t B where
  toFun p := ⟨normalFormMap ρ p.val, by
    intro j e he
    change ρ (p.val j e) = 0
    rw [p.property j e he, map_zero]⟩
  map_zero' := Subtype.ext (map_zero (normalFormMap ρ))
  map_add' p q := Subtype.ext (map_add (normalFormMap ρ) p.val q.val)

@[simp] theorem sectionsMap_apply {t : ℤ} (B : Finset Vertex)
    (p : sections R t B) (j : Fin 3) (e : Exp) :
    (sectionsMap ρ B p).val j e = ρ (p.val j e) := rfl

/-- Mapping every original homogeneous fraction equals coefficient change
of its finite normal form, for arbitrary coefficient maps. -/
theorem pullback_evaluate (i : Vertex) (p : NormalForm R) :
    pullback φ ρ (evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) i p) =
      evaluate (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ))
        (commonCoefficient (ρ.comp φ)) i (normalFormMap ρ p) := by
  classical
  rw [evaluate, map_sum, evaluate]
  apply Finset.sum_congr rfl
  intro j _
  change pullback φ ρ ((p j).sum (fun e c => commonCoefficient φ c *
      monomial φ (torus φ) (torus_le φ) i j e)) =
    (Finsupp.mapRange ρ (map_zero ρ) (p j)).sum (fun e c =>
      commonCoefficient (ρ.comp φ) c *
        monomial (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ)) i j e)
  rw [Finsupp.sum_mapRange_index (fun _ => by rw [map_zero, zero_mul])]
  simp only [Finsupp.sum, map_sum, map_mul, pullback_commonCoefficient, pullback_monomial]

theorem pullback_restrict_face (B : Finset Vertex)
    (s : Γ(threefold φ, B.inf (coordinateOpen φ))) :
    pullback φ ρ ((threefold φ).presheaf.map (homOfLE (torus_le_face φ B)).op s) =
      (threefold (ρ.comp φ)).presheaf.map
        (homOfLE (torus_le_face (ρ.comp φ) B)).op (facePullback φ ρ B s) :=
  CycleQ2ChartSectionPullback.restriction_square (morphism φ ρ) (torus_le_face φ B)
    (morphism_preimage_face φ ρ B).ge (torus_le_face (ρ.comp φ) B)
    (morphism_preimage_torus φ ρ).ge s

def topFacesPullback
    (c : CycleQ2HodgeTwistCoordinates.NativeTopFaces
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ)) :
    CycleQ2HodgeTwistCoordinates.NativeTopFaces
      (F := structureAdditiveSheaf (threefold (ρ.comp φ))) (U := coordinateOpen (ρ.comp φ)) :=
  fun i => facePullback φ ρ (Finset.univ.erase i) (c i)

/-- Coefficient change preserves the original alternating triple-section
boundary through the actual restriction square. -/
theorem pullback_topBoundary
    (c : CycleQ2HodgeTwistCoordinates.NativeTopFaces
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ)) :
    pullback φ ρ (CycleQ2HodgeTwistCoordinates.nativeTopBoundary c) =
      CycleQ2HodgeTwistCoordinates.nativeTopBoundary (topFacesPullback φ ρ c) := by
  change pullback φ ρ
    ((threefold φ).presheaf.map (homOfLE (torus_le_face φ (Finset.univ.erase 0))).op (c 0) -
      (threefold φ).presheaf.map (homOfLE (torus_le_face φ (Finset.univ.erase 1))).op (c 1) +
      (threefold φ).presheaf.map (homOfLE (torus_le_face φ (Finset.univ.erase 2))).op (c 2) -
      (threefold φ).presheaf.map (homOfLE (torus_le_face φ (Finset.univ.erase 3))).op (c 3)) = _
  rw [map_sub, map_add, map_sub, pullback_restrict_face, pullback_restrict_face,
    pullback_restrict_face, pullback_restrict_face]
  rfl

/-- The induced map of native top section quotients is obtained from the
scheme section map and the proved preservation of boundaries. -/
def topQuotientPullback :
    CycleQ2HodgeTwistCoordinates.NativeTopQuotient
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ) →+
    CycleQ2HodgeTwistCoordinates.NativeTopQuotient
      (F := structureAdditiveSheaf (threefold (ρ.comp φ))) (U := coordinateOpen (ρ.comp φ)) :=
  QuotientAddGroup.map _ _ (pullback φ ρ).toAddMonoidHom (by
    rintro _ ⟨c,rfl⟩
    exact ⟨topFacesPullback φ ρ c, (pullback_topBoundary φ ρ c).symm⟩)

variable [Nontrivial R] [Nontrivial S] (h : IsUnit (φ vertexCoefficient))

/-- The Laurent coordinates commute with the actual scheme section
pullback. The proof uses the homogeneous-fraction calculation above. -/
theorem topCoordinates_pullback (s : Γ(threefold φ,torus φ)) :
    CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
        (structureLaurentSections (ρ.comp φ) (h.map ρ)) (pullback φ ρ s) =
      sectionsMap ρ Finset.univ
        (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h) s) := by
  let p := CycleQ2HodgeTwistCoordinates.nativeTopCoordinates (structureLaurentSections φ h) s
  let q := sectionsMap ρ Finset.univ p
  let e := CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
    (structureLaurentSections (ρ.comp φ) (h.map ρ))
  apply e.symm.injective
  change e.symm (e (pullback φ ρ s)) = e.symm q
  rw [AddEquiv.symm_apply_apply]
  have hq := CycleQ2HodgeTwistTorusChart.structureTopCoordinates_evaluate
    (ρ.comp φ) (h.map ρ) (e.symm q)
  change e.symm q = evaluate (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ))
    (commonCoefficient (ρ.comp φ)) 0 (e (e.symm q)).val at hq
  rw [AddEquiv.apply_symm_apply] at hq
  calc
    pullback φ ρ s = pullback φ ρ
        (evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 p.val) :=
      congrArg (pullback φ ρ)
        (CycleQ2HodgeTwistTorusChart.structureTopCoordinates_evaluate φ h s)
    _ = evaluate (ρ.comp φ) (torus (ρ.comp φ)) (torus_le (ρ.comp φ))
        (commonCoefficient (ρ.comp φ)) 0 q.val := pullback_evaluate φ ρ 0 p.val
    _ = e.symm q := hq.symm

/-- The top trace is coefficient-natural for the original projective
scheme morphism and its genuine pullback of structure sections. -/
theorem structureTopSectionTrace_pullback (s : Γ(threefold φ,torus φ)) :
    structureTopSectionTrace (ρ.comp φ) (h.map ρ) (pullback φ ρ s) =
      ρ (structureTopSectionTrace φ h s) := by
  change CycleQ2HodgeTwistCech.topCoefficient
      (CycleQ2HodgeTwistCoordinates.nativeTopCoordinates
        (structureLaurentSections (ρ.comp φ) (h.map ρ)) (pullback φ ρ s)) = _
  rw [topCoordinates_pullback φ ρ h]
  rfl

theorem structureTopTrace_pullback
    (z : CycleQ2HodgeTwistCoordinates.NativeTopQuotient
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ)) :
    CycleQ2HodgeTwistTorusChart.structureTopTraceEquiv (ρ.comp φ) (h.map ρ)
        (topQuotientPullback φ ρ z) =
      ρ (CycleQ2HodgeTwistTorusChart.structureTopTraceEquiv φ h z) := by
  refine QuotientAddGroup.induction_on z ?_
  intro s
  exact structureTopSectionTrace_pullback φ ρ h s

/-- A nonzero trace after any coefficient specialization already detects
a nonzero original coefficient. -/
theorem trace_ne_zero_of_pullback (s : Γ(threefold φ,torus φ))
    (hs : structureTopSectionTrace (ρ.comp φ) (h.map ρ) (pullback φ ρ s) ≠ 0) :
    structureTopSectionTrace φ h s ≠ 0 := by
  intro hz
  apply hs
  rw [structureTopSectionTrace_pullback, hz, map_zero]

variable [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]

/-- For an actual section over an integral coefficient ring, a nonzero
specialized trace remains nonzero over its fraction field. This is proved
on the original fractions, without a cohomology base-change hypothesis. -/
theorem generic_trace_ne_zero_of_pullback (s : Γ(threefold φ,torus φ))
    (hs : structureTopSectionTrace (ρ.comp φ) (h.map ρ) (pullback φ ρ s) ≠ 0) :
    structureTopSectionTrace ((algebraMap R K).comp φ) (h.map (algebraMap R K))
      (pullback φ (algebraMap R K) s) ≠ 0 := by
  rw [structureTopSectionTrace_pullback]
  intro hz
  apply trace_ne_zero_of_pullback φ ρ h s hs
  exact (IsFractionRing.injective R K) (hz.trans (map_zero (algebraMap R K)).symm)

/-- The same conclusion on the genuine native section quotient. The input
is the given relative class; no new class or transport property is supplied. -/
theorem generic_class_ne_zero_of_pullback
    (z : CycleQ2HodgeTwistCoordinates.NativeTopQuotient
      (F := structureAdditiveSheaf (threefold φ)) (U := coordinateOpen φ))
    (hz : CycleQ2HodgeTwistTorusChart.structureTopTraceEquiv (ρ.comp φ) (h.map ρ)
      (topQuotientPullback φ ρ z) ≠ 0) :
    topQuotientPullback φ (algebraMap R K) z ≠ 0 := by
  intro he
  have ha : CycleQ2HodgeTwistTorusChart.structureTopTraceEquiv φ h z = 0 := by
    apply IsFractionRing.injective R K
    rw [map_zero, ← structureTopTrace_pullback φ (algebraMap R K) h z, he, map_zero]
  apply hz
  rw [structureTopTrace_pullback, ha, map_zero]

end CycleQ2HodgeTwistCoefficientChange
end

#print axioms CycleQ2HodgeTwistCoefficientChange.pullback_normalized
#print axioms CycleQ2HodgeTwistCoefficientChange.structureTopSectionTrace_pullback
#print axioms CycleQ2HodgeTwistCoefficientChange.generic_trace_ne_zero_of_pullback
#print axioms CycleQ2HodgeTwistCoefficientChange.generic_class_ne_zero_of_pullback

/-!
## The normalized residue in actual derived H³

The four coordinate opens and every nonempty intersection are affine.
Their original twist frames supply all the local vanishing groups used
by the three Mayer--Vietoris boundaries, over the original coefficient
ring, with no smoothness or cohomology base-change assumption.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeTwistTopCohomology

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold vertexCoefficient coordinateOpen)
open CycleQ2HodgeThreefoldTwist (twist chartFrame cocycle)
open CycleQ2HodgeTwistTorusChart (F nativeLaurentSections structureLaurentSections
  structureTopSectionTrace structureTopGenerator)
open CycleQ2HodgeTwistAnchor (torus)
open CycleQ2HodgeTwistCech (Vertex)
open CycleQ2HodgeTwistTopDerived
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricSheafLocalIso (PatchIso)
open CycleQ2GeometricProjectiveHOne (overIsoOfPatchIso)

local instance (X : TopCat.{0}) : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf X) := HasExt.standard _

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)
  (h : IsUnit (φ vertexCoefficient))

private theorem intersection_affine (S : Finset Vertex) (hS : S.Nonempty) :
    IsAffineOpen (S.inf (coordinateOpen φ)) := by
  obtain ⟨i,hi⟩ := hS
  rw [← CycleQ2HodgeTwistFaces.face_inf φ i S hi]
  exact CycleQ2HodgeTwistFaces.face_affine φ i _

/-- All positive cohomology of the actual structure sheaf vanishes on
every standard nonempty affine intersection. -/
theorem structure_face_acyclic :
    FaceAcyclic (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ) := by
  intro S hS n
  let W := S.inf (coordinateOpen φ)
  exact CycleQ2GeometricAffineHThree.frame_subsingleton
    (intersection_affine φ S hS).isoSpec (structureAdditiveSheaf (threefold φ))
    (Iso.refl _) (n+1) (CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton n Γ(threefold φ,W))

/-- The same local vanishing for every actual integral twist, using its
original chart frame on each affine intersection. -/
theorem twist_face_acyclic (k : ℤ) : FaceAcyclic (F φ k) (coordinateOpen φ) := by
  intro S hS n
  obtain ⟨i,hi⟩ := hS
  let W := S.inf (coordinateOpen φ)
  have hWi : W ≤ coordinateOpen φ i := Finset.inf_le hi
  let fr : PatchIso (F φ k) (structureAdditiveSheaf (threefold φ)) W :=
    { app := fun V hV => (chartFrame φ k i V (hV.trans hWi)).toAddEquiv
      naturality := fun hPQ hP s =>
        (CycleQ2HodgeAtlasLine.coordinate_restrict (cocycle φ k) i (hP.trans hWi) hPQ s).symm }
  exact CycleQ2GeometricAffineHThree.frame_subsingleton
    (intersection_affine φ S ⟨i,hi⟩).isoSpec (F φ k)
    (overIsoOfPatchIso fr) (n+1)
      (CycleQ2GeometricAffineHThree.affine_H_positive_subsingleton n Γ(threefold φ,W))

/-- The genuine coefficient-normalized top trace of the moving threefold. -/
def structureH3Trace : (structureAdditiveSheaf (threefold φ)).H' 3 ⊤ ≃+ R :=
  derivedTopTraceEquiv (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
    (structureLaurentSections φ h) (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)
    (structure_face_acyclic φ)

def structureH3Connecting : Γ(threefold φ,torus φ) →+
    (structureAdditiveSheaf (threefold φ)).H' 3 ⊤ :=
  nativeTopConnecting (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)

theorem structureH3Trace_connecting (s : Γ(threefold φ,torus φ)) :
    structureH3Trace φ h (structureH3Connecting φ h s) = structureTopSectionTrace φ h s :=
  derivedTopTrace_connecting (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
    (structureLaurentSections φ h) (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)
    (structure_face_acyclic φ) s

def structureH3Generator (a : R) : (structureAdditiveSheaf (threefold φ)).H' 3 ⊤ :=
  structureH3Connecting φ h (structureTopGenerator φ h a)

@[simp] theorem structureH3Trace_generator (a : R) :
    structureH3Trace φ h (structureH3Generator φ h a) = a := by
  rw [structureH3Generator, structureH3Trace_connecting,
    CycleQ2HodgeTwistTorusChart.structureTopSectionTrace_generator]

theorem structureH3Generator_one_ne_zero : structureH3Generator φ h 1 ≠ 0 := by
  intro hz
  have he := congrArg (structureH3Trace φ h) hz
  rw [structureH3Trace_generator, map_zero] at he
  exact one_ne_zero he

/-- Positive twists have zero actual derived degree-three cohomology. -/
theorem positive_hThree (k : ℤ) (hk : 0 < k) : Subsingleton ((F φ k).H' 3 ⊤) :=
  derived_hThree_of_positive (F φ k) (coordinateOpen φ) (nativeLaurentSections φ h k) hk
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h) (twist_face_acyclic φ k)

variable {S : Type} [CommRing S] [Nontrivial S] (ρ : R →+* S)

/-- The derived coefficient-change map is induced by the actual face
pullbacks and the actual Mayer--Vietoris comparison on both sides. -/
def structureH3Pullback : (structureAdditiveSheaf (threefold φ)).H' 3 ⊤ →+
    (structureAdditiveSheaf (threefold (ρ.comp φ))).H' 3 ⊤ :=
  (nativeTopCohomologyEquiv (structureAdditiveSheaf (threefold (ρ.comp φ)))
    (coordinateOpen (ρ.comp φ)) (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover
      (ρ.comp φ) (h.map ρ)) (structure_face_acyclic (ρ.comp φ))).toAddMonoidHom.comp
    ((CycleQ2HodgeTwistCoefficientChange.topQuotientPullback φ ρ).comp
      (nativeTopCohomologyEquiv (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
        (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h)
        (structure_face_acyclic φ)).symm.toAddMonoidHom)

theorem structureH3Pullback_connecting (s : Γ(threefold φ,torus φ)) :
    structureH3Pullback φ h ρ (structureH3Connecting φ h s) =
      structureH3Connecting (ρ.comp φ) (h.map ρ)
        (CycleQ2HodgeTwistCoefficientChange.pullback φ ρ s) := by
  let E := nativeTopCohomologyEquiv (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h) (structure_face_acyclic φ)
  let E' := nativeTopCohomologyEquiv (structureAdditiveSheaf (threefold (ρ.comp φ)))
    (coordinateOpen (ρ.comp φ)) (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover
      (ρ.comp φ) (h.map ρ)) (structure_face_acyclic (ρ.comp φ))
  change E' ((CycleQ2HodgeTwistCoefficientChange.topQuotientPullback φ ρ)
    (E.symm (E (QuotientAddGroup.mk s)))) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem structureH3Trace_pullback (z : (structureAdditiveSheaf (threefold φ)).H' 3 ⊤) :
    structureH3Trace (ρ.comp φ) (h.map ρ) (structureH3Pullback φ h ρ z) =
      ρ (structureH3Trace φ h z) := by
  obtain ⟨s,rfl⟩ := nativeTopConnecting_surjective
    (structureAdditiveSheaf (threefold φ)) (coordinateOpen φ)
    (CycleQ2GeometricHodgeThreefold.coordinateOpens_cover φ h) (structure_face_acyclic φ) z
  rw [structureH3Pullback_connecting, structureH3Trace_connecting, structureH3Trace_connecting]
  exact CycleQ2HodgeTwistCoefficientChange.structureTopSectionTrace_pullback φ ρ h s

end CycleQ2HodgeTwistTopCohomology
end

#print axioms CycleQ2HodgeTwistTopCohomology.structureH3Trace
#print axioms CycleQ2HodgeTwistTopCohomology.structureH3Trace_generator
#print axioms CycleQ2HodgeTwistTopCohomology.positive_hThree
#print axioms CycleQ2HodgeTwistTopCohomology.structureH3Trace_pullback
