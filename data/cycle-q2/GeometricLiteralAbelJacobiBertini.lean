import Proposal.GeometricSeedConeSection
import Proposal.GeometricRelativeConstantSection
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Smooth.Field

/-!
# Transversality of a section of the original seed matrix

Choose three complex coefficients algebraically independent over the rationals.
The two seed equations and all matrix entries descend to the field of algebraic
numbers. At a field-valued point of the section, a derivation fixing those
algebraic numbers and varying a single coefficient gives a tangent vector to
the seed surface. Its derivative on the selected section row is the negative
of the corresponding matrix entry. On the open where that entry is a unit,
the section differential is nonzero on the tangent space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open MvPolynomial
open scoped nonZeroDivisors
namespace TranscendentalBertini
variable {K L ι : Type*} [Field K] [Field L] [Algebra K L] [CharZero L]
private abbrev D := TrivSqZeroExt L L
private def fst : D (L := L) →+* L := (TrivSqZeroExt.fstHom L L L).toRingHom

omit [CharZero L] in
private theorem fstKernelNil : IsNilpotent (RingHom.ker (fst (L := L))) := by
  refine ⟨2, ?_⟩
  change RingHom.ker (fst (L := L)) ^ 2 = (⊥ : Ideal (D (L := L)))
  rw [pow_two (RingHom.ker (fst (L := L))), eq_bot_iff, Ideal.mul_le]
  intro a ha b hb
  change a.fst = 0 at ha
  change b.fst = 0 at hb
  change a * b = 0
  ext <;> simp [ha, hb]

/-- Lift polynomial evaluation with the prescribed slopes, then extend along the
separable algebraic extension of its rational function field. -/
private theorem basisDual (t v : ι → L) (ht : IsTranscendenceBasis K t) :
    ∃ d : L →+* D (L := L), (fst.comp d = RingHom.id L) ∧
      (∀ j, d (t j) = ⟨t j, v j⟩) ∧
      (∀ c : K, d (algebraMap K L c) = TrivSqZeroExt.inl (algebraMap K L c)) := by
  let P := MvPolynomial ι K
  let S := FractionRing P
  let F := IntermediateField.adjoin K (Set.range t)
  let f : P →+* D (L := L) := MvPolynomial.eval₂Hom
    ((TrivSqZeroExt.inlHom L L).comp (algebraMap K L))
    (fun j => ⟨t j, v j⟩)
  have fX (j : ι) : f (X j) = ⟨t j, v j⟩ := MvPolynomial.eval₂Hom_X' _ _ _
  have fC (c : K) : f (C c) = TrivSqZeroExt.inl (algebraMap K L c) :=
    MvPolynomial.eval₂Hom_C _ _ _
  have hf : fst.comp f = (MvPolynomial.aeval t).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      exact (congrArg fst (fC c)).trans (MvPolynomial.aeval_C t c).symm
    · intro j
      exact (congrArg fst (fX j)).trans (MvPolynomial.aeval_X t j).symm
  have hunit (x : nonZeroDivisors P) : IsUnit (f x) := by
    apply TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr
    change IsUnit (fst.comp f x)
    rw [hf]
    exact IsUnit.mk0 _ ((map_ne_zero_iff _ (algebraicIndependent_iff_injective_aeval.mp ht.1)).mpr
      (nonZeroDivisors.coe_ne_zero x))
  let g : S →+* D (L := L) := IsLocalization.lift (S := S) hunit
  have hg (x : P) : g (algebraMap P S x) = f x := IsLocalization.lift_eq hunit _
  let e : S ≃ₐ[K] F := ht.1.aevalEquivField
  let fF : F →+* D (L := L) := g.comp e.symm.toRingHom
  have hF (x : F) : fst (fF x) = (x : L) := by
    obtain ⟨x, rfl⟩ := e.surjective x
    change fst (g (e.symm (e x))) = _
    rw [e.symm_apply_apply]
    suffices h : fst.comp g = (IntermediateField.val F).toRingHom.comp e.toRingHom from
      RingHom.congr_fun h x
    apply IsLocalization.ringHom_ext (nonZeroDivisors P)
    apply RingHom.ext
    intro p
    change fst (g (algebraMap P S p)) = (e (algebraMap P S p) : L)
    rw [hg]
    change fst (f p) = (ht.1.aevalEquivField (algebraMap P S p) : L)
    rw [ht.1.aevalEquivField_algebraMap_apply_coe]
    exact RingHom.congr_fun hf p
  let : Algebra F (D (L := L)) := fF.toAlgebra
  let π : D (L := L) →ₐ[F] L := { fst with commutes' := hF }
  have hsurj : Function.Surjective π := fun x => ⟨TrivSqZeroExt.inl x, rfl⟩
  have hnil : IsNilpotent (RingHom.ker π.toRingHom) := fstKernelNil
  let : Algebra.IsAlgebraic F L := ht.isAlgebraic_field
  let : Algebra.FormallyEtale F L := Algebra.FormallyEtale.of_isSeparable _ _
  let d := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id F L) π hsurj hnil
  have dpoly (x : P) : d (aeval t x) = f x := by
    rw [← ht.1.aevalEquivField_algebraMap_apply_coe x]
    change d (algebraMap F L (e (algebraMap P S x))) = _
    rw [d.commutes]
    change g (e.symm (e (algebraMap P S x))) = _
    rw [e.symm_apply_apply, hg]
  refine ⟨d.toRingHom, RingHom.ext (fun x => Algebra.FormallySmooth.liftOfSurjective_apply
    (AlgHom.id F L) π hsurj hnil x), ?_, ?_⟩
  · intro j
    exact (congrArg d (MvPolynomial.aeval_X t j).symm).trans ((dpoly (X j)).trans (fX j))
  · intro c
    exact (congrArg d (MvPolynomial.aeval_C t c).symm).trans ((dpoly (C c)).trans (fC c))
/-- A characteristic-zero field admits a derivation with any prescribed values
on a transcendence basis. -/
theorem basisDerivation (t v : ι → L) (ht : IsTranscendenceBasis K t) :
    ∃ δ : Derivation K L L, ∀ j, δ (t j) = v j := by
  obtain ⟨d, hd, ht', hk⟩ := basisDual t v ht
  have hfst (x : L) : (d x).fst = x := RingHom.congr_fun hd x
  let δ : Derivation K L L :=
    { toFun := fun x => (d x).snd
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by
        change (d (c • x)).snd = c • (d x).snd
        simp only [Algebra.smul_def, map_mul, hk, TrivSqZeroExt.snd_mul,
          TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_mul, add_zero,
          MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        rfl
      map_one_eq_zero' := by change (d 1).snd = 0; rw [map_one]; rfl
      leibniz' := fun x y => by
        change (d (x * y)).snd = _
        rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
        simp [mul_comm] }
  exact ⟨δ, fun j => congrArg TrivSqZeroExt.snd (ht' j)⟩
end TranscendentalBertini

#print axioms TranscendentalBertini.basisDerivation

namespace SmoothSeedGenericCoordinates

open Cardinal

/-- A single vector of three coefficients can be chosen algebraically
independent over the rationals. -/
theorem exists_complex_three_independent : ∃ t : Fin 3 → ℂ, AlgebraicIndependent ℚ t := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ ℂ
  have hℂ : ℵ₀ < #ℂ := by simpa only [Cardinal.mk_complex] using Cardinal.aleph0_lt_continuum
  have hcard := IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'
    ((↑) : s → ℂ) hs Cardinal.mk_le_aleph0 hℂ
  have hle : #(Fin 3) ≤ #s := Cardinal.mk_le_aleph0.trans (hℂ.le.trans_eq hcard)
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hle
  exact ⟨Subtype.val ∘ f, hs.1.comp f f.injective⟩

#print axioms exists_complex_three_independent
end SmoothSeedGenericCoordinates
namespace SmoothSeedTransverse
noncomputable section
open MvPolynomial
open CycleQ2IncidenceEquations CycleQ2IncidenceNormalForm
  CycleQ2IncidenceDehomogenizedChart CycleQ2IncidenceChartSeedFiber
  CycleQ2IncidencePolynomialJacobianBinding CycleQ2IncidenceGenericPointSemantics
  CycleQ2GeometricIncidenceProj CycleQ2IncidenceImageLine CycleQ2RelativeConstantSection
  CycleQ2IncidenceJacobianNaturality

abbrev K := algebraicClosure ℚ ℂ
local instance kSemiring : CommSemiring K := (inferInstance : Field K).toSemifield.toCommSemiring
private def ii : K := ⟨Complex.I, mem_algebraicClosure_iff.mpr
  ⟨Polynomial.X ^ 2 + 1, by
    intro h
    have := congrArg (fun p : Polynomial ℚ => p.coeff 2) h
    norm_num [Polynomial.coeff_one] at this, by simp [Complex.I_sq]⟩⟩

abbrev seed := seedPoint (57 : ℂ) Complex.I
abbrev entry (i : Fin 4) (a b : Fin 3) :=
  dehomogenize i (pointMatrixPolynomial seed a b)
abbrev row (i : Fin 4) (t : Fin 3 → ℂ) (a : Fin 3) :=
  dehomogenize i (relativeSectionPolynomial seed t a)

private lemma entry_descends (i : Fin 4) (a b : Fin 3) :
    ∃ p : ChartPolynomial K, MvPolynomial.map (algebraMap K ℂ) p = entry i a b := by
  refine ⟨dehomogenize i (rawSeedMatrix (57 : K) a b), ?_⟩
  rw [map_dehomogenize, entry, CycleQ2SeedConeSection.pointMatrixPolynomial_seed]
  congr 1
  have h := congrArg (fun M => M a b) (map_rawSeedMatrix (algebraMap K ℂ) (57 : K))
  change MvPolynomial.map (algebraMap K ℂ) (rawSeedMatrix 57 a b) = rawSeedMatrix ((algebraMap K ℂ) 57) a b at h
  simpa only [map_ofNat] using h

private lemma surface_descends (i : Fin 4) (a : Fin 2) :
    ∃ p : ChartPolynomial K, MvPolynomial.map (algebraMap K ℂ) p = dehomogenizedEquations seed i a := by
  fin_cases a
  · refine ⟨dehomogenize i (smoothF 57 ii), ?_⟩
    change _ = dehomogenize i (pointEquationF seed)
    rw [map_dehomogenize, map_smoothF, literal_pointEquationF, map_ofNat]
    rfl
  · refine ⟨dehomogenize i (smoothH ii), ?_⟩
    change _ = dehomogenize i (pointEquationH seed)
    rw [map_dehomogenize, map_smoothH, literal_pointEquationH]
    rfl

theorem row_expansion (i : Fin 4) (t : Fin 3 → ℂ) (a : Fin 3) :
    row i t a = ∑ b, C (t b) * entry i a b := by
  simp only [row, relativeSectionPolynomial, map_sum, map_mul, algHom_C, Algebra.algebraMap_self,
    RingHom.id_apply, entry, MvPolynomial.algebraMap_eq]

variable {L : Type} [Field L] [Algebra ℂ L] [CharZero L]
local instance kAlg : Algebra K L := ((algebraMap ℂ L).comp (algebraMap K ℂ)).toAlgebra
local instance kModule : Module K L := kAlg.toModule
local instance kSMul : SMul K L := kAlg.toSMul
local instance kTower : IsScalarTower K ℂ L where
  smul_assoc c z x := by
    change ((c : ℂ) * z) • x = (algebraMap ℂ L (c : ℂ)) * (z • x)
    rw [mul_smul, Algebra.smul_def (c : ℂ) (z • x)]

omit [CharZero L] in
private lemma eval_map (x : Option (Fin 3) → L) (p : ChartPolynomial K) :
    aeval x (MvPolynomial.map (algebraMap K ℂ) p) = aeval x p :=
  eval₂Hom_map_hom _ _ _ _

abbrev direction (x v : Option (Fin 3) → L) (p : ChartPolynomial ℂ) :=
  ∑ l, aeval x (pderiv l p) * v l

omit [CharZero L] in
private lemma derivation_poly (D : Derivation K L L) (x : Option (Fin 3) → L)
    (p : ChartPolynomial ℂ) (h : ∃ q : ChartPolynomial K, MvPolynomial.map (algebraMap K ℂ) q = p) :
    D (aeval x p) = direction x (fun l => D (x l)) p := by
  obtain ⟨p, rfl⟩ := h
  simp only [direction, pderiv_map, eval_map]
  exact CycleQ2PolynomialDerivationChainRule.derivation_aeval D x p

omit [CharZero L] in
private lemma row_direction (i : Fin 4) (t : Fin 3 → ℂ) (a : Fin 3) (x v : Option (Fin 3) → L) :
    direction x v (row i t a) = ∑ b, algebraMap ℂ L (t b) * direction x v (entry i a b) := by
  simp only [direction, row_expansion, map_sum, pderiv_C_mul, map_mul, aeval_C, Finset.sum_mul,
    Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

/-- At a point of the original seed section, differentiating coefficient j
produces an ambient velocity tangent to both seed equations. Evaluation
of row a on this velocity gives the negative of entry (a,j). -/
theorem transverse_at (t : Fin 3 → ℂ) (ht : AlgebraicIndependent ℚ t)
    (i : Fin 4) (a j : Fin 3) (x : Option (Fin 3) → L)
    (hs : ∀ r, aeval x (dehomogenizedEquations seed i r) = 0)
    (hr : aeval x (row i t a) = 0) :
    ∃ v : Option (Fin 3) → L, (∀ r, direction x v (dehomogenizedEquations seed i r) = 0) ∧
      direction x v (row i t a) = -aeval x (entry i a j) := by
  classical
  let g := IsScalarTower.toAlgHom K ℂ L
  have ht' : AlgebraicIndependent K (g ∘ t) :=
    (g.algebraicIndependent_iff g.injective).mpr (ht.extendScalars K)
  obtain ⟨s, hsub, hb⟩ := exists_isTranscendenceBasis_superset ht'.coe_range
  let b (j : Fin 3) : s := ⟨g (t j), hsub (Set.mem_range_self j)⟩
  have hinj : Function.Injective b := fun _ _ h => ht'.injective (congrArg Subtype.val h)
  obtain ⟨D, hd⟩ := TranscendentalBertini.basisDerivation ((↑) : s → L)
    (fun k => if k = b j then 1 else 0) hb
  have hδ (k : Fin 3) : D (algebraMap ℂ L (t k)) = if k = j then 1 else 0 := by
    change D ((b k : s) : L) = _
    simpa only [hinj.eq_iff] using hd (b k)
  refine ⟨fun l => D (x l), fun r => ?_, ?_⟩
  · exact (derivation_poly D x _ (surface_descends i r)).symm.trans ((congrArg D (hs r)).trans (map_zero D))
  · have h := congrArg D hr
    rw [row_expansion, map_sum, map_sum] at h
    simp only [map_mul, aeval_C, Derivation.leibniz, hδ, smul_eq_mul, mul_ite, mul_one,
      mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_zero] at h
    rw [row_direction]
    simp_rw [← derivation_poly D x _ (entry_descends i a _)]
    exact eq_neg_of_add_eq_zero_left h

#print axioms transverse_at
end
end SmoothSeedTransverse
end
