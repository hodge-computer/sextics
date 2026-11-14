import Proposal.GeometricSurfaceCoordinates
import Proposal.GeometricCurveCoordinates
import Proposal.Workspace
import HodgeTarget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Algebra.MvPolynomial.Equiv
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import HodgeComputer.CertificateOperations
import HodgeComputer.Verify
import HodgeComputer.Constructions.RationalFields.Calculus
import HodgeComputer.Constructions.FiniteAlgebra.FractionDerivation
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Tactic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Irreducible
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.LinearAlgebra.Isomorphisms
import Proposal.GeometricSeed
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
import HodgeComputer.Constructions.HigherResidues.HigherResidue
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.RationalFields.Homogenization
import HodgeComputer.Constructions.RationalFields.CommonDenominatorSubstitution
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.HahnSeries.PowerSeries
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FreeModule.Basic
import HodgeComputer.Constructions.PolynomialCurves.ArithmeticLifting
import HodgeComputer.Constructions.HoldoutCover.GenericIncidence
import Mathlib.RingTheory.Smooth.AdicCompletion
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Fintype.Card
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.Data.Finsupp.MonomialOrder.DegLex
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LaurentSeries
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FunProp
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Algebra.CharP.Basic
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Data.Finsupp.Encodable
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Tactic.Abel
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Data.List.OfFn
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Data.Fintype.Fin
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.Localization.AtPrime.Basic
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Proposal.GeometricFormalInputs
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import Proposal.GeometricTarget08Part04

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Component: continuation_3/CurveRestrictionSourceBasis.lean -/
section
/-! Bases of the actual source pieces for both curve restrictions, including
character one. The source ring is the existing smooth seed quotient. -/

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CurveRestriction

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceGradedBasis
  CycleQ2IncidenceEquations CycleQ2SegreTangentLocal

variable {R : Type*} [CommRing R]

theorem seed_h_normalized (ι : R) :
    smoothH ι=normalizedFullCubic (fun e => seedCubicCoefficients ι e.val) := by
  rw [←seedCubicCoefficients_polynomial,fullInvariantPolynomial_cubic]
  change monomial (Finsupp.single 0 3) (seedCubicCoefficients ι fullCubicLeadingIndex)+_= _
  simp only [seedCubicCoefficients,fullCubicLeadingIndex_exponent,smoothH_leading_coefficient]
  rfl

theorem seed_F_normalized (r ι : R) :
    smoothF r ι=normalizedFullSextic (fun e => seedSexticCoefficients r ι e.val) := by
  rw [←seedSexticCoefficients_polynomial,fullInvariantPolynomial_sextic]
  change monomial (Finsupp.single 4 3) (seedSexticCoefficients r ι fullSexticLeadingIndex)+_= _
  simp only [seedSexticCoefficients,fullSexticLeadingIndex_exponent,smoothF_leading_coefficient]
  rfl

theorem seed_h_leading [Nontrivial R] (ι : R) :
    fullAuxiliaryOrder.degree (smoothH ι)=Finsupp.single 0 3 ∧
      fullAuxiliaryOrder.Monic (smoothH ι) := by
  rw [seed_h_normalized]
  exact normalizedFullCubic_leading_data _

theorem seed_F_leading [Nontrivial R] (r ι : R) :
    fullAuxiliaryOrder.degree (smoothF r ι)=Finsupp.single 4 3 ∧
      fullAuxiliaryOrder.Monic (smoothF r ι) := by
  rw [seed_F_normalized]
  exact normalizedFullSextic_leading_data _

theorem seed_leading_coprime [Nontrivial R] (r ι : R) :
    ∀ j, fullAuxiliaryOrder.degree (smoothH ι) j=0 ∨
      fullAuxiliaryOrder.degree (smoothF r ι) j=0 := by
  rw [(seed_h_leading ι).1,(seed_F_leading r ι).1]
  intro j
  fin_cases j <;> simp

theorem seed_reduced_exponent_iff [Nontrivial R] (r ι : R) (e : FullExponent) :
    e ∈ reducedExponents fullAuxiliaryOrder (smoothH ι) (smoothF r ι) ↔
      e 0<3 ∧ e 4<3 := by
  change (¬ fullAuxiliaryOrder.degree (smoothH ι)≤e) ∧
    (¬ fullAuxiliaryOrder.degree (smoothF r ι)≤e) ↔ _
  rw [(seed_h_leading ι).1,(seed_F_leading r ι).1,
    Finsupp.single_le_iff,Finsupp.single_le_iff]
  omega

def seedGradedExponentEquiv [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3) :
    gradedExponents fullGrading fullAuxiliaryOrder (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3)) ≃
      SourceExponents d ch where
  toFun e := ⟨e.val,by
    have hb := (seed_reduced_exponent_iff r ι e.val).mp e.property.1
    have hg := e.property.2
    rw [fullGrading_weight] at hg
    have hd := congrArg Prod.fst hg
    have hc := congrArg Prod.snd hg
    refine ⟨hb.1,hb.2,hd,?_⟩
    change ((2*e.val 0+2*e.val 1+e.val 2:ℕ):ZMod 3)=(ch:ZMod 3) at hc
    have hm := (ZMod.natCast_eq_natCast_iff' _ _ 3).mp hc
    simpa only [Nat.mod_eq_of_lt hch] using hm⟩
  invFun e := ⟨Finsupp.equivFunOnFinite.symm e.val,by
    constructor
    · apply (seed_reduced_exponent_iff r ι _).mpr
      exact ⟨e.property.1,e.property.2.1⟩
    · rw [fullGrading_weight]
      apply Prod.ext
      · exact e.property.2.2.1
      · have hc := congrArg (fun n : ℕ => (n:ZMod 3)) e.property.2.2.2
        simpa using hc⟩
  left_inv e := by apply Subtype.ext; exact Finsupp.equivFunOnFinite.symm_apply_apply e.val
  right_inv e := by apply Subtype.ext; rfl

abbrev SeedPiece (r ι : R) (d ch : ℕ) :=
  quotientPiece fullGrading (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3))

def seedPieceBasis [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3) :
    Module.Basis (SourceIndex d ch) R (SeedPiece r ι d ch) :=
  (CycleQ2IncidenceGradedBasis.basis fullGrading fullAuxiliaryOrder
    (smoothH ι) (smoothF r ι) (d,(ch:ZMod 3)) (seed_h_leading ι).2
    (seed_F_leading r ι).2 (seed_leading_coprime r ι)
    (smoothH_homogeneous ι) (smoothF_homogeneous r ι)).reindex
      ((seedGradedExponentEquiv r ι d ch hch).trans (sourceExponentEquiv d ch).symm)

theorem seedPieceBasis_apply [Nontrivial R] (r ι : R) (d ch : ℕ) (hch : ch<3)
    (q : SourceIndex d ch) :
    (seedPieceBasis r ι d ch hch q).val=
      Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι))
        (monomial (sourceExponent q) 1) := by
  rw [seedPieceBasis,Module.Basis.reindex_apply,CycleQ2IncidenceGradedBasis.basis_apply]
  rfl

theorem left_seedPiece_rank [Nontrivial R] (r ι : R) :
    Module.finrank R (SeedPiece r ι 10 0)=113 := by
  rw [Module.finrank_eq_card_basis (seedPieceBasis r ι 10 0 (by decide)),left_source_count]

theorem right_seedPiece_rank [Nontrivial R] (r ι : R) :
    Module.finrank R (SeedPiece r ι 8 1)=68 := by
  rw [Module.finrank_eq_card_basis (seedPieceBasis r ι 8 1 (by decide)),right_source_count]

/-- The actual quotient algebra restriction. Both seed generators map into the
explicit curve ideal, as proved by the integral substitution identities. -/
def seedRestriction (s : Side) (r ι : R) : SeedRing r ι →ₐ[R] CurveRing s r ι :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R (curveIdeal s r ι)).comp (substitution s r)) (by
    intro p hp
    change Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p)=0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    obtain ⟨a,b,hab⟩ := Ideal.mem_span_pair.mp hp
    rw [←hab,map_add,map_mul,map_mul]
    exact Ideal.add_mem _
      (Ideal.mul_mem_left _ _ (substitution_h_mem s r ι))
      (Ideal.mul_mem_left _ _ (substitution_F_mem s r ι)))

@[simp] theorem seedRestriction_mk (s : Side) (r ι : R) (p : MvPolynomial (Fin 5) R) :
    seedRestriction s r ι (Ideal.Quotient.mk (equationsIdeal (smoothH ι) (smoothF r ι)) p)=
      Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p) := rfl

def ordinaryWeight : Fin 5 → ℕ := ![1,1,1,1,2]

theorem restrictionValues_homogeneous (s : Side) (r : R) (j : Fin 5) :
    (restrictionValues s r j).IsHomogeneous (ordinaryWeight j) := by
  cases s <;> fin_cases j
  · exact isHomogeneous_X R 0
  · exact isHomogeneous_X R 1
  · exact isHomogeneous_X R 2
  · exact isHomogeneous_X R 3
  · exact (isHomogeneous_X_pow (R:=R) (2 : Fin 4) 2).neg
  · exact (isHomogeneous_X R 0).add (isHomogeneous_X R 2)
  · change (2*X 1 : CurvePoly R).IsHomogeneous 1
    simpa only [map_ofNat] using (isHomogeneous_X R (1 : Fin 4)).C_mul (2 : R)
  · exact (isHomogeneous_X R 0).sub (isHomogeneous_X R 2)
  · change (2*X 3 : CurvePoly R).IsHomogeneous 1
    simpa only [map_ofNat] using (isHomogeneous_X R (3 : Fin 4)).C_mul (2 : R)
  · change (C (4*r)*X 1*X 3 : CurvePoly R).IsHomogeneous 2
    simpa only [mul_assoc] using
      ((isHomogeneous_X R (1 : Fin 4)).mul (isHomogeneous_X R (3 : Fin 4))).C_mul (4*r)

theorem substitution_monomial_homogeneous (s : Side) (r : R) (e : FullExponent) (c : R) :
    (substitution s r (monomial e c)).IsHomogeneous (fullDegree e) := by
  classical
  have he : monomial e c=C c*∏ i : Fin 5, X i^e i := by
    rw [monomial_eq,Finsupp.prod_fintype]
    intro i
    simp
  rw [he,map_mul,map_prod,substitution_C]
  apply IsHomogeneous.C_mul
  simp only [map_pow,substitution_X]
  have hd : (∑ i : Fin 5, ordinaryWeight i*e i)=fullDegree e := by
    norm_num [ordinaryWeight,fullDegree,Fin.sum_univ_succ,Matrix.cons_val_succ,Fin.reduceSucc]
    change e 0+(e 1+(e 2+(e 3+2*e 4)))=e 0+e 1+e 2+e 3+2*e 4
    omega
  rw [←hd]
  exact IsHomogeneous.prod _ _ _ (fun i _ => (restrictionValues_homogeneous s r i).pow (e i))

theorem substitution_homogeneous (s : Side) (r : R) {p : MvPolynomial (Fin 5) R}
    {d : ℕ} {ch : ZMod 3} (hp : p.IsWeightedHomogeneous fullGrading (d,ch)) :
    (substitution s r p).IsHomogeneous d := by
  classical
  rw [p.as_sum,map_sum]
  apply (homogeneousSubmodule (Fin 4) R d).sum_mem
  intro e he
  have hg := hp (mem_support_iff.mp he)
  rw [fullGrading_weight] at hg
  have hd := congrArg Prod.fst hg
  change fullDegree e=d at hd
  change (substitution s r (monomial e (p.coeff e))).IsHomogeneous d
  simpa only [hd] using substitution_monomial_homogeneous s r e (p.coeff e)

/-- Restriction on the actual homogeneous quotient pieces. -/
def seedRestrictionPiece (s : Side) (r ι : R) (d ch : ℕ) :
    SeedPiece r ι d ch →ₗ[R] CurvePiece s r ι d :=
  (((seedRestriction s r ι).toLinearMap.comp (SeedPiece r ι d ch).subtype).codRestrict
    (CurvePiece s r ι d) (by
      intro q
      obtain ⟨p,hp,hpq⟩ := Submodule.mem_map.mp q.property
      apply Submodule.mem_map.mpr
      refine ⟨substitution s r p,substitution_homogeneous s r hp,?_⟩
      change Ideal.Quotient.mk (curveIdeal s r ι) (substitution s r p)=seedRestriction s r ι q.val
      rw [←hpq]
      rfl))

theorem seedRestrictionPiece_apply (s : Side) (r ι : R) (d ch : ℕ)
    (q : SeedPiece r ι d ch) :
    (seedRestrictionPiece s r ι d ch q).val=seedRestriction s r ι q.val := rfl

end CycleQ2CurveRestriction

#print axioms CycleQ2CurveRestriction.left_seedPiece_rank
#print axioms CycleQ2CurveRestriction.right_seedPiece_rank
#print axioms CycleQ2CurveRestriction.seedRestriction

#print axioms CycleQ2CurveRestriction.substitution_homogeneous
#print axioms CycleQ2CurveRestriction.seedRestrictionPiece
end
end


/- Component: continuation_3/IncidenceCoefficientRelations.lean -/
section
/-!
# The actual coefficient-level relations among the incidence equations

The sixteen universal Segre identities are reduced in the same moving
cubic/sextic quotient as the incidence equations.  Expanding in the proved
degree-28 and degree-42 standard bases produces a genuine 39440-by-9522
relation matrix over the localized coefficient ring.  Its identity is
universal, not restricted to the numerical seed or to points on one fiber.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

namespace CycleQ2IncidenceCoefficientRelations

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceEquations CycleQ2IncidenceJacobian
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem standardExponent_injective {d : ℕ} :
    Function.Injective (@standardExponent d) := by
  intro a b hab
  apply (exponentEquiv d 3 3).injective
  apply Subtype.ext
  funext i
  exact congrArg (fun e : FullExponent => e i) hab

def standardExpansion (d : ℕ) (p : Poly R) : Poly R :=
  ∑ e : StandardIndex d, p.coeff (standardExponent e) • monomial (standardExponent e) 1

theorem standardExpansion_coeff (d : ℕ) (p : Poly R) (e : StandardIndex d) :
    (standardExpansion d p).coeff (standardExponent e) = p.coeff (standardExponent e) := by
  classical
  have heq (f : StandardIndex d) : standardExponent f = standardExponent e ↔ f = e :=
    standardExponent_injective.eq_iff
  simp [standardExpansion, coeff_sum, coeff_smul, coeff_monomial, heq]

theorem standardExpansion_eq (d : ℕ) (p : Poly R)
    (hp : FullStandard p) (hg : HG p (d, 0)) : standardExpansion d p = p := by
  classical
  ext e
  by_cases he : ∃ q : StandardIndex d, standardExponent q = e
  · obtain ⟨q, rfl⟩ := he
    exact standardExpansion_coeff d p q
  · have hz : p.coeff e = 0 := by
      by_contra hne
      have hb := hp e (mem_support_iff.mpr hne)
      have hd := (fullGrading_eq_iff e d).mp (hg hne)
      let v : Exponents d 3 3 := ⟨e, hb.1, hb.2, hd.1, hd.2⟩
      let q := (exponentEquiv d 3 3).symm v
      apply he
      refine ⟨q, ?_⟩
      ext i
      exact congrArg (fun z : Exponents d 3 3 => z.val i)
        ((exponentEquiv d 3 3).apply_symm_apply v)
    rw [hz]
    simp only [standardExpansion, coeff_sum, coeff_smul, coeff_monomial, smul_eq_mul]
    apply Finset.sum_eq_zero
    intro q _
    have hq : standardExponent q ≠ e := fun hq => he ⟨q, hq⟩
    simp [hq]

section NormalMultiplication

variable [Nontrivial R]
variable (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
  (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))

theorem sub_fullRemainder_mem (p : Poly R) :
    p - fullRemainder hc Fc hu Fu p ∈
      equationsIdeal (fullInvariantPolynomial 3 hc) (fullInvariantPolynomial 6 Fc) := by
  obtain ⟨_, a, b, hp⟩ := fullRemainder_spec hc Fc hu Fu p
  apply Ideal.mem_span_pair.mpr
  exact ⟨a, b, (sub_eq_iff_eq_add.mpr hp).symm⟩

/-- Multiplication in the actual quotient is computed by remaindering a
product of a polynomial with the other factor's normal form. -/
theorem fullRemainder_mul_remainder (a b : Poly R) :
    fullRemainder hc Fc hu Fu (a * fullRemainder hc Fc hu Fu b) =
      fullRemainder hc Fc hu Fu (a * b) := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hz : fullRemainder hc Fc hu Fu (a * (b - fullRemainder hc Fc hu Fu b)) = 0 :=
    (fullRemainder_eq_zero_iff hc Fc hu Fu _).mpr
      (Ideal.mul_mem_left _ a (sub_fullRemainder_mem hc Fc hu Fu b))
  have hsub : N (a * b) - N (a * fullRemainder hc Fc hu Fu b) = 0 := by
    rw [← map_sub, ← mul_sub]
    exact hz
  exact (sub_eq_zero.mp hsub).symm

end NormalMultiplication

def cofactorPosition : Fin 9 ≃ Fin 3 × Fin 3 :=
  (finProdFinEquiv (m := 3) (n := 3)).symm

theorem cofactor_position (M : Matrix (Fin 3) (Fin 3) R) (k : Fin 9) :
    CycleQ2SegreRelations.cofactors M k =
      CycleQ2SegreLocal.cofactors M (cofactorPosition k).1 (cofactorPosition k).2 := by
  unfold CycleQ2SegreLocal.cofactors
  rw [← CycleQ2SegreRelations.cofactorMatrix_eq_transpose_adjugate]
  fin_cases k <;> rfl

abbrev RelationIndex := Fin 16 × StandardIndex 42
abbrev ColumnIndex := Fin 9 × StandardIndex 28

def columnEquiv : ColumnIndex ≃ EquationIndex :=
  Equiv.prodCongr cofactorPosition (Equiv.refl _)

theorem relationIndex_count : Fintype.card RelationIndex = 39440 := by
  simp only [RelationIndex, Fintype.card_prod, Fintype.card_fin, standard_degree42_count]

theorem columnIndex_count : Fintype.card ColumnIndex = 9522 := by
  simp only [ColumnIndex, Fintype.card_prod, Fintype.card_fin, standard_degree28_count]

section Relations

variable [Nontrivial R]
variable (hc : FullInvariantIndex 3 → R) (Fc : FullInvariantIndex 6 → R)
  (hu : IsUnit (hc fullCubicLeadingIndex)) (Fu : IsUnit (Fc fullSexticLeadingIndex))

def coefficientRelations (M : Matrix (Fin 3) (Fin 3) (Poly R)) :
    Matrix RelationIndex ColumnIndex R := fun row col =>
  (fullRemainder hc Fc hu Fu
    (CycleQ2SegreRelations.relations M row.1 col.1 *
      monomial (standardExponent col.2) 1)).coeff (standardExponent row.2)

theorem normal_cofactor_relations (M : Matrix (Fin 3) (Fin 3) (Poly R)) (k : Fin 16) :
    ∑ j : Fin 9, fullRemainder hc Fc hu Fu
      (CycleQ2SegreRelations.relations M k j *
        fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j)) = 0 := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hm := congrFun (CycleQ2SegreRelations.relations_cofactors M) k
  change (∑ j, CycleQ2SegreRelations.relations M k j *
    CycleQ2SegreRelations.cofactors M j) = 0 at hm
  simp_rw [fullRemainder_mul_remainder]
  change (∑ j, N (CycleQ2SegreRelations.relations M k j *
    CycleQ2SegreRelations.cofactors M j)) = 0
  rw [← map_sum, hm, map_zero]

theorem coefficientRelations_cofactorEquations
    (M : Matrix (Fin 3) (Fin 3) (Poly R)) (hM : ∀ i j, HG (M i j) (14, 0)) :
    coefficientRelations hc Fc hu Fu M *ᵥ
      (fun q : ColumnIndex => cofactorEquations hc Fc hu Fu M (columnEquiv q)) = 0 := by
  let N := fullRemainderLinear hc Fc hu Fu
  have hexp (j : Fin 9) :
      fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j) =
        ∑ e : StandardIndex 28,
          cofactorEquations hc Fc hu Fu M (columnEquiv (j, e)) •
            monomial (standardExponent e) 1 := by
    rw [cofactor_position]
    exact (standardExpansion_eq 28 _ (fullRemainder_spec hc Fc hu Fu _).1
      (fullRemainder_preserves_grading hc Fc hu Fu
        (cofactors_homogeneous M hM _ _))).symm
  have hterm (k : Fin 16) (j : Fin 9) :
      fullRemainder hc Fc hu Fu
        (CycleQ2SegreRelations.relations M k j *
          fullRemainder hc Fc hu Fu (CycleQ2SegreRelations.cofactors M j)) =
        ∑ e : StandardIndex 28, cofactorEquations hc Fc hu Fu M (columnEquiv (j, e)) •
          fullRemainder hc Fc hu Fu
            (CycleQ2SegreRelations.relations M k j * monomial (standardExponent e) 1) := by
    rw [hexp, Finset.mul_sum]
    change N (∑ e : StandardIndex 28, _) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro e _
    rw [mul_smul_comm, map_smul]
    rfl
  funext row
  have hh := congrArg (fun p : Poly R => p.coeff (standardExponent row.2))
    (normal_cofactor_relations hc Fc hu Fu M row.1)
  simp_rw [hterm] at hh
  simp only [coeff_sum, coeff_smul, smul_eq_mul, coeff_zero] at hh
  change (∑ q : ColumnIndex, coefficientRelations hc Fc hu Fu M row q *
    cofactorEquations hc Fc hu Fu M (columnEquiv q)) = 0
  simpa only [coefficientRelations, Fintype.sum_prod_type, mul_comm] using hh

/-- The actual moving incidence equations satisfy every coefficient relation,
over any leading-unit coefficient ring and before solving any subsystem. -/
theorem coefficientRelations_incidenceEquations (r : R)
    (δ : Fin 3 → Fin 3 → StandardIndex 14 → R) :
    coefficientRelations hc Fc hu Fu (incidenceMatrix r δ) *ᵥ
      (fun q : ColumnIndex => incidenceEquations hc Fc hu Fu r δ (columnEquiv q)) = 0 :=
  coefficientRelations_cofactorEquations hc Fc hu Fu (incidenceMatrix r δ)
    (incidenceMatrix_homogeneous r δ)

end Relations

end CycleQ2IncidenceCoefficientRelations

#print axioms CycleQ2IncidenceCoefficientRelations.standardExpansion_eq
#print axioms CycleQ2IncidenceCoefficientRelations.coefficientRelations_incidenceEquations
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechThetaCharts.lean -/
section
/-! Actual quotient charts for the family h+θx₀³, including the smooth
incidence seed θ=1.  The added term is reduced using x₀²=rx₁x₃, so the
cubic remains monic in x₂ without changing the curve ideal. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCechTheta
open CycleQ2CechLinearCubic
open CycleQ2SeedCech (PS LS Jet firstJet endpointX endpointY seriesMap uniformizerUnit
  uniformizer_inv_sq unit_pow_cancel)
open MvPolynomial CycleQ2SeedTrace

def betaCoefficient (r θ : ℂ) (e : Bool) : PS :=
  endpointX e ^ 2 + PowerSeries.C θ * PowerSeries.C r * endpointX e * endpointY e

abbrev PowerChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

abbrev LaurentChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

abbrev JetChart (r θ : ℂ) (e : Bool) :=
  CurveAlgebra (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def powerBase (r θ : ℂ) (e : Bool) : PS →+* PowerChart r θ e :=
  base (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerX0 (r θ : ℂ) (e : Bool) : PowerChart r θ e :=
  x0 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerX2 (r θ : ℂ) (e : Bool) : PowerChart r θ e :=
  x2 (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def powerCoefficient (r θ : ℂ) (e : Bool) : PowerChart r θ e →ₗ[PS] PS :=
  coefficient (PowerSeries.C r) (PowerSeries.C Complex.I) (endpointX e) (endpointY e)
    (betaCoefficient r θ e)

def laurentBase (r θ : ℂ) (e : Bool) : LS →+* LaurentChart r θ e :=
  base (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

def laurentCoefficient (r θ : ℂ) (e : Bool) : LaurentChart r θ e →ₗ[LS] LS :=
  coefficient (seriesMap (PowerSeries.C r)) (seriesMap (PowerSeries.C Complex.I))
    (seriesMap (endpointX e)) (seriesMap (endpointY e)) (seriesMap (betaCoefficient r θ e))

def jetBase (r θ : ℂ) (e : Bool) : Jet →+* JetChart r θ e :=
  base (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetX0 (r θ : ℂ) (e : Bool) : JetChart r θ e :=
  x0 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetX2 (r θ : ℂ) (e : Bool) : JetChart r θ e :=
  x2 (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def jetCoefficient (r θ : ℂ) (e : Bool) : JetChart r θ e →ₗ[Jet] Jet :=
  coefficient (firstJet (PowerSeries.C r)) (firstJet (PowerSeries.C Complex.I))
    (firstJet (endpointX e)) (firstJet (endpointY e)) (firstJet (betaCoefficient r θ e))

def chartEmbedding (r θ : ℂ) (e : Bool) : PowerChart r θ e →+* LaurentChart r θ e :=
  curveMap seriesMap (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)

def jetEmbedding (r θ : ℂ) (e : Bool) : PowerChart r θ e →+* JetChart r θ e :=
  curveMap firstJet (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)

theorem firstJet_powerCoefficient (r θ : ℂ) (e : Bool) (z : PowerChart r θ e) :
    firstJet (powerCoefficient r θ e z) = jetCoefficient r θ e (jetEmbedding r θ e z) := by
  symm
  exact coefficient_curveMap firstJet _ _ _ _ _ z

theorem endpointNorm_isUnit (r θ : ℂ) (e : Bool) :
    IsUnit (norm (PowerSeries.C r) (PowerSeries.C Complex.I)
      (endpointX e) (endpointY e) (betaCoefficient r θ e)) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [isUnit_iff_ne_zero]
  cases e <;>
    norm_num [CycleQ2CechLinearCubic.norm, betaCoefficient, endpointX, endpointY,
      Complex.ext_iff, Complex.I_sq]

def endpointNormUnit (r θ : ℂ) (e : Bool) : PSˣ := (endpointNorm_isUnit r θ e).unit

def powerX2Unit (r θ : ℂ) (e : Bool) : (PowerChart r θ e)ˣ :=
  x2Unit _ _ _ _ _ (endpointNormUnit r θ e) (endpointNorm_isUnit r θ e).unit_spec

@[simp] theorem coe_powerX2Unit (r θ : ℂ) (e : Bool) :
    (powerX2Unit r θ e : PowerChart r θ e) = powerX2 r θ e := rfl

def laurentX2Unit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (chartEmbedding r θ e) (powerX2Unit r θ e)

def jetX2Unit (r θ : ℂ) (e : Bool) : (JetChart r θ e)ˣ :=
  Units.map (jetEmbedding r θ e) (powerX2Unit r θ e)

@[simp] theorem coe_jetX2Unit (r θ : ℂ) (e : Bool) :
    (jetX2Unit r θ e : JetChart r θ e) = jetX2 r θ e := by
  simp [jetX2Unit, jetEmbedding, powerX2, jetX2]

def powerCoordinates (r θ : ℂ) (e : Bool) : Fin 4 → PowerChart r θ e :=
  ![powerX0 r θ e, powerBase r θ e (endpointX e), powerX2 r θ e,
    powerBase r θ e (endpointY e)]

def powerEval (r θ : ℂ) (e : Bool) : Poly →+* PowerChart r θ e :=
  MvPolynomial.eval₂Hom ((powerBase r θ e).comp PowerSeries.C) (powerCoordinates r θ e)

@[simp] theorem powerEval_C (r θ c : ℂ) (e : Bool) :
    powerEval r θ e (C c) = powerBase r θ e (PowerSeries.C c) := by simp [powerEval]

@[simp] theorem powerEval_X_zero (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 0) = powerX0 r θ e := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_one (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 1) = powerBase r θ e (endpointX e) := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_two (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 2) = powerX2 r θ e := by simp [powerEval, powerCoordinates]
@[simp] theorem powerEval_X_three (r θ : ℂ) (e : Bool) :
    powerEval r θ e (X 3) = powerBase r θ e (endpointY e) := by simp [powerEval, powerCoordinates]


theorem powerEval_curveF1 (r θ : ℂ) (e : Bool) : powerEval r θ e (relation r 0) = 0 := by
  simp only [relation, Matrix.cons_val_zero, map_sub, map_mul, map_pow,
    powerEval_C, powerEval_X_zero, powerEval_X_one, powerEval_X_three]
  change x0 _ _ _ _ _ ^ 2 - _ = 0
  rw [x0_sq, sub_eq_zero]
  simp [powerBase, map_mul]

/-- The new chart is bound to the literal smooth-seed equation, not merely
to abstract first-order relations. -/
theorem powerEval_curveH (r θ : ℂ) (e : Bool) : powerEval r θ e (curveH θ) = 0 := by
  have h0 := x0_sq (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)
  have h2 := x2_cubic (PowerSeries.C r) (PowerSeries.C Complex.I)
    (endpointX e) (endpointY e) (betaCoefficient r θ e)
  change powerX0 r θ e ^ 2 = powerBase r θ e
    (PowerSeries.C r * endpointX e * endpointY e) at h0
  change powerX2 r θ e ^ 3 + (powerX0 r θ e + powerBase r θ e (endpointX e)) *
      powerBase r θ e (endpointY e) * powerX2 r θ e +
    powerX0 r θ e * powerBase r θ e (betaCoefficient r θ e) +
    powerBase r θ e ((1-PowerSeries.C Complex.I)*endpointY e^3-
      PowerSeries.C Complex.I*endpointX e^3) = 0 at h2
  simp only [betaCoefficient, map_add, map_sub, map_mul, map_pow, map_one] at h0 h2
  simp only [curveH, h, b, map_add, map_sub, map_mul, map_pow,
    powerEval_C, powerEval_X_zero, powerEval_X_one, powerEval_X_two, powerEval_X_three]
  linear_combination h2 + powerBase r θ e (PowerSeries.C θ) * powerX0 r θ e * h0

theorem powerEval_zero_of_curveIdeal (r θ : ℂ) (e : Bool) {p : Poly}
    (hp : p ∈ curveIdeal r θ) : powerEval r θ e p = 0 := by
  obtain ⟨u,v,hp⟩ := Ideal.mem_span_pair.mp hp
  rw [← hp, map_add, map_mul, map_mul, powerEval_curveF1, powerEval_curveH]
  ring

def curveChart (r θ : ℂ) (e : Bool) : Poly ⧸ curveIdeal r θ →+* PowerChart r θ e :=
  Ideal.Quotient.lift _ (powerEval r θ e) (fun _ hp => powerEval_zero_of_curveIdeal r θ e hp)

def laurentEval (r θ : ℂ) (e : Bool) : Poly →+* LaurentChart r θ e :=
  (chartEmbedding r θ e).comp (powerEval r θ e)

def jetEval (r θ : ℂ) (e : Bool) : Poly →+* JetChart r θ e :=
  (jetEmbedding r θ e).comp (powerEval r θ e)

def chartAUnit (r θ : ℂ) (e : Bool) : (LaurentChart r θ e)ˣ :=
  Units.map (laurentBase r θ e) uniformizerUnit

theorem laurentEval_curveA (r θ : ℂ) (e : Bool) :
    laurentEval r θ e (X 1 * X 3) = (chartAUnit r θ e : LaurentChart r θ e) := by
  have hp : powerEval r θ e (X 1 * X 3) = powerBase r θ e PowerSeries.X := by
    simp only [map_mul, powerEval_X_one, powerEval_X_three]
    rw [← map_mul]
    congr 1
    cases e <;> simp [endpointX, endpointY]
  change chartEmbedding r θ e (powerEval r θ e (X 1 * X 3)) = _
  rw [hp]
  exact curveMap_base seriesMap _ _ _ _ _ _

def fraction (r θ : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : LaurentChart r θ e :=
  laurentEval r θ e p * ((chartAUnit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^n *
    ((laurentX2Unit r θ e)⁻¹ : (LaurentChart r θ e)ˣ)^m

def fractionResidue (r θ : ℂ) (e : Bool) (p : Poly) (n m : ℕ) : ℂ :=
  (laurentCoefficient r θ e (fraction r θ e p n m)).coeff (-1)

def cechResidue (r θ : ℂ) (p : Poly) (n m : ℕ) : ℂ :=
  fractionResidue r θ false p n m - fractionResidue r θ true p n m

theorem fractionResidue_double_pole (r θ : ℂ) (e : Bool) (p : Poly) (m : ℕ) :
    fractionResidue r θ e p 2 m =
      PowerSeries.coeff 1 (powerCoefficient r θ e
        (powerEval r θ e p * ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^m)) := by
  let z : PowerChart r θ e :=
    powerEval r θ e p * ((powerX2Unit r θ e)⁻¹ : (PowerChart r θ e)ˣ)^m
  have heq : fraction r θ e p 2 m =
      laurentBase r θ e (((uniformizerUnit⁻¹ : LSˣ) : LS)^2) * chartEmbedding r θ e z := by
    simp only [fraction, laurentEval, RingHom.comp_apply, z, map_mul, map_pow,
      laurentBase, chartAUnit, laurentX2Unit, Units.coe_map_inv, MonoidHom.coe_coe]
    ring
  unfold fractionResidue
  rw [heq]
  unfold laurentCoefficient laurentBase chartEmbedding
  rw [coefficient_base_mul, coefficient_curveMap, uniformizer_inv_sq,
    HahnSeries.coeff_single_mul]
  norm_num [seriesMap, powerCoefficient, PowerSeries.coeff_coe, z]

end CycleQ2SeedCechTheta

#print axioms CycleQ2SeedCechTheta.powerEval_curveH
#print axioms CycleQ2SeedCechTheta.fractionResidue_double_pole
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechTraceComparison.lean -/
section
/-! Identification of the published finite Artinian trace with the actual
all-poles Čech residue functional on the sparse seed curve. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech
open MvPolynomial CycleQ2SeedTrace

/-- Exact comparison with the previously checked finite trace. -/
theorem cechResidue_eq_trace (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : cechResidue r p 2 4 = (3*r) * traceLinear r p := by
  have hs : (mon 1 8 0 0).IsHomogeneous 9 := by simpa using mon_homogeneous 1 8 0 0
  have hm := homogeneous_degreeNine_mod_trace r hr hp
  have hb := boundary_of_mem_reducedIdeal r (hp.sub (hs.C_mul _)) hm
  have hz := cechResidue_zero_of_boundary r _ 2 4 hb
  rw [cechResidue_sub, cechResidue_C_mul, cechResidue_socle, sub_eq_zero] at hz
  simpa [mul_comm] using hz

/-- The actual degree-one Čech fraction is a coboundary exactly when the
published Artinian trace vanishes.  This includes coboundaries only visible
after increasing either denominator power. -/
theorem cechBoundary_iff_trace_zero (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : CechBoundary r p 2 4 ↔ traceLinear r p = 0 := by
  have hr0 : r ≠ 0 := by intro hh; simp [hh] at hr
  constructor
  · intro hb
    have hz := cechResidue_zero_of_boundary r p 2 4 hb
    rw [cechResidue_eq_trace r hr hp] at hz
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hr0)
  · intro ht
    have hm := homogeneous_degreeNine_mod_trace r hr hp
    simp only [ht, map_zero, zero_mul, sub_zero] at hm
    exact boundary_of_mem_reducedIdeal r hp hm

/-- In degree nine, allowing higher Čech denominator powers introduces no
additional relations beyond the actual four-generator Artinian ideal. -/
theorem cechBoundary_iff_mem_reducedIdeal (r : ℂ) (hr : r^3=2) {p : Poly}
    (hp : p.IsHomogeneous 9) : CechBoundary r p 2 4 ↔ p ∈ reducedIdeal r := by
  constructor
  · intro hb
    have ht := (cechBoundary_iff_trace_zero r hr hp).mp hb
    have hm := homogeneous_degreeNine_mod_trace r hr hp
    simpa only [ht, map_zero, zero_mul, sub_zero] using hm
  · exact boundary_of_mem_reducedIdeal r hp

end CycleQ2SeedCech

#print axioms CycleQ2SeedCech.cechResidue_eq_trace
#print axioms CycleQ2SeedCech.cechBoundary_iff_trace_zero
#print axioms CycleQ2SeedCech.cechBoundary_iff_mem_reducedIdeal
end
end


/- Component: continuation_3/SeedQuotientFiniteFree.lean -/
section
/-! # The actual seed quotient is finite free over the three remaining coordinates

The quotient remains `Poly R / (smoothH,smoothF)`.  Regrouping variables is used
only to construct its basis over `R[x₁,x₂,x₃]`; the resulting basis vectors are
the actual classes of `x₀^a*w^b` for `a,b<3`.
-/

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedQuotientFiniteFree

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2IncidenceFirstOrder CycleQ2SegreTangentLocal
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

/-- The nine basis vectors have their actual weighted degree and character.
The coefficient variables all have weighted degree one, so the degree shifts
of the free summands are `a + 2*b`. -/
theorem basisMonomial_homogeneous (ij : Fin 3 × Fin 3) :
    ((X 0 : Poly R) ^ ij.1.val * X 4 ^ ij.2.val).IsWeightedHomogeneous
      fullGrading (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
  have hh := ((isWeightedHomogeneous_X R fullGrading 0).pow ij.1.val).mul
    ((isWeightedHomogeneous_X R fullGrading 4).pow ij.2.val)
  have hg : ij.1.val • fullGrading 0 + ij.2.val • fullGrading 4 =
      (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
    simp [fullGrading, nsmul_eq_mul, mul_comm]
  exact hg ▸ hh

theorem seedBasis_mem_gradedPiece [Nontrivial R] (r ι : R) (ij : Fin 3 × Fin 3) :
    seedBasis R r ι ij ∈ CycleQ2IncidenceGradedBasis.quotientPiece fullGrading
      (smoothH ι) (smoothF r ι)
      (ij.1.val + 2 * ij.2.val, ((2 * ij.1.val : ℕ) : ZMod 3)) := by
  rw [seedBasis_apply]
  exact Submodule.mem_map.mpr ⟨_, basisMonomial_homogeneous R ij, rfl⟩

end CycleQ2SeedQuotientFiniteFree

#print axioms CycleQ2SeedQuotientFiniteFree.seedBasis_apply
#print axioms CycleQ2SeedQuotientFiniteFree.seedQuotient_rank_nine
#print axioms CycleQ2SeedQuotientFiniteFree.seedBasis_mem_gradedPiece
end
end


