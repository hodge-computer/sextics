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

/-! Source partition of GeometricTarget.lean. See solution.md for verification status. -/

set_option Elab.async false

/- Preserved original module body. -/
section
/-!
Target-side algebra for the nonconstructive route in Chapter 3D.

These lemmas concern the protected F and A, not a replacement instance.
They establish the two diagonal actions and the determinant-weighted source.
They do not assert divisor support, a rational primitive, or certificate existence.
-/

noncomputable section
namespace CycleQ2GeometricTarget
open MvPolynomial

abbrev Poly := HodgeComputer.AmbientPoly 5
abbrev F : Poly := HodgeSubmission.F
abbrev A : Poly := HodgeSubmission.A

/-- The protected equation evaluated on an affine representative. -/
def equationValue (z : Fin 6 → ℂ) : ℂ :=
  z 0 ^ 6 + z 1 ^ 6 + z 2 ^ 6 + z 3 ^ 6 + z 4 ^ 6 + z 5 ^ 6 +
    (z 0 ^ 3 * z 1 * z 3 * z 4 +
     z 1 ^ 3 * z 2 * z 4 * z 5 +
     z 2 ^ 3 * z 0 * z 5 * z 3) / 2

def sourceValue (z : Fin 6 → ℂ) : ℂ :=
  z 0 ^ 2 * z 1 ^ 2 * z 2 ^ 3 * z 3 ^ 2 * z 4 ^ 2 * z 5

theorem eval_F (z : Fin 6 → ℂ) : eval z F = equationValue z := by
  norm_num [F, HodgeSubmission.F, equationValue] <;> ring

theorem eval_A (z : Fin 6 → ℂ) : eval z A = sourceValue z := by
  norm_num [A, HodgeSubmission.A, sourceValue] <;> ring

/-- The paired sign on (X2,Y2). -/
def beta (z : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![z 0, z 1, -z 2, z 3, z 4, -z 5]

/-- The order-three action in the ORIGINAL coordinate order. -/
def gamma (ω : ℂ) (z : Fin 6 → ℂ) : Fin 6 → ℂ :=
  ![ω ^ 2 * z 0, ω ^ 2 * z 1, z 2, ω * z 3, z 4, z 5]

def betaDet : ℂ := 1 * 1 * (-1) * 1 * 1 * (-1)
def gammaDet (ω : ℂ) : ℂ := ω ^ 2 * ω ^ 2 * 1 * ω * 1 * 1

theorem beta_involution (z : Fin 6 → ℂ) : beta (beta z) = z := by
  funext i
  fin_cases i <;> simp [beta]

theorem gamma_order_three (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    gamma ω (gamma ω (gamma ω z)) = z := by
  have h6 : ω ^ 6 = 1 := by
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num
  funext i
  fin_cases i <;> dsimp [gamma] <;> ring_nf <;> simp [hω, h6]

theorem beta_gamma_commute (ω : ℂ) (z : Fin 6 → ℂ) :
    beta (gamma ω z) = gamma ω (beta z) := by
  funext i
  fin_cases i <;> simp [beta, gamma]

theorem equationValue_beta (z : Fin 6 → ℂ) :
    equationValue (beta z) = equationValue z := by
  dsimp [equationValue, beta]
  ring

theorem sourceValue_beta (z : Fin 6 → ℂ) :
    sourceValue (beta z) = sourceValue z := by
  dsimp [sourceValue, beta]
  ring

theorem equationValue_gamma (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    equationValue (gamma ω z) = equationValue z := by
  have h6 : ω ^ 6 = 1 := by
    calc
      ω ^ 6 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; norm_num
  have h9 : ω ^ 9 = 1 := by
    calc
      ω ^ 9 = (ω ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hω]; norm_num
  have h12 : ω ^ 12 = 1 := by
    calc
      ω ^ 12 = (ω ^ 3) ^ 4 := by ring
      _ = 1 := by rw [hω]; norm_num
  dsimp [equationValue, gamma]
  ring_nf
  simp [hω, h6, h9, h12] <;> ring

theorem sourceValue_gamma (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    sourceValue (gamma ω z) = ω * sourceValue z := by
  have h10 : ω ^ 10 = ω := by
    calc
      ω ^ 10 = (ω ^ 3) ^ 3 * ω := by ring
      _ = ω := by rw [hω]; ring
  dsimp [sourceValue, gamma]
  ring_nf
  simp [h10]

theorem beta_F (z : Fin 6 → ℂ) : eval (beta z) F = eval z F := by
  rw [eval_F, eval_F]
  exact equationValue_beta z

theorem gamma_F (ω : ℂ) (hω : ω ^ 3 = 1) (z : Fin 6 → ℂ) :
    eval (gamma ω z) F = eval z F := by
  rw [eval_F, eval_F]
  exact equationValue_gamma ω hω z

/-- Invariance of the source times the determinant, not invariance of A alone. -/
theorem beta_source_with_volume (z : Fin 6 → ℂ) :
    betaDet * eval (beta z) A = eval z A := by
  rw [eval_A, eval_A, sourceValue_beta]
  norm_num [betaDet]

theorem gamma_source_with_volume (ω : ℂ) (hω : ω ^ 3 = 1)
    (z : Fin 6 → ℂ) : gammaDet ω * eval (gamma ω z) A = eval z A := by
  rw [eval_A, eval_A, sourceValue_gamma ω hω]
  calc
    gammaDet ω * (ω * sourceValue z) = (ω ^ 3) ^ 2 * sourceValue z := by
      dsimp [gammaDet]
      ring
    _ = sourceValue z := by rw [hω]; simp

/-- Algebraic application data only. Smoothness, geometric support and the
support-to-certificate theorem are NOT encoded as fields of this structure. -/
structure AlgebraicInputs : Prop where
  pole_parameter : HodgeSubmission.q = 2
  hypersurface_ne_zero : F ≠ 0
  hypersurface_homogeneous : F.IsHomogeneous 6
  source_homogeneous : A.IsHomogeneous 12
  paired_sign_equation : ∀ z, eval (beta z) F = eval z F
  paired_sign_source : ∀ z, betaDet * eval (beta z) A = eval z A
  order_three_equation : ∀ ω : ℂ, ω ^ 3 = 1 →
    ∀ z, eval (gamma ω z) F = eval z F
  order_three_source : ∀ ω : ℂ, ω ^ 3 = 1 →
    ∀ z, gammaDet ω * eval (gamma ω z) A = eval z A

theorem algebraicInputs : AlgebraicInputs where
  pole_parameter := rfl
  hypersurface_ne_zero := CycleQ2Workspace.originalF_ne_zero
  hypersurface_homogeneous := CycleQ2Workspace.originalF_homogeneous
  source_homogeneous := CycleQ2Workspace.originalA_homogeneous
  paired_sign_equation := beta_F
  paired_sign_source := beta_source_with_volume
  order_three_equation := gamma_F
  order_three_source := gamma_source_with_volume

#print axioms beta_F
#print axioms gamma_F
#print axioms gamma_source_with_volume
#print axioms algebraicInputs
end CycleQ2GeometricTarget

end
end

/- Component: continuation_3/AffineFiniteDescent.lean -/
section
/-!
# Finite algebraic descent for the actual affine residue

The derivations on a finite extension are constructed from characteristic-zero
algebra, and their compatibility with the protected tangent derivations is
proved.  A primitive over that extension descends by normalized trace.  There
is no Galois assumption and no hypothesis supplying derivative compatibility.
This does not assert the existence of the initial primitive.
-/

noncomputable section

namespace CycleQ2FiniteDifferentialDescent

open scoped BigOperators

section General

variable {K L : Type*} [Field K] [CharZero K] [Field L]
  [Algebra K L] [FiniteDimensional K L]

/-- The canonical extension of a derivation through a finite algebraic field
extension in characteristic zero. -/
def extend (D : Derivation ℤ K K) : Derivation ℤ L L :=
  letI : Differential K := ⟨D⟩
  letI : Differential L := Differential.differentialFiniteDimensional K L
  Differential.deriv

@[simp] theorem extend_algebraMap (D : Derivation ℤ K K) (x : K) :
    extend (L := L) D (algebraMap K L x) = algebraMap K L (D x) := by
  letI : Differential K := ⟨D⟩
  letI : Differential L := Differential.differentialFiniteDimensional K L
  letI : DifferentialAlgebra K L := Differential.differentialAlgebraFiniteDimensional
  exact deriv_algebraMap x

/-- The extension is unique, so the construction is independent of the
primitive element used internally by the field-theoretic construction. -/
theorem extend_unique (D : Derivation ℤ K K) (E : Derivation ℤ L L)
    (hE : ∀ x, E (algebraMap K L x) = algebraMap K L (D x)) :
    extend D = E := by
  letI : Differential K := ⟨D⟩
  letI : Differential L := ⟨E⟩
  letI : DifferentialAlgebra K L := ⟨hE⟩
  let candidate : {_a : Differential L // DifferentialAlgebra K L} :=
    ⟨inferInstance, inferInstance⟩
  have hu := (Differential.uniqueDifferentialAlgebraFiniteDimensional
    (F := K) (K := L)).uniq candidate
  exact (congrArg (fun q => q.val.deriv) hu).symm

theorem extend_lie (D E : Derivation ℤ K K) :
    extend (L := L) ⁅D, E⁆ = ⁅extend (L := L) D, extend (L := L) E⁆ := by
  apply extend_unique
  intro x
  simp only [Derivation.commutator_apply, extend_algebraMap, map_sub]

@[simp] theorem extend_zero : extend (L := L) (0 : Derivation ℤ K K) = 0 := by
  apply extend_unique
  intro x
  simp

/-- Commuting coordinate directions remain commuting on the finite field. -/
theorem extend_commute (D E : Derivation ℤ K K)
    (hDE : ∀ x, D (E x) = E (D x)) (z : L) :
    extend D (extend E z) = extend E (extend D z) := by
  have hzero : ⁅D, E⁆ = 0 := by
    ext x
    simp only [Derivation.commutator_apply, hDE x, sub_self, Derivation.zero_apply]
  have hcomm : ⁅extend (L := L) D, extend (L := L) E⁆ = 0 := by
    rw [← extend_lie, hzero, extend_zero]
  exact sub_eq_zero.mp (congrArg (fun δ : Derivation ℤ L L => δ z) hcomm)

/-- This is a genuine finite-extension descent theorem with constructed
operators, rather than assumed extensions of the base derivations. -/
theorem residue_solution_descends {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (g r : K) (w : ι → L)
    (hw : HoldoutConstruction.residueDivergence (fun i => extend (D i))
      (algebraMap K L g) w = algebraMap K L r) :
    HoldoutConstruction.residueDivergence D g
      (fun i => Algebra.normalizedTrace K L (w i)) = r := by
  exact HoldoutConstruction.finiteNormalizedTrace_residue_solution D
    (fun i => extend (D i)) (fun i x => extend_algebraMap (D i) x) g r w hw

theorem residue_solution_ascends {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (g : K) (w : ι → K) :
    HoldoutConstruction.residueDivergence (fun i => extend (L := L) (D i))
      (algebraMap K L g) (fun i => algebraMap K L (w i)) =
      algebraMap K L (HoldoutConstruction.residueDivergence D g w) := by
  simp only [HoldoutConstruction.residueDivergence,
    HoldoutConstruction.fieldDivergence, extend_algebraMap,
    map_sub, map_sum, map_div₀, map_mul]

end General

end CycleQ2FiniteDifferentialDescent

namespace CycleQ2AffineFiniteDescent

open MvPolynomial HodgeComputer CycleQ2AffineHypersurface
  CycleQ2AffineClearing CycleQ2AffineResidueClosure
open scoped BigOperators

abbrev K := AffineFunctionField

local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

local instance coefficientIntAlgebra : Algebra ℤ K := Ring.toIntAlgebra _

variable (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

/-- Actual protected tangents extended to the supplied finite field. -/
def tangent (j : Fin 4) : Derivation ℤ L L :=
  CycleQ2FiniteDifferentialDescent.extend (affineTangent j)

@[simp] theorem tangent_algebraMap (j : Fin 4) (x : K) :
    tangent L j (algebraMap K L x) = algebraMap K L (affineTangent j x) :=
  CycleQ2FiniteDifferentialDescent.extend_algebraMap (affineTangent j) x

theorem tangents_commute (i j : Fin 4) :
    Function.Commute (tangent L i) (tangent L j) :=
  CycleQ2FiniteDifferentialDescent.extend_commute
    (affineTangent i) (affineTangent j) (affineTangents_commute i j)

/-- The actual complex constants still have zero derivative. -/
@[simp] theorem tangent_complex_constant (j : Fin 4) (c : ℂ) :
    tangent L j (algebraMap K L (algebraMap ℂ K c)) = 0 := by
  rw [tangent_algebraMap, CycleQ2AffineDifferentials.tangent_complex_constant, map_zero]

/-- The source, normal density, and derivative operators are all the actual
protected data, transported through the field's algebra map. -/
def residueExpression (A : AmbientPoly 4) (w : Fin 4 → L) : L :=
  algebraMap K L (affineNormalSource A) +
    HoldoutConstruction.residueDivergence (tangent L)
      (algebraMap K L (affineMap (pderiv 0 affineF))) w

theorem primitive_descends (A : AmbientPoly 4) (w : Fin 4 → L)
    (hw : residueExpression L A w = 0) :
    affineResidueExpression A
      (fun i => Algebra.normalizedTrace K L (w i)) = 0 := by
  have he : HoldoutConstruction.residueDivergence (tangent L)
      (algebraMap K L (affineMap (pderiv 0 affineF))) w =
      algebraMap K L (-affineNormalSource A) := by
    rw [map_neg]
    exact eq_neg_of_add_eq_zero_right hw
  have hd := CycleQ2FiniteDifferentialDescent.residue_solution_descends
    affineTangent (affineMap (pderiv 0 affineF)) (-affineNormalSource A) w he
  change affineNormalSource A + _ = 0
  rw [hd, add_neg_cancel]

theorem primitive_ascends (A : AmbientPoly 4) (w : Fin 4 → K) :
    residueExpression L A (fun i => algebraMap K L (w i)) =
      algebraMap K L (affineResidueExpression A w) := by
  unfold residueExpression affineResidueExpression tangent
  rw [CycleQ2FiniteDifferentialDescent.residue_solution_ascends, map_add]

theorem primitive_exists_iff (A : AmbientPoly 4) :
    (∃ w : Fin 4 → L, residueExpression L A w = 0) ↔
      ∃ w : Fin 4 → K, affineResidueExpression A w = 0 := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨fun i => Algebra.normalizedTrace K L (w i), primitive_descends L A w hw⟩
  · rintro ⟨w, hw⟩
    exact ⟨fun i => algebraMap K L (w i), by rw [primitive_ascends, hw, map_zero]⟩

/-- Finite algebraic coefficients introduce no extra obstruction to obtaining
the unchanged protected certificate. -/
theorem protected_certificate_of_finite_extension_primitive
    (h : ∃ w : Fin 4 → L, residueExpression L affineA w = 0) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A := by
  exact protected_certificate_of_affine_residue_primitive
    ((primitive_exists_iff L affineA).mp h)

end CycleQ2AffineFiniteDescent

#print axioms CycleQ2FiniteDifferentialDescent.extend_algebraMap
#print axioms CycleQ2FiniteDifferentialDescent.extend_commute
#print axioms CycleQ2AffineFiniteDescent.primitive_exists_iff
#print axioms CycleQ2AffineFiniteDescent.protected_certificate_of_finite_extension_primitive
end
end


/- Component: continuation_3/AffineGenericSpecialization.lean -/
section
/-!
# Specialization of the actual generic residue equation

The total space of the pencil `f + t H = 0` has the rational function field
`ℂ(x₀,...,x₄)`, with base parameter `t = -f/H`.  Thus the generic field can
be built using the existing ambient rational function field; an abstract
quotient-field embedding need not be assumed.  The Hensel root at the exact
protected member gives a faithful Laurent-series embedding.  The generic
tangent operators fix the actual pencil parameter, and their compatibility
with the coefficient derivations is proved from the implicit equation.

Taking the zeroth Laurent coefficient then specializes a generic rational
primitive, including one with a pole in the parameter.  This module does
not assert that such a generic primitive exists.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
noncomputable section

namespace CycleQ2GenericSpecialization

open MvPolynomial HodgeComputer HodgeTestbed.Conic CycleQ2Bridge CycleQ2AffineClearing
  CycleQ2AffineGeometry CycleQ2AffineHypersurface CycleQ2AffineDifferentials
  CycleQ2AffineResidueClosure CycleQ2FormalSpecialization HoldoutConstruction
open scoped BigOperators

abbrev Poly := AmbientPoly 4
abbrev K := AffineFunctionField
abbrev RF := RationalFunction 4
abbrev S := PowerSeries K
abbrev L := HahnSeries ℤ K

local instance rationalAlgebra : Algebra ℚ RF := DivisionRing.toRatAlgebra
local instance rationalModule : Module ℚ RF := Algebra.toModule
local instance coefficientAlgebra : Algebra ℂ L := HahnSeries.instAlgebra
local instance coefficientCharZero : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

/-- The exact three mixed terms, including the protected coefficient one half. -/
def mixed : Poly := C (1 / 2 : ℂ) *
  (X 0 * X 2 * X 3 + X 0 ^ 3 * X 1 * X 3 * X 4 + X 1 ^ 3 * X 4 * X 2)

def fermat : Poly := 1 + X 0 ^ 6 + X 1 ^ 6 + X 2 ^ 6 + X 3 ^ 6 + X 4 ^ 6

theorem affineF_eq : affineF = fermat + mixed := affineF_formula

/-- Zero is the protected member; minus one is the Fermat member. -/
def pencil : Polynomial Poly := Polynomial.C affineF + Polynomial.X * Polynomial.C mixed

@[simp] theorem pencil_zero : pencil.eval 0 = affineF := by simp [pencil]

@[simp] theorem pencil_neg_one : pencil.eval (-1) = fermat := by
  simp only [pencil, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_X, affineF_eq]
  ring

private def degreeTest : Poly →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 0, 1, 1, 0]

private theorem degreeTest_F :
    degreeTest affineF = Polynomial.X ^ 6 + Polynomial.C (1 / 2 : ℂ) * Polynomial.X + 3 := by
  rw [affineF_formula]
  norm_num [degreeTest]
  dsimp
  ring

private theorem degreeTest_mixed :
    degreeTest mixed = Polynomial.C (1 / 2 : ℂ) * Polynomial.X := by
  norm_num [degreeTest, mixed]
  dsimp
  ring

/-- The deformation direction does not vanish at the generic point of the
protected hypersurface. This is a concrete polynomial degree calculation. -/
theorem affineF_not_dvd_mixed : ¬ affineF ∣ mixed := by
  intro h
  have htest := map_dvd degreeTest h
  rw [degreeTest_F, degreeTest_mixed] at htest
  have hsmall : (Polynomial.C (1 / 2 : ℂ) * Polynomial.X).natDegree = 1 := by
    compute_degree!
  have hlarge : (Polynomial.X ^ 6 + Polynomial.C (1 / 2 : ℂ) * Polynomial.X + 3).natDegree = 6 := by
    compute_degree!
  have hnz : Polynomial.C (1 / 2 : ℂ) * Polynomial.X ≠ 0 := by
    exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num)) Polynomial.X_ne_zero
  have hle := Polynomial.natDegree_le_of_dvd htest hnz
  rw [hsmall, hlarge] at hle
  omega

theorem mixed_residue_ne_zero : affineMap mixed ≠ 0 := by
  intro h
  exact affineF_not_dvd_mixed ((affineMap_kernel mixed).mp h)

theorem mixed_ne_zero : mixed ≠ 0 := by
  intro h
  exact mixed_residue_ne_zero (by rw [h, map_zero])

/-- Any direction surviving on the protected target is permitted. This
allows a line chosen by algebraic avoidance, rather than fixing one line
that might lie in the exceptional locus of a geometric theorem. -/
structure Direction where
  polynomial : Poly
  residue_ne_zero : affineMap polynomial ≠ 0

theorem Direction.polynomial_ne_zero (d : Direction) : d.polynomial ≠ 0 := by
  intro h
  exact d.residue_ne_zero (by rw [h, map_zero])

def protectedDirection : Direction := ⟨mixed, mixed_residue_ne_zero⟩

private def normalVariableMap : Poly →+* MvPolynomial (Fin 1) S :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C.comp (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)))
    (Fin.cases (MvPolynomial.X 0)
      (fun j => MvPolynomial.C (PowerSeries.C (fieldCoordinate j.succ))))

private def constantVariableEval : MvPolynomial (Fin 1) S →+* K :=
  MvPolynomial.eval₂Hom PowerSeries.constantCoeff (fun _ => fieldCoordinate 0)

private def seriesVariableEval (z : S) : MvPolynomial (Fin 1) S →+* S :=
  MvPolynomial.eval₂Hom (RingHom.id S) (fun _ => z)

@[simp] private theorem normalVariableMap_C (c : ℂ) :
    normalVariableMap (MvPolynomial.C c) =
      MvPolynomial.C (PowerSeries.C (affineMap (MvPolynomial.C c))) := by
  simp [normalVariableMap]

@[simp] private theorem normalVariableMap_X_zero :
    normalVariableMap (MvPolynomial.X (0 : Fin 5)) = MvPolynomial.X 0 := by
  simp [normalVariableMap]

@[simp] private theorem normalVariableMap_X_succ (j : Fin 4) :
    normalVariableMap (MvPolynomial.X j.succ) =
      MvPolynomial.C (PowerSeries.C (fieldCoordinate j.succ)) := by
  simp [normalVariableMap]

private theorem constantVariableEval_normalVariableMap (P : Poly) :
    constantVariableEval (normalVariableMap P) = affineMap P := by
  have h : constantVariableEval.comp normalVariableMap = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [constantVariableEval]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [constantVariableEval, fieldCoordinate]
      · simp [constantVariableEval, fieldCoordinate]
  exact RingHom.congr_fun h P

private theorem normalVariableMap_derivative (P : Poly) :
    pderiv (0 : Fin 1) (normalVariableMap P) =
      normalVariableMap (pderiv (0 : Fin 5) P) := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp only [map_add, hP, hQ]
  | mul_X P i hP =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [map_mul, pderiv_mul, normalVariableMap_X_zero,
          pderiv_X_self, mul_one, map_add, hP, map_one]
      · simp only [map_mul, pderiv_mul, normalVariableMap_X_succ,
          pderiv_C, pderiv_X, Pi.single_apply, Fin.succ_ne_zero,
          if_false, mul_zero, add_zero, map_add, map_zero, hP]

private def rootPolynomial (H : Poly) : MvPolynomial (Fin 1) S :=
  normalVariableMap affineF + MvPolynomial.C PowerSeries.X * normalVariableMap H

/-- A genuine formal point of every polynomial pencil through the protected
member. The actual nonzero normal derivative supplies the Jacobian unit. -/
theorem direction_formal_coordinate_exists (H : Poly) :
    ∃ z : S, seriesVariableEval z (rootPolynomial H) = 0 ∧
      z.constantCoeff = fieldCoordinate 0 := by
  have hs : constantVariableEval (rootPolynomial H) = 0 := by
    simp [rootPolynomial, constantVariableEval_normalVariableMap,
      show constantVariableEval (MvPolynomial.C PowerSeries.X) = 0 by
        simp [constantVariableEval]]
  have hd : constantVariableEval (pderiv (0 : Fin 1) (rootPolynomial H)) =
      affineMap (pderiv 0 affineF) := by
    simp only [rootPolynomial, map_add, pderiv_mul, pderiv_C,
      normalVariableMap_derivative, zero_mul, zero_add, map_mul,
      constantVariableEval_normalVariableMap]
    simp [constantVariableEval]
  have hj : IsUnit (Matrix.det (fun i j : Fin 1 =>
      MvPolynomial.eval₂ PowerSeries.constantCoeff (fun _ => fieldCoordinate 0)
        (pderiv i (rootPolynomial H)))) := by
    rw [Matrix.det_fin_one]
    change IsUnit (constantVariableEval (pderiv 0 (rootPolynomial H)))
    rw [hd]
    exact isUnit_iff_ne_zero.mpr normal_ne_zero
  obtain ⟨x, hx, heq⟩ := CycleQ2SquareAdicLifting.square_system_powerSeries_lift
    (fun _ : Fin 1 => rootPolynomial H) (fun _ => fieldCoordinate 0)
    (fun _ => hs) hj
  refine ⟨x 0, ?_, hx 0⟩
  have hx' : (fun _ : Fin 1 => x 0) = x := by
    funext i
    fin_cases i
    rfl
  change MvPolynomial.eval₂ (RingHom.id S) (fun _ => x 0) (rootPolynomial H) = 0
  rw [hx']
  exact heq 0

def formalRoot (direction : Direction) : S := Classical.choose (direction_formal_coordinate_exists direction.polynomial)

theorem formalRoot_equation (direction : Direction) : seriesVariableEval (formalRoot direction) (rootPolynomial direction.polynomial) = 0 :=
  (Classical.choose_spec (direction_formal_coordinate_exists direction.polynomial)).1

@[simp] theorem formalRoot_constantCoeff (direction : Direction) :
    (formalRoot direction).constantCoeff = fieldCoordinate 0 :=
  (Classical.choose_spec (direction_formal_coordinate_exists direction.polynomial)).2

def formalCoordinates (direction : Direction) : Fin 5 → S :=
  Fin.cases (formalRoot direction) (fun j => PowerSeries.C (fieldCoordinate j.succ))

def formalMap (direction : Direction) : Poly →+* S :=
  MvPolynomial.eval₂Hom (PowerSeries.C.comp (affineMap.comp MvPolynomial.C)) (formalCoordinates direction)

@[simp] theorem formalMap_C (direction : Direction) (c : ℂ) :
    (formalMap direction) (MvPolynomial.C c) = PowerSeries.C (affineMap (MvPolynomial.C c)) := by
  simp [formalMap]

@[simp] theorem formalMap_X_zero (direction : Direction) : (formalMap direction) (MvPolynomial.X (0 : Fin 5)) = (formalRoot direction) := by
  simp [formalMap, formalCoordinates]

@[simp] theorem formalMap_X_succ (direction : Direction) (j : Fin 4) :
    (formalMap direction) (MvPolynomial.X j.succ) = PowerSeries.C (fieldCoordinate j.succ) := by
  simp [formalMap, formalCoordinates]

/-- The constant term is the actual protected quotient map on all polynomials. -/
theorem constantCoeff_formalMap (direction : Direction) (P : Poly) :
    ((formalMap direction) P).constantCoeff = affineMap P := by
  have h : (PowerSeries.constantCoeff (R := K)).comp (formalMap direction) = affineMap := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [fieldCoordinate]
      · simp [fieldCoordinate]
  exact RingHom.congr_fun h P

/-- The chosen root solves the exact pencil, with its specified parameter. -/
theorem formalMap_pencil (direction : Direction) : (formalMap direction) affineF + PowerSeries.X * (formalMap direction) direction.polynomial = 0 := by
  have hm : (seriesVariableEval (formalRoot direction)).comp normalVariableMap = (formalMap direction) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [seriesVariableEval]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [seriesVariableEval]
      · simp [seriesVariableEval]
  have hm' (P : Poly) := RingHom.congr_fun hm P
  have hc : seriesVariableEval (formalRoot direction) (MvPolynomial.C PowerSeries.X) = PowerSeries.X := by
    simp [seriesVariableEval]
  have h := formalRoot_equation direction
  simp only [rootPolynomial, map_add, map_mul, hc] at h
  simpa only [← RingHom.comp_apply, hm] using h

/-- For the protected three-term direction, the general construction solves
the literal `targetFamily` already used by the existing Hensel chart. -/
theorem protected_formalRoot_targetFamily :
    targetFamily.eval (formalRoot protectedDirection) = 0 := by
  have h := formalMap_pencil protectedDirection
  change formalMap protectedDirection affineF +
    PowerSeries.X * formalMap protectedDirection mixed = 0 at h
  have hc : formalMap protectedDirection (MvPolynomial.C (1 / 2 : ℂ)) =
      PowerSeries.C (1 / 2 : K) := by
    rw [formalMap_C]
    congr 1
    change (affineMap.comp MvPolynomial.C) (1 / 2 : ℂ) = _
    rw [map_div₀, map_one, map_ofNat]
  have h1 : formalMap protectedDirection (MvPolynomial.X (1 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 1) := formalMap_X_succ protectedDirection 0
  have h2 : formalMap protectedDirection (MvPolynomial.X (2 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 2) := formalMap_X_succ protectedDirection 1
  have h3 : formalMap protectedDirection (MvPolynomial.X (3 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 3) := formalMap_X_succ protectedDirection 2
  have h4 : formalMap protectedDirection (MvPolynomial.X (4 : Fin 5)) =
      PowerSeries.C (fieldCoordinate 4) := formalMap_X_succ protectedDirection 3
  have hf := congrArg (formalMap protectedDirection) affineF_formula
  rw [hf] at h
  simp only [mixed, map_add, map_mul, map_pow, map_one, hc, formalMap_X_zero,
    h1, h2, h3, h4] at h
  norm_num only [targetFamily, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
  simp only [map_add, map_mul, map_pow, map_one]
  linear_combination h

theorem formalMap_direction_ne_zero (direction : Direction) : (formalMap direction) direction.polynomial ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
  rw [constantCoeff_formalMap, map_zero] at hc
  exact direction.residue_ne_zero hc

theorem formalMap_F_ne_zero (direction : Direction) : (formalMap direction) affineF ≠ 0 := by
  have hf : (formalMap direction) affineF = -PowerSeries.X * (formalMap direction) direction.polynomial := by
    linear_combination (formalMap_pencil direction)
  rw [hf]
  exact mul_ne_zero (neg_ne_zero.mpr PowerSeries.X_ne_zero) (formalMap_direction_ne_zero direction)

/-- Faithfulness follows from the exact target's irreducibility and the
nonzero image of f. No injectivity premise is passed to this theorem. -/
theorem formalMap_injective (direction : Direction) : Function.Injective (formalMap direction) := by
  have hnonzero (P : Poly) (hP : P ≠ 0) : (formalMap direction) P ≠ 0 := by
    obtain ⟨m, U, hFU, hfactor⟩ := WfDvdMonoid.max_power_factor hP affineF_irreducible
    have hU : (formalMap direction) U ≠ 0 := by
      intro h
      have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
      rw [constantCoeff_formalMap, map_zero] at hc
      exact hFU ((affineMap_kernel U).mp hc)
    rw [hfactor, map_mul, map_pow]
    exact mul_ne_zero (pow_ne_zero _ (formalMap_F_ne_zero direction)) hU
  intro P Q h
  by_contra hn
  exact hnonzero (P - Q) (sub_ne_zero.mpr hn) (by rw [map_sub, h, sub_self])

def formalAlgHom (direction : Direction) : Poly →ₐ[ℂ] S where
  toRingHom := (formalMap direction)
  commutes' c := by
    change (formalMap direction) (MvPolynomial.C c) = algebraMap ℂ S c
    rw [formalMap_C, PowerSeries.algebraMap_apply]
    rfl

def laurentPolynomial (direction : Direction) : Poly →ₐ[ℂ] L where
  toRingHom := (HahnSeries.ofPowerSeries ℤ K).comp (formalMap direction)
  commutes' c := by
    change HahnSeries.ofPowerSeries ℤ K ((formalMap direction) (MvPolynomial.C c)) = algebraMap ℂ L c
    rw [formalMap_C, HahnSeries.ofPowerSeries_C]
    rfl

theorem laurentPolynomial_injective (direction : Direction) : Function.Injective (laurentPolynomial direction) := by
  exact HahnSeries.ofPowerSeries_injective.comp (formalMap_injective direction)

/-- The actual generic field of the pencil, realized as the ambient rational
field with parameter -f/H, embeds faithfully at the protected target. -/
def specialize (direction : Direction) : RF →ₐ[ℂ] L :=
  IsFractionRing.liftAlgHom (g := (laurentPolynomial direction)) (laurentPolynomial_injective direction)

@[simp] theorem specialize_polynomial (direction : Direction) (P : Poly) :
    (specialize direction) (polynomialMap 4 P) = HahnSeries.ofPowerSeries ℤ K ((formalMap direction) P) :=
  IsLocalization.lift_eq _ P

theorem specialize_injective (direction : Direction) : Function.Injective (specialize direction) := (specialize direction).injective

def parameter (direction : Direction) : RF := -polynomialMap 4 affineF / polynomialMap 4 direction.polynomial

theorem generic_pencil_equation (direction : Direction) :
    polynomialMap 4 affineF + (parameter direction) * polynomialMap 4 direction.polynomial = 0 := by
  unfold parameter
  field_simp [polynomialMap_ne_zero direction.polynomial_ne_zero] <;> ring

/-- The actual coordinate equation of the total pencil, before localization. -/
def totalEquation (direction : Direction) : Polynomial Poly :=
  Polynomial.C affineF + Polynomial.X * Polynomial.C direction.polynomial

@[simp] theorem totalEquation_protected : totalEquation protectedDirection = pencil := rfl

def genericEvaluation (direction : Direction) : Polynomial Poly →+* RF :=
  Polynomial.eval₂RingHom (polynomialMap 4) (parameter direction)

theorem totalEquation_primitive (direction : Direction) :
    (totalEquation direction).IsPrimitive := by
  intro r hr
  have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r (totalEquation direction)).mp hr
  have hf : r ∣ affineF := by simpa [totalEquation] using hcoeff 0
  have hh : r ∣ direction.polynomial := by simpa [totalEquation] using hcoeff 1
  have hrel : IsRelPrime affineF direction.polynomial :=
    affineF_irreducible.isRelPrime_iff_not_dvd.mpr (by
      intro hdiv
      exact direction.residue_ne_zero ((affineMap_kernel direction.polynomial).mpr hdiv))
  exact hrel hf hh

theorem totalEquation_fraction_factorization (direction : Direction) :
    (totalEquation direction).map (polynomialMap 4) =
      Polynomial.C (polynomialMap 4 direction.polynomial) *
        (Polynomial.X - Polynomial.C (parameter direction)) := by
  have h : polynomialMap 4 direction.polynomial * parameter direction = -polynomialMap 4 affineF := by
    unfold parameter
    field_simp [polynomialMap_ne_zero direction.polynomial_ne_zero] <;> ring
  simp only [totalEquation, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C]
  rw [mul_sub, ← Polynomial.C_mul, h, Polynomial.C_neg]
  ring

/-- The generic hypersurface has exactly the stipulated defining equation.
This proves faithfulness of the hypersurface model, not merely its relation. -/
theorem genericEvaluation_kernel (direction : Direction) (P : Polynomial Poly) :
    genericEvaluation direction P = 0 ↔ totalEquation direction ∣ P := by
  constructor
  · intro hP
    apply (totalEquation_primitive direction).dvd_of_fraction_map_dvd_fraction_map (K := RF)
    rw [totalEquation_fraction_factorization]
    have hroot : (P.map (polynomialMap 4)).IsRoot (parameter direction) := by
      simpa only [Polynomial.IsRoot, Polynomial.eval_map, genericEvaluation,
        Polynomial.coe_eval₂RingHom] using hP
    obtain ⟨Q, hQ⟩ := Polynomial.dvd_iff_isRoot.mpr hroot
    refine ⟨Polynomial.C ((polynomialMap 4 direction.polynomial)⁻¹) * Q, ?_⟩
    have hu : Polynomial.C (polynomialMap 4 direction.polynomial) *
        Polynomial.C ((polynomialMap 4 direction.polynomial)⁻¹) = (1 : Polynomial RF) := by
      rw [← Polynomial.C_mul, mul_inv_cancel₀ (polynomialMap_ne_zero direction.polynomial_ne_zero),
        Polynomial.C_1]
    calc
      P.map (polynomialMap 4) = (Polynomial.X - Polynomial.C (parameter direction)) * Q := hQ
      _ = (Polynomial.C (polynomialMap 4 direction.polynomial) *
          Polynomial.C ((polynomialMap 4 direction.polynomial)⁻¹)) *
          ((Polynomial.X - Polynomial.C (parameter direction)) * Q) := by rw [hu, one_mul]
      _ = _ := by ring
  · rintro ⟨Q, rfl⟩
    rw [map_mul]
    have he : genericEvaluation direction (totalEquation direction) = 0 := by
      simpa only [genericEvaluation, totalEquation, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
        Polynomial.eval₂_X] using generic_pencil_equation direction
    rw [he, zero_mul]

/-- The quotient coordinate ring of the actual total hypersurface. -/
abbrev GenericCoordinateRing (direction : Direction) :=
  Polynomial Poly ⧸ Ideal.span {totalEquation direction}

def genericCoordinateMap (direction : Direction) : GenericCoordinateRing direction →+* RF :=
  Ideal.Quotient.lift _ (genericEvaluation direction) (by
    intro P hP
    exact (genericEvaluation_kernel direction P).mpr (Ideal.mem_span_singleton.mp hP))

theorem genericCoordinateMap_injective (direction : Direction) :
    Function.Injective (genericCoordinateMap direction) := by
  intro x y hxy
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective y
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  apply (genericEvaluation_kernel direction (P - Q)).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hxy

/-- Every element of RF is a fraction of elements in the faithful total
hypersurface coordinate ring. Together with the kernel theorem this
identifies RF as that hypersurface's function field. -/
theorem generic_rational_generation (direction : Direction) (z : RF) :
    ∃ P Q : Polynomial Poly, genericEvaluation direction Q ≠ 0 ∧
      z = genericEvaluation direction P / genericEvaluation direction Q := by
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective Poly z
  refine ⟨Polynomial.C p, Polynomial.C q, ?_, ?_⟩
  · simpa only [genericEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq : polynomialMap 4 q ≠ 0)
  · simpa only [genericEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C] using hpq.symm

instance genericCoordinateRing_isDomain (direction : Direction) :
    IsDomain (GenericCoordinateRing direction) :=
  Function.Injective.isDomain (genericCoordinateMap direction) (genericCoordinateMap_injective direction)

/-- The ambient rational-field realization is formally a fraction field of
the actual quotient by f+tH, with the proved quotient embedding as structure map. -/
def genericFractionRing (direction : Direction) :
    letI : Algebra (GenericCoordinateRing direction) RF := (genericCoordinateMap direction).toAlgebra
    IsFractionRing (GenericCoordinateRing direction) RF := by
  letI : Algebra (GenericCoordinateRing direction) RF := (genericCoordinateMap direction).toAlgebra
  have hmap := RingHom.algebraMap_toAlgebra (R := GenericCoordinateRing direction) (S := RF)
    (genericCoordinateMap direction)
  apply (isLocalization_iff _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · intro q
    apply isUnit_iff_ne_zero.mpr
    intro hzero
    rw [hmap] at hzero
    have hz : (q : GenericCoordinateRing direction) = 0 :=
      genericCoordinateMap_injective direction (by simpa only [map_zero] using hzero)
    exact (mem_nonZeroDivisors_iff_ne_zero.mp q.property) hz
  · intro z
    obtain ⟨P, Q, hQ, hz⟩ := generic_rational_generation direction z
    let q : GenericCoordinateRing direction := Ideal.Quotient.mk _ Q
    have hq : q ≠ 0 := by
      intro hzero
      apply hQ
      change genericCoordinateMap direction q = 0
      rw [hzero, map_zero]
    refine ⟨(Ideal.Quotient.mk _ P, ⟨q, mem_nonZeroDivisors_iff_ne_zero.mpr hq⟩), ?_⟩
    change z * genericEvaluation direction Q = genericEvaluation direction P
    exact (eq_div_iff hQ).mp hz
  · intro x y hxy
    have he := genericCoordinateMap_injective direction hxy
    exact ⟨1, by simpa only [OneMemClass.coe_one, one_mul] using he⟩

/-- The field embedding sends the true base parameter to the formal parameter. -/
theorem specialize_parameter (direction : Direction) : (specialize direction) (parameter direction) = HahnSeries.single 1 1 := by
  have hF := congrArg (HahnSeries.ofPowerSeries ℤ K) (formalMap_pencil direction)
  simp only [map_add, map_mul, map_zero, HahnSeries.ofPowerSeries_X] at hF
  have hH : HahnSeries.ofPowerSeries ℤ K ((formalMap direction) direction.polynomial) ≠ 0 := by
    rw [← specialize_polynomial]
    exact (map_ne_zero (specialize direction)).mpr (polynomialMap_ne_zero direction.polynomial_ne_zero)
  simp only [parameter, map_div₀, map_neg, specialize_polynomial]
  apply (div_eq_iff hH).mpr
  linear_combination -hF

/-- A polynomial in the formal parameter, with the actual complex constants. -/
def parameterSeries : Polynomial ℂ →+* L :=
  (algebraMap (Polynomial K) L).comp (Polynomial.mapRingHom (algebraMap ℂ K))

theorem parameterSeries_injective : Function.Injective parameterSeries :=
  (Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).comp
    (Polynomial.map_injective _ (algebraMap ℂ K).injective)

theorem specialize_parameterPolynomial (direction : Direction) (p : Polynomial ℂ) :
    specialize direction (Polynomial.aeval (R := ℂ) (parameter direction) p) = parameterSeries p := by
  have h : (specialize direction).toRingHom.comp
      (Polynomial.aeval (R := ℂ) (parameter direction)).toRingHom = parameterSeries := by
    apply Polynomial.ringHom_ext
    · intro c
      change specialize direction (Polynomial.aeval (R := ℂ) (parameter direction) (Polynomial.C c)) =
        algebraMap (Polynomial K) L ((Polynomial.C c).map (algebraMap ℂ K))
      simp only [Polynomial.aeval_C, AlgHom.commutes, Polynomial.map_C,
        Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_C, HahnSeries.ofPowerSeries_C]
      rfl
    · change specialize direction (Polynomial.aeval (R := ℂ) (parameter direction) Polynomial.X) =
        algebraMap (Polynomial K) L (Polynomial.X.map (algebraMap ℂ K))
      simp only [Polynomial.aeval_X, specialize_parameter, Polynomial.map_X,
        Polynomial.algebraMap_hahnSeries_apply, Polynomial.coe_X, HahnSeries.ofPowerSeries_X]
  exact RingHom.congr_fun h p

/-- The base parameter is transcendental, as required for an honest C(t)
generic fiber. Its image is the formal indeterminate, not a complex scalar. -/
theorem parameterPolynomial_injective (direction : Direction) :
    Function.Injective (Polynomial.aeval (R := ℂ) (parameter direction)) := by
  intro p q hpq
  apply parameterSeries_injective
  simpa only [specialize_parameterPolynomial] using congrArg (specialize direction) hpq

theorem parameter_transcendental (direction : Direction) :
    Transcendental ℂ (parameter direction) :=
  transcendental_iff_injective.mpr (parameterPolynomial_injective direction)

abbrev Base := FractionRing (Polynomial ℂ)

/-- The actual inclusion C(t) ⊂ C(x₀,...,x₄) defined by t=-f/H. -/
def baseEmbedding (direction : Direction) : Base →ₐ[ℂ] RF :=
  IsFractionRing.liftAlgHom
    (g := Polynomial.aeval (R := ℂ) (parameter direction)) (parameterPolynomial_injective direction)

@[simp] theorem baseEmbedding_polynomial (direction : Direction) (p : Polynomial ℂ) :
    baseEmbedding direction (algebraMap (Polynomial ℂ) Base p) =
      Polynomial.aeval (R := ℂ) (parameter direction) p := IsLocalization.lift_eq _ p

/-- Complex-linear ambient coordinate derivations. -/
def ambientPartial (direction : Direction) (i : Fin 5) : Derivation ℂ RF RF where
  toFun := rationalPartial 4 i
  map_add' := (rationalPartial 4 i).map_add
  map_smul' c z := by
    have hc : rationalPartial 4 i (algebraMap ℂ RF c) = 0 := by
      change rationalPartial 4 i (polynomialMap 4 (MvPolynomial.C c)) = 0
      rw [rationalPartial_map, pderiv_C, map_zero]
    simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
      hc, mul_zero, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
  map_one_eq_zero' := (rationalPartial 4 i).map_one_eq_zero
  leibniz' := (rationalPartial 4 i).leibniz

@[simp] theorem partial_polynomial (direction : Direction) (i : Fin 5) (P : Poly) :
    (ambientPartial direction) i (polynomialMap 4 P) = polynomialMap 4 (pderiv i P) :=
  rationalPartial_map i P

/-- Coordinate ambientPartial of the pencil, with its base parameter held fixed. -/
def familyPartial (direction : Direction) (i : Fin 5) : RF :=
  polynomialMap 4 (pderiv i affineF) + (parameter direction) * polynomialMap 4 (pderiv i direction.polynomial)

def formalPartial (direction : Direction) (i : Fin 5) : S :=
  (formalMap direction) (pderiv i affineF) + PowerSeries.X * (formalMap direction) (pderiv i direction.polynomial)

@[simp] theorem constantCoeff_formalPartial (direction : Direction) (i : Fin 5) :
    ((formalPartial direction) i).constantCoeff = affineMap (pderiv i affineF) := by
  simp [formalPartial, constantCoeff_formalMap]

@[simp] theorem specialize_familyPartial (direction : Direction) (i : Fin 5) :
    (specialize direction) ((familyPartial direction) i) = HahnSeries.ofPowerSeries ℤ K ((formalPartial direction) i) := by
  simp only [familyPartial, formalPartial, map_add, map_mul, specialize_parameter,
    specialize_polynomial, HahnSeries.ofPowerSeries_X]

theorem formalPartial_zero_ne_zero (direction : Direction) : (formalPartial direction) 0 ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.constantCoeff (R := K)) h
  rw [constantCoeff_formalPartial, map_zero] at hc
  exact normal_ne_zero hc

theorem familyPartial_zero_ne_zero (direction : Direction) : (familyPartial direction) 0 ≠ 0 := by
  intro h
  have hs := congrArg (specialize direction) h
  rw [specialize_familyPartial, map_zero] at hs
  apply formalPartial_zero_ne_zero direction
  apply HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := K)
  simpa only [map_zero] using hs

/-- The generic tangents to the fixed-parameter hypersurface. -/
def tangent (direction : Direction) (j : Fin 4) : Derivation ℂ RF RF :=
  (ambientPartial direction) j.succ - ((familyPartial direction) j.succ / (familyPartial direction) 0) • (ambientPartial direction) 0

theorem tangent_apply (direction : Direction) (j : Fin 4) (z : RF) :
    (tangent direction) j z = (ambientPartial direction) j.succ z - (familyPartial direction) j.succ / (familyPartial direction) 0 * (ambientPartial direction) 0 z := by
  simp only [tangent, Derivation.sub_apply, Derivation.smul_apply, smul_eq_mul]

theorem partial_parameter (direction : Direction) (i : Fin 5) :
    (ambientPartial direction) i (parameter direction) = -(familyPartial direction) i / polynomialMap 4 direction.polynomial := by
  simp only [parameter, familyPartial, Derivation.leibniz_div, map_neg,
    partial_polynomial, smul_eq_mul]
  field_simp [polynomialMap_ne_zero direction.polynomial_ne_zero] <;> ring

/-- These are relative derivations: they annihilate the true pencil parameter. -/
theorem tangent_parameter (direction : Direction) (j : Fin 4) : (tangent direction) j (parameter direction) = 0 := by
  rw [tangent_apply, partial_parameter, partial_parameter]
  field_simp [familyPartial_zero_ne_zero, polynomialMap_ne_zero direction.polynomial_ne_zero] <;> ring

theorem tangent_parameterPolynomial (direction : Direction) (j : Fin 4) (p : Polynomial ℂ) :
    tangent direction j (Polynomial.aeval (R := ℂ) (parameter direction) p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  | monomial n c =>
      simp only [Polynomial.aeval_monomial, Derivation.leibniz,
        Derivation.leibniz_pow, Derivation.map_algebraMap, tangent_parameter,
        smul_zero, add_zero]

/-- The generic tangent operators are zero on every rational base function,
so the primitive equation is relative to C(t), not merely relative to C. -/
theorem tangent_baseEmbedding (direction : Direction) (j : Fin 4) (b : Base) :
    tangent direction j (baseEmbedding direction b) = 0 := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Polynomial ℂ) b
  simp only [map_div₀, baseEmbedding_polynomial, Derivation.leibniz_div,
    tangent_parameterPolynomial, smul_zero, sub_self, zero_div]

/-- The same actual operator, with linearity over C(t) included in its type. -/
def relativeTangent (direction : Direction) (j : Fin 4) :
    letI : Algebra Base RF := (baseEmbedding direction).toAlgebra
    Derivation Base RF RF := by
  letI : Algebra Base RF := (baseEmbedding direction).toAlgebra
  exact {
    toFun := tangent direction j
    map_add' := (tangent direction j).map_add
    map_smul' := by
      intro c z
      have hc : tangent direction j (algebraMap Base RF c) = 0 :=
        tangent_baseEmbedding direction j c
      simp only [Algebra.smul_def, Derivation.leibniz, smul_eq_mul,
        hc, mul_zero, add_zero, Algebra.algebraMap_self, RingHom.id_apply]
    map_one_eq_zero' := (tangent direction j).map_one_eq_zero
    leibniz' := (tangent direction j).leibniz }

@[simp] theorem relativeTangent_apply (direction : Direction) (j : Fin 4) (x : RF) :
    relativeTangent direction j x = tangent direction j x := rfl

def coefficientTangent (direction : Direction) (j : Fin 4) : Derivation ℂ S S :=
  CycleQ2PowerSeriesTangents.extend (complexTangent j)

def laurentTangent (direction : Direction) (j : Fin 4) : Derivation ℂ L L :=
  CycleQ2LaurentDerivation.extend (complexTangent j)

@[simp] theorem coefficientTangent_X (direction : Direction) (j : Fin 4) : (coefficientTangent direction) j PowerSeries.X = 0 :=
  CycleQ2PowerSeriesTangents.extend_X (complexTangent j)

@[simp] theorem coefficientTangent_coordinate (direction : Direction) (j i : Fin 4) :
    (coefficientTangent direction) j (PowerSeries.C (fieldCoordinate i.succ)) = if i = j then 1 else 0 := by
  rw [coefficientTangent, CycleQ2PowerSeriesTangents.extend_C]
  simp only [complexTangent_apply, fieldCoordinate, affineTangent_coordinate]
  split_ifs <;> simp

theorem coefficientTangent_formalMap (direction : Direction) (j : Fin 4) (P : Poly) :
    (coefficientTangent direction) j ((formalMap direction) P) =
      (formalMap direction) (pderiv 0 P) * (coefficientTangent direction) j (formalRoot direction) +
        (formalMap direction) (pderiv j.succ P) := by
  have h := CycleQ2PolynomialChainRule.apply (formalAlgHom direction) ((coefficientTangent direction) j) P
  change (coefficientTangent direction) j ((formalMap direction) P) =
    ∑ i : Fin 5, (formalMap direction) (pderiv i P) * (coefficientTangent direction) j ((formalMap direction) (X i)) at h
  rw [Fin.sum_univ_succ] at h
  simpa only [(formalMap_X_zero direction), (formalMap_X_succ direction), (coefficientTangent_coordinate direction),
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- The implicit tangent equation is differentiated from the actual family. -/
theorem formalRoot_tangent_equation (direction : Direction) (j : Fin 4) :
    (formalPartial direction) 0 * (coefficientTangent direction) j (formalRoot direction) + (formalPartial direction) j.succ = 0 := by
  have h := congrArg ((coefficientTangent direction) j) (formalMap_pencil direction)
  simp only [map_add, Derivation.leibniz, coefficientTangent_X,
    coefficientTangent_formalMap, smul_eq_mul, mul_zero, add_zero, map_zero] at h
  unfold formalPartial
  linear_combination h

private theorem ofPowerSeries_coeff_neg (s : S) (n : ℤ) (hn : n < 0) :
    (HahnSeries.ofPowerSeries ℤ K s).coeff n = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  apply HahnSeries.embDomain_of_notMem_range
  rintro ⟨m, hm⟩
  change (m : ℤ) = n at hm
  omega

/-- The power-series and Laurent coefficient extensions are the same on
the canonical inclusion. -/
theorem laurentTangent_ofPowerSeries (direction : Direction) (j : Fin 4) (s : S) :
    (laurentTangent direction) j (HahnSeries.ofPowerSeries ℤ K s) =
      HahnSeries.ofPowerSeries ℤ K ((coefficientTangent direction) j s) := by
  ext n
  by_cases hn : 0 ≤ n
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    simp only [laurentTangent, CycleQ2LaurentDerivation.extend_coeff,
      HahnSeries.ofPowerSeries_apply_coeff, coefficientTangent,
      CycleQ2PowerSeriesTangents.extend_coeff]
  · have hn' : n < 0 := lt_of_not_ge hn
    simp only [laurentTangent, CycleQ2LaurentDerivation.extend_coeff,
      ofPowerSeries_coeff_neg _ _ hn', map_zero]

theorem formalRoot_laurentTangent (direction : Direction) (j : Fin 4) :
    HahnSeries.ofPowerSeries ℤ K ((coefficientTangent direction) j (formalRoot direction)) =
      -(specialize direction) ((familyPartial direction) j.succ) / (specialize direction) ((familyPartial direction) 0) := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ K) ((formalRoot_tangent_equation direction) j)
  simp only [map_add, map_mul, map_zero, ← specialize_familyPartial] at h
  apply (eq_div_iff ((map_ne_zero (specialize direction)).mpr (familyPartial_zero_ne_zero direction))).mpr
  linear_combination h

/-- Actual compatibility on polynomial generators, derived from the family
equation rather than imposed as a hypothesis. -/
theorem specialize_tangent_polynomial (direction : Direction) (j : Fin 4) (P : Poly) :
    (laurentTangent direction) j ((specialize direction) (polynomialMap 4 P)) =
      (specialize direction) ((tangent direction) j (polynomialMap 4 P)) := by
  rw [specialize_polynomial, laurentTangent_ofPowerSeries, coefficientTangent_formalMap,
    tangent_apply, partial_polynomial, partial_polynomial]
  simp only [map_add, map_sub, map_mul, map_div₀, specialize_polynomial,
    formalRoot_laurentTangent]
  ring

/-- Actual compatibility on the entire generic function field, including
arbitrary denominators and parameter poles. -/
theorem specialize_tangent (direction : Direction) (j : Fin 4) (z : RF) :
    (laurentTangent direction) j ((specialize direction) z) = (specialize direction) ((tangent direction) j z) := by
  obtain ⟨P, Q, _, rfl⟩ := IsFractionRing.div_surjective Poly z
  change (laurentTangent direction) j ((specialize direction) (polynomialMap 4 P / polynomialMap 4 Q)) =
    (specialize direction) ((tangent direction) j (polynomialMap 4 P / polynomialMap 4 Q))
  simp only [map_div₀, Derivation.leibniz_div, smul_eq_mul, map_sub,
    map_mul, map_pow, map_inv₀, specialize_tangent_polynomial]

/-- The relative generic coordinate operators genuinely commute. -/
theorem tangents_commute (direction : Direction) (i j : Fin 4) :
    Function.Commute (tangent direction i) (tangent direction j) := by
  intro z
  apply specialize_injective direction
  simp only [← specialize_tangent]
  exact CycleQ2LaurentDerivation.extend_commute (complexTangent i) (complexTangent j)
    (affineTangents_commute i j) (specialize direction z)

theorem formalPartial_zero_isUnit (direction : Direction) : IsUnit ((formalPartial direction) 0) := by
  apply PowerSeries.isUnit_iff_constantCoeff.mpr
  rw [constantCoeff_formalPartial]
  exact isUnit_iff_ne_zero.mpr normal_ne_zero

def normalInverse (direction : Direction) : S := ↑((formalPartial_zero_isUnit direction).unit⁻¹)

theorem formalPartial_mul_normalInverse (direction : Direction) : (formalPartial direction) 0 * (normalInverse direction) = 1 := by
  exact (formalPartial_zero_isUnit direction).mul_val_inv

theorem constantCoeff_normalInverse (direction : Direction) :
    (normalInverse direction).constantCoeff = (affineMap (pderiv 0 affineF))⁻¹ := by
  have h := congrArg (PowerSeries.constantCoeff (R := K)) (formalPartial_mul_normalInverse direction)
  rw [map_mul, constantCoeff_formalPartial, map_one] at h
  exact eq_inv_of_mul_eq_one_right h

theorem laurent_normalInverse (direction : Direction) :
    HahnSeries.ofPowerSeries ℤ K (normalInverse direction) = ((specialize direction) ((familyPartial direction) 0))⁻¹ := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ K) (formalPartial_mul_normalInverse direction)
  rw [map_mul, map_one, ← specialize_familyPartial] at h
  exact eq_inv_of_mul_eq_one_right h

/-- Higher normal jets at fixed pencil parameter. Differentiating the
rational expression for the parameter would give the wrong normal jets. -/
def familyNormalJet (direction : Direction) (n : ℕ) : RF :=
  polynomialMap 4 ((pderiv (0 : Fin 5))^[n + 1] affineF) +
    (parameter direction) * polynomialMap 4 ((pderiv (0 : Fin 5))^[n + 1] direction.polynomial)

def formalNormalJet (direction : Direction) (n : ℕ) : S :=
  (formalMap direction) ((pderiv (0 : Fin 5))^[n + 1] affineF) +
    PowerSeries.X * (formalMap direction) ((pderiv (0 : Fin 5))^[n + 1] direction.polynomial)

theorem familyNormalJet_zero (direction : Direction) : (familyNormalJet direction) 0 = (familyPartial direction) 0 := rfl
theorem formalNormalJet_zero (direction : Direction) : (formalNormalJet direction) 0 = (formalPartial direction) 0 := rfl

@[simp] theorem constantCoeff_formalNormalJet (direction : Direction) (n : ℕ) :
    ((formalNormalJet direction) n).constantCoeff =
      affineMap ((pderiv (0 : Fin 5))^[n + 1] affineF) := by
  simp [formalNormalJet, constantCoeff_formalMap]

@[simp] theorem specialize_familyNormalJet (direction : Direction) (n : ℕ) :
    (specialize direction) ((familyNormalJet direction) n) = HahnSeries.ofPowerSeries ℤ K ((formalNormalJet direction) n) := by
  simp only [familyNormalJet, formalNormalJet, map_add, map_mul,
    specialize_polynomial, specialize_parameter, HahnSeries.ofPowerSeries_X]

/-- The genuine generic residue density of A/(f+tH)^3 in the fixed-parameter
normal coordinate, with the coordinate volume divided by the normal gradient. -/
def genericDensity (direction : Direction) (A : Poly) : RF :=
  SplitHigherResidue.normalSourceTwo
    (polynomialMap 4 A) (polynomialMap 4 (pderiv 0 A))
    (polynomialMap 4 (pderiv 0 (pderiv 0 A)))
    ((familyNormalJet direction) 0) ((familyNormalJet direction) 1) ((familyNormalJet direction) 2) /
      (familyNormalJet direction) 0

/-- A regular power-series representative of the generic source density.
Only the primitive, not this source, is allowed arbitrary Laurent poles. -/
def formalDensity (direction : Direction) (A : Poly) : S :=
  PowerSeries.C (1 / 2 : K) *
    ((formalMap direction) (pderiv 0 (pderiv 0 A)) * (normalInverse direction) ^ 3 -
      (3 * (formalMap direction) (pderiv 0 A) * (formalNormalJet direction) 1 +
        (formalMap direction) A * (formalNormalJet direction) 2) * (normalInverse direction) ^ 4 +
      3 * (formalMap direction) A * ((formalNormalJet direction) 1) ^ 2 * (normalInverse direction) ^ 5)

/-- The constant term of the source is the exact protected normal density. -/
theorem constantCoeff_formalDensity (direction : Direction) (A : Poly) :
    ((formalDensity direction) A).constantCoeff =
      affineNormalSource A / affineMap (pderiv 0 affineF) := by
  simp only [formalDensity, map_mul, map_add, map_sub, map_pow, map_ofNat,
    PowerSeries.constantCoeff_C, constantCoeff_formalMap,
    constantCoeff_formalNormalJet, constantCoeff_normalInverse,
    Function.iterate_succ_apply', Function.iterate_zero_apply]
  unfold affineNormalSource SplitHigherResidue.normalSourceTwo
  field_simp [normal_ne_zero] <;> ring

theorem specialize_genericDensity (direction : Direction) (A : Poly) :
    (specialize direction) ((genericDensity direction) A) = HahnSeries.ofPowerSeries ℤ K ((formalDensity direction) A) := by
  have hhalf : HahnSeries.ofPowerSeries ℤ K (PowerSeries.C (1 / 2 : K)) = (1 / 2 : L) := by
    change ((HahnSeries.ofPowerSeries ℤ K).comp PowerSeries.C) (1 / 2 : K) = _
    simp only [map_div₀, map_one, map_ofNat]
  simp only [genericDensity, SplitHigherResidue.normalSourceTwo, formalDensity,
    map_div₀, map_one, map_ofNat, map_add, map_sub, map_mul, map_pow,
    specialize_polynomial, hhalf, laurent_normalInverse,
    ← specialize_familyNormalJet, familyNormalJet_zero]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem specialize_genericDensity_coefficient (direction : Direction) (A : Poly) :
    ((specialize direction) ((genericDensity direction) A)).coeff 0 =
      affineNormalSource A / affineMap (pderiv 0 affineF) := by
  rw [specialize_genericDensity]
  change (HahnSeries.ofPowerSeries ℤ K ((formalDensity direction) A)).coeff ((0 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff]
  simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using constantCoeff_formalDensity direction A

/-- Generic exactness specializes even if the primitive has negative
parameter powers. All maps and derivations in the hypothesis are the actual
ones defined from the exact protected pencil. -/
theorem affine_primitive_of_generic_primitive (direction : Direction) (A : Poly)
    (h : ∃ u : Fin 4 → RF, ∑ j, (tangent direction) j (u j) = (genericDensity direction) A) :
    ∃ w : Fin 4 → K, affineResidueExpression A w = 0 := by
  obtain ⟨u, hu⟩ := h
  have hl := congrArg (specialize direction) hu
  simp only [map_sum, ← specialize_tangent] at hl
  have hc := CycleQ2LaurentDerivation.divergence_coefficient
    complexTangent (fun j => (specialize direction) (u j)) ((specialize direction) ((genericDensity direction) A)) hl 0
  rw [specialize_genericDensity_coefficient] at hc
  let v : Fin 4 → K := fun j => ((specialize direction) (u j)).coeff 0
  refine ⟨fun j => affineMap (pderiv 0 affineF) * (-v j), ?_⟩
  rw [affineResidueExpression, residueDivergence_cancel_density _ _ normal_ne_zero]
  simp only [HoldoutConstruction.fieldDivergence, map_neg, Finset.sum_neg_distrib, mul_neg, ← sub_eq_add_neg]
  change affineNormalSource A -
    affineMap (pderiv 0 affineF) * (∑ j, complexTangent j (v j)) = 0
  rw [hc]
  field_simp [normal_ne_zero] <;> ring

/-- The complete actual generic-to-protected certificate implication. -/
theorem protected_certificate_of_generic_primitive (direction : Direction)
    (h : ∃ u : Fin 4 → RF, ∑ j, (tangent direction) j (u j) = (genericDensity direction) affineA) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  protected_certificate_of_affine_residue_primitive
    ((affine_primitive_of_generic_primitive direction) affineA h)

/-- The same certificate implication stated using C(t)-linear derivations
on the verified function field of the actual generic hypersurface. -/
theorem protected_certificate_of_generic_relative_primitive (direction : Direction)
    (h : ∃ u : Fin 4 → RF, ∑ j, relativeTangent direction j (u j) = genericDensity direction affineA) :
    HasCertificate HodgeSubmission.F HodgeSubmission.q HodgeSubmission.A :=
  protected_certificate_of_generic_primitive direction (by simpa only [relativeTangent_apply] using h)

end CycleQ2GenericSpecialization

#print axioms CycleQ2GenericSpecialization.formalMap_injective
#print axioms CycleQ2GenericSpecialization.specialize_parameter
#print axioms CycleQ2GenericSpecialization.tangent_parameter
#print axioms CycleQ2GenericSpecialization.specialize_tangent
#print axioms CycleQ2GenericSpecialization.specialize_genericDensity_coefficient
#print axioms CycleQ2GenericSpecialization.protected_certificate_of_generic_primitive
#print axioms CycleQ2GenericSpecialization.genericEvaluation_kernel
#print axioms CycleQ2GenericSpecialization.genericFractionRing
#print axioms CycleQ2GenericSpecialization.parameter_transcendental
#print axioms CycleQ2GenericSpecialization.protected_certificate_of_generic_relative_primitive
end
end


/- Component: continuation_3/BinaryNaturalPower.lean -/
section
/-! A structurally recursive binary powering function, with a proof that it
agrees with ordinary natural powers for every fuel and exponent. -/
namespace CycleQ2BinaryNaturalPower

def power (b : ℕ) : ℕ → ℕ → ℕ
  | 0, k => b^k
  | f+1, k =>
    let a := power b f (k/2)
    if k%2=0 then a*a else b*(a*a)

theorem power_eq (b f k : ℕ) : power b f k=b^k := by
  induction f generalizing k with
  | zero => rfl
  | succ f ih =>
    simp only [power,ih]
    have hk := Nat.mod_add_div k 2
    have hb : k%2<2 := Nat.mod_lt _ (by decide)
    split_ifs with h
    · calc
        b^(k/2)*b^(k/2)=b^((k/2)*2) := by rw [pow_mul,pow_two]
        _=b^k := by congr 1; omega
    · calc
        b*(b^(k/2)*b^(k/2))=b^((k/2)*2+1) := by rw [pow_succ,pow_mul,pow_two]; ring
        _=b^k := by congr 1; omega
end CycleQ2BinaryNaturalPower
#print axioms CycleQ2BinaryNaturalPower.power_eq
end


/- Component: continuation_3/cylinder_bridge/GenericLinearSection.lean -/
section
/-! A linear form in three independent section parameters is regular as
soon as any one coefficient is a unit.  This is an elementary statement
over arbitrary commutative rings; no integral or smooth surface assumption
is needed. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2GenericLinearSection
open MvPolynomial

variable {R : Type*} [CommRing R]

def linearForm (a : Fin 3 → R) : MvPolynomial (Fin 3) R :=
  ∑ j, C (a j)*X j

theorem regular_of_injective_map {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) (a : A) (ha : IsRegular (f a)) :
    IsRegular a := by
  constructor
  · intro x y h
    apply hf
    apply ha.left
    simpa only [map_mul] using congrArg f h
  · intro x y h
    apply hf
    apply ha.right
    simpa only [map_mul] using congrArg f h

theorem univariate_regular (u : Rˣ) (b : R) :
    IsRegular (Polynomial.C (u : R)*Polynomial.X+Polynomial.C b) := by
  have h : Polynomial.C (u : R)*
      (Polynomial.X+Polynomial.C ((↑(u⁻¹) : R)*b))=
        Polynomial.C (u : R)*Polynomial.X+Polynomial.C b := by
    rw [mul_add,←Polynomial.C_mul,←mul_assoc,Units.mul_inv,one_mul]
  rw [←h]
  exact (u.isUnit.map Polynomial.C).isRegular.mul (Polynomial.monic_X_add_C _).isRegular

theorem linearForm_regular_zero (a : Fin 3 → R) (hu : IsUnit (a 0)) :
    IsRegular (linearForm a) := by
  let e := finSuccEquiv R 2
  have hc (r : R) : e (C r)=Polynomial.C (C r) := e.commutes r
  have hf : e (linearForm a)=
      Polynomial.C (C (a 0))*Polynomial.X+
        Polynomial.C (C (a 1)*X 0+C (a 2)*X 1) := by
    simp only [linearForm,Fin.sum_univ_three,map_add,map_mul,hc]
    change Polynomial.C (C (a 0))*finSuccEquiv R 2 (X 0)+
      Polynomial.C (C (a 1))*finSuccEquiv R 2 (X (Fin.succ 0))+
      Polynomial.C (C (a 2))*finSuccEquiv R 2 (X (Fin.succ 1))=_
    rw [finSuccEquiv_X_zero,finSuccEquiv_X_succ,finSuccEquiv_X_succ]
    ring
  apply regular_of_injective_map e.toRingHom e.injective
  change IsRegular (e (linearForm a))
  rw [hf]
  obtain ⟨u,hu⟩ := hu.map (C : R →+* MvPolynomial (Fin 2) R)
  rw [←hu]
  exact univariate_regular u _

theorem linearForm_regular (a : Fin 3 → R) (j : Fin 3) (hu : IsUnit (a j)) :
    IsRegular (linearForm a) := by
  classical
  fin_cases j
  · exact linearForm_regular_zero a hu
  · let e := renameEquiv R (Equiv.swap (0 : Fin 3) 1)
    have he : e (linearForm a)=linearForm ![a 1,a 0,a 2] := by
      simp only [e,linearForm,Fin.sum_univ_three,map_add,map_mul,renameEquiv_apply,
        rename_C,rename_X]
      change C (a 0)*X 1+C (a 1)*X 0+C (a 2)*X 2=
        C (a 1)*X 0+C (a 0)*X 1+C (a 2)*X 2
      ring
    apply regular_of_injective_map e.toRingHom e.injective
    change IsRegular (e (linearForm a))
    rw [he]
    exact linearForm_regular_zero _ hu
  · let e := renameEquiv R (Equiv.swap (0 : Fin 3) 2)
    have he : e (linearForm a)=linearForm ![a 2,a 1,a 0] := by
      simp only [e,linearForm,Fin.sum_univ_three,map_add,map_mul,renameEquiv_apply,
        rename_C,rename_X]
      change C (a 0)*X 2+C (a 1)*X 1+C (a 2)*X 0=
        C (a 2)*X 0+C (a 1)*X 1+C (a 0)*X 2
      ring
    apply regular_of_injective_map e.toRingHom e.injective
    change IsRegular (e (linearForm a))
    rw [he]
    exact linearForm_regular_zero _ hu

end CycleQ2GenericLinearSection

#print axioms CycleQ2GenericLinearSection.linearForm_regular
end
end


/- Component: continuation_3/HomogeneousComponentProduct.lean -/
section
/-!
# Homogeneous projection of ideal-membership coefficients

An arbitrary polynomial coefficient multiplying a homogeneous equation can
be projected to the unique degree contributing to a prescribed homogeneous
component.  This is used to turn polynomial ideal-membership witnesses into
homogeneous Čech cochains, including witnesses of unbounded degree.
-/

namespace CycleQ2HomogeneousComponent

open MvPolynomial

variable {σ R : Type*} [CommSemiring R]

theorem component_mul_of_homogeneous (p q : MvPolynomial σ R)
    {d e : ℕ} (hq : q.IsHomogeneous e) (hed : e ≤ d) :
    homogeneousComponent d (p * q) = homogeneousComponent (d - e) p * q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    have hm : (monomial a c : MvPolynomial σ R).IsHomogeneous a.degree :=
      isHomogeneous_monomial c rfl
    rw [homogeneousComponent_of_mem (hm.mul hq), homogeneousComponent_of_mem hm]
    by_cases h : d = a.degree + e
    · have h' : d - e = a.degree := by omega
      simp [h, h']
    · have h' : d - e ≠ a.degree := by omega
      simp [h, h']
  | add p s hp hs =>
    simp only [add_mul, map_add, hp, hs]

theorem component_mul_of_homogeneous_left (p q : MvPolynomial σ R)
    {d e : ℕ} (hp : p.IsHomogeneous e) (hed : e ≤ d) :
    homogeneousComponent d (p * q) = p * homogeneousComponent (d - e) q := by
  rw [mul_comm p q, component_mul_of_homogeneous q p hp hed, mul_comm]

theorem component_mul_add (p q : MvPolynomial σ R)
    (d : ℕ) {e : ℕ} (hq : q.IsHomogeneous e) :
    homogeneousComponent (d + e) (p * q) = homogeneousComponent d p * q := by
  simpa using component_mul_of_homogeneous p q hq (Nat.le_add_left e d)

end CycleQ2HomogeneousComponent

#print axioms CycleQ2HomogeneousComponent.component_mul_of_homogeneous
end


/- Component: continuation_3/cylinder_bridge/ImplicitTraceNumerator.lean -/
section
/-! A denominator-free polynomial numerator for the trace of an implicit
affine derivative.  The adjugate identity records the actual differentiated
equations and makes the nonvanishing condition an ordinary principal open. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ImplicitTraceNumerator
open Matrix

variable {R S ι σ : Type*} [CommRing R] [CommRing S]
  [Fintype ι] [DecidableEq ι] [Fintype σ]

def correctionNumerator (J : Matrix ι ι R) (g : ι → R) : ι → R :=
  -(J.adjugate *ᵥ g)

def traceNumerator (J : Matrix ι ι R) (g : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R) : R :=
  J.det * (weights ⬝ᵥ direction) + weights ⬝ᵥ (B *ᵥ correctionNumerator J g)

theorem jacobian_correction (J : Matrix ι ι R) (g : ι → R) :
    J *ᵥ correctionNumerator J g = -(J.det • g) := by
  rw [correctionNumerator,mulVec_neg,mulVec_mulVec,mul_adjugate,smul_mulVec,one_mulVec]

/-- Every genuine implicit derivative has this exact adjugate numerator. -/
theorem scaled_implicit_correction (J : Matrix ι ι R) (g u : ι → R)
    (hu : J *ᵥ u + g=0) : J.det • u=correctionNumerator J g := by
  have he : J *ᵥ u = -g := eq_neg_of_add_eq_zero_left hu
  have h := congrArg (fun v => J.adjugate *ᵥ v) he
  rw [mulVec_mulVec,adjugate_mul,smul_mulVec,one_mulVec,mulVec_neg] at h
  exact h

theorem traceNumerator_eq_scaled_trace (J : Matrix ι ι R) (g u : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R)
    (hu : J *ᵥ u + g=0) :
    traceNumerator J g weights direction B =
      J.det * (weights ⬝ᵥ (direction + B *ᵥ u)) := by
  rw [traceNumerator,← scaled_implicit_correction J g u hu,
    mulVec_smul,dotProduct_smul,dotProduct_add,smul_eq_mul,mul_add]

theorem trace_isUnit_of_numerator_isUnit (J : Matrix ι ι R) (g u : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R)
    (hu : J *ᵥ u + g=0) (hN : IsUnit (traceNumerator J g weights direction B)) :
    IsUnit (weights ⬝ᵥ (direction + B *ᵥ u)) := by
  rw [traceNumerator_eq_scaled_trace J g u weights direction B hu] at hN
  exact isUnit_of_mul_isUnit_right hN

theorem traceNumerator_seed (weights direction : σ → R) (B : Matrix σ ι R)
    (htrace : weights ⬝ᵥ direction=1) :
    traceNumerator (1 : Matrix ι ι R) (0 : ι → R) weights direction B=1 := by
  simp only [traceNumerator,correctionNumerator,det_one,mulVec_zero,neg_zero,
    dotProduct_zero,htrace,one_mul,add_zero]

theorem correctionNumerator_map (φ : R →+* S) (J : Matrix ι ι R) (g : ι → R) :
    φ ∘ correctionNumerator J g = correctionNumerator (J.map φ) (φ ∘ g) := by
  funext i
  have ha : J.adjugate.map φ=(J.map φ).adjugate := φ.map_adjugate J
  simp only [correctionNumerator,Function.comp_apply,Pi.neg_apply,map_neg,
    RingHom.map_mulVec,ha]

theorem traceNumerator_map (φ : R →+* S) (J : Matrix ι ι R) (g : ι → R)
    (weights direction : σ → R) (B : Matrix σ ι R) :
    φ (traceNumerator J g weights direction B) =
      traceNumerator (J.map φ) (φ ∘ g) (φ ∘ weights) (φ ∘ direction) (B.map φ) := by
  have hdet : φ J.det=(J.map φ).det := φ.map_det J
  have hc := correctionNumerator_map φ J g
  have hB : φ ∘ (B *ᵥ correctionNumerator J g) =
      B.map φ *ᵥ correctionNumerator (J.map φ) (φ ∘ g) := by
    funext i
    rw [Function.comp_apply,RingHom.map_mulVec,hc]
  simp only [traceNumerator,map_add,map_mul,hdet,RingHom.map_dotProduct,hB]

section Field
variable {K : Type*} [Field K]

def implicitCorrection (J : Matrix ι ι K) (g : ι → K) : ι → K :=
  J.det⁻¹ • correctionNumerator J g

theorem implicitCorrection_equation (J : Matrix ι ι K) (g : ι → K)
    (hJ : J.det≠0) : J *ᵥ implicitCorrection J g + g=0 := by
  rw [implicitCorrection,mulVec_smul,jacobian_correction,smul_neg,smul_smul,
    inv_mul_cancel₀ hJ,one_smul,neg_add_cancel]

theorem implicit_trace_eq_div (J : Matrix ι ι K) (g : ι → K)
    (weights direction : σ → K) (B : Matrix σ ι K) (hJ : J.det≠0) :
    weights ⬝ᵥ (direction + B *ᵥ implicitCorrection J g) =
      traceNumerator J g weights direction B / J.det := by
  apply (eq_div_iff hJ).mpr
  rw [mul_comm]
  exact (traceNumerator_eq_scaled_trace J g (implicitCorrection J g)
    weights direction B (implicitCorrection_equation J g hJ)).symm

end Field
end CycleQ2ImplicitTraceNumerator

#print axioms CycleQ2ImplicitTraceNumerator.scaled_implicit_correction
#print axioms CycleQ2ImplicitTraceNumerator.trace_isUnit_of_numerator_isUnit
#print axioms CycleQ2ImplicitTraceNumerator.implicit_trace_eq_div
end
end


/- Component: continuation_3/IncidenceMonomialCounts.lean -/
section
/-!
# Exact monomial counts for the invariant incidence quotient

The small finite index determines the x3 exponent from the weighted degree.
Its equivalence with the complete exponent set proves exhaustiveness; the
cardinality calculations use the ordinary kernel decision procedure.
-/

namespace CycleQ2IncidenceMonomials

abbrev RawIndex (d xBound wBound : ℕ) :=
  (Fin xBound × Fin wBound) × (Fin (d + 1) × Fin (d + 1))

def Allowed (d xBound wBound : ℕ) (q : RawIndex d xBound wBound) : Prop :=
  q.1.1.val + q.2.1.val + q.2.2.val + 2 * q.1.2.val ≤ d ∧
    (2 * q.1.1.val + 2 * q.2.1.val + q.2.2.val) % 3 = 0

instance (d xBound wBound : ℕ) (q : RawIndex d xBound wBound) :
    Decidable (Allowed d xBound wBound q) := inferInstanceAs (Decidable (_ ∧ _))

abbrev Index (d xBound wBound : ℕ) :=
  {q : RawIndex d xBound wBound // Allowed d xBound wBound q}

def coordinates {d xBound wBound : ℕ} (q : Index d xBound wBound) : Fin 5 → ℕ :=
  ![q.val.1.1.val, q.val.2.1.val, q.val.2.2.val,
    d - (q.val.1.1.val + q.val.2.1.val + q.val.2.2.val + 2 * q.val.1.2.val),
    q.val.1.2.val]

abbrev Exponents (d xBound wBound : ℕ) :=
  {e : Fin 5 → ℕ // e 0 < xBound ∧ e 4 < wBound ∧
    e 0 + e 1 + e 2 + e 3 + 2 * e 4 = d ∧
    (2 * e 0 + 2 * e 1 + e 2) % 3 = 0}

def exponentEquiv (d xBound wBound : ℕ) :
    Index d xBound wBound ≃ Exponents d xBound wBound where
  toFun q := ⟨coordinates q, by
    have hw := q.property.1
    have hc := q.property.2
    change q.val.1.1.val < xBound ∧ q.val.1.2.val < wBound ∧
      q.val.1.1.val + q.val.2.1.val + q.val.2.2.val +
        (d - (q.val.1.1.val + q.val.2.1.val + q.val.2.2.val + 2 * q.val.1.2.val)) +
        2 * q.val.1.2.val = d ∧
      (2 * q.val.1.1.val + 2 * q.val.2.1.val + q.val.2.2.val) % 3 = 0
    exact ⟨q.val.1.1.isLt, q.val.1.2.isLt, by omega, hc⟩⟩
  invFun e := ⟨((⟨e.val 0, e.property.1⟩, ⟨e.val 4, e.property.2.1⟩),
    (⟨e.val 1, by have := e.property.2.2.1; omega⟩,
     ⟨e.val 2, by have := e.property.2.2.1; omega⟩)), by
      constructor
      · have := e.property.2.2.1
        dsimp
        omega
      · exact e.property.2.2.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv e := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · rfl
    · rfl
    · change d - (e.val 0 + e.val 1 + e.val 2 + 2 * e.val 4) = e.val 3
      have := e.property.2.2.1
      omega
    · rfl

abbrev StandardIndex (d : ℕ) := Index d 3 3
abbrev FullIndex (d : ℕ) := Index d (d + 1) (d / 2 + 1)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem invariant_cubic_count : Fintype.card (FullIndex 3) = 9 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem invariant_sextic_count : Fintype.card (FullIndex 6) = 45 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree14_count : Fintype.card (StandardIndex 14) = 239 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree28_count : Fintype.card (StandardIndex 28) = 1058 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
theorem standard_degree42_count : Fintype.card (StandardIndex 42) = 2465 := by decide

/-- There are nine degree-fourteen matrix entries and nine raw cubic-section
coefficients. The scalar direction of the cubic remains present. -/
theorem incidence_variable_count :
    9 * Fintype.card (StandardIndex 14) + Fintype.card (FullIndex 3) = 2160 := by
  rw [standard_degree14_count, invariant_cubic_count]

theorem cofactor_equation_count : 9 * Fintype.card (StandardIndex 28) = 9522 := by
  rw [standard_degree28_count]

theorem coefficient_relation_count : 16 * Fintype.card (StandardIndex 42) = 39440 := by
  rw [standard_degree42_count]

end CycleQ2IncidenceMonomials

#print axioms CycleQ2IncidenceMonomials.exponentEquiv
#print axioms CycleQ2IncidenceMonomials.invariant_sextic_count
#print axioms CycleQ2IncidenceMonomials.standard_degree42_count
end


/- Component: continuation_3/IncidenceNormalForm.lean -/
section
/-!
# Normal forms for the two equations of the Segre incidence chart

This file proves the product criterion needed here from the division algorithm.
It does not take a Groebner basis as a hypothesis.  The coefficient ring may have
zero divisors: the two leading coefficients are normalized to one.
-/

noncomputable section

open MvPolynomial
open scoped MonomialOrder

namespace CycleQ2IncidenceNormalForm

variable {σ R : Type*} [CommRing R]

/-- No monomial of `p` is divisible by either distinguished leading monomial. -/
def Reduced (m : MonomialOrder σ) (h F p : MvPolynomial σ R) : Prop :=
  ∀ d ∈ p.support, ¬ m.degree h ≤ d ∧ ¬ m.degree F ≤ d

lemma degree_mul_monic (m : MonomialOrder σ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.Monic q) :
    m.degree (p * q) = m.degree p + m.degree q := by
  apply m.degree_mul_of_mul_leadingCoeff_ne_zero
  simpa [hq.leadingCoeff_eq_one] using m.leadingCoeff_ne_zero_iff.mpr hp

lemma reduced_sub (m : MonomialOrder σ) {h F p q : MvPolynomial σ R}
    (hp : Reduced m h F p) (hq : Reduced m h F q) :
    Reduced m h F (p - q) := by
  intro d hd
  by_cases hpd : p.coeff d = 0
  · have hqd : q.coeff d ≠ 0 := by
      intro hqd
      have := mem_support_iff.mp hd
      simp [coeff_sub, hpd, hqd] at this
    exact hq d (mem_support_iff.mpr hqd)
  · exact hp d (mem_support_iff.mpr hpd)

/-- The two-monic-polynomial product criterion, proved by dividing the first
coefficient by the second equation.  Disjoint supports of the leading exponents
prevent cancellation of the two remaining leading terms. -/
theorem reduced_eq_zero_of_representation
    (m : MonomialOrder σ) {h F p a b : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hp : Reduced m h F p) (heq : p = a * h + b * F) : p = 0 := by
  obtain ⟨q, r, ha, _, hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff F) by rw [hF.leadingCoeff_eq_one]; exact isUnit_one) a
  let s := b + q * h
  have hp' : p = r * h + s * F := by
    rw [heq, ha]
    dsimp [s]
    ring
  by_contra hp0
  have hpn := hp (m.degree p) (m.degree_mem_support hp0)
  by_cases hr0 : r = 0
  · have hs0 : s ≠ 0 := by
      intro hs0
      simp [hr0, hs0] at hp'
      exact hp0 hp'
    have hpd : m.degree p = m.degree s + m.degree F := by
      rw [hp', hr0, zero_mul, zero_add, degree_mul_monic m hs0 hF]
    apply hpn.2
    rw [hpd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hrd : m.degree (r * h) = m.degree r + m.degree h :=
    degree_mul_monic m hr0 hh
  have hrn : ¬ m.degree F ≤ m.degree (r * h) := by
    intro hd
    apply hr (m.degree r) (m.degree_mem_support hr0)
    rw [hrd] at hd
    intro i
    rcases hcop i with hi | hi
    · simpa only [Finsupp.add_apply, hi, add_zero] using hd i
    · simp [hi]
  have hhd : m.degree h ≤ m.degree (r * h) := by
    rw [hrd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  by_cases hs0 : s = 0
  · have hpd : m.degree p = m.degree (r * h) := by
      rw [hp', hs0, zero_mul, add_zero]
    apply hpn.1
    rw [hpd]
    exact hhd
  have hsd : m.degree (s * F) = m.degree s + m.degree F :=
    degree_mul_monic m hs0 hF
  have hFd : m.degree F ≤ m.degree (s * F) := by
    rw [hsd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hne : m.toSyn (m.degree (r * h)) ≠ m.toSyn (m.degree (s * F)) := by
    intro hd
    apply hrn
    rwa [m.toSyn.injective hd]
  rcases lt_or_gt_of_ne hne with hd | hd
  · have hpd : m.degree p = m.degree (s * F) := by
      rw [hp', m.degree_add_eq_right_of_lt hd]
    apply hpn.2
    rw [hpd]
    exact hFd
  · have hpd : m.degree p = m.degree (r * h) := by
      rw [hp', m.degree_add_of_lt hd]
    apply hpn.1
    rw [hpd]
    exact hhd

/-- Uniqueness is an actual consequence of the two polynomial equations and the
coprimality of their leading monomials, over an arbitrary coefficient ring. -/
theorem reduced_unique
    (m : MonomialOrder σ) {h F p r₁ r₂ a₁ a₂ b₁ b₂ : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hr₁ : Reduced m h F r₁) (hr₂ : Reduced m h F r₂)
    (hp₁ : p = a₁ * h + b₁ * F + r₁)
    (hp₂ : p = a₂ * h + b₂ * F + r₂) : r₁ = r₂ := by
  apply sub_eq_zero.mp
  apply reduced_eq_zero_of_representation m hh hF hcop (reduced_sub m hr₁ hr₂)
    (a := a₂ - a₁) (b := b₂ - b₁)
  linear_combination hp₂ - hp₁

/-- Existence of a reduced representative uses the library's ordinary
multivariate division theorem. -/
theorem exists_reduced_representation
    (m : MonomialOrder σ) (h F p : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F) :
    ∃ a b r, p = a * h + b * F + r ∧ Reduced m h F r := by
  let equations : Fin 2 → MvPolynomial σ R := ![h, F]
  have he : ∀ i, IsUnit (m.leadingCoeff (equations i)) := by
    intro i
    fin_cases i
    · change IsUnit (m.leadingCoeff h)
      rw [hh.leadingCoeff_eq_one]
      exact isUnit_one
    · change IsUnit (m.leadingCoeff F)
      rw [hF.leadingCoeff_eq_one]
      exact isUnit_one
  obtain ⟨q, r, hp, _, hr⟩ := m.div he p
  refine ⟨q 0, q 1, r, ?_, ?_⟩
  · simpa [Finsupp.linearCombination_apply, Finsupp.sum_fintype, equations,
      Fin.sum_univ_two, smul_eq_mul] using hp
  · intro d hd
    exact ⟨hr d hd 0, hr d hd 1⟩

theorem existsUnique_reduced_representative
    (m : MonomialOrder σ) (h F p : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    ∃! r, Reduced m h F r ∧ ∃ a b, p = a * h + b * F + r := by
  obtain ⟨a, b, r, hp, hr⟩ := exists_reduced_representation m h F p hh hF
  refine ⟨r, ⟨hr, a, b, hp⟩, ?_⟩
  rintro r' ⟨hr', a', b', hp'⟩
  exact reduced_unique m hh hF hcop hr' hr hp' hp

theorem unit_scaled_representation_iff (u v : Rˣ) (h F p r : MvPolynomial σ R) :
    (∃ a b, p = a * h + b * F + r) ↔
      (∃ a b, p = a * (C (u : R) * h) + b * (C (v : R) * F) + r) := by
  constructor
  · rintro ⟨a, b, hp⟩
    refine ⟨a * C (↑u⁻¹ : R), b * C (↑v⁻¹ : R), ?_⟩
    have hcancel (z : Rˣ) (a q : MvPolynomial σ R) :
        (a * C (↑z⁻¹ : R)) * (C (z : R) * q) = a * q := by
      calc
        _ = a * (C (↑z⁻¹ : R) * C (z : R)) * q := by ring
        _ = a * q := by rw [← map_mul, Units.inv_mul, map_one, mul_one]
    simpa only [hcancel] using hp
  · rintro ⟨a, b, hp⟩
    exact ⟨a * C (u : R), b * C (v : R), by simpa only [mul_assoc] using hp⟩

def equationsIdeal (h F : MvPolynomial σ R) : Ideal (MvPolynomial σ R) :=
  Ideal.span {h, F}

def reducedExponents (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    Set (σ →₀ ℕ) :=
  {d | ¬ m.degree h ≤ d ∧ ¬ m.degree F ≤ d}

def reducedSubmodule (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R (reducedExponents m h F)

lemma mem_reducedSubmodule (m : MonomialOrder σ) (h F p : MvPolynomial σ R) :
    p ∈ reducedSubmodule m h F ↔ Reduced m h F p := Iff.rfl

def reducedQuotientMap (m : MonomialOrder σ) (h F : MvPolynomial σ R) :
    reducedSubmodule m h F →ₗ[R] MvPolynomial σ R ⧸ equationsIdeal h F :=
  (Ideal.Quotient.mkₐ R (equationsIdeal h F)).toLinearMap.comp
    (reducedSubmodule m h F).subtype

theorem reducedQuotientMap_bijective
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    Function.Bijective (reducedQuotientMap m h F) := by
  constructor
  · intro p q hpq
    apply Subtype.ext
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk (equationsIdeal h F) p.val =
      Ideal.Quotient.mk (equationsIdeal h F) q.val at hpq
    have hpq' := Ideal.Quotient.eq.mp hpq
    obtain ⟨a, b, heq⟩ := Ideal.mem_span_pair.mp hpq'
    exact reduced_eq_zero_of_representation m hh hF hcop
      (reduced_sub m p.property q.property) heq.symm
  · intro q
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, r, hp, hr⟩ := exists_reduced_representation m h F p hh hF
    refine ⟨⟨r, hr⟩, ?_⟩
    change Ideal.Quotient.mk (equationsIdeal h F) r =
      Ideal.Quotient.mk (equationsIdeal h F) p
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨-a, -b, ?_⟩
    rw [hp]
    ring

/-- The standard-monomial submodule is the whole quotient, with no unproved
injectivity or flatness assumption. -/
noncomputable def reducedQuotientEquiv
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    reducedSubmodule m h F ≃ₗ[R] MvPolynomial σ R ⧸ equationsIdeal h F :=
  LinearEquiv.ofBijective (reducedQuotientMap m h F)
    (reducedQuotientMap_bijective m h F hh hF hcop)

/-- The classes of standard monomials form a basis over the coefficient ring. -/
noncomputable def quotientBasis
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0) :
    Module.Basis (reducedExponents m h F) R (MvPolynomial σ R ⧸ equationsIdeal h F) :=
  (MvPolynomial.basisRestrictSupport R (reducedExponents m h F)).map
    (reducedQuotientEquiv m h F hh hF hcop)

theorem quotientBasis_apply
    (m : MonomialOrder σ) (h F : MvPolynomial σ R)
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (d : reducedExponents m h F) :
    quotientBasis m h F hh hF hcop d =
      Ideal.Quotient.mk (equationsIdeal h F) (monomial d.val 1) := by
  change Ideal.Quotient.mk (equationsIdeal h F)
    (AddMonoidAlgebra.ofCoeff
      (((Finsupp.supportedEquivFinsupp (R := R) (reducedExponents m h F)).symm
        (Finsupp.single d 1) : Finsupp.supported R R (reducedExponents m h F)) :
        (σ →₀ ℕ) →₀ R)) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Reduction preserves every grading for which the two defining equations
are homogeneous.  Taking the grading monoid to be `ℕ × ZMod 3` preserves the
ordinary weighted degree and the order-three character simultaneously. -/
theorem reduced_isWeightedHomogeneous
    {M : Type*} [AddCommMonoid M] (w : σ → M)
    (m : MonomialOrder σ) {h F p r a b : MvPolynomial σ R} {dh dF d : M}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hhhom : h.IsWeightedHomogeneous w dh) (hFhom : F.IsWeightedHomogeneous w dF)
    (hphom : p.IsWeightedHomogeneous w d) (hr : Reduced m h F r)
    (heq : p = a * h + b * F + r) : r.IsWeightedHomogeneous w d := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra R w
  have hI : (equationsIdeal h F).IsHomogeneous (weightedHomogeneousSubmodule R w) := by
    apply Ideal.homogeneous_span
    intro q hq
    rcases hq with rfl | hq
    · exact ⟨dh, hhhom⟩
    · obtain rfl := hq
      exact ⟨dF, hFhom⟩
  have hpr : p - r ∈ equationsIdeal h F := by
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by rw [heq]; ring⟩
  have hprojected := weightedHomogeneousComponent_mem_of_mem R w hI hpr d
  rw [map_sub, weightedHomogeneousComponent_eq_self hphom] at hprojected
  obtain ⟨a', b', heq'⟩ := Ideal.mem_span_pair.mp hprojected
  have hr' : Reduced m h F (weightedHomogeneousComponent w d r) := by
    intro e he
    rw [support_weightedHomogeneousComponent] at he
    exact hr e (Finset.mem_filter.mp he).1
  have hrep' : p = a' * h + b' * F + weightedHomogeneousComponent w d r := by
    linear_combination -heq'
  have hequal : r = weightedHomogeneousComponent w d r :=
    reduced_unique m hh hF hcop hr hr' heq hrep'
  rw [hequal]
  exact weightedHomogeneousComponent_isWeightedHomogeneous (w := w) d r

theorem reduced_isHomogeneous
    (m : MonomialOrder σ) {h F p r a b : MvPolynomial σ R} {dh dF d : ℕ}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i = 0 ∨ m.degree F i = 0)
    (hhhom : h.IsHomogeneous dh) (hFhom : F.IsHomogeneous dF)
    (hphom : p.IsHomogeneous d) (hr : Reduced m h F r)
    (heq : p = a * h + b * F + r) : r.IsHomogeneous d :=
  reduced_isWeightedHomogeneous (1 : σ → ℕ) m hh hF hcop hhhom hFhom hphom hr heq

/-! ## The concrete auxiliary order

The coefficient ring in this presentation contains `x₁,x₂,x₃`.  The two
polynomial variables are `x₀,w`, with auxiliary weights `3,7`.  This is enough
to prove the rank-nine freeness over that coefficient ring; the ordinary
weighted degree and character gradings can subsequently be taken componentwise.
-/

abbrev Exponent := Fin 2 →₀ ℕ

def auxiliaryWeight : Exponent →+ ℕ where
  toFun d := 3 * d 0 + 7 * d 1
  map_zero' := by simp
  map_add' a b := by
    simp only [Finsupp.add_apply]
    omega

/-- A separate type keeps the auxiliary order distinct from the divisibility
order on exponent vectors. -/
def AuxiliaryExponent := Exponent

def toAuxiliary : Exponent ≃ AuxiliaryExponent := Equiv.refl _
def ofAuxiliary : AuxiliaryExponent ≃ Exponent := Equiv.refl _

noncomputable instance : AddCommMonoid AuxiliaryExponent := ofAuxiliary.addCommMonoid

lemma ofAuxiliary_add (a b : AuxiliaryExponent) :
    ofAuxiliary (a + b) = ofAuxiliary a + ofAuxiliary b := rfl

def auxiliaryKey (a : AuxiliaryExponent) : Lex (ℕ × Lex Exponent) :=
  toLex (auxiliaryWeight (ofAuxiliary a), toLex (ofAuxiliary a))

lemma auxiliaryKey_injective : Function.Injective auxiliaryKey := by
  intro a b hab
  exact ofAuxiliary.injective (toLex.injective (Prod.mk.inj (toLex.injective hab)).2)

noncomputable instance : LinearOrder AuxiliaryExponent :=
  LinearOrder.lift' auxiliaryKey auxiliaryKey_injective

lemma auxiliaryKey_add (a b : AuxiliaryExponent) :
    auxiliaryKey (a + b) = auxiliaryKey a + auxiliaryKey b := by
  change toLex (auxiliaryWeight (ofAuxiliary a + ofAuxiliary b),
    toLex (ofAuxiliary a + ofAuxiliary b)) =
    toLex (auxiliaryWeight (ofAuxiliary a) + auxiliaryWeight (ofAuxiliary b),
      toLex (ofAuxiliary a) + toLex (ofAuxiliary b))
  rw [map_add, toLex_add]

noncomputable instance : IsOrderedCancelAddMonoid AuxiliaryExponent where
  le_of_add_le_add_left a b c h := by
    change auxiliaryKey b ≤ auxiliaryKey c
    change auxiliaryKey (a + b) ≤ auxiliaryKey (a + c) at h
    simpa only [auxiliaryKey, ofAuxiliary_add, map_add, toLex_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_left, add_right_inj,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    change auxiliaryKey a ≤ auxiliaryKey b at h
    change auxiliaryKey (a + c) ≤ auxiliaryKey (b + c)
    simpa only [auxiliaryKey, ofAuxiliary_add, map_add, toLex_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

noncomputable instance : WellFoundedLT AuxiliaryExponent :=
  ⟨InvImage.wf auxiliaryKey wellFounded_lt⟩

noncomputable def auxiliaryOrder : MonomialOrder (Fin 2) where
  syn := AuxiliaryExponent
  toSyn := { toEquiv := toAuxiliary, map_add' _ _ := rfl }
  toSyn_monotone a b hab := by
    change toLex (auxiliaryWeight a, toLex a) ≤ toLex (auxiliaryWeight b, toLex b)
    rw [Prod.Lex.toLex_le_toLex]
    have hw : auxiliaryWeight a ≤ auxiliaryWeight b := by
      have h0 := hab 0
      have h1 := hab 1
      dsimp [auxiliaryWeight]
      omega
    rcases lt_or_eq_of_le hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, Finsupp.toLex_monotone hab⟩

lemma auxiliaryOrder_lt_of_weight_lt {a b : Exponent}
    (h : auxiliaryWeight a < auxiliaryWeight b) : a ≺[auxiliaryOrder] b := by
  change toLex (auxiliaryWeight a, toLex a) < toLex (auxiliaryWeight b, toLex b)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

lemma degree_monic_add_sum [Nontrivial R] {ι : Type*} [Fintype ι]
    (m : MonomialOrder σ) (d : σ →₀ ℕ) (e : ι → σ →₀ ℕ) (c : ι → R)
    (hd : 0 ≺[m] d) (he : ∀ i, e i ≺[m] d) :
    m.degree (monomial d 1 + ∑ i, monomial (e i) (c i)) = d ∧
      m.Monic (monomial d 1 + ∑ i, monomial (e i) (c i)) := by
  classical
  have htail : m.degree (∑ i, monomial (e i) (c i)) ≺[m] d := by
    apply lt_of_le_of_lt m.degree_sum_le
    apply (Finset.sup_lt_iff (by simpa using hd)).mpr
    intro i _
    exact lt_of_le_of_lt (m.degree_monomial_le _) (he i)
  have hlead : m.degree (monomial d (1 : R)) = d := by
    rw [m.degree_monomial, if_neg one_ne_zero]
  have htail' : m.degree (∑ i, monomial (e i) (c i)) ≺[m]
      m.degree (monomial d (1 : R)) := by
    rwa [hlead]
  exact ⟨(m.degree_add_of_lt htail').trans hlead,
    m.monic_monomial_one.add_of_lt htail'⟩

def cubicTailExponent (i : Fin 4) : Exponent :=
  ![0, Finsupp.single 0 1, Finsupp.single 0 2, Finsupp.single 1 1] i

/-- The invariant cubic has no `x₀ w` term.  Its only term involving `w` is
`w x₃`, whose coefficient is absorbed into the coefficient ring here. -/
def normalizedCubic (c : Fin 4 → R) : MvPolynomial (Fin 2) R :=
  monomial (Finsupp.single 0 3) 1 + ∑ i, monomial (cubicTailExponent i) (c i)

abbrev SexticTailIndex :=
  {ij : Fin 7 × Fin 3 // ij.1.val + 2 * ij.2.val ≤ 6}

def sexticTailExponent (i : SexticTailIndex) : Exponent :=
  Finsupp.single 0 i.val.1.val + Finsupp.single 1 i.val.2.val

/-- Every term of the weighted sextic other than `w³` has `w` exponent at most
two and satisfies `x₀` exponent plus twice `w` exponent at most six. -/
def normalizedSextic (c : SexticTailIndex → R) : MvPolynomial (Fin 2) R :=
  monomial (Finsupp.single 1 3) 1 + ∑ i, monomial (sexticTailExponent i) (c i)

theorem normalizedCubic_leading_data [Nontrivial R] (c : Fin 4 → R) :
    auxiliaryOrder.degree (normalizedCubic c) = Finsupp.single 0 3 ∧
      auxiliaryOrder.Monic (normalizedCubic c) := by
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro i
    apply auxiliaryOrder_lt_of_weight_lt
    fin_cases i <;> norm_num [auxiliaryWeight, cubicTailExponent]

theorem normalizedSextic_leading_data [Nontrivial R] (c : SexticTailIndex → R) :
    auxiliaryOrder.degree (normalizedSextic c) = Finsupp.single 1 3 ∧
      auxiliaryOrder.Monic (normalizedSextic c) := by
  apply degree_monic_add_sum auxiliaryOrder
  · apply auxiliaryOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight]
  · intro i
    apply auxiliaryOrder_lt_of_weight_lt
    have hi := i.property
    have hj := i.val.2.isLt
    simp only [auxiliaryWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      sexticTailExponent, Finsupp.add_apply, Finsupp.single_apply]
    norm_num
    omega

/-- Standard monomials for the actual incidence chart have both distinguished
exponents strictly less than three. -/
def Standard (p : MvPolynomial (Fin 2) R) : Prop :=
  ∀ d ∈ p.support, d 0 < 3 ∧ d 1 < 3

lemma single_three_le_iff (i : σ) (d : σ →₀ ℕ) :
    Finsupp.single i 3 ≤ d ↔ 3 ≤ d i := by
  classical
  constructor
  · intro h
    simpa using h i
  · intro h j
    by_cases hji : j = i
    · subst j
      simpa using h
    · simp [Ne.symm hji]

theorem reduced_iff_standard [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    Reduced auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff) p ↔
      Standard p := by
  simp only [Reduced, Standard, (normalizedCubic_leading_data hcoeff).1,
    (normalizedSextic_leading_data Fcoeff).1, single_three_le_iff, not_le]

/-- The actual two-variable coefficient chart has unique standard remainders.
The assumptions here are just the coefficients of its normalized cubic and
sextic; no basis, confluence, Groebner, or rank hypothesis is supplied. -/
theorem existsUnique_standard_representative [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    ∃! r, Standard r ∧ ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff + r := by
  obtain ⟨hd, hm⟩ := normalizedCubic_leading_data hcoeff
  obtain ⟨Fd, Fm⟩ := normalizedSextic_leading_data Fcoeff
  have hcop : ∀ i, auxiliaryOrder.degree (normalizedCubic hcoeff) i = 0 ∨
      auxiliaryOrder.degree (normalizedSextic Fcoeff) i = 0 := by
    intro i
    rw [hd, Fd]
    fin_cases i <;> simp
  simpa only [reduced_iff_standard] using
    existsUnique_reduced_representative auxiliaryOrder
      (normalizedCubic hcoeff) (normalizedSextic Fcoeff) p hm Fm hcop

noncomputable def standardRemainder [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose

theorem standardRemainder_spec [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    Standard (standardRemainder hcoeff Fcoeff p) ∧ ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff +
        standardRemainder hcoeff Fcoeff p :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose_spec.1

theorem eq_standardRemainder [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p r : MvPolynomial (Fin 2) R)
    (hr : Standard r) (hp : ∃ a b,
      p = a * normalizedCubic hcoeff + b * normalizedSextic Fcoeff + r) :
    r = standardRemainder hcoeff Fcoeff p :=
  (existsUnique_standard_representative hcoeff Fcoeff p).choose_spec.2 r ⟨hr, hp⟩

lemma standard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {p : MvPolynomial (Fin 2) R} (hp : Standard p) :
    Standard (MvPolynomial.map φ p) := by
  intro d hd
  exact hp d (MvPolynomial.support_map_subset φ p hd)

@[simp] theorem map_normalizedCubic {S : Type*} [CommRing S]
    (φ : R →+* S) (c : Fin 4 → R) :
    MvPolynomial.map φ (normalizedCubic c) = normalizedCubic (φ ∘ c) := by
  simp [normalizedCubic]

@[simp] theorem map_normalizedSextic {S : Type*} [CommRing S]
    (φ : R →+* S) (c : SexticTailIndex → R) :
    MvPolynomial.map φ (normalizedSextic c) = normalizedSextic (φ ∘ c) := by
  simp [normalizedSextic]

/-- Normal reduction commutes with every coefficient specialization.  In
particular, it commutes with maps from the localized universal coefficient ring
to the residue field or to the generic lifted field. -/
theorem standardRemainder_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    MvPolynomial.map φ (standardRemainder hcoeff Fcoeff p) =
      standardRemainder (φ ∘ hcoeff) (φ ∘ Fcoeff) (MvPolynomial.map φ p) := by
  obtain ⟨hr, a, b, hp⟩ := standardRemainder_spec hcoeff Fcoeff p
  apply eq_standardRemainder _ _ _ _ (standard_map φ hr)
  refine ⟨MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
  simpa only [map_add, map_mul, map_normalizedCubic, map_normalizedSextic] using
    congrArg (MvPolynomial.map φ) hp

theorem standardRemainder_eq_zero_iff [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R)
    (p : MvPolynomial (Fin 2) R) :
    standardRemainder hcoeff Fcoeff p = 0 ↔
      p ∈ equationsIdeal (normalizedCubic hcoeff) (normalizedSextic Fcoeff) := by
  constructor
  · intro hr
    obtain ⟨_, a, b, hp⟩ := standardRemainder_spec hcoeff Fcoeff p
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by simpa [hr] using hp.symm⟩
  · intro hp
    obtain ⟨a, b, hp⟩ := Ideal.mem_span_pair.mp hp
    symm
    apply eq_standardRemainder _ _ _ _ (by simp [Standard])
    exact ⟨a, b, by simpa using hp.symm⟩

lemma concrete_coprime [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    ∀ i, auxiliaryOrder.degree (normalizedCubic hcoeff) i = 0 ∨
      auxiliaryOrder.degree (normalizedSextic Fcoeff) i = 0 := by
  intro i
  rw [(normalizedCubic_leading_data hcoeff).1, (normalizedSextic_leading_data Fcoeff).1]
  fin_cases i <;> simp

noncomputable def concreteExponentEquiv [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    reducedExponents auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff) ≃
      Fin 3 × Fin 3 where
  toFun d :=
    (⟨d.val 0, by
      have hd := d.property.1
      rw [(normalizedCubic_leading_data hcoeff).1, single_three_le_iff] at hd
      omega⟩,
     ⟨d.val 1, by
      have hd := d.property.2
      rw [(normalizedSextic_leading_data Fcoeff).1, single_three_le_iff] at hd
      omega⟩)
  invFun ij := ⟨Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val, by
    constructor
    · rw [(normalizedCubic_leading_data hcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.1.isLt
    · rw [(normalizedSextic_leading_data Fcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.2.isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext i
    fin_cases i <;> simp
  right_inv ij := by
    apply Prod.ext <;> apply Fin.ext <;> simp

/-- Rank-nine quotient basis for the normalized incidence chart, indexed by
the exponents `0 ≤ i,j < 3` of `x₀ⁱ wʲ`. -/
noncomputable def incidenceBasis [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) R
      (MvPolynomial (Fin 2) R ⧸ equationsIdeal
        (normalizedCubic hcoeff) (normalizedSextic Fcoeff)) :=
  (quotientBasis auxiliaryOrder (normalizedCubic hcoeff) (normalizedSextic Fcoeff)
    (normalizedCubic_leading_data hcoeff).2 (normalizedSextic_leading_data Fcoeff).2
    (concrete_coprime hcoeff Fcoeff)).reindex (concreteExponentEquiv hcoeff Fcoeff)

theorem incidenceBasis_apply [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) (ij : Fin 3 × Fin 3) :
    incidenceBasis hcoeff Fcoeff ij =
      Ideal.Quotient.mk (equationsIdeal (normalizedCubic hcoeff) (normalizedSextic Fcoeff))
        (X 0 ^ ij.1.val * X 1 ^ ij.2.val) := by
  rw [incidenceBasis, Module.Basis.reindex_apply, quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val) 1 = _
  rw [MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

/-- Scaling either defining equation by a unit does not change which polynomial
is its standard remainder.  This is the precise passage from a localization
chart with invertible leading coefficients to the monic presentation. -/
theorem existsUnique_standard_unit_scaled [Nontrivial R]
    (hcoeff : Fin 4 → R) (Fcoeff : SexticTailIndex → R) (u v : Rˣ)
    (p : MvPolynomial (Fin 2) R) :
    ∃! r, Standard r ∧ ∃ a b,
      p = a * (C (u : R) * normalizedCubic hcoeff) +
        b * (C (v : R) * normalizedSextic Fcoeff) + r := by
  apply (existsUnique_congr (fun r ↦ and_congr_right (fun _ ↦
    unit_scaled_representation_iff u v (normalizedCubic hcoeff)
      (normalizedSextic Fcoeff) p r))).mp
  exact existsUnique_standard_representative hcoeff Fcoeff p

/-- Grouping the eight non-leading invariant cubic coefficients by powers of
`x₀` gives the exact cubic family used by the incidence chart.  The three
coefficient-ring variables are `x₁,x₂,x₃`, in that order. -/
def invariantCubicTailCoefficients (c : Fin 8 → R) : Fin 4 → MvPolynomial (Fin 3) R :=
  ![C (c 2) * X 0 ^ 3 + C (c 4) * X 0 * X 1 * X 2 +
      C (c 5) * X 1 ^ 3 + C (c 6) * X 2 ^ 3,
    C (c 1) * X 0 ^ 2 + C (c 3) * X 1 * X 2,
    C (c 0) * X 0,
    C (c 7) * X 2]

noncomputable def invariantIncidenceBasis [Nontrivial R]
    (hcoeff : Fin 8 → R) (Fcoeff : SexticTailIndex → MvPolynomial (Fin 3) R) :
    Module.Basis (Fin 3 × Fin 3) (MvPolynomial (Fin 3) R)
      (MvPolynomial (Fin 2) (MvPolynomial (Fin 3) R) ⧸ equationsIdeal
        (normalizedCubic (invariantCubicTailCoefficients hcoeff))
        (normalizedSextic Fcoeff)) :=
  incidenceBasis (invariantCubicTailCoefficients hcoeff) Fcoeff

/-! ## Full-variable weighted order and invariant polynomial family -/

/-- Adding an additive natural-valued weight in front of a monomial order gives
another monomial order.  The old order breaks ties, so zero weights are allowed. -/
def WeightedExponent (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) := σ →₀ ℕ

def toWeighted (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    (σ →₀ ℕ) ≃ WeightedExponent m W := Equiv.refl _
def ofWeighted (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    WeightedExponent m W ≃ (σ →₀ ℕ) := Equiv.refl _

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    AddCommMonoid (WeightedExponent m W) := (ofWeighted m W).addCommMonoid

lemma ofWeighted_add (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ)
    (a b : WeightedExponent m W) :
    ofWeighted m W (a + b) = ofWeighted m W a + ofWeighted m W b := rfl

def weightedKey (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ)
    (a : WeightedExponent m W) : Lex (ℕ × m.syn) :=
  toLex (W (ofWeighted m W a), m.toSyn (ofWeighted m W a))

lemma weightedKey_injective (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    Function.Injective (weightedKey m W) := by
  intro a b hab
  exact (ofWeighted m W).injective (m.toSyn.injective (Prod.mk.inj (toLex.injective hab)).2)

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    LinearOrder (WeightedExponent m W) :=
  LinearOrder.lift' (weightedKey m W) (weightedKey_injective m W)

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    IsOrderedCancelAddMonoid (WeightedExponent m W) where
  le_of_add_le_add_left a b c h := by
    change weightedKey m W b ≤ weightedKey m W c
    change weightedKey m W (a + b) ≤ weightedKey m W (a + c) at h
    simpa only [weightedKey, ofWeighted_add, map_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_left, add_right_inj,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    change weightedKey m W a ≤ weightedKey m W b at h
    change weightedKey m W (a + c) ≤ weightedKey m W (b + c)
    simpa only [weightedKey, ofWeighted_add, map_add,
      Prod.Lex.toLex_le_toLex, add_lt_add_iff_right, add_left_inj,
      add_le_add_iff_right] using h

noncomputable instance (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    WellFoundedLT (WeightedExponent m W) :=
  ⟨InvImage.wf (weightedKey m W) wellFounded_lt⟩

noncomputable def weightedOrder (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) :
    MonomialOrder σ where
  syn := WeightedExponent m W
  toSyn := { toEquiv := toWeighted m W, map_add' _ _ := rfl }
  toSyn_monotone a b hab := by
    change toLex (W a, m.toSyn a) ≤ toLex (W b, m.toSyn b)
    rw [Prod.Lex.toLex_le_toLex]
    have hw : W a ≤ W b := by
      rw [← add_tsub_cancel_of_le hab, map_add]
      exact Nat.le_add_right _ _
    rcases lt_or_eq_of_le hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr ⟨hw, m.toSyn_monotone hab⟩

lemma weightedOrder_lt_of_weight_lt
    (m : MonomialOrder σ) (W : (σ →₀ ℕ) →+ ℕ) {a b : σ →₀ ℕ}
    (h : W a < W b) : a ≺[weightedOrder m W] b := by
  change toLex (W a, m.toSyn a) < toLex (W b, m.toSyn b)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

abbrev FullExponent := Fin 5 →₀ ℕ

def fullAuxiliaryWeight : FullExponent →+ ℕ where
  toFun e := 3 * e 0 + e 1 + e 2 + e 3 + 7 * e 4
  map_zero' := by simp
  map_add' a b := by
    simp only [Finsupp.add_apply]
    omega

noncomputable def fullAuxiliaryOrder : MonomialOrder (Fin 5) :=
  weightedOrder MonomialOrder.lex fullAuxiliaryWeight

def fullDegree (e : Fin 5 → ℕ) : ℕ := e 0 + e 1 + e 2 + e 3 + 2 * e 4
def fullCharacter (e : Fin 5 → ℕ) : ℕ := (2 * e 0 + 2 * e 1 + e 2) % 3

/-- All invariant monomials of the stated weighted degree; no search-selected
subset of the coefficients is used. -/
abbrev FullInvariantIndex (d : ℕ) :=
  {e : Fin 5 → Fin (d + 1) //
    fullDegree (fun i ↦ (e i).val) = d ∧ fullCharacter (fun i ↦ (e i).val) = 0}

abbrev FullCubicTailIndex := {e : FullInvariantIndex 3 // (e.val 0).val < 3}
abbrev FullSexticTailIndex := {e : FullInvariantIndex 6 // (e.val 4).val < 3}

def fullExponentOf {d : ℕ} (e : Fin 5 → Fin (d + 1)) : FullExponent :=
  ∑ i, Finsupp.single i (e i).val

@[simp] lemma fullExponentOf_apply {d : ℕ} (e : Fin 5 → Fin (d + 1)) (i : Fin 5) :
    fullExponentOf e i = (e i).val := by
  classical
  simp [fullExponentOf, Finsupp.single_apply]

def normalizedFullCubic (c : FullCubicTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 0 3) 1 + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def normalizedFullSextic (c : FullSexticTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 4 3) 1 + ∑ e, monomial (fullExponentOf e.val.val) (c e)

theorem normalizedFullCubic_leading_data [Nontrivial R] (c : FullCubicTailIndex → R) :
    fullAuxiliaryOrder.degree (normalizedFullCubic c) = Finsupp.single 0 3 ∧
      fullAuxiliaryOrder.Monic (normalizedFullCubic c) := by
  apply degree_monic_add_sum fullAuxiliaryOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [fullAuxiliaryWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have hc := e.val.property.2
    have h0 := e.property
    simp only [fullDegree, fullCharacter] at hd hc
    simp [fullAuxiliaryWeight]
    have h4 : (e.val.val 4).val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h4 with h4 | h4
    · omega
    · have hc_lt : 2 * (e.val.val 0).val + 2 * (e.val.val 1).val +
          (e.val.val 2).val < 3 := by omega
      rw [Nat.mod_eq_of_lt hc_lt] at hc
      omega

theorem normalizedFullSextic_leading_data [Nontrivial R] (c : FullSexticTailIndex → R) :
    fullAuxiliaryOrder.degree (normalizedFullSextic c) = Finsupp.single 4 3 ∧
      fullAuxiliaryOrder.Monic (normalizedFullSextic c) := by
  apply degree_monic_add_sum fullAuxiliaryOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [fullAuxiliaryWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have h4 := e.property
    simp only [fullDegree] at hd
    simp [fullAuxiliaryWeight]
    omega

def FullStandard (p : MvPolynomial (Fin 5) R) : Prop :=
  ∀ e ∈ p.support, e 0 < 3 ∧ e 4 < 3

theorem full_reduced_iff_standard [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    Reduced fullAuxiliaryOrder (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) p ↔
      FullStandard p := by
  simp only [Reduced, FullStandard, (normalizedFullCubic_leading_data hcoeff).1,
    (normalizedFullSextic_leading_data Fcoeff).1, single_three_le_iff, not_le]

lemma full_coprime [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R) :
    ∀ i, fullAuxiliaryOrder.degree (normalizedFullCubic hcoeff) i = 0 ∨
      fullAuxiliaryOrder.degree (normalizedFullSextic Fcoeff) i = 0 := by
  intro i
  rw [(normalizedFullCubic_leading_data hcoeff).1, (normalizedFullSextic_leading_data Fcoeff).1]
  fin_cases i <;> simp

theorem existsUnique_full_standard_representative [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * normalizedFullCubic hcoeff + b * normalizedFullSextic Fcoeff + r := by
  simpa only [full_reduced_iff_standard] using
    existsUnique_reduced_representative fullAuxiliaryOrder
      (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff) p
      (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
      (full_coprime hcoeff Fcoeff)

def fullGrading : Fin 5 → ℕ × ZMod 3 :=
  ![(1, 2), (1, 2), (1, 1), (1, 0), (2, 0)]

theorem fullGrading_weight (e : FullExponent) :
    Finsupp.weight fullGrading e =
      (fullDegree e, ((2 * e 0 + 2 * e 1 + e 2 : ℕ) : ZMod 3)) := by
  rw [Finsupp.weight_eq_sum]
  apply Prod.ext <;>
    simp [fullGrading, fullDegree, Fin.sum_univ_succ, nsmul_eq_mul] <;> ring

theorem fullGrading_eq_iff (e : FullExponent) (d : ℕ) :
    Finsupp.weight fullGrading e = (d, 0) ↔ fullDegree e = d ∧ fullCharacter e = 0 := by
  rw [fullGrading_weight, Prod.mk.injEq]
  simp only [fullCharacter, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]

def fullIndexOf {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) : FullInvariantIndex d := by
  have hh := (fullGrading_eq_iff e d).mp he
  have hb : ∀ i, e i < d + 1 := by
    intro i
    have hd := hh.1
    simp only [fullDegree] at hd
    fin_cases i
    · change e 0 < d + 1
      omega
    · change e 1 < d + 1
      omega
    · change e 2 < d + 1
      omega
    · change e 3 < d + 1
      omega
    · change e 4 < d + 1
      omega
  exact ⟨fun i ↦ ⟨e i, hb i⟩, hh⟩

@[simp] lemma fullIndexOf_apply {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) (i : Fin 5) :
    ((fullIndexOf e he).val i).val = e i := rfl

@[simp] lemma fullIndexOf_exponent {d : ℕ} (e : FullExponent)
    (he : Finsupp.weight fullGrading e = (d, 0)) :
    fullExponentOf (fullIndexOf e he).val = e := by
  ext i
  simp

theorem fullGrading_of_invariant {d : ℕ} (e : FullInvariantIndex d) :
    Finsupp.weight fullGrading (fullExponentOf e.val) = (d, 0) := by
  rw [fullGrading_weight]
  apply Prod.ext
  · simpa only [fullDegree, fullExponentOf_apply] using e.property.1
  · have hc := congrArg (fun n : ℕ ↦ (n : ZMod 3)) e.property.2
    simpa [fullCharacter] using hc

theorem normalizedFullCubic_homogeneous (c : FullCubicTailIndex → R) :
    (normalizedFullCubic c).IsWeightedHomogeneous fullGrading (3, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (3, 0)).add_mem
  · apply isWeightedHomogeneous_monomial
    rw [Finsupp.weight_single]
    decide
  · apply (weightedHomogeneousSubmodule R fullGrading (3, 0)).sum_mem
    intro e _
    exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e.val)

theorem normalizedFullSextic_homogeneous (c : FullSexticTailIndex → R) :
    (normalizedFullSextic c).IsWeightedHomogeneous fullGrading (6, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (6, 0)).add_mem
  · apply isWeightedHomogeneous_monomial
    rw [Finsupp.weight_single]
    decide
  · apply (weightedHomogeneousSubmodule R fullGrading (6, 0)).sum_mem
    intro e _
    exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e.val)

/-- The raw full families have all nine cubic and all forty-five sextic
coefficients, including their leading coefficients. -/
def rawFullCubic (a : R) (c : FullCubicTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 0 3) a + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def rawFullSextic (a : R) (c : FullSexticTailIndex → R) : MvPolynomial (Fin 5) R :=
  monomial (Finsupp.single 4 3) a + ∑ e, monomial (fullExponentOf e.val.val) (c e)

def fullCubicLeadingIndex : FullInvariantIndex 3 :=
  ⟨![3, 0, 0, 0, 0], by decide⟩

def fullSexticLeadingIndex : FullInvariantIndex 6 :=
  ⟨![0, 0, 0, 0, 3], by decide⟩

lemma fullCubic_tail_iff_ne (e : FullInvariantIndex 3) :
    (e.val 0).val < 3 ↔ e ≠ fullCubicLeadingIndex := by
  constructor
  · intro he h
    subst e
    change (3 : ℕ) < 3 at he
    omega
  · intro he
    by_contra h0
    apply he
    have hd := e.property.1
    have hb := (e.val 0).isLt
    simp only [fullDegree] at hd
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i <;> simp [fullCubicLeadingIndex] <;> omega

lemma fullSextic_tail_iff_ne (e : FullInvariantIndex 6) :
    (e.val 4).val < 3 ↔ e ≠ fullSexticLeadingIndex := by
  constructor
  · intro he h
    subst e
    change (3 : ℕ) < 3 at he
    omega
  · intro he
    by_contra h4
    apply he
    have hd := e.property.1
    simp only [fullDegree] at hd
    apply Subtype.ext
    funext i
    apply Fin.ext
    fin_cases i <;> simp [fullSexticLeadingIndex] <;> omega

noncomputable def fullCubicTailEquiv :
    FullCubicTailIndex ≃ {e : FullInvariantIndex 3 // e ≠ fullCubicLeadingIndex} :=
  Equiv.subtypeEquivRight fullCubic_tail_iff_ne

noncomputable def fullSexticTailEquiv :
    FullSexticTailIndex ≃ {e : FullInvariantIndex 6 // e ≠ fullSexticLeadingIndex} :=
  Equiv.subtypeEquivRight fullSextic_tail_iff_ne

@[simp] lemma fullCubicLeadingIndex_exponent :
    fullExponentOf fullCubicLeadingIndex.val = Finsupp.single 0 3 := by
  ext i
  fin_cases i <;> simp [fullCubicLeadingIndex]

@[simp] lemma fullSexticLeadingIndex_exponent :
    fullExponentOf fullSexticLeadingIndex.val = Finsupp.single 4 3 := by
  ext i
  fin_cases i <;> simp [fullSexticLeadingIndex]

/-- The complete invariant coefficient family, with one independent coefficient
for every invariant monomial of weighted degree `d`. -/
def fullInvariantPolynomial (d : ℕ) (c : FullInvariantIndex d → R) :
    MvPolynomial (Fin 5) R :=
  ∑ e, monomial (fullExponentOf e.val) (c e)

lemma fullExponentOf_injective {d : ℕ} :
    Function.Injective (fullExponentOf (d := d)) := by
  intro e f h
  funext i
  apply Fin.ext
  simpa only [fullExponentOf_apply] using congrArg (fun s : FullExponent ↦ s i) h

theorem fullInvariantPolynomial_coeff (d : ℕ) (c : FullInvariantIndex d → R)
    (e : FullInvariantIndex d) :
    (fullInvariantPolynomial d c).coeff (fullExponentOf e.val) = c e := by
  classical
  have heq (f : FullInvariantIndex d) :
      fullExponentOf f.val = fullExponentOf e.val ↔ f = e := by
    constructor
    · intro h
      exact Subtype.ext (fullExponentOf_injective h)
    · rintro rfl
      rfl
  simp [fullInvariantPolynomial, coeff_sum, coeff_monomial, heq]

/-- Every homogeneous invariant polynomial is exactly a member of the full
coefficient family, with its own monomial coefficients. -/
theorem fullInvariantPolynomial_of_homogeneous {d : ℕ} {p : MvPolynomial (Fin 5) R}
    (hp : p.IsWeightedHomogeneous fullGrading (d, 0)) :
    fullInvariantPolynomial d (fun e ↦ p.coeff (fullExponentOf e.val)) = p := by
  classical
  ext s
  by_cases hs : ∃ e : FullInvariantIndex d, fullExponentOf e.val = s
  · obtain ⟨e, rfl⟩ := hs
    exact fullInvariantPolynomial_coeff d _ e
  · have hp0 : p.coeff s = 0 := by
      by_contra hp0
      exact hs ⟨fullIndexOf s (hp hp0), fullIndexOf_exponent s (hp hp0)⟩
    rw [hp0]
    simp only [fullInvariantPolynomial, coeff_sum, coeff_monomial]
    apply Finset.sum_eq_zero
    intro e _
    have he : fullExponentOf e.val ≠ s := fun he ↦ hs ⟨e, he⟩
    simp [he]

theorem fullInvariantPolynomial_homogeneous (d : ℕ) (c : FullInvariantIndex d → R) :
    (fullInvariantPolynomial d c).IsWeightedHomogeneous fullGrading (d, 0) := by
  apply (weightedHomogeneousSubmodule R fullGrading (d, 0)).sum_mem
  intro e _
  exact isWeightedHomogeneous_monomial fullGrading _ _ (fullGrading_of_invariant e)

@[simp] theorem map_fullInvariantPolynomial {S : Type*} [CommRing S]
    (φ : R →+* S) (d : ℕ) (c : FullInvariantIndex d → R) :
    MvPolynomial.map φ (fullInvariantPolynomial d c) =
      fullInvariantPolynomial d (φ ∘ c) := by
  simp [fullInvariantPolynomial]

theorem fullInvariantPolynomial_cubic (c : FullInvariantIndex 3 → R) :
    fullInvariantPolynomial 3 c =
      rawFullCubic (c fullCubicLeadingIndex) (fun e ↦ c e.val) := by
  classical
  rw [fullInvariantPolynomial,
    Fintype.sum_eq_add_sum_subtype_ne _ fullCubicLeadingIndex]
  simp only [fullCubicLeadingIndex_exponent, rawFullCubic]
  exact congrArg (fun q : MvPolynomial (Fin 5) R ↦
    monomial (Finsupp.single 0 3) (c fullCubicLeadingIndex) + q)
    (fullCubicTailEquiv.sum_comp
      (fun e ↦ monomial (fullExponentOf e.val.val) (c e.val))).symm

theorem fullInvariantPolynomial_sextic (c : FullInvariantIndex 6 → R) :
    fullInvariantPolynomial 6 c =
      rawFullSextic (c fullSexticLeadingIndex) (fun e ↦ c e.val) := by
  classical
  rw [fullInvariantPolynomial,
    Fintype.sum_eq_add_sum_subtype_ne _ fullSexticLeadingIndex]
  simp only [fullSexticLeadingIndex_exponent, rawFullSextic]
  exact congrArg (fun q : MvPolynomial (Fin 5) R ↦
    monomial (Finsupp.single 4 3) (c fullSexticLeadingIndex) + q)
    (fullSexticTailEquiv.sum_comp
      (fun e ↦ monomial (fullExponentOf e.val.val) (c e.val))).symm

theorem rawFullCubic_eq_unit_mul (u : Rˣ) (c : FullCubicTailIndex → R) :
    rawFullCubic (u : R) c =
      C (u : R) * normalizedFullCubic (fun e ↦ (↑u⁻¹ : R) * c e) := by
  simp [rawFullCubic, normalizedFullCubic, mul_add, Finset.mul_sum,
    C_mul_monomial, ← mul_assoc]

theorem rawFullSextic_eq_unit_mul (u : Rˣ) (c : FullSexticTailIndex → R) :
    rawFullSextic (u : R) c =
      C (u : R) * normalizedFullSextic (fun e ↦ (↑u⁻¹ : R) * c e) := by
  simp [rawFullSextic, normalizedFullSextic, mul_add, Finset.mul_sum,
    C_mul_monomial, ← mul_assoc]

/-- This applies directly over the localized universal coefficient ring: the
inverted leading coefficients are units, and no inverse equations are asserted
in an unconstrained polynomial ring. -/
theorem existsUnique_full_standard_unit_leading [Nontrivial R]
    (u v : Rˣ) (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * rawFullCubic (u : R) hcoeff + b * rawFullSextic (v : R) Fcoeff + r := by
  rw [rawFullCubic_eq_unit_mul, rawFullSextic_eq_unit_mul]
  apply (existsUnique_congr (fun r ↦ and_congr_right (fun _ ↦
    unit_scaled_representation_iff u v
      (normalizedFullCubic (fun e ↦ (↑u⁻¹ : R) * hcoeff e))
      (normalizedFullSextic (fun e ↦ (↑v⁻¹ : R) * Fcoeff e)) p r))).mp
  exact existsUnique_full_standard_representative
    (fun e ↦ (↑u⁻¹ : R) * hcoeff e) (fun e ↦ (↑v⁻¹ : R) * Fcoeff e) p

/-- The normal-form chart for the entire invariant cubic/sextic coefficient
space.  Its only open conditions are invertibility of the two indicated
leading coefficients. -/
theorem existsUnique_full_invariant_representative [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    ∃! r, FullStandard r ∧ ∃ a b,
      p = a * fullInvariantPolynomial 3 hcoeff + b * fullInvariantPolynomial 6 Fcoeff + r := by
  rw [fullInvariantPolynomial_cubic, fullInvariantPolynomial_sextic]
  simpa only [hu.unit_spec, Fu.unit_spec] using
    existsUnique_full_standard_unit_leading hu.unit Fu.unit
      (fun e ↦ hcoeff e.val) (fun e ↦ Fcoeff e.val) p

theorem full_standard_preserves_grading [Nontrivial R]
    (hcoeff : FullCubicTailIndex → R) (Fcoeff : FullSexticTailIndex → R)
    {p r a b : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) (hr : FullStandard r)
    (heq : p = a * normalizedFullCubic hcoeff + b * normalizedFullSextic Fcoeff + r) :
    r.IsWeightedHomogeneous fullGrading (d, χ) := by
  exact reduced_isWeightedHomogeneous fullGrading fullAuxiliaryOrder
    (normalizedFullCubic_leading_data hcoeff).2 (normalizedFullSextic_leading_data Fcoeff).2
    (full_coprime hcoeff Fcoeff) (normalizedFullCubic_homogeneous hcoeff)
    (normalizedFullSextic_homogeneous Fcoeff) hp
    ((full_reduced_iff_standard hcoeff Fcoeff r).mpr hr) heq

theorem full_invariant_standard_preserves_grading [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    {p r a b : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) (hr : FullStandard r)
    (heq : p = a * fullInvariantPolynomial 3 hcoeff +
      b * fullInvariantPolynomial 6 Fcoeff + r) :
    r.IsWeightedHomogeneous fullGrading (d, χ) := by
  let hc : FullCubicTailIndex → R := fun e ↦ (↑hu.unit⁻¹ : R) * hcoeff e.val
  let Fc : FullSexticTailIndex → R := fun e ↦ (↑Fu.unit⁻¹ : R) * Fcoeff e.val
  have hh : fullInvariantPolynomial 3 hcoeff = C (hu.unit : R) * normalizedFullCubic hc := by
    rw [fullInvariantPolynomial_cubic]
    exact (congrArg (fun z ↦ rawFullCubic z (fun e ↦ hcoeff e.val)) hu.unit_spec.symm).trans
      (rawFullCubic_eq_unit_mul hu.unit _)
  have hF : fullInvariantPolynomial 6 Fcoeff = C (Fu.unit : R) * normalizedFullSextic Fc := by
    rw [fullInvariantPolynomial_sextic]
    exact (congrArg (fun z ↦ rawFullSextic z (fun e ↦ Fcoeff e.val)) Fu.unit_spec.symm).trans
      (rawFullSextic_eq_unit_mul Fu.unit _)
  rw [hh, hF] at heq
  exact full_standard_preserves_grading hc Fc hp hr
    (a := a * C (hu.unit : R)) (b := b * C (Fu.unit : R))
    (by simpa only [mul_assoc] using heq)

noncomputable def fullRemainder [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial (Fin 5) R :=
  (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose

theorem fullRemainder_spec [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    FullStandard (fullRemainder hcoeff Fcoeff hu Fu p) ∧ ∃ a b,
      p = a * fullInvariantPolynomial 3 hcoeff + b * fullInvariantPolynomial 6 Fcoeff +
        fullRemainder hcoeff Fcoeff hu Fu p :=
  (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose_spec.1

theorem fullRemainder_preserves_grading [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex))
    {p : MvPolynomial (Fin 5) R} {d : ℕ} {χ : ZMod 3}
    (hp : p.IsWeightedHomogeneous fullGrading (d, χ)) :
    (fullRemainder hcoeff Fcoeff hu Fu p).IsWeightedHomogeneous fullGrading (d, χ) := by
  obtain ⟨hr, a, b, heq⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
  exact full_invariant_standard_preserves_grading hcoeff Fcoeff hu Fu hp hr heq

lemma fullStandard_map {S : Type*} [CommRing S] (φ : R →+* S)
    {p : MvPolynomial (Fin 5) R} (hp : FullStandard p) :
    FullStandard (MvPolynomial.map φ p) := by
  intro d hd
  exact hp d (MvPolynomial.support_map_subset φ p hd)

/-- Actual full-family coefficient specialization, including the leading-unit
chart, commutes with reduction. -/
theorem fullRemainder_map [Nontrivial R] {S : Type*} [CommRing S] [Nontrivial S]
    (φ : R →+* S) (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map φ (fullRemainder hcoeff Fcoeff hu Fu p) =
      fullRemainder (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ) (MvPolynomial.map φ p) := by
  obtain ⟨hr, a, b, hp⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
  apply (existsUnique_full_invariant_representative
    (φ ∘ hcoeff) (φ ∘ Fcoeff) (hu.map φ) (Fu.map φ) (MvPolynomial.map φ p)).choose_spec.2
  refine ⟨fullStandard_map φ hr, MvPolynomial.map φ a, MvPolynomial.map φ b, ?_⟩
  simpa only [map_add, map_mul, map_fullInvariantPolynomial] using congrArg (MvPolynomial.map φ) hp

theorem fullRemainder_eq_zero_iff [Nontrivial R]
    (hcoeff : FullInvariantIndex 3 → R) (Fcoeff : FullInvariantIndex 6 → R)
    (hu : IsUnit (hcoeff fullCubicLeadingIndex))
    (Fu : IsUnit (Fcoeff fullSexticLeadingIndex)) (p : MvPolynomial (Fin 5) R) :
    fullRemainder hcoeff Fcoeff hu Fu p = 0 ↔
      p ∈ equationsIdeal (fullInvariantPolynomial 3 hcoeff) (fullInvariantPolynomial 6 Fcoeff) := by
  constructor
  · intro hr
    obtain ⟨_, a, b, hp⟩ := fullRemainder_spec hcoeff Fcoeff hu Fu p
    apply Ideal.mem_span_pair.mpr
    exact ⟨a, b, by simpa [hr] using hp.symm⟩
  · intro hp
    obtain ⟨a, b, hp⟩ := Ideal.mem_span_pair.mp hp
    symm
    apply (existsUnique_full_invariant_representative hcoeff Fcoeff hu Fu p).choose_spec.2
    exact ⟨by simp [FullStandard], a, b, by simpa using hp.symm⟩

end CycleQ2IncidenceNormalForm

#print axioms CycleQ2IncidenceNormalForm.reduced_eq_zero_of_representation
#print axioms CycleQ2IncidenceNormalForm.quotientBasis_apply
#print axioms CycleQ2IncidenceNormalForm.fullInvariantPolynomial_of_homogeneous
#print axioms CycleQ2IncidenceNormalForm.existsUnique_full_invariant_representative
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_map
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_preserves_grading
#print axioms CycleQ2IncidenceNormalForm.fullRemainder_eq_zero_iff
end
end


/- Component: continuation_3/LinearAnnihilatorKernel.lean -/
section
/-! Exactness forced by a small annihilator and dimension bounds. The proof
uses only the actual entry image, the full image, and the restricted detector.
No preselected entry correction or large invertible matrix is assumed.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearAnnihilatorKernel

variable {K V W X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup X] [Module K X]

theorem annihilator_kernel_eq_entry_range
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J))) :
    LinearMap.range J ⊓ LinearMap.ker L=LinearMap.range E := by
  let U : Submodule K V := LinearMap.range J
  let P : Submodule K U := (LinearMap.range E).comap U.subtype
  let T : U →ₗ[K] (Fin s → K) := L.domRestrict U
  have hPK : P≤LinearMap.ker T := by
    intro y hy
    change (y:V)∈LinearMap.range E at hy
    obtain ⟨w,hw⟩ := hy
    change L (y:V)=0
    rw [←hw]
    exact LinearMap.congr_fun hLE w
  have hPdim : Module.finrank K P=Module.finrank K (LinearMap.range E) :=
    (Submodule.comapSubtypeEquivOfLe hEJ).finrank_eq
  have hPbound : r≤Module.finrank K P := by
    rw [hPdim]
    exact hE
  have hTsurj : Function.Surjective T := hsurj
  have hTdim : Module.finrank K (LinearMap.range T)=s := by
    rw [LinearMap.range_eq_top.mpr hTsurj]
    simp only [finrank_top,Module.finrank_fintype_fun_eq_card,Fintype.card_fin]
  have hUbound : Module.finrank K U≤r+s := hJ
  have hnull := T.finrank_range_add_finrank_ker
  rw [hTdim] at hnull
  have hKbound : Module.finrank K (LinearMap.ker T)≤r := by omega
  have heq : P=LinearMap.ker T :=
    Submodule.eq_of_le_of_finrank_eq hPK
      (Nat.le_antisymm (Submodule.finrank_mono hPK) (hKbound.trans hPbound))
  ext y
  constructor
  · intro hy
    let q : U := ⟨y,hy.1⟩
    have hq : q∈LinearMap.ker T := by
      change L y=0
      exact hy.2
    have hp : q∈P := by rw [heq]; exact hq
    change y∈LinearMap.range E at hp
    exact hp
  · intro hy
    refine ⟨hEJ hy,?_⟩
    obtain ⟨w,rfl⟩ := hy
    change L (E w)=0
    exact LinearMap.congr_fun hLE w

theorem exists_entry_correction
    (E : W →ₗ[K] V) (J : X →ₗ[K] V) (r s : ℕ) (L : V →ₗ[K] (Fin s → K))
    (hEJ : LinearMap.range E≤LinearMap.range J)
    (hJ : Module.finrank K (LinearMap.range J)≤r+s)
    (hE : r≤Module.finrank K (LinearMap.range E))
    (hLE : L.comp E=0)
    (hsurj : Function.Surjective (L.domRestrict (LinearMap.range J)))
    (y : V) (hy : y∈LinearMap.range J) (hLy : L y=0) :
    ∃ w : W, E w=y := by
  change y∈LinearMap.range E
  rw [←annihilator_kernel_eq_entry_range E J r s L hEJ hJ hE hLE hsurj]
  exact ⟨hy,hLy⟩

end CycleQ2LinearAnnihilatorKernel

#print axioms CycleQ2LinearAnnihilatorKernel.annihilator_kernel_eq_entry_range
#print axioms CycleQ2LinearAnnihilatorKernel.exists_entry_correction
end
end


/- Component: continuation_3/LinearAnnihilatorRank.lean -/
section
/-! # Rank gained by directions detected by an annihilator of an existing image -/

noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearAnnihilatorRank

variable {K X Z V Y W : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Z] [Module K Z]
  [AddCommGroup V] [Module K V] [AddCommGroup Y] [Module K Y]
  [AddCommGroup W] [Module K W] [FiniteDimensional K Y]

/-- The old image lies in the kernel of the restricted detector, while the
new detected image lies in its range. Rank-nullity gives the sum bound. -/
theorem rank_add_le_of_annihilator (f : X →ₗ[K] Y) (g : Z →ₗ[K] Y)
    (H : V →ₗ[K] Y) (L : Y →ₗ[K] W)
    (hf : LinearMap.range f≤LinearMap.range H)
    (hg : LinearMap.range g≤LinearMap.range H) (hLf : L.comp f=0) :
    Module.finrank K (LinearMap.range f)+Module.finrank K (LinearMap.range (L.comp g))≤
      Module.finrank K (LinearMap.range H) := by
  let R := LinearMap.range H
  let T : R →ₗ[K] W := L.comp R.subtype
  have hzero (y : LinearMap.range f) : L y.val=0 := by
    obtain ⟨x,hx⟩ := y.property
    rw [←hx]
    exact LinearMap.congr_fun hLf x
  let inclusion : LinearMap.range f →ₗ[K] LinearMap.ker T :=
    { toFun := fun y => ⟨⟨y.val,hf y.property⟩,hzero y⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective inclusion := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun y : LinearMap.ker T => y.val.val) hab
  have h1 : Module.finrank K (LinearMap.range f)≤Module.finrank K (LinearMap.ker T) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h2 : LinearMap.range (L.comp g)≤LinearMap.range T := by
    rintro z ⟨x,rfl⟩
    exact ⟨⟨g x,hg ⟨x,rfl⟩⟩,rfl⟩
  have h3 := Submodule.finrank_mono h2
  have h4 := T.finrank_range_add_finrank_ker
  change Module.finrank K (LinearMap.range T)+Module.finrank K (LinearMap.ker T)=
    Module.finrank K (LinearMap.range H) at h4
  omega

variable {m n a b k : Type*} [Fintype m] [Fintype n] [Fintype a] [Fintype b] [Fintype k]

theorem selected_columns_range_le (H : Matrix m n K) (c : a → n) :
    LinearMap.range (Matrix.mulVecLin (H.submatrix id c))≤
      LinearMap.range (Matrix.mulVecLin H) := by
  rw [Matrix.range_mulVecLin,Matrix.range_mulVecLin]
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨c j,rfl⟩

/-- A checked left-annihilator of one selected column block detects new
independent columns without any assumption about an unchecked large minor. -/
theorem selected_column_rank_add_le (H : Matrix m n K) (c0 : a → n) (c1 : b → n)
    (L : Matrix k m K) (hL : L*H.submatrix id c0=0) :
    (H.submatrix id c0).rank+(L*H.submatrix id c1).rank≤H.rank := by
  simp only [Matrix.rank]
  rw [Matrix.mulVecLin_mul L (H.submatrix id c1)]
  apply rank_add_le_of_annihilator (Matrix.mulVecLin (H.submatrix id c0))
    (Matrix.mulVecLin (H.submatrix id c1)) (Matrix.mulVecLin H) (Matrix.mulVecLin L)
    (selected_columns_range_le H c0) (selected_columns_range_le H c1)
  rw [←Matrix.mulVecLin_mul,hL]
  ext x
  simp

end CycleQ2LinearAnnihilatorRank

#print axioms CycleQ2LinearAnnihilatorRank.rank_add_le_of_annihilator
#print axioms CycleQ2LinearAnnihilatorRank.selected_column_rank_add_le
end
end


/- Component: continuation_3/LinearExactSequenceSplit.lean -/
section
/-! # Compatible nonconstructive coordinates for an exact Jacobian sequence

The equation space is split into the image of the Jacobian and a complement
detected by the actual relation matrix.  Both square seed blocks become the
identity in these coordinates.  The coordinate changes are selected from
proved exactness; no numerical pivot or inverse is an extra premise.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LinearExactSequenceSplit

open Matrix

variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- A compatible splitting, including an extension of the relation-coordinate
projection from the actual image to the whole relation space. -/
theorem exists_split (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z)
    (hexact : LinearMap.range f = LinearMap.ker g) :
    ∃ (B : LinearMap.ker g →ₗ[K] X)
      (S : LinearMap.range g →ₗ[K] Y)
      (P : Y →ₗ[K] LinearMap.ker g)
      (T : Z →ₗ[K] LinearMap.range g),
      f.comp B = (LinearMap.ker g).subtype ∧
      g.rangeRestrict.comp S = LinearMap.id ∧
      (LinearMap.ker g).subtype.comp P + S.comp g.rangeRestrict = LinearMap.id ∧
      P.comp (LinearMap.ker g).subtype = LinearMap.id ∧
      P.comp S = 0 ∧
      T.comp (LinearMap.range g).subtype = LinearMap.id := by
  let f' : X →ₗ[K] LinearMap.ker g :=
    f.codRestrict (LinearMap.ker g) (fun x => hexact ▸ LinearMap.mem_range_self f x)
  have hf' : Function.Surjective f' := by
    intro y
    obtain ⟨x,hx⟩ := (show y.val ∈ LinearMap.range f from hexact.symm ▸ y.property)
    exact ⟨x,Subtype.ext hx⟩
  obtain ⟨B,hB⟩ := f'.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hf')
  obtain ⟨S,hS⟩ := g.rangeRestrict.exists_rightInverse_of_surjective g.range_rangeRestrict
  obtain ⟨T,hT⟩ := (LinearMap.range g).subtype.exists_leftInverse_of_injective
    (LinearMap.range g).ker_subtype
  have hSval (z : LinearMap.range g) : g (S z)=z.val := by
    exact congrArg Subtype.val (LinearMap.congr_fun hS z)
  let P : Y →ₗ[K] LinearMap.ker g :=
    (LinearMap.id - S.comp g.rangeRestrict).codRestrict (LinearMap.ker g) (by
      intro y
      change g (y-S (g.rangeRestrict y))=0
      rw [map_sub,hSval]
      exact sub_self _)
  refine ⟨B,S,P,T,?_,hS,?_,?_,?_,hT⟩
  · ext y
    exact congrArg Subtype.val (LinearMap.congr_fun hB y)
  · ext y
    change y-S (g.rangeRestrict y)+S (g.rangeRestrict y)=y
    exact sub_add_cancel _ _
  · ext y
    change y.val-S (g.rangeRestrict y.val)=y.val
    have hz : g.rangeRestrict y.val=0 := Subtype.ext y.property
    rw [hz,map_zero,sub_zero]
  · ext z
    change S z-S (g.rangeRestrict (S z))=0
    have hsz := LinearMap.congr_fun hS z
    change g.rangeRestrict (S z)=z at hsz
    rw [hsz,sub_self]

variable {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq m]

/-- Compatible square blocks for an exact pair of literal matrices.  The
first block is the Jacobian on chosen parameter directions; the second
is the relation matrix on complementary equation coordinates. -/
theorem exists_matrix_split (J : Matrix m n K) (R : Matrix l m K)
    (hexact : LinearMap.range (Matrix.mulVecLin J)=LinearMap.ker (Matrix.mulVecLin R)) :
    ∃ (P : Matrix (Fin J.rank) m K)
      (Q : Matrix m (Fin J.rank) K)
      (V : Matrix m (Fin R.rank) K)
      (W : Matrix (Fin R.rank) m K)
      (T : Matrix (Fin R.rank) l K)
      (B : Matrix n (Fin J.rank) K),
      Q*P+V*W=1 ∧ P*J*B=1 ∧ T*R*V=1 ∧ R*Q=0 ∧ P*V=0 := by
  classical
  let f := Matrix.mulVecLin J
  let g := Matrix.mulVecLin R
  obtain ⟨B,S,P,T,hB,hS,hdecomp,hP,hPS,hT⟩ := exists_split f g hexact
  have hdim : Module.finrank K (LinearMap.ker g)=J.rank := by
    rw [←hexact]
    rfl
  let bU : Module.Basis (Fin J.rank) K (LinearMap.ker g) :=
    (Module.finBasis K (LinearMap.ker g)).reindex (finCongr hdim)
  let bV := Module.finBasis K (LinearMap.range g)
  let P0 := bU.equivFun.toLinearMap.comp P
  let Q0 := (LinearMap.ker g).subtype.comp bU.equivFun.symm.toLinearMap
  let V0 := S.comp bV.equivFun.symm.toLinearMap
  let W0 := bV.equivFun.toLinearMap.comp g.rangeRestrict
  let T0 := bV.equivFun.toLinearMap.comp T
  let B0 := B.comp bU.equivFun.symm.toLinearMap
  refine ⟨LinearMap.toMatrix' P0,LinearMap.toMatrix' Q0,LinearMap.toMatrix' V0,
    LinearMap.toMatrix' W0,LinearMap.toMatrix' T0,LinearMap.toMatrix' B0,?_,?_,?_,?_,?_⟩
  · apply Matrix.toLin'.injective
    simp only [map_add,Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro y
    change (bU.equivFun.symm (bU.equivFun (P y))).val+
      S (bV.equivFun.symm (bV.equivFun (g.rangeRestrict y)))=y
    simp only [LinearEquiv.symm_apply_apply]
    exact LinearMap.congr_fun hdecomp y
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (f (B (bU.equivFun.symm x))))=x
    have hb := LinearMap.congr_fun hB (bU.equivFun.symm x)
    change f (B (bU.equivFun.symm x))=(bU.equivFun.symm x).val at hb
    have hp := LinearMap.congr_fun hP (bU.equivFun.symm x)
    change P (bU.equivFun.symm x).val=bU.equivFun.symm x at hp
    rw [hb,hp,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',Matrix.toLin'_one]
    apply LinearMap.ext
    intro x
    change bV.equivFun (T (g (S (bV.equivFun.symm x))))=x
    have hSv := congrArg Subtype.val (LinearMap.congr_fun hS (bV.equivFun.symm x))
    change g (S (bV.equivFun.symm x))=(bV.equivFun.symm x).val at hSv
    have ht := LinearMap.congr_fun hT (bV.equivFun.symm x)
    change T (bV.equivFun.symm x).val=bV.equivFun.symm x at ht
    rw [hSv,ht,LinearEquiv.apply_symm_apply]
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    exact (bU.equivFun.symm x).property
  · apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul,Matrix.toLin'_toMatrix',map_zero]
    apply LinearMap.ext
    intro x
    change bU.equivFun (P (S (bV.equivFun.symm x)))=0
    have hps := LinearMap.congr_fun hPS (bV.equivFun.symm x)
    change P (S (bV.equivFun.symm x))=0 at hps
    rw [hps,map_zero]

end CycleQ2LinearExactSequenceSplit

#print axioms CycleQ2LinearExactSequenceSplit.exists_split
#print axioms CycleQ2LinearExactSequenceSplit.exists_matrix_split
end
end


/- Component: continuation_3/LinearKernelProjection.lean -/
section
/-! # A projection from a kernel with a compensating family

If every value of a linear map can be produced using directions killed by a
parameter projection, every parameter direction lifts to its kernel. This is
pure linear algebra; it makes no assertion about nonlinear integration.
-/

noncomputable section

namespace CycleQ2LinearKernelProjection

variable {K U V W T : Type*} [Ring K]
  [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
  [AddCommGroup T] [Module K T]

theorem exists_kernel_correction
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i)) (v : V) :
    ∃u : U, f (v-i u)=0 ∧ p (v-i u)=p v := by
  obtain ⟨u,hu⟩ := hrange (LinearMap.mem_range_self f v)
  refine ⟨u,?_,?_⟩
  · change f (i u)=f v at hu
    rw [map_sub,hu,sub_self]
  · have hpu : p (i u)=0 := congrArg (fun q : U →ₗ[K] T => q u) hip
    rw [map_sub,hpu,sub_zero]

theorem kernel_projection_surjective
    (f : V →ₗ[K] W) (i : U →ₗ[K] V) (p : V →ₗ[K] T)
    (hip : p.comp i=0)
    (hrange : LinearMap.range f≤LinearMap.range (f.comp i))
    (hp : Function.Surjective p) :
    Function.Surjective (p.comp (LinearMap.ker f).subtype) := by
  intro t
  obtain ⟨v,hv⟩ := hp t
  obtain ⟨u,hu,hup⟩ := exists_kernel_correction f i p hip hrange v
  exact ⟨⟨v-i u,hu⟩,hup.trans hv⟩

end CycleQ2LinearKernelProjection

#print axioms CycleQ2LinearKernelProjection.kernel_projection_surjective
end
end


/- Component: continuation_3/LinearKernelTrace.lean -/
section
/-! A strict rank increase after adjoining a scalar row is equivalent to a
kernel direction with nonzero scalar value. Over a field that direction can
be normalized to any prescribed value. Both directions use finite-dimensional
linear algebra and require no chosen matrix minor or explicit kernel vector.
-/

noncomputable section
set_option maxHeartbeats 300000

namespace CycleQ2LinearKernelTrace

variable {K V W U : Type*} [Field K]
  [AddCommGroup V] [Module K V] [Module.Finite K V]
  [AddCommGroup W] [Module K W] [AddCommGroup U] [Module K U]

theorem rank_le_of_kernel_le (f : V →ₗ[K] W) (g : V →ₗ[K] U)
    (hker : LinearMap.ker f≤LinearMap.ker g) :
    Module.finrank K (LinearMap.range g)≤Module.finrank K (LinearMap.range f) := by
  have hk := Submodule.finrank_mono hker
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_one_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) :
    ∃ v : V, f v=0 ∧ ℓ v=1 := by
  classical
  have hex : ∃ v : V, f v=0 ∧ ℓ v≠0 := by
    by_contra hn
    push_neg at hn
    have hk : LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
      intro v hv
      change f v=0 at hv
      change (f v,ℓ v)=(0,0)
      exact Prod.ext hv (hn v hv)
    exact not_lt_of_ge (rank_le_of_kernel_le f (f.prod ℓ) hk) hrank
  obtain ⟨v,hv,hℓ⟩ := hex
  refine ⟨(ℓ v)⁻¹ • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,smul_eq_mul,inv_mul_cancel₀ hℓ]

theorem rank_add_one_le_of_kernel_trace_one (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hex : ∃ v : V, f v=0 ∧ ℓ v=1) :
    Module.finrank K (LinearMap.range f)+1≤
      Module.finrank K (LinearMap.range (f.prod ℓ)) := by
  obtain ⟨v,hv,hℓ⟩ := hex
  have hle : LinearMap.ker (f.prod ℓ)≤LinearMap.ker f := by
    intro w hw
    change (f.prod ℓ) w=0 at hw
    change f w=0
    exact congrArg Prod.fst hw
  have hn : ¬LinearMap.ker f≤LinearMap.ker (f.prod ℓ) := by
    intro hk
    have hz := hk (show v∈LinearMap.ker f from hv)
    change (f.prod ℓ) v=0 at hz
    have hzero : ℓ v=0 := congrArg Prod.snd hz
    exact one_ne_zero (hℓ.symm.trans hzero)
  have hd := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hn)
  have hf := f.finrank_range_add_finrank_ker
  have hg := (f.prod ℓ).finrank_range_add_finrank_ker
  omega

theorem exists_kernel_trace_value_of_rank_lt (f : V →ₗ[K] W) (ℓ : V →ₗ[K] K)
    (hrank : Module.finrank K (LinearMap.range f)<
      Module.finrank K (LinearMap.range (f.prod ℓ))) (a : K) :
    ∃ v : V, f v=0 ∧ ℓ v=a := by
  obtain ⟨v,hv,hℓ⟩ := exists_kernel_trace_one_of_rank_lt f ℓ hrank
  refine ⟨a • v,?_,?_⟩
  · simp only [map_smul,hv,smul_zero]
  · simp only [map_smul,hℓ,smul_eq_mul,mul_one]

end CycleQ2LinearKernelTrace

#print axioms CycleQ2LinearKernelTrace.exists_kernel_trace_one_of_rank_lt
#print axioms CycleQ2LinearKernelTrace.rank_add_one_le_of_kernel_trace_one
end
end


/- Component: continuation_3/cylinder_bridge/LinearRangeDescent.lean -/
section
/-! # Linear descent to the actual range

A linear map that kills the kernel of another map descends to that map's
actual range. The generic construction keeps the quotient universal
property separate from the concrete localized coefficient rings.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2LinearRangeDescent

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

def descendRange (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) : LinearMap.range f →ₗ[R] P :=
  ((LinearMap.ker f).liftQ g h).comp f.quotKerEquivRange.symm.toLinearMap

theorem descendRange_apply_image (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (h : LinearMap.ker f ≤ LinearMap.ker g) (x : M) :
    descendRange f g h ⟨f x,⟨x,rfl⟩⟩=g x := by
  unfold descendRange
  rw [LinearMap.comp_apply,LinearEquiv.coe_coe,
    LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

def kernelQuotientInjection (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : (M ⧸ K) →ₗ[R] P :=
  K.liftQ g (le_of_eq h.symm)

theorem kernelQuotientInjection_injective (g : M →ₗ[R] P) (K : Submodule R M)
    (h : LinearMap.ker g=K) : Function.Injective (kernelQuotientInjection g K h) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot' K g h.symm

end CycleQ2LinearRangeDescent

#print axioms CycleQ2LinearRangeDescent.descendRange_apply_image
#print axioms CycleQ2LinearRangeDescent.kernelQuotientInjection_injective
end
end


/- Component: continuation_3/LinkageIdealPrincipal.lean -/
section
/-!
# Local principality from a regular linkage pairing

If I*J is contained in (p), p is regular, and a selected pairing a*b is
p times a unit, the selected sections generate I and J. The argument
works in arbitrary commutative rings, including reducible seed rings.
-/

noncomputable section
set_option maxHeartbeats 1000000

namespace CycleQ2LinkageIdealPrincipal

variable {R : Type*} [CommRing R]

theorem factors_regular (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (hab : a*b=p*u) :
    Function.Injective (fun x : R => a*x) ∧
      Function.Injective (fun x : R => b*x) := by
  constructor
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = b*(a*x) := by rw [← mul_assoc, ← hab]; ring
      _ = b*(a*y) := congrArg (b*·) h
      _ = p*(u*y) := by linear_combination y * hab
  · intro x y h
    apply hu.mul_right_injective
    apply hp
    calc
      p*(u*x) = a*(b*x) := by rw [← mul_assoc, ← hab]; ring
      _ = a*(b*y) := congrArg (a*·) h
      _ = p*(u*y) := by linear_combination y * hab

theorem ideal_eq_selected (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) : I=Ideal.span {a} := by
  rcases hu with ⟨v,rfl⟩
  have hbinj := (factors_regular p a b (v:R) hp v.isUnit hab).2
  apply le_antisymm
  · intro x hx
    obtain ⟨q,hq⟩ := hpair x hx b hb
    apply Ideal.mem_span_singleton.mpr
    refine ⟨(↑(v⁻¹):R)*q, ?_⟩
    apply hbinj
    calc
      b*x = p*q := by simpa only [mul_comm] using hq
      _ = b*(a*((↑(v⁻¹):R)*q)) := by
        calc
          p*q = (p*(v:R))*(↑(v⁻¹):R)*q := by simp [mul_assoc]
          _ = b*(a*((↑(v⁻¹):R)*q)) := by rw [← hab]; ring
  · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha)

/-- Both actual factor ideals become principal on every chart where
one selected product has unit quotient by the linkage element. -/
theorem ideals_principal (I J : Ideal R) (p a b u : R)
    (hp : Function.Injective (fun x : R => p*x)) (hu : IsUnit u)
    (ha : a∈I) (hb : b∈J) (hab : a*b=p*u)
    (hpair : ∀ x∈I, ∀ y∈J, p ∣ x*y) :
    I=Ideal.span {a} ∧ J=Ideal.span {b} := by
  refine ⟨ideal_eq_selected I J p a b u hp hu ha hb hab hpair, ?_⟩
  apply ideal_eq_selected J I p b a u hp hu hb ha (by simpa [mul_comm] using hab)
  intro y hy x hx
  simpa only [mul_comm] using hpair x hx y hy

/-- Regularity survives every localization, without requiring that the
localization map itself be injective. -/
theorem localization_mul_injective (M : Submonoid R) (S : Type*)
    [CommRing S] [Algebra R S] [IsLocalization M S]
    (p : R) (hp : Function.Injective (fun x : R => p*x)) :
    Function.Injective (fun x : S => algebraMap R S p*x) := by
  have hpn : p ∈ nonZeroDivisors R := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    apply hp
    simpa only [mul_zero] using hx
  have hsn : algebraMap R S p ∈ nonZeroDivisors S :=
    IsLocalization.nonZeroDivisors_le_comap M S hpn
  intro x y h
  change algebraMap R S p*x=algebraMap R S p*y at h
  apply sub_eq_zero.mp
  apply (mem_nonZeroDivisors_iff_left.mp hsn)
  rw [mul_sub, h, sub_self]

end CycleQ2LinkageIdealPrincipal

#print axioms CycleQ2LinkageIdealPrincipal.ideals_principal
#print axioms CycleQ2LinkageIdealPrincipal.localization_mul_injective
end
end


/- Component: continuation_3/LocalizationKernel.lean -/
section
/-! # Kernels of the actual localized ring map

This is the fraction calculation for a map of localizations whose target
denominators are exactly the images of the source denominators.
-/

noncomputable section

namespace CycleQ2LocalizationKernel

theorem kernel_map {R S P Q : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring P] [CommSemiring Q]
    {M : Submonoid R} {T : Submonoid P}
    [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
    (g : R →+* P) (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S →+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

theorem kernel_away {R S P Q : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring P] [CommSemiring Q]
    [Algebra R S] [Algebra P Q] (g : R →+* P) (x : R)
    [IsLocalization.Away x S] [IsLocalization.Away (g x) Q] :
    RingHom.ker (IsLocalization.Away.map S Q g x) =
      (RingHom.ker g).map (algebraMap R S) := by
  exact kernel_map g (Submonoid.map_powers g x)

end CycleQ2LocalizationKernel

#print axioms CycleQ2LocalizationKernel.kernel_away
end
end


/- Component: continuation_3/LocalizationRegularFactor.lean -/
section
/-! # Faithfulness when a regular factor is added to an open -/

noncomputable section

namespace CycleQ2LocalizationRegularFactor

theorem pow_mul_injective {R : Type*} [CommMonoid R] (b : R)
    (hb : Function.Injective (fun x : R => b*x)) (n : ℕ) :
    Function.Injective (fun x : R => b^n*x) := by
  induction n with
  | zero =>
    intro x y h
    simpa only [pow_zero,one_mul] using h
  | succ n ih =>
    intro x y h
    apply ih
    apply hb
    simpa only [pow_succ',mul_assoc] using h

/-- Passing from D(a) to D(a*b) is faithful whenever b is regular.
The source denominator a need not be regular. -/
theorem restriction_injective {R S T : Type*}
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    (a b : R) [IsLocalization.Away a S] [IsLocalization.Away (a*b) T]
    (hb : Function.Injective (fun x : R => b*x)) (f : S →+* T)
    (hf : ∀ x : R, f (algebraMap R S x)=algebraMap R T x) :
    Function.Injective f := by
  have hz : ∀ z : S, f z=0 → z=0 := by
    intro z hz
    obtain ⟨n,x,hx⟩ := IsLocalization.Away.surj a z
    have ht : algebraMap R T x=0 := by
      have hh := congrArg f hx
      simp only [map_mul,map_pow,hf,hz,zero_mul] at hh
      exact hh.symm
    obtain ⟨m,hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (a*b)) T x).mp ht
    obtain ⟨k,hk⟩ := m.property
    have hax : a^k*x=0 := by
      apply pow_mul_injective b hb k
      have hprod : (a*b)^k*x=b^k*(a^k*x) := by rw [mul_pow]; ring
      simpa only [← hk,hprod,mul_zero] using hm
    have hs : algebraMap R S x=0 :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers a) S x).mpr
        ⟨⟨a^k,⟨k,rfl⟩⟩,hax⟩
    have hu : IsUnit (algebraMap R S a^n) :=
      (IsLocalization.Away.algebraMap_isUnit a).pow n
    apply hu.mul_left_injective
    simpa only [hs,zero_mul] using hx
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub,h,sub_self]

end CycleQ2LocalizationRegularFactor

#print axioms CycleQ2LocalizationRegularFactor.restriction_injective
end
end


/- Component: continuation_3/cylinder_bridge/MatrixImageLocalization.lean -/
section
/-! Localization of the actual matrix image is the image of its localized
matrix.  This is proved using the span of the literal columns and mathlib's
localization of submodules, so local image trivializations apply to the
global image module itself. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixImageLocalization
open Matrix LinearMap

variable {R S α β : Type*} [CommRing R] [CommRing S]
  [Algebra R S] [Fintype α] [Fintype β]
  (p : Submonoid R) [IsLocalization p S]

def vectorMap : (α → R) →ₗ[R] (α → S) :=
  LinearMap.pi (fun i => (Algebra.linearMap R S).comp (LinearMap.proj i))

instance vectorMap_localized : IsLocalizedModule p (vectorMap (R := R) (S := S) (α := α)) :=
  IsLocalizedModule.pi p (fun _ : α => Algebra.linearMap R S)

theorem localized_image (M : Matrix α β R) :
    (LinearMap.range M.mulVecLin).localized' S p (vectorMap (R := R) (S := S))=
      LinearMap.range (M.map (algebraMap R S)).mulVecLin := by
  rw [Matrix.range_mulVecLin,Submodule.localized'_span,Matrix.range_mulVecLin]
  congr 1
  rw [←Set.range_comp]
  rfl

end CycleQ2MatrixImageLocalization

#print axioms CycleQ2MatrixImageLocalization.localized_image
end
end


/- Component: continuation_3/MatrixTraceAugment.lean -/
section
/-! Appending one actual scalar functional to a matrix preserves the
linear-map product description and commutes with coefficient maps. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MatrixTraceAugment
open Matrix

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K]
  {m n : Type*} [Fintype n]

def rowLinear (r : n → R) : (n → R) →ₗ[R] R :=
  dotProductBilin R R r

def augment (A : Matrix m n R) (r : n → R) : Matrix (m ⊕ Unit) n R :=
  fun i j => Sum.elim (fun k => A k j) (fun _ => r j) i

theorem augment_apply_left (A : Matrix m n R) (r x : n → R) (i : m) :
    (augment A r *ᵥ x) (Sum.inl i)=(A*ᵥx) i := rfl

theorem augment_apply_right (A : Matrix m n R) (r x : n → R) :
    (augment A r *ᵥ x) (Sum.inr ())=rowLinear r x := rfl

theorem augment_map (φ : R →+* S) (A : Matrix m n R) (r : n → R) :
    (augment A r).map φ=augment (A.map φ) (φ ∘ r) := by
  funext i j
  rcases i with i | i <;> rfl

theorem augment_ker (A : Matrix m n K) (r : n → K) :
    LinearMap.ker (Matrix.mulVecLin (augment A r))=
      LinearMap.ker ((Matrix.mulVecLin A).prod (rowLinear r)) := by
  ext x
  change (augment A r *ᵥ x=0) ↔ (A*ᵥx,rowLinear r x)=0
  constructor
  · intro h
    apply Prod.ext
    · funext i
      exact congrFun h (Sum.inl i)
    · exact congrFun h (Sum.inr ())
  · intro h
    funext i
    rcases i with i | i
    · exact congrFun (congrArg Prod.fst h) i
    · cases i
      exact congrArg Prod.snd h

theorem augment_rank [Fintype m] (A : Matrix m n K) (r : n → K) :
    (augment A r).rank=
      Module.finrank K (LinearMap.range ((Matrix.mulVecLin A).prod (rowLinear r))) := by
  classical
  have hA := (Matrix.mulVecLin (augment A r)).finrank_range_add_finrank_ker
  have hB := ((Matrix.mulVecLin A).prod (rowLinear r)).finrank_range_add_finrank_ker
  rw [augment_ker] at hA
  change (augment A r).rank+_= _ at hA
  omega

end CycleQ2MatrixTraceAugment

#print axioms CycleQ2MatrixTraceAugment.augment_rank
end
end


/- Component: continuation_3/NaturalPolynomialDigits.lean -/
section
/-! Exact extraction of polynomial coefficients from a natural base evaluation.
The coefficient bound rules out carries. -/

namespace CycleQ2NaturalPolynomialDigits
open Polynomial

theorem eval_split (B : ℕ) (p : ℕ[X]) :
    p.eval B=p.coeff 0+B*p.divX.eval B := by
  have h := congrArg (Polynomial.eval B) (divX_mul_X_add p)
  simpa only [eval_add,eval_mul,eval_X,eval_C,Nat.mul_comm,Nat.add_comm] using h.symm

theorem div_eval (B : ℕ) (hB : 0<B) (p : ℕ[X]) (h0 : p.coeff 0<B) :
    p.eval B/B=p.divX.eval B := by
  rw [eval_split,Nat.add_mul_div_left _ _ hB,Nat.div_eq_of_lt h0,zero_add]

theorem coefficient (B : ℕ) (hB : 0<B) (p : ℕ[X])
    (hc : ∀ n,p.coeff n<B) (k : ℕ) :
    p.coeff k=(p.eval B/B^k)%B := by
  induction k generalizing p with
  | zero =>
    rw [Nat.pow_zero,Nat.div_one,eval_split]
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (hc 0)]
  | succ k ih =>
    have h := ih p.divX (fun n => by simpa only [coeff_divX] using hc (n+1))
    rw [coeff_divX,←div_eval B hB p (hc 0)] at h
    simpa only [Nat.div_div_eq_div_mul,Nat.pow_succ,Nat.mul_comm] using h

end CycleQ2NaturalPolynomialDigits

#print axioms CycleQ2NaturalPolynomialDigits.coefficient
end


/- Component: continuation_3/PointedEtaleGeneric.lean -/
section
/-! A finite separable generic point specializing to a prescribed seed.

Flat going-down first produces a prime below the seed kernel and contracting
to zero in the base domain.  Localizing at the nonzero base elements then
gives a prime of the actual generic fiber.  That fiber is an étale algebra
over a field, hence finite; its prime is maximal and its quotient separable.
The contraction containment is retained in the conclusion, so this does not
choose an unrelated component of the generic fiber.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PointedEtaleGeneric

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R B : Type*} [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]

theorem exists_generic_prime_below [Module.Flat R B]
    (q : Ideal B) [q.IsPrime] :
    ∃ P : Ideal B, P≤q ∧ P.IsPrime ∧ P.under R=⊥ := by
  obtain ⟨P,hP,hprime,hlying⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R))
      (q := q.under R) q bot_le
  exact ⟨P,hP,hprime,hlying.over.symm⟩

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

theorem genericFiber_isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) (K ⊗[R] B) :=
  (Algebra.isLocalization_iff_isPushout (nonZeroDivisors R) K).mpr inferInstance

theorem generic_prime_disjoint (P : Ideal B) (hP : P.under R=⊥) :
    Disjoint (Algebra.algebraMapSubmonoid B (nonZeroDivisors R) : Set B) P := by
  rw [Set.disjoint_left]
  intro b hb hmem
  obtain ⟨r,hr,rfl⟩ := hb
  have hz : r∈P.under R := hmem
  rw [hP,Ideal.mem_bot] at hz
  exact (mem_nonZeroDivisors_iff_ne_zero.mp hr) hz

/-- The chosen maximal ideal of the generic fiber lies on a component
whose closure contains the prescribed seed. -/
theorem exists_pointed_fieldFactor [Algebra.Etale R B]
    {T : Type*} [Field T] [Algebra R T] (seed : B →ₐ[R] T) :
    ∃ I : Ideal (K ⊗[R] B), I.IsMaximal ∧
      Module.Finite K ((K ⊗[R] B) ⧸ I) ∧
      Algebra.IsSeparable K ((K ⊗[R] B) ⧸ I) ∧
      I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
        RingHom.ker seed.toRingHom := by
  let q : Ideal B := RingHom.ker seed.toRingHom
  letI : q.IsPrime := RingHom.ker_isPrime seed.toRingHom
  obtain ⟨P,hP,hprime,hzero⟩ := exists_generic_prime_below (R := R) q
  letI : P.IsPrime := hprime
  let M : Submonoid B := Algebra.algebraMapSubmonoid B (nonZeroDivisors R)
  letI : IsLocalization M (K ⊗[R] B) := genericFiber_isLocalization K
  have hd : Disjoint (M : Set B) P := generic_prime_disjoint P hzero
  let I : Ideal (K ⊗[R] B) := P.map (algebraMap B (K ⊗[R] B))
  letI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M _ P hprime hd
  letI : Module.Finite K (K ⊗[R] B) :=
    Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] B)
  letI : IsArtinianRing (K ⊗[R] B) := IsArtinianRing.of_finite K (K ⊗[R] B)
  refine ⟨I,inferInstance,inferInstance,inferInstance,?_⟩
  have hIP : I.under B=P :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hprime hd
  change I.under B≤q
  rw [hIP]
  exact hP

theorem seed_zero_of_generic_zero {T : Type*} [Field T] [Algebra R T]
    (seed : B →ₐ[R] T) (I : Ideal (K ⊗[R] B))
    (hI : I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
      RingHom.ker seed.toRingHom) (b : B)
    (hb : Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)=0) :
    seed b=0 := by
  apply hI
  change Algebra.TensorProduct.includeRight b∈I
  exact Ideal.Quotient.eq_zero_iff_mem.mp hb

theorem generic_ne_zero_of_seed_ne_zero {T : Type*} [Field T] [Algebra R T]
    (seed : B →ₐ[R] T) (I : Ideal (K ⊗[R] B))
    (hI : I.comap (Algebra.TensorProduct.includeRight : B →ₐ[R] K ⊗[R] B).toRingHom ≤
      RingHom.ker seed.toRingHom) (b : B) (hb : seed b≠0) :
    Ideal.Quotient.mk I (Algebra.TensorProduct.includeRight b)≠0 :=
  fun h => hb (seed_zero_of_generic_zero K seed I hI b h)

end CycleQ2PointedEtaleGeneric

#print axioms CycleQ2PointedEtaleGeneric.exists_pointed_fieldFactor
#print axioms CycleQ2PointedEtaleGeneric.generic_ne_zero_of_seed_ne_zero
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialAffineSlice.lean -/
section
/-! Affine polynomial substitution and its literal Jacobian.  The centre may
belong to a parameter coefficient ring; it need not be a constant complex
point.  Thus the same construction fixes the external family parameters. -/

noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2PolynomialAffineSlice
open MvPolynomial Matrix

variable {R S σ ι m : Type*} [CommRing R] [CommRing S]
  [Fintype ι]

def affinePoint (a : σ → R) (B : Matrix σ ι R) : σ → MvPolynomial ι R :=
  fun k => C (a k) + ∑ j, C (B k j) * X j

def substitute (a : σ → R) (B : Matrix σ ι R) :
    MvPolynomial σ R →ₐ[R] MvPolynomial ι R :=
  aeval (affinePoint a B)

def pointValue (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) : σ → S :=
  fun k => φ (a k) + ∑ j, φ (B k j) * x j

theorem eval_affinePoint (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (k : σ) :
    eval₂Hom φ x (affinePoint a B k) = pointValue φ a B x k := by
  simp [affinePoint,pointValue]

theorem eval_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (p : MvPolynomial σ R) :
    eval₂Hom φ x (substitute a B p) = eval₂Hom φ (pointValue φ a B x) p := by
  have h : (eval₂Hom φ x).comp (substitute a B).toRingHom =
      eval₂Hom φ (pointValue φ a B x) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [substitute]
    · intro k
      change eval₂Hom φ x (aeval (affinePoint a B) (X k)) =
        eval₂Hom φ (pointValue φ a B x) (X k)
      rw [aeval_X,eval₂Hom_X']
      exact eval_affinePoint φ a B x k
  exact RingHom.congr_fun h p

theorem eval_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (substitute a B p) = eval₂Hom φ (φ ∘ a) p := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_substitute,hp]

theorem pderiv_affinePoint (a : σ → R) (B : Matrix σ ι R) (j : ι) (k : σ) :
    pderiv j (affinePoint a B k) = C (B k j) := by
  classical
  simp [affinePoint,Pi.single_apply]

theorem substitute_C (a : σ → R) (B : Matrix σ ι R) (r : R) :
    substitute a B (C r) = C r := by
  exact aeval_C (affinePoint a B) r

theorem substitute_X (a : σ → R) (B : Matrix σ ι R) (k : σ) :
    substitute a B (X k) = affinePoint a B k := aeval_X _ k

variable [Fintype σ]

/-- The exact chain rule for the chosen affine parameter directions. -/
theorem pderiv_substitute (a : σ → R) (B : Matrix σ ι R) (j : ι)
    (p : MvPolynomial σ R) :
    pderiv j (substitute a B p) =
      ∑ k, C (B k j) * substitute a B (pderiv k p) := by
  classical
  refine MvPolynomial.induction_on (motive := fun f =>
    pderiv j (substitute a B f) = ∑ k, C (B k j) * substitute a B (pderiv k f))
    p ?_ ?_ ?_
  · intro r
    simp only [substitute_C,pderiv_C,map_zero,mul_zero,Finset.sum_const_zero]
  · intro p q hp hq
    simp only [map_add,hp,hq,mul_add,Finset.sum_add_distrib]
  · intro p k hp
    have hx : substitute a B (X k) = affinePoint a B k := substitute_X a B k
    have hs : (∑ l, C (B l j) * substitute a B p *
        substitute a B (pderiv l (X k))) = C (B k j) * substitute a B p := by
      rw [Finset.sum_eq_single k]
      · rw [pderiv_X_self,map_one,mul_one]
      · intro l _ hl
        rw [pderiv_X_of_ne (Ne.symm hl),map_zero,mul_zero]
      · intro hk
        exact (hk (Finset.mem_univ k)).elim
    calc
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p)) * affinePoint a B k +
          substitute a B p * C (B k j) := by
        rw [map_mul,pderiv_mul,hp,hx,pderiv_affinePoint]
      _ = (∑ l, C (B l j) * substitute a B (pderiv l p) * affinePoint a B k) +
          ∑ l, C (B l j) * substitute a B p * substitute a B (pderiv l (X k)) := by
        rw [← Finset.sum_mul,hs,mul_comm (substitute a B p)]
      _ = ∑ l, C (B l j) * substitute a B (pderiv l (p * X k)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro l _
        rw [pderiv_mul,map_add,map_mul,map_mul,hx]
        simp only [mul_add,mul_assoc]
theorem eval_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ x (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (pointValue φ a B x) (pderiv k p) := by
  rw [pderiv_substitute]
  simp only [map_sum,map_mul,eval₂Hom_C,eval_substitute]

theorem eval_zero_pderiv_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (j : ι) (p : MvPolynomial σ R) :
    eval₂Hom φ (0 : ι → S) (pderiv j (substitute a B p)) =
      ∑ k, φ (B k j) * eval₂Hom φ (φ ∘ a) (pderiv k p) := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [eval_pderiv_substitute,hp]

def jacobian (φ : R →+* S) (x : σ → S) (e : m → MvPolynomial σ R) :
    Matrix m σ S := fun q k => eval₂Hom φ x (pderiv k (e q))

theorem jacobian_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (x : ι → S) (e : m → MvPolynomial σ R) :
    jacobian φ x (fun q => substitute a B (e q)) =
      jacobian φ (pointValue φ a B x) e * B.map φ := by
  funext q j
  simp only [jacobian,eval_pderiv_substitute,Matrix.mul_apply,Matrix.map_apply,mul_comm]

theorem jacobian_zero_substitute (φ : R →+* S) (a : σ → R) (B : Matrix σ ι R)
    (e : m → MvPolynomial σ R) :
    jacobian φ (0 : ι → S) (fun q => substitute a B (e q)) =
      jacobian φ (φ ∘ a) e * B.map φ := by
  have hp : pointValue φ a B (0 : ι → S) = φ ∘ a := by
    funext k
    simp [pointValue]
  rw [jacobian_substitute,hp]

end CycleQ2PolynomialAffineSlice

#print axioms CycleQ2PolynomialAffineSlice.pderiv_substitute
#print axioms CycleQ2PolynomialAffineSlice.jacobian_zero_substitute
end
end


/- Component: continuation_3/cylinder_bridge/PolynomialDualEvaluation.lean -/
section
/-! A literal single-coordinate dual-number evaluation of a polynomial has
first coefficient equal to its formal partial derivative at the base point. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace CycleQ2PolynomialDualEvaluation
open MvPolynomial

variable {R σ : Type*} [CommRing R]

abbrev Dual (R : Type*) := TrivSqZeroExt R R

def point (x : σ → R) (j : σ) : σ → Dual R := by
  classical
  exact fun i => ⟨x i,if j=i then 1 else 0⟩

theorem eval_point (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    aeval (point x j) p = (⟨eval x p,eval x (pderiv j p)⟩ : Dual R) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c =>
      apply TrivSqZeroExt.ext <;> simp [point, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
      rw [map_add,hp,hq]
      apply TrivSqZeroExt.ext <;> simp
  | mul_X p i hp =>
      rw [map_mul,hp,aeval_X]
      apply TrivSqZeroExt.ext
      · simp [point]
      · by_cases hij : j=i
        · subst i
          simp [point,pderiv_mul,pderiv_X,smul_eq_mul,op_smul_eq_smul]
          ring
        · simp [point,pderiv_mul,pderiv_X,Pi.single_apply,hij,Ne.symm hij,
            smul_eq_mul,op_smul_eq_smul]
          ring

theorem eval_point_fst (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).fst=eval x p := by rw [eval_point]; rfl

theorem eval_point_snd (x : σ → R) (j : σ) (p : MvPolynomial σ R) :
    (aeval (point x j) p).snd=eval x (pderiv j p) := by rw [eval_point]; rfl

end CycleQ2PolynomialDualEvaluation

#print axioms CycleQ2PolynomialDualEvaluation.eval_point_snd
end
end


/- Component: continuation_3/PolynomialSurjectivityOpen.lean -/
section
/-! A single principal open preserves surjectivity of an actual finite
coefficient matrix. A coefficient section lifts a nonconstructively chosen
seed right inverse. The resulting determinant evaluates to one at the seed.
No evaluated choice of a maximal minor is required. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2PolynomialSurjectivityOpen
open Matrix

variable {R K : Type*} [CommRing R] [CommRing K]
  {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]

/-- A surjective seed matrix remains surjective after any coefficient map
on which the chosen determinant is a unit. This holds over arbitrary
commutative target rings, including actual coordinate localizations. -/
theorem exists_surjectivity_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x) = x) (A : Matrix m n R)
    (hA : Function.Surjective (A.map f).mulVec) :
    ∃ (B : Matrix n m R) (s : R),
      s = (A * B).det ∧ f s = 1 ∧
      ∀ (S : Type*) [CommRing S] (g : R →+* S), IsUnit (g s) →
        Function.Surjective (A.map g).mulVec := by
  classical
  obtain ⟨B, hB⟩ := mulVec_surjective_iff_exists_right_inverse.mp hA
  let B₀ : Matrix n m R := B.map c
  have hmap : B₀.map f = B := by
    ext i j
    exact hfc (B i j)
  have hproduct : f.mapMatrix (A * B₀) = 1 := by
    change (A * B₀).map f = 1
    rw [Matrix.map_mul, hmap]
    exact hB
  refine ⟨B₀, (A * B₀).det, rfl, ?_, ?_⟩
  · rw [f.map_det, hproduct, Matrix.det_one]
  · intro S _ g hs
    have hdet : IsUnit (g.mapMatrix (A * B₀)).det := by
      rwa [← g.map_det]
    have hu : IsUnit (g.mapMatrix (A * B₀)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr hdet
    have hsurj := mulVec_surjective_iff_isUnit.mpr hu
    intro y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨B₀.map g *ᵥ x, ?_⟩
    rw [mulVec_mulVec]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_mul] using hx

end CycleQ2PolynomialSurjectivityOpen

#print axioms CycleQ2PolynomialSurjectivityOpen.exists_surjectivity_open
end
end


/- Component: continuation_3/cylinder_bridge/SeedCechAlgebra.lean -/
section
/-!
# The actual sparse seed curve and its two residue charts

The two monic equations below are the equations obtained from the published
sparse seed after eliminating `w = -x₂²`.  This is deliberately not the smooth
Segre incidence seed, whose cubic has the additional term `x₀³`.
-/

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace CycleQ2SeedCech

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

def quadratic (r x y : R) : R[X] := X ^ 2 - C (r * x * y)

theorem quadratic_monic (r x y : R) : (quadratic r x y).Monic :=
  monic_X_pow_sub_C _ (by decide)

abbrev Quadratic (r x y : R) := AdjoinRoot (quadratic r x y)

def a (r x y : R) : Quadratic r x y := AdjoinRoot.root _

theorem a_sq (r x y : R) :
    a r x y ^ 2 = algebraMap R (Quadratic r x y) (r * x * y) := by
  have hh := AdjoinRoot.mk_self (f := quadratic r x y)
  change AdjoinRoot.mk (quadratic r x y) (X ^ 2 - C (r * x * y)) = 0 at hh
  rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  exact sub_eq_zero.mp hh

def cubic (r i x y : R) : (Quadratic r x y)[X] :=
  X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
    C (a r x y * algebraMap R _ (x ^ 2) +
      algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))

theorem cubic_monic (r i x y : R) : (cubic r i x y).Monic := by
  unfold cubic
  rw [add_assoc]
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_mul_le _ _)
    calc
      _ ≤ 0 + 1 := add_le_add degree_C_le degree_X_le
      _ < (3 : WithBot ℕ) := by norm_num
  · exact lt_of_le_of_lt degree_C_le (by norm_num)

abbrev CurveAlgebra (r i x y : R) := AdjoinRoot (cubic r i x y)

def x0 (r i x y : R) : CurveAlgebra r i x y :=
  algebraMap (Quadratic r x y) _ (a r x y)

def x2 (r i x y : R) : CurveAlgebra r i x y := AdjoinRoot.root _

def base (r i x y : R) : R →+* CurveAlgebra r i x y :=
  (algebraMap (Quadratic r x y) _).comp (algebraMap R _)

theorem x0_sq (r i x y : R) : x0 r i x y ^ 2 = base r i x y (r * x * y) := by
  rw [x0, ← map_pow, a_sq]
  rfl

theorem x2_cubic (r i x y : R) :
    x2 r i x y ^ 3 + (x0 r i x y + base r i x y x) *
        base r i x y y * x2 r i x y +
      x0 r i x y * base r i x y (x ^ 2) +
        base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) = 0 := by
  have hh := AdjoinRoot.mk_self (f := cubic r i x y)
  change AdjoinRoot.mk (cubic r i x y)
    (X ^ 3 + C ((a r x y + algebraMap R _ x) * algebraMap R _ y) * X +
      C (a r x y * algebraMap R _ (x ^ 2) +
        algebraMap R _ ((1 - i) * y ^ 3 - i * x ^ 3))) = 0 at hh
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hh
  simpa only [x0, x2, base, RingHom.comp_apply, AdjoinRoot.algebraMap_eq,
    map_pow, add_assoc] using hh

def coefficient (r i x y : R) : CurveAlgebra r i x y →ₗ[R] R :=
  (Polynomial.lcoeff R 1).comp
    ((AdjoinRoot.modByMonicHom (quadratic_monic r x y)).comp
      (((Polynomial.lcoeff (Quadratic r x y) 2).comp
        (AdjoinRoot.modByMonicHom (cubic_monic r i x y))).restrictScalars R))

theorem modByMonicHom_map (f : R →+* S) (p : R[X])
    (hp : p.Monic) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom (hp.map f)
      (AdjoinRoot.map f p (p.map f) (dvd_refl _) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  induction z using AdjoinRoot.induction_on
  rename_i z
  have hm : AdjoinRoot.map f p (p.map f) (dvd_refl _) (AdjoinRoot.mk p z) =
      AdjoinRoot.mk (p.map f) (z.map f) := by
    rw [AdjoinRoot.map, AdjoinRoot.lift_mk, ← Polynomial.eval₂_map]
    exact AdjoinRoot.aeval_eq _
  rw [hm, AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk,
    Polynomial.map_modByMonic _ hp]

theorem modByMonicHom_map_eq (f : R →+* S) (p : R[X]) (q : S[X])
    (hp : p.Monic) (hq : q.Monic) (hpq : p.map f = q) (z : AdjoinRoot p) :
    AdjoinRoot.modByMonicHom hq
      (AdjoinRoot.map f p q (by rw [hpq]) z) =
      (AdjoinRoot.modByMonicHom hp z).map f := by
  subst q
  exact modByMonicHom_map f p hp z

theorem quadratic_map (f : R →+* S) (r x y : R) :
    (quadratic r x y).map f = quadratic (f r) (f x) (f y) := by
  simp [quadratic]

def quadraticMap (f : R →+* S) (r x y : R) :
    Quadratic r x y →+* Quadratic (f r) (f x) (f y) :=
  AdjoinRoot.map f _ _ (by rw [quadratic_map])

@[simp] theorem quadraticMap_a (f : R →+* S) (r x y : R) :
    quadraticMap f r x y (a r x y) = a (f r) (f x) (f y) := by
  simp [quadraticMap, a]

@[simp] theorem quadraticMap_base (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (algebraMap R (Quadratic r x y) z) =
      algebraMap S _ (f z) := by
  simp [quadraticMap, AdjoinRoot.algebraMap_eq]

@[simp] theorem quadraticMap_of (f : R →+* S) (r x y z : R) :
    quadraticMap f r x y (AdjoinRoot.of (quadratic r x y) z) =
      AdjoinRoot.of (quadratic (f r) (f x) (f y)) (f z) := by
  simp [quadraticMap]

theorem cubic_map (f : R →+* S) (r i x y : R) :
    (cubic r i x y).map (quadraticMap f r x y) =
      cubic (f r) (f i) (f x) (f y) := by
  simp [cubic]

def curveMap (f : R →+* S) (r i x y : R) :
    CurveAlgebra r i x y →+* CurveAlgebra (f r) (f i) (f x) (f y) :=
  AdjoinRoot.map (quadraticMap f r x y) _ _
    (by rw [cubic_map])

@[simp] theorem curveMap_x0 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x0 r i x y) = x0 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x0, AdjoinRoot.algebraMap_eq]

@[simp] theorem curveMap_x2 (f : R →+* S) (r i x y : R) :
    curveMap f r i x y (x2 r i x y) = x2 (f r) (f i) (f x) (f y) := by
  simp [curveMap, x2]

@[simp] theorem curveMap_base (f : R →+* S) (r i x y z : R) :
    curveMap f r i x y (base r i x y z) = base (f r) (f i) (f x) (f y) (f z) := by
  simp [curveMap, base, AdjoinRoot.algebraMap_eq]

@[simp] theorem coefficient_curveMap (f : R →+* S) (r i x y : R)
    (z : CurveAlgebra r i x y) :
    coefficient (f r) (f i) (f x) (f y) (curveMap f r i x y z) =
      f (coefficient r i x y z) := by
  change ((AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
    (((AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z)).coeff 2)).coeff 1 =
    f (((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
      (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).coeff 1)
  rw [show (AdjoinRoot.modByMonicHom (cubic_monic (f r) (f i) (f x) (f y)))
      (curveMap f r i x y z) =
      ((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).map
        (quadraticMap f r x y) from
    modByMonicHom_map_eq _ _ _ (cubic_monic r i x y)
      (cubic_monic (f r) (f i) (f x) (f y)) (cubic_map f r i x y) z]
  rw [coeff_map]
  rw [show (AdjoinRoot.modByMonicHom (quadratic_monic (f r) (f x) (f y)))
      (quadraticMap f r x y
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)) =
      ((AdjoinRoot.modByMonicHom (quadratic_monic r x y))
        (((AdjoinRoot.modByMonicHom (cubic_monic r i x y)) z).coeff 2)).map f from
    modByMonicHom_map_eq _ _ _ (quadratic_monic r x y)
      (quadratic_monic (f r) (f x) (f y)) (quadratic_map f r x y) _]
  rw [coeff_map]

def norm (r i x y : R) : R :=
  ((1 - i) * y ^ 3 - i * x ^ 3) ^ 2 - r * x ^ 5 * y

def inverseNumerator (r i x y : R) : CurveAlgebra r i x y :=
  -(x2 r i x y ^ 2 + (x0 r i x y + base r i x y x) * base r i x y y) *
    (base r i x y ((1 - i) * y ^ 3 - i * x ^ 3) -
      x0 r i x y * base r i x y (x ^ 2))

/-- An explicit inverse numerator for x₂; no irreducibility or smoothness is
needed.  The only scalar denominator is the displayed binary sextic. -/
theorem x2_mul_inverseNumerator (r i x y : R) :
    x2 r i x y * inverseNumerator r i x y = base r i x y (norm r i x y) := by
  have h0 := x0_sq r i x y
  have h2 := x2_cubic r i x y
  simp only [map_sub, map_mul, map_pow, map_one] at h0 h2 ⊢
  unfold inverseNumerator norm
  simp only [map_sub, map_mul, map_pow, map_one]
  linear_combination
    -((1 - base r i x y i) * base r i x y y ^ 3 -
      base r i x y i * base r i x y x ^ 3 -
      x0 r i x y * base r i x y x ^ 2) * h2 -
    base r i x y x ^ 4 * h0

def x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (CurveAlgebra r i x y)ˣ where
  val := x2 r i x y
  inv := inverseNumerator r i x y * base r i x y (↑(u⁻¹) : R)
  val_inv := by
    rw [← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp
  inv_val := by
    rw [mul_comm, ← mul_assoc, x2_mul_inverseNumerator, ← hu, ← map_mul]
    simp

@[simp] theorem coe_x2Unit (r i x y : R) (u : Rˣ) (hu : (u : R) = norm r i x y) :
    (x2Unit r i x y u hu : CurveAlgebra r i x y) = x2 r i x y := rfl

end CycleQ2SeedCech
end
end


/- Component: continuation_3/SeedCechCover.lean -/
section
/-!
# The two actual projective seed charts cover the curve

The proof includes the perturbation by θ x₀³.  Consequently the same two
opens cover both the sparse trace seed (θ = 0) and the smooth incidence
seed (θ = 1).  No smoothness conclusion is inferred from this cover.
-/

namespace CycleQ2SeedCechCover

set_option backward.isDefEq.respectTransparency false

open MvPolynomial CycleQ2SeedTrace

theorem zero_of_chart_equations {R : Type*} [CommRing R] [NoZeroDivisors R]
    (r i θ : R) (hi : i ≠ 0) (h1 : 1 - i ≠ 0) (x : Fin 4 → R)
    (hf : x 0 ^ 2 - r * x 1 * x 3 = 0)
    (hh : x 3 ^ 3 + x 2 ^ 3 + x 1 * x 2 * x 3 + x 0 * x 2 * x 3 +
      x 0 * x 1 ^ 2 - i * (x 1 ^ 3 + x 3 ^ 3) + θ * x 0 ^ 3 = 0)
    (hA : x 1 * x 3 = 0) (hB : x 2 = 0) : x = 0 := by
  have hx0sq : x 0 ^ 2 = 0 := by
    rw [sub_eq_zero] at hf
    rw [hf, mul_assoc, hA, mul_zero]
  have hx0 : x 0 = 0 := eq_zero_of_pow_eq_zero hx0sq
  have hc : (1 - i) * x 3 ^ 3 - i * x 1 ^ 3 = 0 := by
    have hh' : x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) = 0 := by
      simpa only [hx0, hB, zero_pow (by decide : 3 ≠ 0), mul_zero,
        zero_mul, add_zero, zero_add] using hh
    calc
      _ = x 3 ^ 3 - i * (x 1 ^ 3 + x 3 ^ 3) := by ring
      _ = 0 := hh'
  have hx13 : x 1 = 0 ∧ x 3 = 0 := by
    rcases mul_eq_zero.mp hA with hx1 | hx3
    · have hz : (1 - i) * x 3 ^ 3 = 0 := by simpa [hx1] using hc
      exact ⟨hx1, eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left h1)⟩
    · have hz : i * x 1 ^ 3 = 0 := by simpa [hx3] using hc
      exact ⟨eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hz).resolve_left hi), hx3⟩
  funext j
  fin_cases j
  · exact hx0
  · exact hx13.1
  · exact hB
  · exact hx13.2

/-- A nonzero homogeneous representative satisfying the actual curve
equations lies in D₊(x₁x₃) or D₊(x₂). -/
theorem projective_cover (r θ : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0)
    (hh : eval x (h + C θ * X 0 ^ 3) = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  by_contra hcover
  push Not at hcover
  apply hx
  apply zero_of_chart_equations r Complex.I θ Complex.I_ne_zero
    (by norm_num [Complex.ext_iff]) x
  · simpa [relation] using hf
  · simpa [h, b] using hh
  · exact hcover.1
  · exact hcover.2

theorem sparse_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x h = 0) (hx : x ≠ 0) :
    x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 0 x hf (by simpa using hh) hx

theorem smooth_seed_projective_cover (r : ℂ) (x : Fin 4 → ℂ)
    (hf : eval x (relation r 0) = 0) (hh : eval x (h + X 0 ^ 3) = 0)
    (hx : x ≠ 0) : x 1 * x 3 ≠ 0 ∨ x 2 ≠ 0 := by
  exact projective_cover r 1 x hf (by simpa using hh) hx

/-- The same cover holds at every relevant prime ideal, including the
nonclosed points of the projective curve. -/
theorem prime_chart_cover (r θ : ℂ) (P : Ideal Poly) [P.IsPrime]
    (hf : relation r 0 ∈ P) (hh : h + C θ * X 0 ^ 3 ∈ P)
    (hrelevant : ∃ j : Fin 4, X j ∉ P) :
    X 1 * X 3 ∉ P ∨ X 2 ∉ P := by
  by_contra hcover
  push Not at hcover
  let π : Poly →+* Poly ⧸ P := Ideal.Quotient.mk P
  have hi : π (C Complex.I) ≠ 0 := by
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne Complex.I_ne_zero
    simpa only [RingHom.comp_apply, map_zero] using hn
  have h1 : 1 - π (C Complex.I) ≠ 0 := by
    have hc : (1 : ℂ) - Complex.I ≠ 0 := by norm_num [Complex.ext_iff]
    have hn := (π.comp (C : ℂ →+* Poly)).injective.ne hc
    simpa only [RingHom.comp_apply, map_sub, map_one, map_zero] using hn
  have hf' : π (relation r 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hf
  have hh' : π (h + C θ * X 0 ^ 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hh
  have hA : π (X 1 * X 3) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.1
  have hB : π (X 2) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hcover.2
  have hz : (fun j : Fin 4 => π (X j)) = 0 := by
    apply zero_of_chart_equations (π (C r)) (π (C Complex.I)) (π (C θ)) hi h1
    · simpa [relation] using hf'
    · simpa [h, b] using hh'
    · simpa only [map_mul] using hA
    · exact hB
  obtain ⟨j, hj⟩ := hrelevant
  exact hj (Ideal.Quotient.eq_zero_iff_mem.mp (congrFun hz j))

section ProjectiveSpectrum

open CycleQ2SupportEquation
attribute [local instance] MvPolynomial.gradedAlgebra

theorem projective_coordinate_exists (p : AmbientProjectiveSpace 3) :
    ∃ j : Fin 4, X j ∉ p.asHomogeneousIdeal.toIdeal := by
  by_contra hn
  push Not at hn
  have hvars : idealOfVars (Fin 4) ℂ ≤ p.asHomogeneousIdeal.toIdeal := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact hn j
  apply p.not_irrelevant_le
  apply (HomogeneousIdeal.irrelevant_le (ambientGrading 3)).mpr
  intro d hd q hq
  apply hvars
  have hqhom : q.IsHomogeneous d := hq
  have hmem : q ∈ idealOfVars (Fin 4) ℂ ^ 1 := by
    apply (mem_pow_idealOfVars_iff 1 q).mpr
    intro e he
    have heq : e.degree = d := by
      rw [Finsupp.degree_eq_weight_one, ← Pi.one_def]
      exact hqhom (mem_support_iff.mp he)
    rw [heq]
    exact hd
  simpa only [pow_one] using hmem

/-- The actual closed curve in the standard projective spectrum. -/
def projectiveCurve (r θ : ℂ) : Set (AmbientProjectiveSpace 3) :=
  ProjectiveSpectrum.zeroLocus (ambientGrading 3)
    ({relation r 0, h + C θ * X 0 ^ 3} : Set Poly)

/-- The two genuine standard opens cover the closed projective seed curve. -/
theorem projectiveCurve_covered (r θ : ℂ) :
    projectiveCurve r θ ⊆
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 1 * X 3) :
        Set (AmbientProjectiveSpace 3)) ∪
      (ProjectiveSpectrum.basicOpen (ambientGrading 3) (X 2) :
        Set (AmbientProjectiveSpace 3)) := by
  intro p hp
  have hf : relation r 0 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  have hh : h + C θ * X 0 ^ 3 ∈ p.asHomogeneousIdeal.toIdeal := hp (by simp)
  exact prime_chart_cover r θ p.asHomogeneousIdeal.toIdeal hf hh
    (projective_coordinate_exists p)

end ProjectiveSpectrum

end CycleQ2SeedCechCover

#print axioms CycleQ2SeedCechCover.projective_cover
#print axioms CycleQ2SeedCechCover.prime_chart_cover
#print axioms CycleQ2SeedCechCover.projectiveCurve_covered
end


/- Component: continuation_3/SegreGenericLifting.lean -/
section
/-!
# Algebraic generic lifting with all redundant equations

A nonsingular square subsystem and a complementary relation minor at any
special-fiber seed give an actual finite separable generic solution of the
entire polynomial system. The prescribed open and complementary minor are
kept invertible by the proved open-square construction. The special-fiber
coefficient map may have positive-characteristic image.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace CycleQ2SegreGenericLifting

open MvPolynomial Matrix HoldoutConstruction

variable {R T K ι κ : Type*} [CommRing R] [CommRing T] [Nontrivial T]
  [Algebra R T] [Field K] [Algebra R K]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The existence conclusion concerns the complete polynomial incidence
system. Neither a formal solution nor an algebraic generic solution is a
premise; only the literal equations, relations, and the two seed minors
remain to be supplied by a concrete incidence calculation. -/
theorem lift_all_equations_on_open
    (equations : ι → MvPolynomial ι R)
    (residual : κ → MvPolynomial ι R)
    (A : Matrix κ κ (MvPolynomial ι R))
    (B : Matrix κ ι (MvPolynomial ι R))
    (c : MvPolynomial ι R)
    (hrelations : A *ᵥ residual + B *ᵥ equations = 0)
    (seed : ι → T)
    (hseed : ∀ i, aeval seed (equations i) = 0)
    (hjac : IsUnit (Matrix.det (fun i j => aeval seed (pderiv i (equations j)))))
    (hcomplement : IsUnit (aeval seed A.det))
    (hc : IsUnit (aeval seed c))
    (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))),
      I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K
        (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I) ∧
      ∃ x : ι → ((SquareGenericAlgebra K
          (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I),
        (∀ i, aeval x (equations i) = 0) ∧
        (∀ j, aeval x (residual j) = 0) ∧
        IsUnit (aeval x c) ∧ IsUnit (aeval x A.det) := by
  have hprod : IsUnit (aeval seed (c * A.det)) := by
    rw [map_mul]
    exact hc.mul hcomplement
  obtain ⟨I, hI, hfinite, hsep, x, heq, hopen⟩ :=
    CycleQ2OpenSquareLifting.square_system_generic_lift_on_open
      (K := K) equations (c * A.det) seed hseed hjac hprod hinj
  let E := (SquareGenericAlgebra K
    (CycleQ2OpenSquareLifting.openSystem equations (c * A.det))) ⧸ I
  letI : I.IsMaximal := hI
  letI : Field E := Ideal.Quotient.field I
  have hprod' : IsUnit (aeval x c * aeval x A.det) := by
    simpa only [map_mul] using hopen
  have hA := isUnit_of_mul_isUnit_right hprod'
  let φ : MvPolynomial ι R →+* E := (aeval x).toRingHom
  have heq' : φ ∘ equations = 0 := by
    funext i
    exact heq i
  have hres : φ ∘ residual = 0 :=
    CycleQ2SegreRelations.evaluated_residual_eq_zero
      φ A B residual equations hrelations heq' hA
  exact ⟨I, hI, hfinite, hsep, x, heq, fun j => congrFun hres j,
    isUnit_of_mul_isUnit_left hprod', hA⟩

end CycleQ2SegreGenericLifting

#print axioms CycleQ2SegreGenericLifting.lift_all_equations_on_open
end
end


/- Component: continuation_3/cylinder_bridge/SegreTransitionDerivative.lean -/
section
/-! # First-order logarithmic variation of the actual Segre transition unit

The overlap unit is the existing matrix-entry transition.  The first-order
functional is the universal Kähler differential evaluated by the genuine
special-fiber derivation on the dual numbers.  Its entry formula is proved
without replacing the transition by an assumed cocycle.  Applying it to a
moving surface requires local trivializations of that deformation; this file
does not supply an Abel--Jacobi comparison.
-/

noncomputable section
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SegreTransitionDerivative

open CycleQ2SegreCech

variable {R : Type*} [CommRing R]

abbrev Jet (R : Type*) := TrivSqZeroExt R R

attribute [local instance] TrivSqZeroExt.algebraBase

/-- The parameter derivative takes values in the special fiber.  In
particular it is not the invalid derivation ε↦1 with values in R[ε]/ε². -/
def tangentDerivation : Derivation R (Jet R) R where
  toLinearMap := TrivSqZeroExt.sndHom R R
  map_one_eq_zero' := rfl
  leibniz' x y := by
    simp only [TrivSqZeroExt.sndHom_apply, TrivSqZeroExt.snd_mul,
      smul_eq_mul, op_smul_eq_smul]
    rfl

def unitLogTangent (u : (Jet R)ˣ) : R :=
  (tangentDerivation (R := R)).liftKaehlerDifferential (unitDlog R u)

theorem unitLogTangent_eq (u : (Jet R)ˣ) :
    unitLogTangent u = (↑(u⁻¹) : Jet R).fst*(u : Jet R).snd := by
  rw [unitLogTangent, unitDlog_apply]
  rfl

theorem unitLogTangent_mul (u v : (Jet R)ˣ) :
    unitLogTangent (u*v)=unitLogTangent u+unitLogTangent v := by
  simp only [unitLogTangent, unitDlog_mul, map_add]

theorem unitLogTangent_inv (u : (Jet R)ˣ) : unitLogTangent u⁻¹= -unitLogTangent u := by
  simp only [unitLogTangent, unitDlog_inv, map_neg]

theorem unitLogTangent_pow (u : (Jet R)ˣ) (d : ℕ) :
    unitLogTangent (u^d)=d • unitLogTangent u := by
  simp only [unitLogTangent, unitDlog_pow, map_nsmul]

theorem inverse_snd (u : (Jet R)ˣ) :
    (↑(u⁻¹) : Jet R).snd =
      -((↑(u⁻¹) : Jet R).fst^2*(u : Jet R).snd) := by
  have h₀ := congrArg TrivSqZeroExt.fst u.inv_mul
  have h₁ := congrArg TrivSqZeroExt.snd u.mul_inv
  simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_one] at h₀
  simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_one,
    smul_eq_mul, op_smul_eq_smul] at h₁
  linear_combination (↑(u⁻¹) : Jet R).fst*h₁-
    (↑(u⁻¹) : Jet R).snd*h₀

/-- Literal entry formula for the first-order logarithmic transition.
`p` and `q` are the same pivot charts used by the published image-line
construction, and both pivot units belong to the actual square-zero ring. -/
theorem transition_logTangent_entries
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2) :
    unitLogTangent (transition M hM p q up uq hp hq)=
      (↑((transition M hM p q up uq hp hq)⁻¹) : Jet R).fst*
        ((M q.1 p.2).snd*(↑(up⁻¹) : Jet R).fst-
          (M q.1 p.2).fst*(↑(up⁻¹) : Jet R).fst^2*(M p.1 p.2).snd) := by
  rw [unitLogTangent_eq]
  change _*(M q.1 p.2*(↑(up⁻¹) : Jet R)).snd = _
  rw [TrivSqZeroExt.snd_mul, inverse_snd up, hp]
  simp only [smul_eq_mul, op_smul_eq_smul]
  ring

theorem transition_logTangent_cocycle
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q s : Chart) (up uq us : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2)
    (hs : (us : Jet R)=M s.1 s.2) :
    unitLogTangent (transition M hM p q up uq hp hq)+
      unitLogTangent (transition M hM q s uq us hq hs)=
        unitLogTangent (transition M hM p s up us hp hs) := by
  rw [← unitLogTangent_mul, transition_cocycle]

/-- The homogeneous O(d) correction survives at first order as well. -/
theorem twistedTransition_logTangent
    (M : Matrix (Fin 3) (Fin 3) (Jet R)) (hM : CycleQ2SegreLocal.cofactors M=0)
    (p q : Chart) (up uq : (Jet R)ˣ)
    (hp : (up : Jet R)=M p.1 p.2) (hq : (uq : Jet R)=M q.1 q.2)
    (xp xq : (Jet R)ˣ) (d : ℕ) :
    unitLogTangent (twistedTransition M hM p q up uq hp hq xp xq d)=
      d • (unitLogTangent xp-unitLogTangent xq)+
        unitLogTangent (transition M hM p q up uq hp hq) := by
  simp only [twistedTransition, unitLogTangent_mul, unitLogTangent_pow,
    unitLogTangent_inv, sub_eq_add_neg]

end CycleQ2SegreTransitionDerivative

#print axioms CycleQ2SegreTransitionDerivative.tangentDerivation
#print axioms CycleQ2SegreTransitionDerivative.transition_logTangent_entries
#print axioms CycleQ2SegreTransitionDerivative.twistedTransition_logTangent
end
end


