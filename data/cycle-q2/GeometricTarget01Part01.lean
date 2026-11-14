import Proposal.GeometricSurfaceBindings
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
import Proposal.GeometricFormalInputs04
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


