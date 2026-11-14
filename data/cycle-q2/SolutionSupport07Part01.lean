import Proposal.GeometricSeedCubicGradient
import Proposal.GeometricSeedCurveGradientArithmetic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.NumberTheory.Zsqrtd.GaussianInt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dual.Defs
import HodgeTarget
import Proposal.GeometricTarget11Part04
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs04
import Proposal.Normalization09Part02
import Proposal.SolutionSupport06Part03
import Proposal.GeometricSeedConormalBases

/-! Components extracted from SolutionSupport07.lean, in their original order.
See solution.md for the mathematical and verification status. -/

set_option Elab.async false

/- Component: continuation_3/cylinder_bridge/IncidenceCertifiedGenericPoint.lean -/
section
/-! The proved exact ranks discharge the last finite-linear input of the
actual generic incidence and trace-preserving family.  The basepoint open
is included using its proved seed value.  No cylinder or primitive claim
is made by these algebraic existence statements. -/

noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace CycleQ2IncidenceCertifiedGenericPoint
open Matrix MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialRelations
  CycleQ2IncidenceCoefficientRelations CycleQ2SegreFullJacobianBounds
  CycleQ2IncidenceCompatibleGenericPoint CycleQ2IncidenceFiniteGenericSolution
  CycleQ2IncidenceTraceFamily CycleQ2IncidenceTraceFieldDerivation
  CycleQ2IncidenceTraceGenericPoint
open CycleQ2IncidenceBasepointOpen (basepointPolynomial)

theorem literal_exactness :
    LinearMap.range (Matrix.mulVecLin fixedJacobian)=
      LinearMap.ker (Matrix.mulVecLin literalRelations) := by
  rw [fixedJacobian_eq_ordered,literalRelations_eq]
  exact CycleQ2SegreExactRanks.fixed_range_eq_relation_kernel

theorem finite_generic_incidence :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericFamilyAlgebra P V T₀ B)),
      I.IsMaximal ∧
      Module.Finite GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      Algebra.IsSeparable GenericField ((GenericFamilyAlgebra P V T₀ B) ⧸ I) ∧
      ∃ (h : FullInvariantIndex 3 → ((GenericFamilyAlgebra P V T₀ B) ⧸ I))
        (δ : Fin 3 → Fin 3 → StandardIndex 14 → ((GenericFamilyAlgebra P V T₀ B) ⧸ I)),
        IsGenericIncidence h δ :=
  finite_generic_incidence_of_exactness literal_exactness

theorem finite_trace_point :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B basepointPolynomial)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I),
        IsTracePoint P B basepointPolynomial z := by
  apply finite_trace_point_of_exactness literal_exactness basepointPolynomial
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

theorem finite_pointed_trace_point :
    ∃ (P : Matrix SquareIndex ColumnIndex ℂ)
      (V : Matrix ColumnIndex ComplementIndex ℂ)
      (T₀ : Matrix ComplementIndex RelationIndex ℂ)
      (B : Matrix FixedSexticParameters SquareIndex ℂ)
      (I : Ideal (GenericTraceAlgebra P V T₀ B basepointPolynomial)),
      I.IsMaximal ∧
      Module.Finite TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      Algebra.IsSeparable TraceField ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I) ∧
      ∃ z : SquareIndex → ((GenericTraceAlgebra P V T₀ B basepointPolynomial) ⧸ I),
        IsPointedTracePoint P B basepointPolynomial z := by
  apply finite_pointed_trace_point_of_exactness literal_exactness basepointPolynomial
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

end CycleQ2IncidenceCertifiedGenericPoint

#print axioms CycleQ2IncidenceCertifiedGenericPoint.literal_exactness
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_generic_incidence
#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_trace_point

#print axioms CycleQ2IncidenceCertifiedGenericPoint.finite_pointed_trace_point
end
end


/- Component: continuation_3/cylinder_bridge/IncidenceTraceGeometry.lean -/
section
/-! The finite trace family, restricted to the proved basepoint open,
has the actual cofactor incidence, a rank-one localized global image, and
regular principal equations for the literal generic-column section ideal.
No line bundle or regular section is an input hypothesis. -/

noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceTraceGeometry
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidenceCoefficientRelations
  CycleQ2IncidencePolynomialRelations CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds
  CycleQ2PolynomialAffineSlice CycleQ2PolynomialImplicitTrace
  CycleQ2IncidenceTraceDirection CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceDerivative CycleQ2IncidenceTraceGenericPoint
  CycleQ2IncidenceImageLine CycleQ2SegreGenericSection
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)
open CycleQ2IncidenceBasepointOpen (basepointPolynomial curveCoordinate curveMatrix)

theorem basepoint_seed : eval (seedPoint (57:ℂ) Complex.I) basepointPolynomial=1 := by
  change CycleQ2IncidenceBasepointOpen.seedEvaluation basepointPolynomial=1
  exact CycleQ2IncidenceBasepointOpen.seed_basepointPolynomial

variable {S : Type} [CommRing S] [Algebra TraceRing S]
  [Algebra ℂ S] [IsScalarTower ℂ TraceRing S]

abbrev tracePointValue (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) : ParameterIndex → S :=
  pointValue (algebraMap TraceRing S) centre (directions B) z

theorem tracePoint_original_equations
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) (q : ColumnIndex) :
    aeval (tracePointValue B z) ((presentation ℂ 57).equation q)=0 := by
  rw [←eval_coefficient_map]
  exact hz.1 q

theorem tracePoint_leading_unit
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) :
    IsUnit (aeval (tracePointValue B z) (leadingProduct ℂ)) := by
  exact (protectedOpen_components P
    (CycleQ2IncidenceSexticFamily.extendDirections B) (tracePointValue B z) hz.2.1).1

theorem tracePoint_extra_unit
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ) (c : ParameterPolynomial ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B c z) :
    IsUnit (aeval (tracePointValue B z) c) := by
  have h := hz.2.2.1
  rwa [eval_coefficient_map] at h

theorem tracePoint_localized_image_line [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B basepointPolynomial z)
    (p : Ideal (PointSurface (tracePointValue B z))) [p.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap (tracePointValue B z)) j∉p) :
    Nonempty (PointPrimeRing (tracePointValue B z) p ≃ₗ[PointPrimeRing (tracePointValue B z) p]
      (LinearMap.range (curveMatrix (pointMap (tracePointValue B z))).mulVecLin).localized'
        (PointPrimeRing (tracePointValue B z) p) p.primeCompl
        (CycleQ2MatrixImageLocalization.vectorMap
          (R := PointSurface (tracePointValue B z))
          (S := PointPrimeRing (tracePointValue B z) p))) :=
  localized_global_image_line (tracePointValue B z)
    (tracePoint_original_equations P B _ z hz) (tracePoint_leading_unit P B _ z hz)
    (tracePoint_extra_unit P B _ z hz) p hx

/-- The chosen generic-section ideal is locally principal with a proved
regular generator at every relevant prime, over the polynomial ring in
the three independent section coefficients. -/
theorem tracePoint_regular_section [Nontrivial S]
    (P : Matrix SquareIndex ColumnIndex ℂ)
    (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → S) (hz : IsTracePoint P B basepointPolynomial z)
    (p : Ideal (PointSurface (tracePointValue B z))) [p.IsPrime]
    (hx : ∃ j, curveCoordinate (pointMap (tracePointValue B z)) j∉p) :
    ∃ q : CycleQ2SegreCech.Chart,
      sectionIdeal (primeMatrix (tracePointValue B z) p)=
        Ideal.span {localEquation (primeMatrix (tracePointValue B z) p) q} ∧
      IsRegular (localEquation (primeMatrix (tracePointValue B z) p) q) := by
  let y := tracePointValue B z
  have hb := tracePoint_extra_unit P B _ z hz
  obtain ⟨i,j,hij⟩ := CycleQ2IncidenceBasepointOpen.specialized_prime_pivot_cover
    (pointMap y) hb p hx
  have hu : IsUnit (primeMatrix y p i j) :=
    IsLocalization.map_units (M := p.primeCompl) (PointPrimeRing y p)
      ⟨curveMatrix (pointMap y) i j,hij⟩
  have hcof := @CycleQ2SegreCech.cofactors_map_zero
    (PointSurface y) (inferInstance : CommRing (PointSurface y))
    (PointPrimeRing y p) (inferInstance : CommRing (PointPrimeRing y p))
    (algebraMap (PointSurface y) (PointPrimeRing y p)) (curveMatrix (pointMap y))
    (curveMatrix_cofactors y (tracePoint_original_equations P B _ z hz)
      (tracePoint_leading_unit P B _ z hz))
  obtain ⟨u,hu'⟩ := hu
  exact ⟨(i,j),sectionIdeal_principal (primeMatrix y p) hcof (i,j) u hu',
    localEquation_regular (primeMatrix y p) (i,j) ⟨u,hu'⟩⟩

end CycleQ2IncidenceTraceGeometry

#print axioms CycleQ2IncidenceTraceGeometry.tracePoint_localized_image_line
#print axioms CycleQ2IncidenceTraceGeometry.tracePoint_regular_section
end
end


/- Component: continuation_20261111/ConormalJacobian.lean -/
section
/-! Genuine ideal-conormal bases from unit Jacobian data. -/
noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace CycleQ2ConormalJacobian

section General
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra R S] [Algebra k S] [IsScalarTower k R S]
variable (I : Ideal R) (hI : ∀ x ∈ I, algebraMap R S x = 0)

/-- A derivation becomes R-linear on an ideal annihilated in the target. -/
def idealDerivative (d : Derivation k R S) : I →ₗ[R] S where
  toFun x := d x
  map_add' x y := d.map_add x y
  map_smul' c x := by
    change d (c*x.val) = c • d x.val
    rw [d.leibniz]
    have hx : x.val • d c = 0 := by
      rw [Algebra.smul_def, hI x.val x.property, zero_mul]
    rw [hx, add_zero]

theorem idealDerivative_product (d : Derivation k R S) (x y : I) :
    idealDerivative I hI d (x*y)=0 := by
  change d (x.val*y.val)=0
  rw [d.leibniz, Algebra.smul_def, Algebra.smul_def,
    hI x.val x.property, hI y.val y.property, zero_mul, zero_mul, add_zero]

/-- The actual derivative functional on the base-changed conormal module. -/
def conormalDerivative (d : Derivation k R S) : S ⊗[R] I.Cotangent →ₗ[S] S :=
  (Ideal.Cotangent.lift (idealDerivative I hI d) (idealDerivative_product I hI d)).liftBaseChange S

@[simp] theorem conormalDerivative_generator (d : Derivation k R S) (x : I) :
    conormalDerivative I hI d (1 ⊗ₜ[R] I.toCotangent x)=d x := by
  simp [conormalDerivative, idealDerivative]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (f : ι → R) (hf : Ideal.span (Set.range f)=I)

include hI in
theorem generators_independent
    (d : ι → Derivation k R S)
    (hd : ∀ i j, d i (f j)=if i=j then 1 else 0) :
    LinearIndependent S (generator (S := S) I f hf) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := congrArg (conormalDerivative I hI (d i)) hc
  simp only [map_sum,map_smul,map_zero,generator,conormalDerivative_generator,hd] at hh
  simpa using hh

def conormalBasis
    (d : ι → Derivation k R S)
    (hd : ∀ i j, d i (f j)=if i=j then 1 else 0) :
    Module.Basis ι S (S ⊗[R] I.Cotangent) :=
  Module.Basis.mk (generators_independent I hI f hf d hd)
    (by rw [generators_span I f hf])

@[simp] theorem conormalBasis_apply
    (d : ι → Derivation k R S)
    (hd : ∀ i j, d i (f j)=if i=j then 1 else 0) (i : ι) :
    conormalBasis I hI f hf d hd i=generator (S := S) I f hf i :=
  Module.Basis.mk_apply _ _ _

def derivationMatrix (d : ι → Derivation k R S) : Matrix ι ι S :=
  fun i j => d i (f j)

def inverseJacobianDerivations (d : ι → Derivation k R S) : ι → Derivation k R S :=
  fun i => ∑ j, (derivationMatrix f d)⁻¹ i j • d j

theorem inverseJacobianDerivations_equations (d : ι → Derivation k R S)
    (hd : IsUnit (derivationMatrix f d).det) (i j : ι) :
    inverseJacobianDerivations f d i (f j)=if i=j then 1 else 0 := by
  have hh := congrFun (congrFun (Matrix.nonsing_inv_mul _ hd) i) j
  have hs : (∑ a, (derivationMatrix f d)⁻¹ i a • d a) (f j)=
      ∑ a, (derivationMatrix f d)⁻¹ i a * d a (f j) := by
    have he := congrFun (map_sum (Derivation.coeFnAddMonoidHom :
      Derivation k R S →+ (R → S))
      (fun a => (derivationMatrix f d)⁻¹ i a • d a) Finset.univ) (f j)
    simpa only [Derivation.coeFnAddMonoidHom_apply,Finset.sum_apply,
      Derivation.smul_apply,smul_eq_mul] using he
  rw [inverseJacobianDerivations,hs]
  simpa [derivationMatrix,Matrix.mul_apply,Matrix.one_apply] using hh

/-- A basis of the actual base-changed ideal cotangent module follows from
the unit determinant of the actual equation derivative matrix. -/
def conormalBasisOfJacobian (d : ι → Derivation k R S)
    (hd : IsUnit (derivationMatrix f d).det) :
    Module.Basis ι S (S ⊗[R] I.Cotangent) :=
  conormalBasis I hI f hf (inverseJacobianDerivations f d)
    (inverseJacobianDerivations_equations f d hd)

@[simp] theorem conormalBasisOfJacobian_apply (d : ι → Derivation k R S)
    (hd : IsUnit (derivationMatrix f d).det) (i : ι) :
    conormalBasisOfJacobian I hI f hf d hd i=generator (S := S) I f hf i :=
  conormalBasis_apply _ _ _ _ _ _ _

end General

end CycleQ2ConormalJacobian
end
end


/- Component: continuation_20261111/LocalizationDerivation.lean -/
section
/-!
# Derivations on actual localization rings

A derivation extends to every localization, without a domain or fraction
field assumption.  The construction uses the localization universal property
on the actual dual-number graph, and proves that its first coordinate is the
identity.  This supplies the local coordinate derivatives needed on Jacobian
minor opens of the moving surface.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2LocalizationDerivation

variable {K A S : Type*} [CommRing K] [CommRing A] [CommRing S]
  [Algebra K A] [Algebra A S] [Algebra K S] [IsScalarTower K A S]

abbrev Jet (S : Type*) := TrivSqZeroExt S S

/-- The first-order graph, after the actual coefficient map into S. -/
def graph (D : Derivation K A A) : A →ₐ[K] Jet S where
  toFun a := ⟨algebraMap A S a, algebraMap A S (D a)⟩
  map_zero' := by ext <;> simp
  map_one' := by ext <;> simp [Derivation.map_one_eq_zero]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A S (a + b) = algebraMap A S a + algebraMap A S b
      exact map_add _ _ _
    · change algebraMap A S (D (a + b)) = algebraMap A S (D a) + algebraMap A S (D b)
      rw [map_add, map_add]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · change algebraMap A S (a * b) = algebraMap A S a * algebraMap A S b
      exact map_mul _ _ _
    · rw [TrivSqZeroExt.snd_mul]
      dsimp only [TrivSqZeroExt.fst, TrivSqZeroExt.snd]
      simp only [Derivation.leibniz, smul_eq_mul, op_smul_eq_smul, map_add, map_mul]
  commutes' k := by
    ext
    · exact (IsScalarTower.algebraMap_apply K A S k).symm
    · change algebraMap A S (D (algebraMap K A k)) = 0
      simp

@[simp] theorem graph_fst (D : Derivation K A A) (a : A) :
    (graph (S := S) D a).fst = algebraMap A S a := rfl

@[simp] theorem graph_snd (D : Derivation K A A) (a : A) :
    (graph (S := S) D a).snd = algebraMap A S (D a) := rfl

variable (M : Submonoid A) [IsLocalization M S]

theorem graph_units (D : Derivation K A A) (a : M) :
    IsUnit (graph (S := S) D a) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  exact IsLocalization.map_units S a

/-- Universal localization of the first-order graph. -/
def localizedGraph (D : Derivation K A A) : S →ₐ[K] Jet S :=
  IsLocalization.liftAlgHom (graph_units (S := S) M D)

@[simp] theorem localizedGraph_map (D : Derivation K A A) (a : A) :
    localizedGraph (S := S) M D (algebraMap A S a) = graph D a :=
  IsLocalization.lift_eq _ a

theorem localizedGraph_fst (D : Derivation K A A) (s : S) :
    (localizedGraph (S := S) M D s).fst = s := by
  have h : (TrivSqZeroExt.fstHom K S S).toRingHom.comp
      (localizedGraph (S := S) M D).toRingHom = RingHom.id S := by
    apply IsLocalization.ringHom_ext M
    ext a
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, RingHom.id_apply]
    exact congrArg TrivSqZeroExt.fst (localizedGraph_map M D a)
  exact RingHom.congr_fun h s

/-- The second coordinate is the required derivation on the localization. -/
def extend (D : Derivation K A A) : Derivation K S S where
  toLinearMap := (TrivSqZeroExt.sndHom S S).restrictScalars K |>.comp
    (localizedGraph (S := S) M D).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' x y := by
    change (localizedGraph M D (x * y)).snd =
      x * (localizedGraph M D y).snd + y * (localizedGraph M D x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    simp only [localizedGraph_fst, smul_eq_mul, op_smul_eq_smul]

@[simp] theorem extend_map (D : Derivation K A A) (a : A) :
    extend (S := S) M D (algebraMap A S a) = algebraMap A S (D a) := by
  change (localizedGraph M D (algebraMap A S a)).snd = _
  rw [localizedGraph_map, graph_snd]

/-- Uniqueness is proved using the first-order graph and localization
epimorphy, rather than assuming an inverse rule. -/
theorem extend_unique (D : Derivation K A A) (E : Derivation K S S)
    (hE : ∀ a : A, E (algebraMap A S a) = algebraMap A S (D a)) :
    E = extend (S := S) M D := by
  have h : (graph (A := S) (S := S) E).toRingHom =
      (localizedGraph (S := S) M D).toRingHom := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro a
    change graph (A := S) (S := S) E (algebraMap A S a) =
      localizedGraph M D (algebraMap A S a)
    rw [localizedGraph_map]
    apply TrivSqZeroExt.ext
    · rfl
    · exact hE a
  ext s
  exact congrArg TrivSqZeroExt.snd (RingHom.congr_fun h s)

end CycleQ2LocalizationDerivation

#print axioms CycleQ2LocalizationDerivation.extend_map
#print axioms CycleQ2LocalizationDerivation.extend_unique
end
end


/- Source component moved verbatim to Proposal.GeometricSeedCubicGradient. -/
