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
import Proposal.GeometricTarget
import Proposal.GeometricSeed
import Proposal.GeometricFormalInputs
import Proposal.Normalization
import Proposal.SolutionSupport06

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

def generator (i : ι) : S ⊗[R] I.Cotangent :=
  1 ⊗ₜ[R] I.toCotangent ⟨f i, hf ▸ Ideal.subset_span ⟨i,rfl⟩⟩

theorem generators_span :
    Submodule.span S (Set.range (generator (S := S) I f hf))=⊤ := by
  apply top_unique
  intro z hzTop
  clear hzTop
  induction z using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | add z w hz hw => exact Submodule.add_mem _ hz hw
  | tmul s m =>
    obtain ⟨x,rfl⟩ := I.toCotangent_surjective m
    suffices hx : (1:S) ⊗ₜ[R] I.toCotangent x ∈
        Submodule.span S (Set.range (generator (S := S) I f hf)) by
      simpa only [TensorProduct.smul_tmul',smul_eq_mul,mul_one] using
        Submodule.smul_mem _ s hx
    have hgen : ∀ y (hy : y∈Ideal.span (Set.range f)),
        (1:S) ⊗ₜ[R] I.toCotangent ⟨y,hf ▸ hy⟩ ∈
          Submodule.span S (Set.range (generator (S := S) I f hf)) := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨i,rfl⟩ := hy
        exact Submodule.subset_span ⟨i,rfl⟩
      | zero =>
        change (1:S) ⊗ₜ[R] I.toCotangent (0:I) ∈ _
        rw [map_zero,TensorProduct.tmul_zero]
        exact Submodule.zero_mem _
      | add a b ha hb iha ihb =>
        change (1:S) ⊗ₜ[R] I.toCotangent
          ((⟨a,hf ▸ ha⟩ : I)+⟨b,hf ▸ hb⟩) ∈ _
        rw [map_add,TensorProduct.tmul_add]
        exact Submodule.add_mem _ iha ihb
      | smul c a ha iha =>
        change (1:S) ⊗ₜ[R] I.toCotangent (c • (⟨a,hf ▸ ha⟩ : I)) ∈ _
        rw [map_smul,TensorProduct.tmul_smul]
        simpa only [algebraMap_smul] using
          Submodule.smul_mem _ (algebraMap R S c) iha
    exact hgen x.val (hf.symm ▸ x.property)

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


/- Component: continuation_20261111/SeedCubicGradient.lean -/
section
/-! Exact characteristic-zero gradient certificates for the literal cubic
smoothH used by the r=57 incidence seed.  These certify the algebraic
projective Jacobian condition; a geometric smoothness criterion is separate. -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
namespace CycleQ2SeedCubicGradient
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def derivativeFormula {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![x2*x3+x1^2+3*x0^2, x2*x3+2*x0*x1-3*i*x1^2,
    3*x2^2+x1*x3+x0*x3, 3*(1-i)*x3^2+x1*x2+x0*x2]

def numerator0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-123842238*i*x1^3 - 269482980*i*x1*x2*x3 + 46094022*i*x3^3 + 1424185737*x0^3 - 474728579*x0*x1^2 - 474728579*x0*x2*x3 - 24958752*x1*x2*x3 - 44711550*x3^3,
    185763357*i*x0*x1^2 + 404224470*i*x0*x2*x3 + 4216836*i*x1*x2*x3 - 74892060*i*x2^3 + 69637752*i*x3^3 + 37438128*x0*x2*x3 - 41280746*x1^3 - 158402621*x1*x2*x3 - 31954605*x2^3 + 15033528*x3^3,
    -138282066*i*x0*x3^2 - 81882645*i*x1^2*x2 - 993438*i*x1*x3^2 + 24964020*i*x2^2*x3 + 134134650*x0*x3^2 + 53588990*x1^2*x2 - 164201706*x1*x3^2 + 10651535*x2^2*x3,
    149784120*i*x1*x2^2 - 14342292*i*x2*x3^2 + 63909210*x1*x2^2 + 24234966*x2*x3^2]

theorem identity0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    4272557211*x0^5 =
      ∑ k, numerator0 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator0 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      4272557211*x0^5 = (i^2+1)*(-557290071*x0*x1^4 - 1212673410*x0*x1^2*x2*x3 - 12650508*x1^3*x2*x3 + 224676180*x1^2*x2^3 - 208913256*x1^2*x3^3 - 449352360*x1*x2^2*x3^2 + 43026876*x2*x3^4) := by
    simp [Fin.sum_univ_succ, numerator0, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![386917466*i*x1*x2*x3 - 65354276*i*x3^3 - 495368952*x1^3 - 126722024*x1*x2*x3 + 17973020*x3^3,
    -580376199*i*x0*x2*x3 + 1114580142*i*x1^3 + 231964681*i*x1*x2*x3 + 100165083*i*x2^3 - 56808496*i*x3^3 + 743053428*x0*x1^2 + 190083036*x0*x2*x3 + 535939118*x1*x2*x3 + 39543024*x2^3 - 49266704*x3^3,
    196062828*i*x0*x3^2 + 106319746*i*x1^2*x2 - 82445836*i*x1*x3^2 - 33388361*i*x2^2*x3 - 53919060*x0*x3^2 - 73803067*x1^2*x2 + 152452468*x1*x3^2 - 13181008*x2^2*x3,
    -200330166*i*x1*x2^2 + 25576076*i*x2*x3^2 - 79086048*x1*x2^2 - 15144848*x2*x3^2]

theorem identity1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    2848371474*x1^5 =
      ∑ k, numerator1 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator1 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      2848371474*x1^5 = (i^2+1)*(1741128597*x0*x1^2*x2*x3 - 3343740426*x1^5 - 695894043*x1^3*x2*x3 - 300495249*x1^2*x2^3 + 170425488*x1^2*x3^3 + 600990498*x1*x2^2*x3^2 - 76728228*x2*x3^4) := by
    simp [Fin.sum_univ_succ, numerator1, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![1043866*i*x1^2*x3 - 148112*i*x1*x2^2 + 808014*x1^2*x3 + 1954376*x1*x2^2,
    -1565799*i*x0*x1*x3 + 222168*i*x0*x2^2 - 1669279*i*x1^2*x3 - 4717897*i*x1*x2^2 - 65130*i*x2*x3^2 - 1212021*x0*x1*x3 - 2931564*x0*x2^2 + 248787*x1^2*x3 - 133175*x1*x2^2 + 1398138*x2*x3^2,
    -297505*i*x1^3 + 1696059*i*x1*x2*x3 + 4199823*x1^3 - 1584255*x1*x2*x3 + 3175442*x2^3,
    641102*i*x1^2*x2 - 222168*i*x2^2*x3 - 400154*x1^2*x2 - 243878*x2^2*x3]

theorem identity2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    9526326*x2^5 =
      ∑ k, numerator2 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator2 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      9526326*x2^5 = (i^2+1)*(4697397*x0*x1^3*x3 - 666504*x0*x1^2*x2^2 + 5007837*x1^4*x3 + 14153691*x1^3*x2^2 - 1727916*x1^2*x2*x3^2 + 666504*x2^2*x3^3) := by
    simp [Fin.sum_univ_succ, numerator2, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![-114864*i*x1*x3^2 + 182601*i*x2^2*x3 - 121972*x1*x3^2 + 12935*x2^2*x3,
    172296*i*x0*x3^2 + 214200*i*x1*x3^2 + 516468*i*x2^2*x3 + 182958*x0*x3^2 + 1870*x1*x3^2 + 19630*x2^2*x3,
    -547803*i*x0*x2^2 + 120474*i*x1^2*x3 - 547803*i*x1*x2^2 - 1760017*i*x2*x3^2 - 38805*x0*x2^2 - 520628*x1^2*x3 - 38805*x1*x2^2 - 1770679*x2*x3^2,
    62670*i*x1*x2*x3 + 1643409*i*x2^3 + 1587721*i*x3^3 + 38350*x1*x2*x3 + 116415*x2^3 + 1587721*x3^3]

theorem identity3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    9526326*x3^5 =
      ∑ k, numerator3 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator3 i x0 x1 x2 x3 k * derivativeFormula i x0 x1 x2 x3 k) -
      9526326*x3^5 = (i^2+1)*(-516888*x0*x1^2*x3^2 - 642600*x1^3*x3^2 - 1549404*x1^2*x2^2*x3 - 188010*x1*x2*x3^3 - 4930227*x2^3*x3^2 - 4763163*x3^5) := by
    simp [Fin.sum_univ_succ, numerator3, derivativeFormula]
    ring
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def denominator : Fin 4 → ℕ := ![4272557211, 2848371474, 9526326, 9526326]

def numerators {R : Type*} [CommRing R] (j : Fin 4) (i x0 x1 x2 x3 : R) : Fin 4 → R :=
  ![numerator0 i x0 x1 x2 x3, numerator1 i x0 x1 x2 x3,
    numerator2 i x0 x1 x2 x3, numerator3 i x0 x1 x2 x3] j

theorem polynomial_derivative (j : Fin 4) :
    pderiv (j.castSucc) (smoothH Complex.I : Poly ℂ) =
      derivativeFormula (C Complex.I) (X 0) (X 1) (X 2) (X 3) j := by
  fin_cases j <;>
    simp [smoothH, smoothB, smoothA, derivativeFormula, Derivation.leibniz,
      Fin.castSucc] <;> ring

theorem coordinate_power_identity (j : Fin 4) :
    (denominator j : Poly ℂ) * X j.castSucc^5 =
      ∑ k, numerators j (C Complex.I) (X 0) (X 1) (X 2) (X 3) k *
        pderiv k.castSucc (smoothH Complex.I : Poly ℂ) := by
  have hi : (C Complex.I : Poly ℂ)^2+1=0 := by
    rw [←map_pow, Complex.I_sq, map_neg, map_one]
    ring
  simp_rw [polynomial_derivative]
  fin_cases j
  · exact identity0 _ _ _ _ _ hi
  · exact identity1 _ _ _ _ _ hi
  · exact identity2 _ _ _ _ _ hi
  · exact identity3 _ _ _ _ _ hi


theorem denominator_ne_zero (j : Fin 4) : (denominator j : ℂ) ≠ 0 := by
  fin_cases j <;> norm_num [denominator]

/-- The explicit identities place every fifth coordinate power in the
literal four-generator Jacobian ideal, over characteristic zero. -/
theorem coordinate_power_mem_gradient_ideal (j : Fin 4) :
    (X j.castSucc : Poly ℂ)^5 ∈
      Ideal.span (Set.range (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) := by
  let J : Ideal (Poly ℂ) :=
    Ideal.span (Set.range (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ)))
  have hsum : (denominator j : Poly ℂ)*X j.castSucc^5 ∈ J := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left J (C ((denominator j : ℂ)⁻¹)) hsum
  have hc : C ((denominator j : ℂ)⁻¹)*(denominator j : Poly ℂ)=1 := by
    rw [←map_natCast C, ←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- Algebraic projective Jacobian criterion for the actual cubic, valid
under every map to a field. No point enumeration or modular hypothesis. -/
theorem nonzero_gradient {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (hx : ∃ j : Fin 4, φ (X j.castSucc) ≠ 0) :
    ∃ j : Fin 4, φ (pderiv j.castSucc (smoothH Complex.I : Poly ℂ)) ≠ 0 := by
  by_contra! hzero
  have hle : Ideal.span (Set.range
      (fun k : Fin 4 => pderiv k.castSucc (smoothH Complex.I : Poly ℂ))) ≤
      RingHom.ker φ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact hzero k
  obtain ⟨j, hj⟩ := hx
  have h := hle (coordinate_power_mem_gradient_ideal j)
  change φ ((X j.castSucc)^5)=0 at h
  rw [map_pow] at h
  exact (pow_ne_zero 5 hj) h

/-- In particular the literal cubic has no projective singular point over
any field extension of the complex coefficients. -/
theorem nonzero_gradient_over_complex_extension {K : Type*} [Field K] [Algebra ℂ K]
    (x : Fin 5 → K) (hx : ∃ j : Fin 4, x j.castSucc ≠ 0) :
    ∃ j : Fin 4, aeval x (pderiv j.castSucc (smoothH Complex.I : Poly ℂ)) ≠ 0 := by
  apply nonzero_gradient (aeval x).toRingHom
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_X] using hx

end CycleQ2SeedCubicGradient

#print axioms CycleQ2SeedCubicGradient.coordinate_power_identity

#print axioms CycleQ2SeedCubicGradient.nonzero_gradient_over_complex_extension
end
end
