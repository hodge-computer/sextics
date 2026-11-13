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


/- Component: continuation_20261111/SeedCurveGradientArithmetic.lean -/
section
/-! Exact integral identities for the actual r=57 quadric-cubic seed curve.
The generators are f,h and the six2x2 minors of their4-variable Jacobian.
The only algebraic input is i^2+1=0. -/

set_option maxHeartbeats 2500000
set_option maxRecDepth 20000
namespace CycleQ2SeedCurveGradientArithmetic
open scoped BigOperators

def generators {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![x0^2 - 57*x1*x3,
    -i*x1^3 - i*x3^3 + x0^3 + x0*x1^2 + x0*x2*x3 + x1*x2*x3 + x2^3 + x3^3,
    -6*i*x0*x1^2 + 4*x0^2*x1 + 171*x0^2*x3 + 2*x0*x2*x3 + 57*x1^2*x3 + 57*x2*x3^2,
    2*x0^2*x3 + 2*x0*x1*x3 + 6*x0*x2^2,
    -6*i*x0*x3^2 + 171*x0^2*x1 + 2*x0^2*x2 + 2*x0*x1*x2 + 6*x0*x3^2 + 57*x1^3 + 57*x1*x2*x3,
    -57*x0*x3^2 - 57*x1*x3^2 - 171*x2^2*x3,
    -171*i*x1^3 + 171*i*x3^3 + 114*x0*x1^2 - 57*x0*x2*x3 - 171*x3^3,
    57*x0*x1*x3 + 57*x1^2*x3 + 171*x1*x2^2]

def numerator0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![1854032751781693307752990613058284625471228657389887526737858728084832829640*i*x0^2*x1^2 - 2161843145283051199263584592474554191232446731650581755371019717898603703878440*i*x0^2*x1*x2 + 2046455533992212788403670450075442990075176945420936579961327702190138229842058*i*x0^2*x1*x3 + 355600876740270276518744261710610127697542520751217701890196659805545996705674*i*x0^2*x2^2 - 57728681045950857368478645510257662904941835879566177231306504309507617418689000*i*x0^2*x2*x3 + 442729142235431736186687226781970989940681137872846834430817996468243287570040*i*x0^2*x3^2 + 30999367325986093702591506919593978266485942001855493539529038696895852068841720*i*x0*x1^2*x2 + 3080269971647236490243448989793708257066326154193127982515939227524420479109199792*i*x0*x1^2*x3 - 233807632408784697368858641411055453414236635932356147418660945772867237570072*i*x0*x1*x2^2 + 54038291586958182280475719217274743124246899825969430725733616502617478711678940*i*x0*x1*x2*x3 + 7276345602891090931516360142215679933994917888833996137749143223317040765953314*i*x0*x1*x3^2 - 21853713311226541535009810667156902930243006294130262819235285681394802506364698*i*x0*x2^2*x3 + 3079146131493929177887759556621794747264649157758145252399547253834722499808050220*i*x0*x2*x3^2 - 1189308408753025053754616470436619258432162526383629138243461106422175693651454840*i*x0*x3^3 + 618010917260564435917663537686094875157076219129962508912619576028277609880*i*x1^4 + 12456489676697953147782046031519697687288452378399315343514118601710470498566360*i*x1^3*x2 - 1646397986235556638908725041316429527682570854097486518568609548592809565547358*i*x1^3*x3 + 112395323675140147918754751165747715821774806938649559411739860506166819330198*i*x1^2*x2^2 + 25816184855935798356086006824656957396874252794167457504066034814062340993397420*i*x1^2*x2*x3 + 3362618429381694204779178217641720241425498313007775139329153036848222139136422*i*x1^2*x3^2 + 27035129298739134300905160186532374269047604241774667400386153990598099248172820*i*x1*x2^3 + 3249667499466457463423620452808255248873381434782322430763336082605724505017340*i*x1*x2^2*x3 + 4620677270040573524229385680923959894861071204380642346663192854253121543449344808*i*x1*x2*x3^2 + 27046619995325201124987479868443303009577906353488063307315961895222222525429380*i*x1*x3^3 + 3957038780782559196021317020576368698101348937950199139980415887999204417996100*i*x2^4 + 4620612322088193579852218426462566189818217936247186043630008639654273031585082860*i*x2^3*x3 - 1208071757134529685172751343502174226518206412112943951899223891487663255128720*i*x2^2*x3^2 + 20483518168178308281180237837505900076043267132525166332040767331951376968677642*i*x2*x3^3 + 4618553267034386262770529841531527811053329888599578289977126814514887225737361758*i*x3^4 + 621670727904138046969000177387915358039720247826119404514141842177482385037331220*x0^4 + 324338715472256088141686270016689920924162230388122797049855883447767859925694240*x0^2*x1^2 - 61982807276561261481221921987611427110654401330251834303135264941868652820037520*x0^2*x1*x2 - 32353482297510295809145665789998849161138432321864832098178485142882575600807349124*x0^2*x1*x3 - 246718500479423376342008788913683403071455455272026547502791020700620591454272*x0^2*x2^2 - 400285013070398108324647771281209352436437312513557542509884719563573728584922040*x0^2*x2*x3 - 3060447191248337702403546664125368747256101678162105161276538225098053921094860*x0^2*x3^2 - 14106385425651742533404347344350244900145427593655629007805590075410263689002200*x0*x1^2*x2 + 1797423402865009342018151790093431441103766536993991622141806492523675357759604*x0*x1^2*x3 - 5153656500844366997039216919953799651526528086844069596646166681352418836744*x0*x1*x2^2 + 414415857563897686258092345192407025168165503763344662698573965264262487079158800*x0*x1*x2*x3 - 10028623447459297054245800444476666087718239096858571056994119337769699360842982*x0*x1*x3^2 - 1484695654162109521432781835222772224405194938533296909603167756302385714794666*x0*x2^2*x3 + 2640776329313687528129022119153011265646771084441223029781027746145339504069860*x0*x2*x3^2 + 1189241465995076349865066745668106372694787172583571787035095941712587018775070320*x0*x3^3 + 108112905157418696047228756672229973641387410129374265683285294482589286641898080*x1^4 - 7837590204497486101348804357398840101394922367536821825032609996268289152703800*x1^3*x2 - 6164144556011303606787110218322387667432613237274082694332414921662177374682379546*x1^3*x3 - 226572547680218853958503590448115527400809085633144544816302415311049122405644*x1^2*x2^2 - 253573263527468377478568235681570676595518849636655289526604661461291758476864620*x1^2*x2*x3 - 2541884572241758053066862662746251153310800950922352309911757365723364134353126*x1^2*x3^2 - 11490696586066824082319681910928740530302111713395906929807904624123277256560*x1*x2^3 - 24958489943294100177749863977263019936012691187054213017744224291371443982245020*x1*x2^2*x3 - 10782498589177610527674530571920530609485782721585294269801186569213775903417824824*x1*x2*x3^2 + 27023638602153067476822840504621445528517302130061271493456346085973975970916260*x1*x3^3 - 13163860958014054880379742599287811136516419881567192052731198407103950411545120*x2^4 + 1781546416372725964698874552422889903019793278124292039806543499034665295610960*x2^3*x3 - 334639548689561872400809512485357347227328353412541491902573994048658822593333320*x2^2*x3^2 - 11748706749473253737425288241457693591725871894539345222662539884828110127902146*x2*x3^3 + 4622462120850518526523549736530809282659881405548912036649485610265505038646339006*x3^4,
    -1854032751781693307752990613058284625471228657389887526737858728084832829640*i*x0*x1^2 + 2161843145283051199263584592474554191232446731650581755371019717898603703878440*i*x0*x1*x2 - 2046455533992212788403670450075442990075176945420936579961327702190138229842058*i*x0*x1*x3 - 355600876740270276518744261710610127697542520751217701890196659805545996705674*i*x0*x2^2 + 57728681045950857368478645510257662904941835879566177231306504309507617418689000*i*x0*x2*x3 - 442729142235431736186687226781970989940681137872846834430817996468243287570040*i*x0*x3^2 + 3081217796986432837346019565158554248779541188687166571973630892753794669294095280*i*x1^2*x3 + 225551210504605874173215070172853015791776889463161350978883705615954651825777700*i*x1*x2*x3 + 263368495825577551063145081287549825199836581202094101462024023288244711291647901734*i*x1*x3^2 + 1540215426958302182194425434526208915443827746906010530151620115289703012148244540*i*x2*x3^2 - 324338715472256088141686270016689920924162230388122797049855883447767859925694240*x0*x1^2 + 61982807276561261481221921987611427110654401330251834303135264941868652820037520*x0*x1*x2 + 67788713788046164486378675901110024569402486447953638155484570146999071547935228664*x0*x1*x3 + 246718500479423376342008788913683403071455455272026547502791020700620591454272*x0*x2^2 + 400285013070398108324647771281209352436437312513557542509884719563573728584922040*x0*x2*x3 + 3060447191248337702403546664125368747256101678162105161276538225098053921094860*x0*x3^2 - 17613311141926086423653410824053703941976672245203931504009657916805911881580*x1^2*x3 - 750340074606801128181645328159405234781435933249329947005678309204925173458071840*x1*x2*x3 + 114462780951017854663470554143647309533974334734173885323502217117705721826946428*x1*x3^2 + 637356394263882886268568458098884506285243695418362763495040905658220891742340*x2*x3^2,
    -1161116855157265698398772019718625301879065623461154769675091901421731564089020*i*x0*x1*x2 - 1540371942158417331897367138738065626461466835720073638622392530069553787100823768*i*x0*x1*x3 + 135513018936573457701853311933814965865166409006512646389251994019851095393938*i*x0*x2^2 - 27013810283346382222702836205543881068470625173474595219597469994879681356469560*i*x0*x2*x3 + 6957484477230400093295769129295311285063197037414186566837552606417315456752320*i*x0*x3^2 + 309005458630282217958831768843047437578538109564981254456309788014138804940*i*x1^3 - 707371281316101732597696567768113449227967503167876709217079805393479912978760*i*x1^2*x2 + 361720977817388179748653101554575902738031509659950066054236365752904852469246*i*x1^2*x3 + 112395323675140147918754751165747715821774806938649559411739860506166819330198*i*x1*x2^2 - 28229395037104743407881969493084786778164307235025409393155717142184207327904940*i*x1*x2*x3 + 3362618429381694204779178217641720241425498313007775139329153036848222139136422*i*x1*x3^2 - 27021323279970213722709218149582612551646100822912465441256493250696544072776220*i*x2^3 - 184377701762303654662643888995123144062988569264997473458281906398226168877100*i*x2*x3^2 - 27010141588842777180844857299440526858553377249308634515581141655860434934324600*i*x3^3 + 1964807949452766236109140725486966346934838182896398377002803183005859091754960*x0*x1*x2 - 444952522930770813898624594817344434290447466187196922659449208651717361469506*x0*x1*x3 - 16978116950346445060587518701012659772516247691944057161640731263541507343394*x0*x2^2 - 19170366804547195405833863024864887555157981168769507563017945332184563718200*x0*x2*x3 - 7086819020599187108139986996351186295647394729826160122935570775123088413704480*x0*x3^2 + 54056452578709348023614378336114986820693705064687132841642647241294643320949040*x1^3 - 11794628985280045297370121377975208799496271305487020965013025884267493570699900*x1^2*x2 - 10784644482775822046491409890033788109535009398714330088403011821455944239448132208*x1^2*x3 - 226572547680218853958503590448115527400809085633144544816302415311049122405644*x1*x2^2 - 334650730380689308942673873335499432920421076986145322828249345643494931731784940*x1*x2*x3 - 2541884572241758053066862662746251153310800950922352309911757365723364134353126*x1*x3^2 - 11181691127436541864360850142085693092723573603830925675351594836109138451620*x2^3 + 137774634158573998221939970386494618806074765278382017202406327822621612290780*x2*x3^2 - 27032504971097650264573578999724698244738824396516296366931844845532653211227840*x3^3,
    13508360636856953431655285401966345989589466508312532394106636502031346173822010*i*x0*x1*x2 - 659506463463759866003552836762728116350224822991699856663402647999867402999350*i*x0*x2^2 - 210718426686681099480025336439485656822083507098382342880194637592624726595940*i*x0*x3^2 - 185452797600314957901502125629168293555566509754473453565837245194279023829932*i*x1^3 - 10872685668806259646402018373242645655145035494265944420895285048094999646680*i*x1^2*x2 - 2048799448742705867279795275532988462494740534490532918653555678710124280791355*i*x1^2*x3 - 360307190880508533210597432079092365205407788608430292561836619649767283979740*i*x1*x2^2 + 343122022967018779485331742591836829482775946451852654844107625730250320386463*i*x1*x2*x3 - 234178403551715415128623151643982019559430808503817019910979774749475675867887491*i*x1*x3^2 + 59266812790045046086457376951768354616257086791869616981699443300924332784279*i*x2^3 - 614339081001738320510034868515406300274939038956874391465586301352421545522760*i*x2^2*x3 - 1213585489524875892136491925574247010728967362583062334959424277110544858314071*i*x2*x3^2 + 90472328864317576970378336401140879648810516099106093624204318623574016072421*i*x3^3 + 9369576849302165256627180413211918816866067688119934938535713994759971843840*x0*x1*x2 + 2193976826335675813396623766547968522752736646927865342121866401183991735257520*x0*x2^2 + 11302293263692322813435515353973241930458663108350796993443330416730549984197880*x0*x3^2 - 53128510885095101832297374213979361205517720146779942430040417205242486545919*x1^3 + 81077775858679561746323596485697599372339805887599598282899140491991187393725260*x1^2*x2 - 3190167307356559634351341141400717547558222646509971135687371187664713189067825*x1^2*x3 - 10330467879426876913536986997935237851775733555041972383855877490311442136672920*x1*x2^2 - 11298070853658520610709164483298067354547177633347647758459989900474819421680786704*x1*x2*x3 + 159359283353519132996015900130396896106034918095892285394766101585400865188788433*x1*x3^2 - 41119750079903896057001464818947233845242575878671091250465170116770098575712*x2^3 - 66710441614690539206819841596820863508375310894391646776422336062316918384669800*x2^2*x3 - 348782420846431722325009683027941190037112593286882317177169423846031333753567*x2*x3^2 + 48114603589834359266136211057058595228783127687321047929929160289330236810817*x3^3,
    -154122221668754566719277303162102205023214500046847219069173515153268572002840*i*x0*x1*x2 + 36533062151115073619694645862002219370795759427310149121604545867759224105160*x0*x1*x2,
    -61459233920767884887547962998374381354329523088332491152760635466075389625700*i*x3^3 + 45924878052857999407313323462164872935358255092794005734135442607540537430260*x3^3,
    0,
    0]

theorem identity0 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    621670727904138046969000177387915358039720247826119404514141842177482385037331220*x0^6 =
      ∑ k, numerator0 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator0 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k) -
      621670727904138046969000177387915358039720247826119404514141842177482385037331220*x0^6 = (i^2+1)*(6966701130943594190392632118311751811274393740766928618050551408530389384534120*x0^2*x1^3*x2 + 9242231652950503991384202832428393758768801014320441831734355180417322722604942608*x0^2*x1^3*x3 - 813078113619440746211119871602889795190998454039075878335511964119106572363628*x0^2*x1^2*x2^2 + 162082861700078293336217017233263286410823751040847571317584819969278088138817360*x0^2*x1^2*x2*x3 - 41744906863382400559774614775771867710379182224485119401025315638503892740513920*x0^2*x1^2*x3^2 + 924733330012527400315663818972613230139287000281083314415041090919611432017040*x0^2*x1*x2*x3^2 + 2082384542613559196322594814134126504135358287356678499931459114462275773994120*x0*x1^4*x2 - 123870332912116290088248159252012426353012112538763816364090492327290884973418*x0*x1^4*x3 - 318771065310570610993784245283876167233106320880679654580242503231454919275514*x0*x1^3*x2^2 + 111647689176677603078813171448251057764044007530586279127627798543597626548740640*x0*x1^3*x2*x3 - 19732981434054733492488382079068350458612308740173804001544100224621089547248492*x0*x1^3*x3^2 + 162127939679821282336255308897495675309876604937474792647538959504179264436657320*x0*x1^2*x2^3 + 1106266210573821927975863333970738864377931415589984840749691438389357013262600*x0*x1^2*x2*x3^2 + 162062703565808444778376896787256219435945734724509196981013587793890694438777240*x0*x1^2*x3^3 - 2161843145283051199263584592474554191232446731650581755371019717898603703878440*x0*x1*x2*x3^3 + 2046455533992212788403670450075442990075176945420936579961327702190138229842058*x0*x1*x3^4 + 355600876740270276518744261710610127697542520751217701890196659805545996705674*x0*x2^2*x3^3 - 57728681045950857368478645510257662904941835879566177231306504309507617418689000*x0*x2*x3^4 + 442729142235431736186687226781970989940681137872846834430817996468243287570040*x0*x3^5 - 3081217796986432837346019565158554248779541188687166571973630892753794669294095280*x1^5*x3 - 225551210504605874173215070172853015791776889463161350978883705615954651825777700*x1^4*x2*x3 - 263368495825577551063145081287549825199836581202094101462024023288244711291647901734*x1^4*x3^2 - 1540215426958302182194425434526208915443827746906010530151620115289703012148244540*x1^3*x2*x3^2 - 3081217796986432837346019565158554248779541188687166571973630892753794669294095280*x1^2*x3^4 - 225551210504605874173215070172853015791776889463161350978883705615954651825777700*x1*x2*x3^4 - 263368495825577551063145081287549825199836581202094101462024023288244711291647901734*x1*x3^5 - 1540215426958302182194425434526208915443827746906010530151620115289703012148244540*x2*x3^5) := by
    simp [Fin.sum_univ_succ, numerator0, generators]
    ring1
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![-45553608202943748827137912930062052300370184104299897710061802427863117420256600*i*x0^2*x1^2 + 219040362634112216716374117118325444256960170218462896177165207165761409643940433720*i*x0^2*x1*x2 - 4853088487203634624344805246298171156458434976203810981180231157928593658010102672*i*x0^2*x1*x3 + 995845167376111782352343690705135726737999808930922435289712416600459601041321884*i*x0^2*x2^2 + 2107618979974310435283939255372160127912410046558902217216289776948721064344244385480*i*x0^2*x2*x3 - 4823438163481987466360896188466431847676962703100107959007084025637043591045470380*i*x0^2*x3^2 - 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*i*x0*x1^3 - 162973182170175607652118305878728535920576388508140891412145924194875046287099459740*i*x0*x1^2*x2 - 120135000901998423625288865977740130972784670813504508115396577219920722234153851606828*i*x0*x1^2*x3 - 629633694342069272220094889559053151541833050863943653775530298076286242828326472*i*x0*x1*x2^2 - 2107635966901843352613837518615182364782355065423572888600889815134467230649295215440*i*x0*x1*x2*x3 + 173596016582313125010621921907566825325665945724875953298826692031741952315762915304*i*x0*x1*x3^2 - 206072355942525514583478270575570579904768813126763148855042779377932419541915527908*i*x0*x2^2*x3 - 120138106779562436686474909305518023408023292896658267089426537435551845892235119545620*i*x0*x2*x3^2 + 3951791921200649421677850790392679717917146439622571573976434826731187216362662909320*i*x0*x3^3 - 15184536067647916275712637643354017433456728034766632570020600809287705806752200*i*x1^4 + 219041540337288646822394761389269388171274476779041978603025515071526737578345021160*i*x1^3*x2 - 2022785886321841954131020672192105933327663731868753748526680763562423186368989858*i*x1^3*x3 + 416562008530062482731856342232014173622207328723243359260986031324720507599650148*i*x1^2*x2^2 - 1053850267248854018971092334946427672716811837621557515158923896702988890680122562820*i*x1^2*x2*x3 + 86889283119935626654583883743240992007054364774053924604213981741563528235885407952*i*x1^2*x3^2 - 1053807570083843809787429934726432379616393312543878324691477886579562313112961423780*i*x1*x2^3 - 199954590071022429518742153281105734213863103332214386980828856740635100809701265620*i*x1*x2^2*x3 - 180204645784177744954311619529334980912060942836492349999186109843964818841093317432672*i*x1*x2*x3^2 - 1053807287760535639755910499857855200859274370568051635651132845181213416366667180340*i*x1*x3^3 - 343838667060108198843392166205004551039707430299234786497949686729316684120296999580*i*x2^4 - 180203516410109010074584422798193309248853940623392140784754767506149991025354177598920*i*x2^3*x3 - 27230305634391235867252713774760325866126373817734794530948124268393115060143400*i*x2^2*x3^2 - 181791920591969694691063533996392987687222915713159282807831019904908001616662304428*i*x2*x3^3 - 180205186523746327390399035566871078881036988247676601330678972453792168544105190213202*i*x3^4 + 17651332258297258597033717350970951567349372415581462722219223606501710803837740525460*x0^2*x1^2 - 51247464544440761114164476561466096743183866035461497738904522696160307765387781180*x0^2*x1*x2 + 225247385951146585486209422014920081382055768632341211443895806226619231177317974705666*x0^2*x1*x3 + 409467827917158493711187170517529299595588488989954933751566846786785733594489158*x0^2*x2^2 + 1317216844254471162971252107979766057632808852298711512241237593557785145620479585240*x0^2*x2*x3 - 3215405539583503199481740377843523467793094070703924781218114003250946815693969960*x0^2*x3^2 - 80920007769789099727887714480271172830956858001547029522296343797368983693505564240*x0*x1^2*x2 - 944341314559785534117373303118929723002824660957897520961027677675570184802923836*x0*x1^2*x3 - 597711295913841880466317772501917305955482061740123489999907245400441024448523744*x0*x1*x2^2 + 41743328619161440299610897298663369757067452825993684104137065734259377195848080*x0*x1*x2*x3 - 184149851630974742514589198070532652292210073809892944307104865135581290024006753692*x0*x1*x3^2 - 60249544389186177451181001900513270968769467381155626733872960473497316641422359936*x0*x2^2*x3 + 1521819709660670511960608476274341199559381358326347694429115704980396357075751540*x0*x2*x3^2 - 3951618897253165505222240492312032605519152794015324889661749623707309791543172027000*x0*x3^3 + 1844161029511330503140009297656976525907688634819697016873514178364623063306668574260*x1^4 - 245371123735717858504106378827066913884696823206553471657575903301567910098327970300*x1^3*x2 - 105120698882885683343432498853757527008243904727773058615038831485849592566592401732286*x1^3*x3 - 17468339473838111128287126317175398974347173271807488199841983398404512482706594*x1^2*x2^2 + 3776102411289266925908151082281089311774545390953373635663690767523249179748208887760*x1^2*x2*x3 + 89584673837839579621357590343968677145826892991291257507268800241456021518782569264*x1^2*x3^2 - 282323308170031519434868577178757118941975826689040345041398348896746294243440*x1*x2^3 - 82995614495420143190157991420766460415211705097606682417449156667445868087163896540*x1*x2^2*x3 + 75084882526798982608154793708795802872048636612915630714149665294680545764783751056716*x1*x2*x3^2 - 1053807852407151979818949369595009558373512254519705013731822927977911209859255667220*x1*x3^3 - 75157463348202877497744748465370571345430149812021579085904685082845154267749287200*x2^4 + 1207872190648529531860008440613023165189949280142755020993435942851128875222336480*x2^3*x3 + 878134094017400783012231284766257585007582385565624983139043743977412700074873133160*x2^2*x3^2 - 329411456570471496719779324326406445239310687119965108076585571570705816869263717516*x2*x3^3 - 180202848663933085585049882896452230537363669938772253045126593551062590563182962371614*x3^4,
    45553608202943748827137912930062052300370184104299897710061802427863117420256600*i*x0*x1^2 - 219040362634112216716374117118325444256960170218462896177165207165761409643940433720*i*x0*x1*x2 + 4853088487203634624344805246298171156458434976203810981180231157928593658010102672*i*x0*x1*x3 - 995845167376111782352343690705135726737999808930922435289712416600459601041321884*i*x0*x2^2 - 2107618979974310435283939255372160127912410046558902217216289776948721064344244385480*i*x0*x2*x3 + 4823438163481987466360896188466431847676962703100107959007084025637043591045470380*i*x0*x3^2 + 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*i*x1^3 - 120135011328053636659004809793276482363805741691132431339386051184169985694087666571780*i*x1^2*x3 - 13539379437544533790266508744685248414450170271495196994583791607867130187898061574720*i*x1*x2*x3 - 10271624179410699787812827815308525851992571081351089249602499624054334997514121303196876*i*x1*x3^2 - 60067979833274539501121303513869836725671322876131366831971811649134933846648865416320*i*x2*x3^2 - 17651332258297258597033717350970951567349372415581462722219223606501710803837740525460*x0*x1^2 + 51247464544440761114164476561466096743183866035461497738904522696160307765387781180*x0*x1*x2 - 225247385951146585486209422014920081382055768632341211443895806226619231177317974705666*x0*x1*x3 - 409467827917158493711187170517529299595588488989954933751566846786785733594489158*x0*x2^2 - 1317216844254471162971252107979766057632808852298711512241237593557785145620479585240*x0*x2*x3 + 3215405539583503199481740377843523467793094070703924781218114003250946815693969960*x0*x3^2 + 432759277927965613857810172835589496853516748990849028245587123064699615492437700*x1^2*x3 - 4283975410847564017371450662526122566689518539285230007896567049722173793261709370400*x1*x2*x3 + 69844410216974955650332847315021318157364897844630063024016841796223403099187455218*x1*x3^2 + 448851706493657410465597681734778652633209371112124327912946828951814154264313780*x2*x3^2,
    37579377296691026693265812347864062236773196385572064540808211157301742935099771080*i*x0*x1*x2 + 60067503057513015071073418942754153334147603126159234863695657101022676982060379544652*i*x0*x1*x3 + 120403531821156204373576188801247828898664101997118564762850178128229237471115608*i*x0*x2^2 + 1053836763817760094664305338125075205460202431419822420592972801664834969233239678140*i*x0*x2*x3 - 23109860152025616434361456085483742998679791966197010689141728143627092629840463480*i*x0*x3^2 - 7592268033823958137856318821677008716728364017383316285010300404643852903376100*i*x1^3 + 37578382517478163292950982590565290601052164588753981345202574976332095469212095340*i*x1^2*x2 - 797445356199474311142725105261907369163367278454191239333402837312889798663946784*i*x1^2*x3 + 416562008530062482731856342232014173622207328723243359260986031324720507599650148*i*x1*x2^2 + 1053796977295673319310120528231310094510472871453048349976904343965818165598077846360*i*x1*x2*x3 - 19416411351671979377115146590092534217737797604212493567704273270785959605498230668*i*x1*x3^2 + 1053824207601307710545987780945084854836338997826866084771435292090086558713137989760*i*x2^3 + 84633295994657066677850305822258335783361506968220167252051053809794567123763180*i*x2*x3^2 + 1053832082192649704535645072132483710602174668166710157128065343788840099312335609300*i*x3^3 + 25052451295514847212970762438867517719753827485932501301111767968515618301875494800*x0*x1*x2 + 127895509157954980064890782570835056537326977991762123178860138652717642327621534*x0*x1*x3 + 205830740388607514338788025801499496220035579593460625956557887597752038316798816*x0*x2^2 - 11524394246516537558047989228123507907559010113675274984456506046387195972748920*x0*x2*x3 + 23108827336997371318290006733974634866740565682167889554875734907435792521699004040*x0*x3^2 + 3951792807196482023473427013328493760360420945190441426336427357034271935132767987800*x1^3 - 7838151147217265692413242955395889069781555285585103331544471584600713819414609340*x1^2*x2 + 75083234089231856793634655800778014254783658102947805413075197006331723179269375516782*x1^2*x3 - 17468339473838111128287126317175398974347173271807488199841983398404512482706594*x1*x2^2 + 878126219426058789022573993578858729241746715225780910782413692278659159475675513620*x1*x2*x3 - 16721020633768026410341439989364849078965269386975160664649454770893466322601069356*x1*x3^2 - 7874591341993989657291187398855765835670339844072356630051698753540599197619540*x2^3 + 423097037003446877149612450858418700814213514410738565275010422573052126670496860*x2*x3^2 + 1053816333009965716556330489757685999070503327487022012414805240391333018113940370220*x3^3,
    2502797415720585599837335499657687657451749514653328582167293054221829749856168611460*i*x0*x1*x2 + 92741676000553901817798371145278600581548625842627937140297699459002609967177379470*i*x0*x2^2 - 2917602134505701020899887479832571451006701441373066599657085477188329971827120*i*x0*x3^2 - 85712977460031193413484988070096948906945254770133310491769791196202134748454787*i*x1^3 - 15466859375817947795147506220532774552398703861455672915061999158184452100995640*i*x1^2*x2 - 7828499857621267542496029603349536787265865997623622482205427030433830604892441830*i*x1^2*x3 + 71941958596221238129962029630832082784424082495832622086833619531743397554451285160*i*x1*x2^2 - 837052621002169733595603689493129280979586071282724901584843601585176934308086952*i*x1*x2*x3 - 58122419994179489540254502366941620245472886226138000156951137980052498186062985026*i*x1*x3^2 + 165974194562685297058723948450855954456333301488487072548285402766743266840220314*i*x2^3 - 4905871384164301339384419668263626711324849138325387763467871908675513671932340*i*x2^2*x3 + 104357954558726290845756573841643933208975359625443773813503330982525136153567128614*i*x2*x3^2 - 49765598386042598135883891817815967440004415417769110100667049744219152099488549*i*x3^3 + 5296781446024331691433269695433636743603889200496411144208032227176523847453600*x0*x1*x2 + 12526243891367146249624124744228428557571691635336929847650780847140859044624881200*x0*x2^2 + 4711313307504897324670401185021653258031182307887888999477267894635166321168080*x0*x3^2 - 250587813967377185673132393781158219165874027234756286712700628557977240759429834*x1^3 + 1888064502114902055626298444216740406388556404770044368931768642326865241926485431150*x1^2*x2 - 9643439611168138081195958423624568566201859171292904646385945863928547601842313840*x1^2*x3 - 8541244090740126852360746093577682790530644339243582956484087116026717960897963530*x1*x2^2 + 37541282311062912989126803230103287903175574619835624727026895603636203196138667185271*x1*x2*x3 - 242725244820626531201547446796898063188081207325185025289886360242865680129460788832*x1*x3^2 + 68244637986193082285197861752921549932598081498325822291927807797797622265748193*x2^3 + 219538765572859191825094448392427294860746698829733276159082949492548704469812470720*x2^2*x3 + 103814401514651917445566920691912027099402975360344554761794602746295685674758388208*x2*x3^2 + 127859614474026958684573943962348153800469245744461097448722072322232849579531997*x3^3,
    74009783528722227362895067177030917973588321437734697362064792781684646471932020*i*x0*x1*x2 - 106305694471607606031699030333333526224792162378266418171918255012349487841383638620*i*x2^3 - 112805832820294088444417165352040339462330128316859506913162152495283564409335760*x0*x1*x2,
    28211098664885688892616768607419445261120502322740055750683684603264855707921060*i*x3^3 + 141032345667815625716537483619472900271404504803579521758336807524350708890165620*x3^3,
    0,
    0]

theorem identity1 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x1^6 =
      ∑ k, numerator1 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator1 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k) -
      6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x1^6 = (i^2+1)*(-225476263780146160159594874087184373420639178313432387244849266943810457610598626480*x0^2*x1^3*x2 - 360405018345078090426440513656524920004885618756955409182173942606136061892362277267912*x0^2*x1^3*x3 - 722421190926937226241457132807486973391984611982711388577101068769375424826693648*x0^2*x1^2*x2^2 - 6323020582906560567985832028750451232761214588518934523557836809989009815399438068840*x0^2*x1^2*x2*x3 + 138659160912153698606168736512902457992078751797182064134850368861762555779042780880*x0^2*x1^2*x3^2 - 444058701172333364177370403062185507841529928626408184172388756690107878831592120*x0^2*x1*x2*x3^2 - 6429932470756763041331778425066299349352817314060991894050242692231163171332138320*x0*x1^4*x2 - 68416350006788757488454614726726941478231305478663545179814134051254866026421968*x0*x1^4*x3 - 1503526883804263114038794362686949314995244163408537720276203771347863444556579004*x0*x1^3*x2^2 - 4215162883799729480576783914015700439150427182159387882645136286846187929244222692680*x0*x1^3*x2*x3 + 111675029946549888796329983352088773458749822922174853447218555599078714041943913628*x0*x1^3*x3^2 - 6322945245607846263275926685670509129018033986961196508628611752540519352278827938560*x0*x1^2*x2^3 - 507799775967942400067101834933550014700169041809321003512306322858767402742579080*x0*x1^2*x2*x3^2 - 6323038046764101170962697570707832325665348379184365242666102124535468458991433912400*x0*x1^2*x3^3 + 219040362634112216716374117118325444256960170218462896177165207165761409643940433720*x0*x1*x2*x3^3 - 4853088487203634624344805246298171156458434976203810981180231157928593658010102672*x0*x1*x3^4 + 637834166829645636190194182000001157348752974269598509031509530074096927048301831720*x0*x2^3*x3^2 + 995845167376111782352343690705135726737999808930922435289712416600459601041321884*x0*x2^2*x3^3 + 2107618979974310435283939255372160127912410046558902217216289776948721064344244385480*x0*x2*x3^4 - 4823438163481987466360896188466431847676962703100107959007084025637043591045470380*x0*x3^5 - 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x1^6 + 120135011328053636659004809793276482363805741691132431339386051184169985694087666571780*x1^5*x3 + 13539379437544533790266508744685248414450170271495196994583791607867130187898061574720*x1^4*x2*x3 + 10271624179410699787812827815308525851992571081351089249602499624054334997514121303196876*x1^4*x3^2 + 60067979833274539501121303513869836725671322876131366831971811649134933846648865416320*x1^3*x2*x3^2 - 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x1^3*x3^3 + 120135011328053636659004809793276482363805741691132431339386051184169985694087666571780*x1^2*x3^4 + 13539379437544533790266508744685248414450170271495196994583791607867130187898061574720*x1*x2*x3^4 + 10271624179410699787812827815308525851992571081351089249602499624054334997514121303196876*x1*x3^5 + 60067979833274539501121303513869836725671322876131366831971811649134933846648865416320*x2*x3^5) := by
    simp [Fin.sum_univ_succ, numerator1, generators]
    ring1
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![-5739200739306131905349555095524116419141850202784573826774724421558408208081040*i*x0^2*x1^2 - 427330933142183553910351254075320846520497039633246797872056060645970708501607435320*i*x0^2*x1*x2 - 6468617078244088898000391598307437774461563977366911331264051416390887685772620478*i*x0^2*x1*x3 - 20837852112530198689942146972894796718614860446375477991453730877011419850032029874*i*x0^2*x2^2 - 72094621955643118086601966996891134203070238756577878964318328654434397242217755440*i*x0^2*x2*x3 - 686883618152728319323522876514597268469852193848985090394763238102216158866001920*i*x0^2*x3^2 + 284794782047168004787176590470082761974448086048153900685640493884010155428780784040*i*x0*x1^2*x2 + 24115566322462145417604966627106577435770870873506476603266693656024920758038392328*i*x0*x1^2*x3 + 15451580055233230633532105873352215752416757672113754029661001878474871474452993752*i*x0*x1*x2^2 - 16016690804750551082627476655188051579250646433930651332860347211283558698345160*i*x0*x1*x2*x3 + 290883404430956696292441093343099632992348724624518459901907532384578313162039741586*i*x0*x1*x3^2 + 1014251480211347036168203212969486718072657248325104797246349005047104036642392487198*i*x0*x2^2*x3 + 550256933695862143215608021187549027621556161737633356220201846559419049843162240*i*x0*x2*x3^2 - 33235974864740586938149479803481344095213228861481409691157475888247856411880960*i*x0*x3^3 - 1913066913102043968449851698508038806380616734261524608924908140519469402693680*i*x1^4 - 142161698828332434972161146475710917012578943922037177154402884077475704317466755720*i*x1^3*x2 - 8212782851647642350519517046000736502027730603230002093767658332598879594144142052*i*x1^3*x3 - 13168413126628864135435722141011114759759416682289653375943630054254884730929339878*i*x1^2*x2^2 - 24034290142676142270323658836465327090452071888191422074786203397706354833224746000*i*x1^2*x2*x3 - 2633444750109020940554808473833757991276314446718747849256586494891999727118779542*i*x1^2*x3^2 - 9644291328897256716526398859143032464950853947563902332382792956041016358340800*i*x1*x2^3 + 566542979540851794659539052504180680756265665817173258200500427125932325084046264960*i*x1*x2^2*x3 + 3473276235170595702001756477553046567469602957745930155745523051230556264168920772*i*x1*x2*x3^2 - 13299116815094153301349484708458355153857538261132532476503484413316467926936400*i*x1*x3^3 + 637835050109938692076759564488944984014242285312024292548307847409714589035383284320*i*x2^4 - 5373959512117192136083623115125059745685039729565703804079621285189172632717734320*i*x2^3*x3 - 24026387609920339866223505671756991341869647101823165277989016388067069799032307120*i*x2^2*x3^2 + 351720588157368921517866060857497559818779321681586565548619287096430173259367491178*i*x2*x3^3 + 3901398226460887584096615532600641419480529322273381232064115429215772086777698452*i*x3^4 - 29801662101227020238475947239978218207458601945856135954681290052414431033719280*x0^2*x1^2 - 2187149688220851473831457126567644216853022530654233028144964844117866389684309480*x0^2*x1*x2 - 5722903803499320147810031483089795162859714856615373276306511534974133511586952026*x0^2*x1*x3 - 12907331071817634232667698077725225935162220465982914091785184693756586002168371718*x0^2*x2^2 - 4114377367915696079224075758392374378627989674476449052398453409803432001257986303400*x0^2*x2*x3 - 728206216862951638783329251618635134840246326508676461690303903059379321840822360*x0^2*x3^2 - 1265105508682511291787493273496730066095777162115213528647713459079257871772443960*x0*x1^2*x2 + 6919660544738469268387801553183196816109103692651022378123711947091065515187585176*x0*x1^2*x3 + 29998252653029087068537779485101087446609800569470558530323831154846282143578266904*x0*x1*x2^2 - 4039607593151464062287917057880441503948733388285700103364295869502917629010976864080*x0*x1*x2*x3 + 369988071769170260298115094704627485281608499610960967403451642975111088782769222602*x0*x1*x3^2 - 12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x0*x2^3 + 1377551208726320467942227364790506836618341873409895149210337131394227013130558602606*x0*x2^2*x3 - 550089078340858089989668622150034168800467530808540000479493193266647226041694800*x0*x2*x3^2 + 15202308228987283386813581307486229640549632163641993594852472125872828945161760*x0*x3^3 - 9933887367075673412825315746659406069152867315285378651560430017471477011239760*x1^4 + 424786227720687047862188163739285524012112517493035583003448756457951424618322813800*x1^3*x2 + 8192672706866427097317381171776251654415606163113461869850184478549216582622177936*x1^3*x3 + 2046445228491814675155673248984513049745270007721887829265654908060451089407297774*x1^2*x2^2 - 24924093543465330642372995027279044440716813045219144251696276183728744287479506360*x1^2*x2*x3 - 221501050159198825251888940404096633463569214183387295334103436187744831087526937094*x1^2*x3^2 + 3654825486196896584823085849315322688906684313568630144120691457275451568595600*x1*x2^3 - 142179194130006106659630766258712846247527443391802566738263627158069724050930734160*x1*x2^2*x3 + 4366477850646895007848491301623044183642106484589776708444853998253478699442642524*x1*x2*x3^2 - 5989465842700360131703313009827709776044169633995272188262101498765564789745200*x1*x3^3 + 283481017202460749618338695157613666204186649183718979150431973818392416048897013600*x2^4 + 5940225574414708271454311240078769413924563149271749000140908610453499226507429800*x2^3*x3 - 24927458772913349122261519196240843389801517716164991405521219238124589278395203000*x2^2*x3^2 + 274592239266770192316413197909127911855691070799290303676963364990964222631218806346*x2*x3^3 + 11663407822978150157789213295434114318546475383390342996211454275999784876001091544*x3^4,
    5739200739306131905349555095524116419141850202784573826774724421558408208081040*i*x0*x1^2 + 427330933142183553910351254075320846520497039633246797872056060645970708501607435320*i*x0*x1*x2 + 6468617078244088898000391598307437774461563977366911331264051416390887685772620478*i*x0*x1*x3 + 20837852112530198689942146972894796718614860446375477991453730877011419850032029874*i*x0*x2^2 + 72094621955643118086601966996891134203070238756577878964318328654434397242217755440*i*x0*x2*x3 + 686883618152728319323522876514597268469852193848985090394763238102216158866001920*i*x0*x3^2 - 283115789961656692265521498779793072970856718485633291569472255497937094820333160*i*x1^2*x3 + 24237748686503238360761605717869842099185503751663013003654866230945889961099112403560*i*x1*x2*x3 + 444283856027165303963069644475505135802239486305265125596248499836745589598061516806*i*x1*x3^2 + 266608815785486940576483236191359777531341956525509141376346942996400837605092440*i*x2*x3^2 + 29801662101227020238475947239978218207458601945856135954681290052414431033719280*x0*x1^2 + 2187149688220851473831457126567644216853022530654233028144964844117866389684309480*x0*x1*x2 + 5722903803499320147810031483089795162859714856615373276306511534974133511586952026*x0*x1*x3 + 12907331071817634232667698077725225935162220465982914091785184693756586002168371718*x0*x2^2 + 4114377367915696079224075758392374378627989674476449052398453409803432001257986303400*x0*x2*x3 + 728206216862951638783329251618635134840246326508676461690303903059379321840822360*x0*x3^2 + 54522407023408253100820773407479105981847576926453451354359882004804877976769880*x1^2*x3 + 4039568810776995640631616165983956984012332492349610139975941436240526100869394972520*x1*x2*x3 + 221945479717604934989022365492372612758219709068342086739889461036403743814707525482*x1*x3^2 + 12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x2^3 - 153802645689814852234095120003494287285833428946958466860519531059895861433179320*x2*x3^2,
    -70870607270793695121887710088980589669797294628977720537917232932302089345139058360*i*x0*x1*x2 - 5958112633125122181334861282081696090700003538755210827924305350131745915804514792*i*x0*x1*x3 - 3859057724439906417740845912448696033732087349220710383046912568581285710577504138*i*x0*x2^2 - 4776992687025433238550241271221688919022796013234751447933033857051578289171080*i*x0*x2*x3 + 70917499951568473188187635354341315678778098549339366519225045662801162210617692760*i*x0*x3^2 - 956533456551021984224925849254019403190308367130762304462454070259734701346840*i*x1^3 - 71292070569086897417220511984764303257976619494851034347807420283782263951337019360*i*x1^2*x2 - 4319002505724748754220879054906480137848437461680140922892404630205831457044010026*i*x1^2*x3 - 13168413126628864135435722141011114759759416682289653375943630054254884730929339878*i*x1*x2^2 - 24031064957565699286233619412742804671300021522113086490995618966014375076885028040*i*x1*x2*x3 - 2633444750109020940554808473833757991276314446718747849256586494891999727118779542*i*x1*x3^2 - 4677347645359420010113740985813329430374420289921213006602577947305277852720920*i*x2^3 + 212611388943215212063398060666667052449584324756532836343836510024698975682767277240*i*x2^2*x3 - 2174873616327543129463493426528308756336533297878493226081087629324376998674760*i*x2*x3^2 - 7375639675005294610711900985874632716090796236359080846260815334320994719969680*i*x3^3 + 158672917254878218009943425452746001936288634247221070582572227658063132100360*x0*x1*x2 - 1743545737940469380372155581647668980522737817394368957369517957273967598291088764*x0*x1*x3 - 7503260446347954491634197659286368116278438540050616897622961833068788739459607786*x0*x2^2 + 4116325871524403170899203170488470503428660583365488113099489615944696417981720*x0*x2*x3 - 73446807574738732810874713933812175592610010476216490608288383329416593322425142360*x0*x3^2 - 4966943683537836706412657873329703034576433657642689325780215008735738505619880*x1^3 - 437433446036432151173340082992407552545443062455873201022580927064188734293193280*x1^2*x2 + 398219092354755097965282145890196640341229210389512297986175709483504484410572378*x1^2*x3 + 2046445228491814675155673248984513049745270007721887829265654908060451089407297774*x1*x2^2 - 24924760480883703247660921036240782086515801340218553537681561000737573561527954240*x1*x2*x3 - 221501050159198825251888940404096633463569214183387295334103436187744831087526937094*x1*x3^2 + 2698292029645874600598160000061303285716375946437867839658237387015716867248760*x2^3 - 212611388943215212063398060666667052449584324756532836343836510024698975682767277240*x2^2*x3 + 74478412369246313584571164638591179121584132650403239583424586376926077931938120*x2*x3^2 - 1979055615713545409515580985752026144658044343483345166944340560289560985472160*x3^3,
    -6059419859267981821317385232106210595421455514138667961006947403519796596604239197260*i*x0*x1*x2 - 177176304666061519367259280970379848152235155804181660872663477909852090066819639800*i*x0*x2^2 - 6063429627871672087296573748056280749863479819354085096688895825431555245079606790500*i*x0*x3^2 + 4197667073794753713933622928605384038938973418719040177896519023686548756435359727*i*x1^3 + 1741758573094852616373234150807283882526067579307105535195783316755982165901920*i*x1^2*x2 - 29181125148510525348024883412367355219987341790082018780645934854612598196168305585*i*x1^2*x3 - 142092285171435663006191229234775825236610948191052078426621513449228109977856998300*i*x1*x2^2 + 996051294443362263262714672519710099885671514938123904386786906796322534899673227*i*x1*x2*x3 + 6269034371726398178279161569132727014409223027385445247152013991831783361443984794181*i*x1*x3^2 - 3472975352088366448323691162149132786435810074395912998575621812835236641672004979*i*x2^3 - 12014211210058733207763623252486584590701581652666339423050853916423297781085385600*i*x2^2*x3 - 246935284145133293169213298533379223823735911890088530667902137837760122686347747329*i*x2*x3^2 - 1320081921017491102832440232008039612514501582927989203676758003523440994831441586*i*x3^3 - 2407998934130065831202620974926755971962031349886683583792273500889719839598440*x0*x1*x2 - 47246836200410124936389782526268944367364441530619829858405328969732069341482835600*x0*x2^2 + 6279694446486047161688094634550287270053335620900428126011859348429055792652877090900*x0*x3^2 + 9695437774540497687112030978861981973323606607893740377368008241419648089257334899*x1^3 - 2019808484556582693018977875250224514644655287200429666742766022871701699446942032740*x1^2*x2 + 143485531638797982657150259579737344164491645745354360694184699621826462928711782215*x1^2*x3 - 364524948036808578971909521094607369475503755109038838024160807352977731614051580*x1*x2^2 - 115132137226357986449938922047116799285653099367081872173242363724676761903278232924691*x1*x2*x3 + 12637898417789011052913969769147320207646062509647192310222238804117804916562578410297*x1*x3^2 - 2151221845302939038777949679620870989193703410997152348630864115626097667028061953*x2^3 - 2705538655710503743097827735452066081810144603058452266622135632947674607768242600600*x2^2*x3 - 70581319424648398978204384223160643717551091428292476445421253252822387317285381253*x2*x3^2 - 5662494656345566946381024473435258923904974900327345486331986020095134973742676092*x3^3,
    -7674578736802481284361111778715808744204137615456248736675802074864316071488600*i*x0*x1*x2 + 212611388943215212063398060666667052449584324756532836343836510024698975682767277240*i*x2^3 + 7394566181365448999505576022192509251976795365954530084008088714436407130082120*x0*x1*x2,
    -724957872109181043154497808842769585445511099292831075360362543108125666224920*i*x3^3 + 24826137456415437861523721546197059707194710883467746527808195458975359310646040*x3^3,
    0,
    0]

theorem identity2 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x2^6 =
      ∑ k, numerator2 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator2 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k) -
      12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x2^6 = (i^2+1)*(425223643624762170731326260533883538018783767773866323227503397593812536070834350160*x0^2*x1^3*x2 + 35748675798750733088009167692490176544200021232531264967545832100790475494827088752*x0^2*x1^3*x3 + 23154346346639438506445075474692176202392524095324262298281475411487714263465024828*x0^2*x1^2*x2^2 + 28661956122152599431301447627330133514136776079408508687598203142309469735026480*x0^2*x1^2*x2*x3 - 425504999709410839129125812126047894072668591296036199115350273976806973263706156560*x0^2*x1^2*x3^2 + 46047472420814887706166670672294852465224825692737492420054812449185896428931600*x0^2*x1*x2*x3^2 + 421490272337830592971817833264973027362677335859408214788461056722875206414680840*x0*x1^4*x2 + 19445397956104403627324882731131443052629060792713934206090376364844101056491439678*x0*x1^4*x3 + 58172626647242986122672185873171891839941639647362442264208049448517888535544009394*x0*x1^3*x2^2 + 72091767789751077630799749479565693824729890376100639981655385141651853219092412800*x0*x1^3*x2*x3 + 15113784882501397324005327966487950679188034486463502005144755731249782203846675332*x0*x1^3*x3^2 + 28064085872156520060682445914879976582246521739527278039615467683831667116325520*x0*x1^2*x2^3 - 1275668333659291272380388364000002314697505948539197018063019060148193854096603663440*x0*x1^2*x2^2*x3 + 13049241697965258776780960559169852538019199787270959356486525775946261992048560*x0*x1^2*x2*x3^2 + 38514637310725635758921850819723679877402927215369911250790167584367560111737040*x0*x1^2*x3^3 - 427330933142183553910351254075320846520497039633246797872056060645970708501607435320*x0*x1*x2*x3^3 - 6468617078244088898000391598307437774461563977366911331264051416390887685772620478*x0*x1*x3^4 - 1275668333659291272380388364000002314697505948539197018063019060148193854096603663440*x0*x2^3*x3^2 - 20837852112530198689942146972894796718614860446375477991453730877011419850032029874*x0*x2^2*x3^3 - 72094621955643118086601966996891134203070238756577878964318328654434397242217755440*x0*x2*x3^4 - 686883618152728319323522876514597268469852193848985090394763238102216158866001920*x0*x3^5 + 283115789961656692265521498779793072970856718485633291569472255497937094820333160*x1^5*x3 - 24237748686503238360761605717869842099185503751663013003654866230945889961099112403560*x1^4*x2*x3 - 444283856027165303963069644475505135802239486305265125596248499836745589598061516806*x1^4*x3^2 - 266608815785486940576483236191359777531341956525509141376346942996400837605092440*x1^3*x2*x3^2 + 283115789961656692265521498779793072970856718485633291569472255497937094820333160*x1^2*x3^4 - 24237748686503238360761605717869842099185503751663013003654866230945889961099112403560*x1*x2*x3^4 - 444283856027165303963069644475505135802239486305265125596248499836745589598061516806*x1*x3^5 - 266608815785486940576483236191359777531341956525509141376346942996400837605092440*x2*x3^5) := by
    simp [Fin.sum_univ_succ, numerator2, generators]
    ring1
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def numerator3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![7002187416794957321026822660540659333597814467391058752959235504357325656692240*i*x0^2*x1^2 + 57966383794758055900476896081100280807540124306551839027577028882250349828862909820*i*x0^2*x1*x2 + 2011817216183565944540293944806527074937802718557448993529881938568179076121728198*i*x0^2*x1*x3 - 6145097113087349377077206495147919231734249491085960040065448275495891126067198006*i*x0^2*x2^2 + 1982417895529773693155464266320462767723437535702535497211098003372938855841158519900*i*x0^2*x2*x3 - 217949600091684311923252807914549668089955704901215870815490041035040685366220100*i*x0^2*x3^2 - 628958056183885588740211857251862020715241800284316155880288814160958903035522460*i*x0*x1^2*x2 + 5902867239356015558372817166793770915119386570218925159905527473532125716412897112*i*x0*x1^2*x3 + 14880225020770362937540417276984739168823194231356709231993540817010214144644074048*i*x0*x1*x2^2 - 19782898678809903930832049914477520020631726340985054107596401833966878435172480*i*x0*x1*x2*x3 + 246299665422145008713478199111970104553861525530639282452929896033252192931659004034*i*x0*x1*x3^2 + 636445415398748428964479034762549325623937231218489937303991349028469141762941434742*i*x0*x2^2*x3 + 1410946695086883749827468690492119594001348592867319745133786635038347069551378920*i*x0*x2*x3^2 - 135536034378167863082721652180843158644707014251905157376593807285713934953985400*i*x0*x3^3 + 2334062472264985773675607553513553111199271489130352917653078501452441885564080*i*x1^4 + 11592863419824095835961588951332334480393222541453789808080295638190378828067454700*i*x1^3*x2 + 1376552377627712564765782714952383713497903386694621135241149932488213083728495112*i*x1^3*x3 + 1218177839231588204603125085557886243011715470162504213061159877595825238224061118*i*x1^2*x2^2 + 660781060010999360508144066733599130224655898437082627606865873290197401880686226380*i*x1^2*x2*x3 - 213817753116223758348633804061830411536715623596131944876214783980967109399298466318*i*x1^2*x3^2 - 17750793406211025918410926970163623452361691628645314338038204747058750106305040*i*x1*x2^3 - 94710595472254565496498350890269856513272110411072584452803850107051717709478735200*i*x1*x2^2*x3 + 6287652591612080802472531305744870337592516655489291018905648662095185778970321068*i*x1*x2*x3^2 + 2823161276831789012130201243109214772319332003802949600980664289583837963197600*i*x1*x3^3 + 1864926508243340852453755185840617320155611419674286983376960443461707827578520*i*x2^4 + 6389831514189901925914083038592605575601545618170422737708407932700998927521677000*i*x2^3*x3 + 660817050696616349363219343181229053133221741880854590832225277285479650776976469980*i*x2^2*x3^2 - 1204869899521004302769926376523013083617817042499803869445629302488601604713480758*i*x2*x3^3 + 5446977593760465676727842021204451721989597729243786699821472171609695203691043408*i*x3^4 + 258894493537790171909180429534367833945383348385623830996874554156461967525840*x0^2*x1^2 + 1049258324563112591204414868220594609431151383044017862596343855689847114580053460*x0^2*x1*x2 + 9060594282216043078590116207456205970725270343310651010451551743373331852178126*x0^2*x1*x3 + 10773129276857889017532509953440653757424816649807023927135540795982705217259280178*x0^2*x2^2 + 35984782813307730460418022551462168061458562252906434922431844245255827432086608220*x0^2*x2*x3 + 203008448012200134737976311019191237689739302743440853641541502645094144256451500*x0^2*x3^2 + 34779451315968695988252310390671167906542639045613627022942497337054993683127222420*x0*x1^2*x2 - 8836160505326611671799775467909730884876143046057410362580659218268835489074590776*x0*x1^2*x3 - 7755466548049637850978805650756383884547872421085919879508875302781886111133902784*x0*x1*x2^2 + 25784030349661393796659668708685985719679052336642983795226427757031178070411640*x0*x1*x2*x3 - 80899940052326245288593237766564734034273358400573895957678215461366036553571549542*x0*x1*x3^2 - 348935602341581208574967083060236953496308202138789294655467883272017572459039279986*x0*x2^2*x3 + 1587002098830952798445045333147948273218852933344831410231219949620619466231988400*x0*x2*x3^2 - 9617756794441830287903362644071016316555795311324395038899030643210199974383600*x0*x3^3 + 86298164512596723969726809844789277981794449461874610332291518052153989175280*x1^4 + 211760660451650876906009372451100380111157800169683879705695763925251024346262580*x1^3*x2 + 6809153055114772199459216828946265939435694325306770602875397443335211919582181044*x1^3*x3 + 6702259640626944412510997954830732429911792100787906517171244034016635700125072046*x1^2*x2^2 + 11996792533101656751945312676289084460426195273262675671122176956862749000595261260*x1^2*x2*x3 + 109686437993915849686583568620944746047318238249761859112069257094138005676897704714*x1^2*x3^2 - 20573954683042814930541128213272838224681023632448263939018869036642588069502640*x1*x2^3 - 106095428084643497137258837979522771848194486375196038955145203902203768928855084360*x1*x2^2*x3 + 1355576608865439296150578323035714820699095792533662294756816746663932589464938236*x1*x2*x3^2 - 38324748089253840848952055183436461677042715261093578277057073783701338175807680*x1*x3^3 + 370653020701358386636736545494613806673814320369624050732306663929596009870200*x2^4 + 6419550492910689221187776533697250200059749168540728574901282522008953925562825720*x2^3*x3 + 11999529396213975944233473150722348885920532810817016746112825329634280684569283580*x2^2*x3^2 + 109688673573444794385822659112676081278445067675501903023103366361245396980735153434*x2*x3^3 + 4888682401766979860212556242482020288169362366600077862777743586283633203487829756*x3^4,
    -7002187416794957321026822660540659333597814467391058752959235504357325656692240*i*x0*x1^2 - 57966383794758055900476896081100280807540124306551839027577028882250349828862909820*i*x0*x1*x2 - 2011817216183565944540293944806527074937802718557448993529881938568179076121728198*i*x0*x1*x3 + 6145097113087349377077206495147919231734249491085960040065448275495891126067198006*i*x0*x2^2 - 1982417895529773693155464266320462767723437535702535497211098003372938855841158519900*i*x0*x2*x3 + 217949600091684311923252807914549668089955704901215870815490041035040685366220100*i*x0*x3^2 + 2459497688609006633137214080576494422481141809663426394470308264486388691495480*i*x1^2*x3 + 106300810969870428589864045592915187248869850921434358052486745277317346171975640*i*x1*x2*x3 + 294784259472623882114724603322979001957620318436451355904893139140994900289964105274*i*x1*x3^2 + 1014254721842637483982560051379903031207097564642446343662647978846835144750882760*i*x2*x3^2 + 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*i*x3^3 - 258894493537790171909180429534367833945383348385623830996874554156461967525840*x0*x1^2 - 1049258324563112591204414868220594609431151383044017862596343855689847114580053460*x0*x1*x2 - 9060594282216043078590116207456205970725270343310651010451551743373331852178126*x0*x1*x3 - 10773129276857889017532509953440653757424816649807023927135540795982705217259280178*x0*x2^2 - 35984782813307730460418022551462168061458562252906434922431844245255827432086608220*x0*x2*x3 - 203008448012200134737976311019191237689739302743440853641541502645094144256451500*x0*x3^2 - 66520780459552094549754815275136263669179237440215058153112737291394593738576280*x1^2*x3 + 21127222179977428038293983093192986980407416261068570891741479843986972562601400*x1*x2*x3 - 16114421419826545905423621004608487101566447138089142709387806184437861150048040582*x1*x3^2 + 1106194636473888356491089492881415515137639109609335986370962797797232926223074200*x2*x3^2 + 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x3^3,
    -347545277028071652636162215257470307335862020950731333104520360426862640157560*i*x0*x1*x2 - 1476331684261156141251488595218586852385466928007147146574999445449153026276098148*i*x0*x1*x3 - 3721899378693444529342270273942421318234876292483528533382048089912210455323580362*i*x0*x2^2 - 14182464426488428267894904923228202486599100336314421571908974350205743943288080*i*x0*x2*x3 - 72157801721527797668549563163142688688391749819467119073374532500610481432102581500*i*x0*x3^2 + 1167031236132492886837803776756776555599635744565176458826539250726220942782040*i*x1^3 + 11593234072844797194348225687877829094199896355774159432131027944854308424077324900*i*x1^2*x2 + 1093843229911457373442561293818901483645860454447443192971188420480531309166248786*i*x1^2*x3 + 1218177839231588204603125085557886243011715470162504213061159877595825238224061118*i*x1*x2^2 + 660799256754127882038938947390853967115130389292001214580582072934973565949875577300*i*x1*x2*x3 - 107512058644616152316934773728496885311923461217865526704296528968617621557914827698*i*x1*x3^2 - 17793942488467324280395790375086018091352588853376251643204350506084827100892680*i*x2^3 - 106305694471607606031699030333333526224792162378266418171918255012349487841383638620*i*x2^2*x3 + 22155686742309707719012058891249521356826053033929301287212186509480780506456400*i*x2*x3^2 + 1612980958442997763307534061430043577728799034506835836987979279831540025827920*i*x3^3 - 97347259128547853734063042771658391219390333568581828770244107122884081025920*x0*x1*x2 + 2225670321446540941587382570796216787136330570874406355183442988890057520703291764*x0*x1*x3 + 2040559800541450929986915956953716091818189630079314334484316534352274165639625166*x0*x2^2 - 15749688510554626637053420035259437358809894988036066646796390335776914575760600*x0*x2*x3 - 70893815873801427454356390208744962366118180520215112017325682363598984584160825380*x0*x3^2 + 43149082256298361984863404922394638990897224730937305166145759026076994587640*x1^3 + 209895733943407536053555617265259762791002188750009592722318803481789316518684060*x1^2*x2 + 1637499380156458478148258875911546606845864177298852078228149388230038230284565162*x1^2*x3 + 6702259640626944412510997954830732429911792100787906517171244034016635700125072046*x1*x2^2 + 11980122472767065622189769826285832824251451422929133658632632999848364317442562980*x1*x2*x3 + 3380743522308243654884538287611219822526075871495440940151002081788517835514066094*x1*x3^2 - 19406923446910322043703324436516061669081387887883087480192329785916367126720600*x2^3 - 106305694471607606031699030333333526224792162378266418171918255012349487841383638620*x2^2*x3 + 786376425236009325540868257650443705274547481988158798628870441576133742619400*x2*x3^2 - 37200865935377646324099114811602079760433976741259339123396680292001194227613280*x3^3,
    14821093893346720506665681411751282636295341173691720151809267795233009751645960*i*x0*x1*x2 - 310821084707223475408959197640102886692601903279047830562826740576951304596420*i*x0*x2^2 + 3139847522766999012689106646774784807030240335290971715452540557853878615932814010280*i*x0*x3^2 + 4906738094483962909588912962590623470340989325820069195981987234686184830581858683*i*x1^3 - 18239892210777829156865520659759285113481752143317911021365790535190146183938560*i*x1^2*x2 + 72955765929696083279215039263186759243811523444331985175880683114512000456068284805*i*x1^2*x3 + 9661063965793009316746149346850046801256687384425306504596171480375058304810484970*i*x1*x2^2 - 753544978500751674897348981623531927595854647081922132106011666714566469617421007*i*x1*x2*x3 + 6046217290202513705628971121817389806904110243982775250300096736502724912736933230409*i*x1*x3^2 - 1024182852181224896179534415857986538622374915180993340010908045915981854344533001*i*x2^3 + 330408913902458437967337509650202156626603373480040374952397402012325170915893384210*i*x2^2*x3 + 70756950654774977653997368912245086320147052953865457812632960184776655158474189629*i*x2*x3^2 - 2861398668827109147126715172854494586890611182072227813973208314230444274053808864*i*x3^3 + 16366941411780683850892404326556180816834429197330102309964698030051342762730840*x0*x1*x2 - 61775503450226397772789424249102301112302386728270675122051110654932668311700*x0*x2^2 + 3031713773647602496359192950029010820404686084595454821779195023751074383566304061120*x0*x3^2 - 2242360691412813100782659501415872781634090385343497553072067923511807092568594119*x1^3 + 17837091570723622642380653780008412730343486078107188948370496265110904095480320*x1^2*x2 + 15222233280681038266020501180718116000153131287633767075898832073525824127415740945*x1^2*x3 + 174876387427185431867402478036765768238525230507336310432723975948307852430008910*x1*x2^2 - 1035562083733291128375844304082262135928274638560192183095834886494682431704185419*x1*x2*x3 - 3314888039930694242798715974498508242566148612169013892365936447021131622333904714007*x1*x3^2 + 1795521546142981502922084992240108959570802774967837321189256799330450869543213363*x2^3 + 6003932776700258517417571533389200030799454171447033516232038150804610027723341570*x2^2*x3 + 16083748126727451531480304571887404408939542524125893355312001511544073730927515713*x2*x3^2 + 736332836591298830604196195150967675432423828077634563661544371824285504717020562*x3^3,
    3686247001707589914331909392473052058155469288702450767325771319313838325123700*i*x0*x1*x2 - 203386327058082934484429088529240241362443049615668729214195417313605275712298940*x0*x1*x2,
    7385228914103235906337352963749840452275351011309767095737395503160260168818800*i*x3^3 + 262125475078669775180289419216814568424849160662719599542956813858711247539800*x3^3,
    0,
    0]

theorem identity3 {R : Type*} [CommRing R] (i x0 x1 x2 x3 : R)
    (hi : i^2+1=0) :
    12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x3^6 =
      ∑ k, numerator3 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k := by
  have hh : (∑ k, numerator3 i x0 x1 x2 x3 k * generators i x0 x1 x2 x3 k) -
      12118849169763267087613689458000021989626306511122371671598681071407841613917734802680*x3^6 = (i^2+1)*(2085271662168429915816973291544821844015172125704387998627122162561175840945360*x0^2*x1^3*x2 + 8857990105566936847508931571311521114312801568042882879449996672694918157656588888*x0^2*x1^3*x3 + 22331396272160667176053621643654527909409257754901171200292288539473262731941482172*x0^2*x1^2*x2^2 + 85094786558930569607369429539369214919594602017886529431453846101234463659728480*x0^2*x1^2*x2*x3 + 432946810329166786011297378978856132130350498916802714440247195003662888592615489000*x0^2*x1^2*x3^2 - 22117482010245539485991456354838312348932815732214704603954627915883029950742200*x0^2*x1*x2*x3^2 - 11593020642310727265612458046166693757659253828093117565209138786875500715601039580*x0*x1^4*x2 - 4551242163285178296115073818106881826937360008127210164297248584315008778875764518*x0*x1^4*x3 - 13454164148476878604695957008495236689804542312060985318432407541070842555411564714*x0*x1^3*x2^2 - 1982377644994993599078169418024661034967344800049471790272394434236902539858094943900*x0*x1^3*x2*x3 + 644854402267605229589685389563066762203450811602291944354963683770670688662122746088*x0*x1^3*x3^2 + 106763654930803945682374742250516108548115533120257509859226103036508962605356080*x0*x1^2*x2^3 + 637834166829645636190194182000001157348752974269598509031509530074096927048301831720*x0*x1^2*x2^2*x3 - 132934120453858246314072353347497128140956318203575807723273119056884683038738400*x0*x1^2*x2*x3^2 - 2675698333863029258818381708039602132774979739649956268968640174631914498275280*x0*x1^2*x3^3 + 57966383794758055900476896081100280807540124306551839027577028882250349828862909820*x0*x1*x2*x3^3 + 2011817216183565944540293944806527074937802718557448993529881938568179076121728198*x0*x1*x3^4 - 6145097113087349377077206495147919231734249491085960040065448275495891126067198006*x0*x2^2*x3^3 + 1982417895529773693155464266320462767723437535702535497211098003372938855841158519900*x0*x2*x3^4 - 217949600091684311923252807914549668089955704901215870815490041035040685366220100*x0*x3^5 - 2459497688609006633137214080576494422481141809663426394470308264486388691495480*x1^5*x3 - 106300810969870428589864045592915187248869850921434358052486745277317346171975640*x1^4*x2*x3 - 294784259472623882114724603322979001957620318436451355904893139140994900289964105274*x1^4*x3^2 - 1014254721842637483982560051379903031207097564642446343662647978846835144750882760*x1^3*x2*x3^2 - 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x1^3*x3^3 - 2459497688609006633137214080576494422481141809663426394470308264486388691495480*x1^2*x3^4 - 106300810969870428589864045592915187248869850921434358052486745277317346171975640*x1*x2*x3^4 - 294784259472623882114724603322979001957620318436451355904893139140994900289964105274*x1*x3^5 - 1014254721842637483982560051379903031207097564642446343662647978846835144750882760*x2*x3^5 - 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340*x3^6) := by
    simp [Fin.sum_univ_succ, numerator3, generators]
    ring1
  rw [hi, zero_mul] at hh
  exact (sub_eq_zero.mp hh).symm

def denominator : Fin 4 → ℕ := ![621670727904138046969000177387915358039720247826119404514141842177482385037331220, 6059424584881633543806844729000010994813153255561185835799340535703920806958867401340, 12118849169763267087613689458000021989626306511122371671598681071407841613917734802680, 12118849169763267087613689458000021989626306511122371671598681071407841613917734802680]

def numerators {R : Type*} [CommRing R] (j : Fin 4) (i x0 x1 x2 x3 : R) : Fin 8 → R :=
  ![numerator0 i x0 x1 x2 x3, numerator1 i x0 x1 x2 x3,
    numerator2 i x0 x1 x2 x3, numerator3 i x0 x1 x2 x3] j

end CycleQ2SeedCurveGradientArithmetic

#print axioms CycleQ2SeedCurveGradientArithmetic.identity0
#print axioms CycleQ2SeedCurveGradientArithmetic.identity1
#print axioms CycleQ2SeedCurveGradientArithmetic.identity2
#print axioms CycleQ2SeedCurveGradientArithmetic.identity3
end


