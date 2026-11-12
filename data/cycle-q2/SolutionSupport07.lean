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

/-! Source partition of Solution.lean. See solution.md for verification status. -/

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


/- Component: continuation_20261111/SegreKodairaSpencer.lean -/
section
/-!
# The actual Segre transition cocycle and the Kodaira--Spencer contraction

The local derivations below may differ.  This retains the variation of the
surface coordinates, which a single global parameter derivation would lose.
All logarithmic forms are in the actual universal Kaehler module; all Segre
units are the previously constructed matrix-entry units, including the
degree twist.  The main identity identifies their contracted Chern cocycle
with an explicit Cech boundary.  It is a chain-level identity on overlap
rings, not an assumed Abel--Jacobi or global de Rham comparison.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace CycleQ2SegreKodairaSpencer

open CycleQ2SegreCech

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

/-- Evaluation of the actual universal logarithmic differential. -/
def logDerivative (D : Derivation K R R) (u : Rˣ) : R :=
  D.liftKaehlerDifferential (unitDlog K u)

theorem logDerivative_eq (D : Derivation K R R) (u : Rˣ) :
    logDerivative D u = (↑(u⁻¹) : R) * D (u : R) := by
  simp [logDerivative, unitDlog_apply, smul_eq_mul]

theorem logDerivative_mul (D : Derivation K R R) (u v : Rˣ) :
    logDerivative D (u * v) = logDerivative D u + logDerivative D v := by
  simp only [logDerivative, unitDlog_mul, map_add]

theorem logDerivative_inv (D : Derivation K R R) (u : Rˣ) :
    logDerivative D u⁻¹ = -logDerivative D u := by
  simp only [logDerivative, unitDlog_inv, map_neg]

theorem logDerivative_pow (D : Derivation K R R) (u : Rˣ) (n : ℕ) :
    logDerivative D (u ^ n) = n • logDerivative D u := by
  simp only [logDerivative, unitDlog_pow, map_nsmul]

theorem logDerivative_add (D E : Derivation K R R) (u : Rˣ) :
    logDerivative (D + E) u = logDerivative D u + logDerivative E u := by
  simp only [logDerivative_eq, Derivation.add_apply, mul_add]

theorem logDerivative_sub (D E : Derivation K R R) (u : Rˣ) :
    logDerivative (D - E) u = logDerivative D u - logDerivative E u := by
  simp only [logDerivative_eq, Derivation.sub_apply, mul_sub]

/-- The Cech boundary of the local logarithmic variations equals the
Kodaira--Spencer difference contracted against the actual Chern form.
The sign convention is delta(a) = a_qr - a_pr + a_pq. -/
theorem boundary_eq_contraction
    (Dp Dq : Derivation K R R) (gpq gqr gpr : Rˣ)
    (hg : gpq * gqr = gpr) :
    logDerivative Dq gqr - logDerivative Dp gpr + logDerivative Dp gpq =
      (Dq - Dp).liftKaehlerDifferential (unitDlog K gqr) := by
  change _ = logDerivative (Dq - Dp) gqr
  rw [← hg, logDerivative_mul, logDerivative_sub]
  abel

/-- On a quadruple overlap the contracted cochain is a genuine cocycle.
This uses both the transition cocycle and the additive cocycle of local
derivation differences; no commutativity of derivations is required. -/
theorem contraction_cocycle
    (Dp Dq Dr : Derivation K R R) (gqr grs gqs : Rˣ)
    (hg : gqr * grs = gqs) :
    logDerivative (Dr - Dq) grs - logDerivative (Dr - Dp) grs +
      logDerivative (Dq - Dp) gqs - logDerivative (Dq - Dp) gqr = 0 := by
  rw [← hg, logDerivative_mul]
  simp only [logDerivative_sub]
  abel

/-- The exact entrywise inverse rule works in overlap rings with zero
divisors as well; only the displayed element is assumed invertible. -/
theorem derivative_unit_inverse (D : Derivation K R R) (u : Rˣ) :
    D (↑(u⁻¹) : R) = -(↑(u⁻¹) : R)^2 * D (u : R) := by
  have h := congrArg D u.mul_inv
  simp only [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul] at h
  linear_combination (↑(u⁻¹) : R) * h - D (↑(u⁻¹) : R) * u.inv_mul

/-- An explicit matrix-entry formula for the contraction. -/
theorem transition_logDerivative_entries
    (D : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2) :
    logDerivative D (transition M hM p q up uq hp hq) =
      (↑((transition M hM p q up uq hp hq)⁻¹) : R) *
        (D (M q.1 p.2) * (↑(up⁻¹) : R) -
          M q.1 p.2 * (↑(up⁻¹) : R)^2 * D (M p.1 p.2)) := by
  rw [logDerivative_eq]
  change _ * D (M q.1 p.2 * (↑(up⁻¹) : R)) = _
  rw [Derivation.leibniz, derivative_unit_inverse D up, hp]
  simp only [smul_eq_mul]
  ring

/-- The obstruction identity for the literal Segre image line. -/
theorem segre_boundary_eq_contraction
    (Dp Dq : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) :
    logDerivative Dq (transition M hM q r uq ur hq hr) -
        logDerivative Dp (transition M hM p r up ur hp hr) +
        logDerivative Dp (transition M hM p q up uq hp hq) =
      (Dq - Dp).liftKaehlerDifferential
        (unitDlog K (transition M hM q r uq ur hq hr)) :=
  boundary_eq_contraction Dp Dq _ _ _ (transition_cocycle M hM p q r up uq ur hp hq hr)

/-- The homogeneous divisor bundle includes O(d).  Its logarithmic
variation retains the coordinate-trivialization terms. -/
theorem twisted_logDerivative
    (D : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q : Chart) (up uq : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (xp xq : Rˣ) (d : ℕ) :
    logDerivative D (twistedTransition M hM p q up uq hp hq xp xq d) =
      d • (logDerivative D xp - logDerivative D xq) +
        logDerivative D (transition M hM p q up uq hp hq) := by
  simp only [twistedTransition, logDerivative_mul, logDerivative_pow,
    logDerivative_inv, sub_eq_add_neg]

/-- The actual degree-twisted Chern cocycle satisfies the same obstruction
identity.  This is the cocycle appropriate to the degree-fourteen entries,
not the untwisted image-line class. -/
theorem twisted_boundary_eq_contraction
    (Dp Dq : Derivation K R R)
    (M : Matrix (Fin 3) (Fin 3) R) (hM : CycleQ2SegreLocal.cofactors M = 0)
    (p q r : Chart) (up uq ur : Rˣ)
    (hp : (up : R) = M p.1 p.2) (hq : (uq : R) = M q.1 q.2)
    (hr : (ur : R) = M r.1 r.2) (xp xq xr : Rˣ) (d : ℕ) :
    logDerivative Dq (twistedTransition M hM q r uq ur hq hr xq xr d) -
        logDerivative Dp (twistedTransition M hM p r up ur hp hr xp xr d) +
        logDerivative Dp (twistedTransition M hM p q up uq hp hq xp xq d) =
      (Dq - Dp).liftKaehlerDifferential
        (unitDlog K (twistedTransition M hM q r uq ur hq hr xq xr d)) :=
  boundary_eq_contraction Dp Dq _ _ _
    (twistedTransition_cocycle M hM p q r up uq ur hp hq hr xp xq xr d)

/-- Changing local derivation lifts changes the contracted cochain by the
explicit Cech boundary of their difference, with the same transition units. -/
theorem change_lifts_boundary
    (Dp Dq Ep Eq : Derivation K R R) (gpq gqr gpr : Rˣ)
    (hg : gpq * gqr = gpr) :
    logDerivative ((Dq + Eq) - (Dp + Ep)) gqr - logDerivative (Dq - Dp) gqr =
      logDerivative Eq gqr - logDerivative Ep gpr + logDerivative Ep gpq := by
  rw [← hg, logDerivative_mul]
  simp only [logDerivative_sub, logDerivative_add]
  abel

/-- The contraction is compatible with a restriction map whenever the
local derivations are compatible with that restriction. -/
theorem logDerivative_natural
    {S : Type*} [CommRing S] [Algebra K S]
    (f : R →ₐ[K] S) (D : Derivation K R R) (E : Derivation K S S)
    (hDE : ∀ x : R, E (f x) = f (D x)) (u : Rˣ) :
    f (logDerivative D u) =
      logDerivative E (Units.map f.toMonoidHom u) := by
  simp only [logDerivative_eq, Units.coe_map, Units.coe_map_inv, map_mul]
  change f (↑(u⁻¹) : R) * f (D (u : R)) =
    f (↑(u⁻¹) : R) * E (f (u : R))
  rw [hDE]

end CycleQ2SegreKodairaSpencer

#print axioms CycleQ2SegreKodairaSpencer.boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.contraction_cocycle
#print axioms CycleQ2SegreKodairaSpencer.segre_boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.twisted_boundary_eq_contraction
#print axioms CycleQ2SegreKodairaSpencer.change_lifts_boundary
#print axioms CycleQ2SegreKodairaSpencer.logDerivative_natural
end
end


/- Component: continuation_20261111/PolynomialCoefficientDerivation.lean -/
section
/-!
# The actual coefficient motion on a multivariate polynomial ring

This extends a derivation of the coefficient ring while holding every
polynomial coordinate fixed.  The construction uses the actual polynomial
evaluation into dual numbers, not a postulated coefficient operator.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2PolynomialCoefficientDerivation

open MvPolynomial CycleQ2LocalizationDerivation

variable {K A : Type*} {σ : Type*} [CommRing K] [CommRing A] [Algebra K A]

abbrev Poly := MvPolynomial σ A

def polynomialGraph (D : Derivation K A A) : Poly (σ := σ) (A := A) →ₐ[K]
    Jet (Poly (σ := σ) (A := A)) where
  __ := eval₂Hom (graph (S := Poly (σ := σ) (A := A)) D).toRingHom
    (fun j => TrivSqZeroExt.inl (X j))
  commutes' k := by
    change eval₂Hom _ _ (C (algebraMap K A k)) = _
    rw [eval₂Hom_C]
    exact (graph (S := Poly (σ := σ) (A := A)) D).commutes k

@[simp] theorem polynomialGraph_C (D : Derivation K A A) (a : A) :
    polynomialGraph (σ := σ) D (C a) =
      graph (S := Poly (σ := σ) (A := A)) D a :=
  eval₂Hom_C _ _ _

@[simp] theorem polynomialGraph_X (D : Derivation K A A) (j : σ) :
    polynomialGraph D (X j) = TrivSqZeroExt.inl (X j) := by
  exact eval₂Hom_X' (graph (S := Poly (σ := σ) (A := A)) D).toRingHom
    (fun k => TrivSqZeroExt.inl (X k)) j

theorem polynomialGraph_fst (D : Derivation K A A) (p : Poly (σ := σ) (A := A)) :
    (polynomialGraph D p).fst = p := by
  induction p using MvPolynomial.induction_on with
  | C a => rw [polynomialGraph_C, graph_fst]; rfl
  | add p q hp hq =>
      rw [map_add, TrivSqZeroExt.fst_add, hp, hq]
  | mul_X p j hp =>
      rw [map_mul, TrivSqZeroExt.fst_mul, hp, polynomialGraph_X]
      rfl

def coefficientDerivation (D : Derivation K A A) :
    Derivation K (Poly (σ := σ) (A := A)) (Poly (σ := σ) (A := A)) where
  toLinearMap := (TrivSqZeroExt.sndHom _ _).restrictScalars K |>.comp
    (polynomialGraph D).toLinearMap
  map_one_eq_zero' := by simp
  leibniz' p q := by
    change (polynomialGraph D (p * q)).snd =
      p * (polynomialGraph D q).snd + q * (polynomialGraph D p).snd
    rw [map_mul, TrivSqZeroExt.snd_mul]
    simp only [polynomialGraph_fst, smul_eq_mul, op_smul_eq_smul]

@[simp] theorem coefficientDerivation_C (D : Derivation K A A) (a : A) :
    coefficientDerivation (σ := σ) D (C a) = C (D a) := by
  change (polynomialGraph D (C a)).snd = _
  rw [polynomialGraph_C, graph_snd]
  rfl

@[simp] theorem coefficientDerivation_X (D : Derivation K A A) (j : σ) :
    coefficientDerivation D (X j) = 0 := by
  change (polynomialGraph D (X j)).snd = 0
  rw [polynomialGraph_X]
  rfl

theorem coefficientDerivation_monomial (D : Derivation K A A)
    (e : σ →₀ ℕ) (a : A) :
    coefficientDerivation D (monomial e a) = monomial e (D a) := by
  classical
  rw [MvPolynomial.monomial_eq]
  rw [Derivation.leibniz, coefficientDerivation_C]
  have hz' (s : Finset σ) :
      coefficientDerivation D (∏ j ∈ s, (X j : Poly (A := A)) ^ e j) = 0 := by
    induction s using Finset.induction_on with
    | empty => simp [Derivation.map_one_eq_zero]
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, Derivation.leibniz, ih,
          Derivation.leibniz_pow, coefficientDerivation_X]
        simp
  have hz : coefficientDerivation D (e.prod fun j n => (X j : Poly (A := A)) ^ n) = 0 :=
    hz' e.support
  rw [hz, smul_zero, zero_add]
  simpa only [smul_eq_mul, mul_comm] using
    (MvPolynomial.monomial_eq (s := e) (a := D a)).symm

/-- Uniqueness follows from the genuine polynomial induction principle. -/
theorem coefficientDerivation_unique (D : Derivation K A A)
    (E : Derivation K (Poly (σ := σ) (A := A)) (Poly (σ := σ) (A := A)))
    (hC : ∀ a : A, E (C a) = C (D a)) (hX : ∀ j : σ, E (X j) = 0) :
    E = coefficientDerivation D := by
  apply Derivation.ext
  intro p
  induction p using MvPolynomial.induction_on with
  | C a => rw [hC, coefficientDerivation_C]
  | add p q hp hq => rw [map_add, map_add, hp, hq]
  | mul_X p j hp =>
      rw [Derivation.leibniz, Derivation.leibniz, hX, coefficientDerivation_X, hp]

end CycleQ2PolynomialCoefficientDerivation

#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_C
#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_monomial
#print axioms CycleQ2PolynomialCoefficientDerivation.coefficientDerivation_unique
end
end


/- Component: continuation_20261111/RelativeKodairaSpencer.lean -/
section
/-!
# The overlap correction is a genuine relative derivation

Two local lifts of the same coefficient motion have a difference which
annihilates the coefficient ring.  Thus the preceding Cech identity lives
in the actual relative Kaehler module of the surface, not just in absolute
differentials over the complex constants.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2RelativeKodairaSpencer

open CycleQ2SegreCech CycleQ2SegreKodairaSpencer

variable {K A R : Type*} [CommRing K] [CommRing A] [CommRing R]
  [Algebra K A] [Algebra A R] [Algebra K R] [IsScalarTower K A R]

/-- The Kodaira--Spencer difference is linear over the coefficient ring
because the two actual local lifts induce the same coefficient motion. -/
def relativeDifference (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) :
    Derivation A R R where
  toFun x := Dq x - Dp x
  map_add' x y := by simp only [map_add]; abel
  map_smul' a x := by
    simp only [RingHom.id_apply, Algebra.smul_def]
    simp only [Derivation.leibniz, h, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    change Dq 1 - Dp 1 = 0
    simp only [Derivation.map_one_eq_zero, sub_self]
  leibniz' x y := by
    change Dq (x * y) - Dp (x * y) =
      x * (Dq y - Dp y) + y * (Dq x - Dp x)
    simp only [Derivation.leibniz, smul_eq_mul]
    ring

theorem relativeDifference_coefficients (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) (a : A) :
    relativeDifference Dp Dq h (algebraMap A R a) = 0 := by
  simp [relativeDifference, h]

/-- The absolute and relative evaluations are the same actual scalar. -/
theorem contraction_eq_relative (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a)) (u : Rˣ) :
    (Dq - Dp).liftKaehlerDifferential (unitDlog K u) =
      (relativeDifference Dp Dq h).liftKaehlerDifferential (unitDlog A u) := by
  rw [unitDlog_apply, unitDlog_apply]
  rfl

/-- The Cech boundary is identified with the contraction against the
relative Chern form over the actual coefficient ring. -/
theorem boundary_eq_relative_contraction
    (Dp Dq : Derivation K R R)
    (h : ∀ a : A, Dp (algebraMap A R a) = Dq (algebraMap A R a))
    (gpq gqr gpr : Rˣ) (hg : gpq * gqr = gpr) :
    logDerivative Dq gqr - logDerivative Dp gpr + logDerivative Dp gpq =
      (relativeDifference Dp Dq h).liftKaehlerDifferential (unitDlog A gqr) := by
  rw [boundary_eq_contraction Dp Dq gpq gqr gpr hg,
    contraction_eq_relative Dp Dq h gqr]

end CycleQ2RelativeKodairaSpencer

#print axioms CycleQ2RelativeKodairaSpencer.contraction_eq_relative
#print axioms CycleQ2RelativeKodairaSpencer.boundary_eq_relative_contraction
end
end


/- Component: continuation_20261111/SeedConormalBasis.lean -/
section
/-! # Actual conormal bases on a literal seed Jacobian open

The cotangent module is the genuine ideal quotient I/I², then base changed
to the chosen localization of the actual curve.  Its coordinate functionals
are induced by genuine polynomial partial derivations.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ConormalJacobian

section LiteralSeed
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting

abbrev P := WeightedPoly

def firstPivot (r : ℂ) : P := -C r * X 3
def secondPivot : P := 3*X 2^2+X 1*X 3+X 0*X 3
def crossPartial : P := X 2*X 3+2*X 0*X 1-3*C Complex.I*X 1^2
def jacobianMinor (r : ℂ) : P := firstPivot r*secondPivot

theorem firstPivot_is_partial (r : ℂ) : pderiv 1 (originalF1 r)=firstPivot r := by
  simp [originalF1,firstPivot] <;> ring

theorem secondPivot_is_partial (θ : ℂ) : pderiv 2 (thetaH θ)=secondPivot := by
  simp [thetaH,originalH,originalB,secondPivot] <;> ring

theorem crossPartial_is_partial (θ : ℂ) : pderiv 1 (thetaH θ)=crossPartial := by
  simp [thetaH,originalH,originalB,crossPartial] <;> ring

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

def mappedPartial (j : Fin 5) : Derivation ℂ P S :=
  (Algebra.linearMap P S).compDer (pderiv j)

@[simp] theorem mappedPartial_apply (j : Fin 5) (p : P) :
    mappedPartial (S := S) j p=algebraMap P S (pderiv j p) := rfl

/-- The same binding applies on any actual unit Jacobian-minor chart. -/
def seedConormalBasisOnMinor (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (c : Fin 3 → Fin 5)
    (hc : IsUnit (derivationMatrix (curveEquations r θ)
      (fun i => mappedPartial (S := S) (c i))).det) :
    Module.Basis (Fin 3) S (S ⊗[P] (ambientCurveIdeal r θ).Cotangent) :=
  conormalBasisOfJacobian (ambientCurveIdeal r θ) hI (curveEquations r θ) rfl
    (fun i => mappedPartial (c i)) hc

/-- Duals to (f1,f2,h), with the actual triangular Jacobian inverted. -/
def seedDualDerivations (u v : Sˣ) : Fin 3 → Derivation ℂ P S := ![
    (↑(u⁻¹):S) • mappedPartial 1 -
      ((↑(u⁻¹):S)*(↑(v⁻¹):S)*algebraMap P S crossPartial) • mappedPartial 2 +
      (2*algebraMap P S (X 2)*(↑(u⁻¹):S)*(↑(v⁻¹):S)*
        algebraMap P S crossPartial) • mappedPartial 4,
    mappedPartial 4,
    (↑(v⁻¹):S) • mappedPartial 2 -
      (2*algebraMap P S (X 2)*(↑(v⁻¹):S)) • mappedPartial 4]

theorem seedDualDerivations_equations (r θ : ℂ) (u v : Sˣ)
    (hu : (u:S)=algebraMap P S (firstPivot r))
    (hv : (v:S)=algebraMap P S secondPivot) (i j : Fin 3) :
    seedDualDerivations u v i (curveEquations r θ j)=if i=j then 1 else 0 := by
  have hf11 := congrArg (algebraMap P S) (firstPivot_is_partial r)
  have hh1 := congrArg (algebraMap P S) (crossPartial_is_partial θ)
  have hh2 := congrArg (algebraMap P S) (secondPivot_is_partial θ)
  rw [←hu] at hf11
  rw [←hv] at hh2
  fin_cases i <;> fin_cases j <;>
    simp [seedDualDerivations,curveEquations,Derivation.add_apply,
      Derivation.sub_apply,Derivation.smul_apply,mappedPartial_apply,
      hf11,hh1,hh2,smul_eq_mul]
  all_goals try simp [originalF1,originalF2,thetaH,originalH,originalB,
    map_ofNat,mul_assoc,mul_left_comm,mul_comm]
  all_goals ring_nf <;> simp [mul_assoc]

/-- The actual conormal relation after any scalar extension, with no
independent equation-normal presentation supplied as a hypothesis. -/
theorem baseChangedConormal_relation (r θ : ℂ) :
    (1:S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩ =
      algebraMap P S (originalG1 r) • ((1:S) ⊗ₜ[P] conormalGenerator r θ 0)+
      algebraMap P S originalG2 • ((1:S) ⊗ₜ[P] conormalGenerator r θ 1)+
      algebraMap P S (thetaK θ) • ((1:S) ⊗ₜ[P] conormalGenerator r θ 2) := by
  rw [actual_conormal_relation]
  simp only [TensorProduct.tmul_add,TensorProduct.tmul_smul,algebraMap_smul]

/-- Literal evaluation of the actual two conormal equation classes is the
checked equationMap, on every scalar extension including all prime charts. -/
theorem baseChangedNormalMap_eq (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ![φ ((1:S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
          ⟨actualSeedEquation r θ,actualSeedEquation_mem r θ⟩),
      φ ((1:S) ⊗ₜ[P] conormalGenerator r θ 2)] =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (fun i => φ ((1:S) ⊗ₜ[P] conormalGenerator r θ i)) := by
  ext i
  fin_cases i
  · simp only [Matrix.cons_val_zero,baseChangedConormal_relation,
      map_add,map_smul,smul_eq_mul]
    rfl
  · rfl

def surfaceEquations (r θ : ℂ) : Fin 2 → P := ![actualSeedEquation r θ,thetaH θ]
def surfaceIdeal (r θ : ℂ) : Ideal P := Ideal.span (Set.range (surfaceEquations r θ))

theorem surfaceIdeal_le_curveIdeal (r θ : ℂ) : surfaceIdeal r θ≤ambientCurveIdeal r θ := by
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact actualSeedEquation_mem r θ
  · exact curveEquation_mem r θ 2

theorem sourceDual_F (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (i : Fin 3) :
    d i (actualSeedEquation r θ)=
      ![algebraMap P S (originalG1 r),algebraMap P S originalG2,
        algebraMap P S (thetaK θ)] i := by
  have hf1 : algebraMap P S (originalF1 r)=0 := hI _ (curveEquation_mem r θ 0)
  have hf2 : algebraMap P S originalF2=0 := hI _ (curveEquation_mem r θ 1)
  have hh : algebraMap P S (thetaH θ)=0 := hI _ (curveEquation_mem r θ 2)
  have hd0 : d i (originalF1 r)=if i=0 then 1 else 0 := hd i 0
  have hd1 : d i originalF2=if i=1 then 1 else 0 := hd i 1
  have hd2 : d i (thetaH θ)=if i=2 then 1 else 0 := hd i 2
  simp only [actualSeedEquation,map_add,Derivation.leibniz,Algebra.smul_def,
    hf1,hf2,hh,zero_mul,zero_add,hd0,hd1,hd2]
  fin_cases i <;> simp

def surfaceDualDerivations (d : Fin 3 → Derivation ℂ P S) (u : Sˣ) (k : S) :
    Fin 2 → Derivation ℂ P S :=
  ![(↑(u⁻¹):S) • d 0,d 2-(k*(↑(u⁻¹):S)) • d 0]

theorem surfaceDualDerivations_equations (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (u : Sˣ) (hu : (u:S)=algebraMap P S (originalG1 r)) (i j : Fin 2) :
    surfaceDualDerivations d u (algebraMap P S (thetaK θ)) i
      (surfaceEquations r θ j)=if i=j then 1 else 0 := by
  have hF0 := sourceDual_F r θ hI d hd 0
  have hF2 := sourceDual_F r θ hI d hd 2
  have hh0 : d 0 (thetaH θ)=0 := by simpa [curveEquations] using hd 0 2
  have hh2 : d 2 (thetaH θ)=1 := by simpa [curveEquations] using hd 2 2
  simp only [Matrix.cons_val_zero,Matrix.cons_val_two] at hF0 hF2
  rw [←hu] at hF0
  fin_cases i <;> fin_cases j <;>
    simp [surfaceDualDerivations,surfaceEquations,Derivation.smul_apply,
      Derivation.sub_apply,hF0,hF2,hh0,hh2,smul_eq_mul,mul_assoc]

/-- The target two-equation conormal module also has its actual equation
classes as a basis on every g1-unit chart. Together with the source basis,
this removes both normal-presentation assumptions. -/
def surfaceConormalBasisOnFirstOpen (r θ : ℂ)
    (hI : ∀ p∈ambientCurveIdeal r θ, algebraMap P S p=0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j)=if i=j then 1 else 0)
    (u : Sˣ) (hu : (u:S)=algebraMap P S (originalG1 r)) :
    Module.Basis (Fin 2) S (S ⊗[P] (surfaceIdeal r θ).Cotangent) :=
  conormalBasis (surfaceIdeal r θ)
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (surfaceEquations r θ) rfl
    (surfaceDualDerivations d u (algebraMap P S (thetaK θ)))
    (surfaceDualDerivations_equations r θ hI d hd u hu)

end LiteralSeed

section ActualLocalization
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting

abbrev ActualCurve (r θ : ℂ) := P ⧸ ambientCurveIdeal r θ
abbrev ActualLocalCurve (r θ : ℂ) :=
  Localization.Away (Ideal.Quotient.mk (ambientCurveIdeal r θ) (jacobianMinor r))

def actualLocalMap (r θ : ℂ) : P →+* ActualLocalCurve r θ :=
  (algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)).comp
    (Ideal.Quotient.mk (ambientCurveIdeal r θ))

instance localScalarTower (r θ : ℂ) : IsScalarTower ℂ P (ActualLocalCurve r θ) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := P) (A := ActualLocalCurve r θ)
    fun _ => rfl

theorem actualLocalMap_ideal (r θ : ℂ) (p : P) (hp : p∈ambientCurveIdeal r θ) :
    algebraMap P (ActualLocalCurve r θ) p=0 := by
  change algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)
    (Ideal.Quotient.mk (ambientCurveIdeal r θ) p)=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]

theorem actualLocalMap_minor_unit (r θ : ℂ) :
    IsUnit (algebraMap P (ActualLocalCurve r θ) (jacobianMinor r)) := by
  change IsUnit (algebraMap (ActualCurve r θ) (ActualLocalCurve r θ)
    (Ideal.Quotient.mk (ambientCurveIdeal r θ) (jacobianMinor r)))
  exact IsLocalization.Away.algebraMap_isUnit (S := ActualLocalCurve r θ) _

def actualFirstUnit (r θ : ℂ) : (ActualLocalCurve r θ)ˣ :=
  (isUnit_of_mul_isUnit_left (x := algebraMap P (ActualLocalCurve r θ) (firstPivot r))
    (y := algebraMap P (ActualLocalCurve r θ) secondPivot) (by
    rw [← map_mul]
    exact actualLocalMap_minor_unit r θ)).unit

def actualSecondUnit (r θ : ℂ) : (ActualLocalCurve r θ)ˣ :=
  (isUnit_of_mul_isUnit_right (x := algebraMap P (ActualLocalCurve r θ) (firstPivot r))
    (y := algebraMap P (ActualLocalCurve r θ) secondPivot) (by
    rw [← map_mul]
    exact actualLocalMap_minor_unit r θ)).unit

@[simp] theorem actualFirstUnit_value (r θ : ℂ) :
    (actualFirstUnit r θ : ActualLocalCurve r θ)=
      algebraMap P (ActualLocalCurve r θ) (firstPivot r) := IsUnit.unit_spec _

@[simp] theorem actualSecondUnit_value (r θ : ℂ) :
    (actualSecondUnit r θ : ActualLocalCurve r θ)=
      algebraMap P (ActualLocalCurve r θ) secondPivot := IsUnit.unit_spec _

/-- The genuine localized conormal module of the actual seed curve. -/
abbrev ActualConormal (r θ : ℂ) :=
  ActualLocalCurve r θ ⊗[P] (ambientCurveIdeal r θ).Cotangent

/-- A basis of the actual conormal module on the literal Jacobian open. -/
def actualConormalBasis (r θ : ℂ) :
    Module.Basis (Fin 3) (ActualLocalCurve r θ) (ActualConormal r θ) :=
  conormalBasis (ambientCurveIdeal r θ) (actualLocalMap_ideal r θ)
    (curveEquations r θ) rfl
    (seedDualDerivations (actualFirstUnit r θ) (actualSecondUnit r θ))
    (seedDualDerivations_equations r θ _ _
      (actualFirstUnit_value r θ) (actualSecondUnit_value r θ))

@[simp] theorem actualConormalBasis_apply (r θ : ℂ) (i : Fin 3) :
    actualConormalBasis r θ i=(1:ActualLocalCurve r θ) ⊗ₜ[P] conormalGenerator r θ i := by
  exact conormalBasis_apply _ _ _ _ _ _ _

/-- Coordinates in this proved basis identify the actual normal module with
three scalar normal coordinates; no presentation is assumed. -/
def actualNormalCoordinates (r θ : ℂ) :
    (ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) ≃ₗ[ActualLocalCurve r θ]
      (Fin 3 → ActualLocalCurve r θ) :=
  (actualConormalBasis r θ).constr (ActualLocalCurve r θ) |>.symm

def localConormalClass (r θ : ℂ) (p : P) (hp : p∈ambientCurveIdeal r θ) :
    ActualConormal r θ :=
  (1:ActualLocalCurve r θ) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent ⟨p,hp⟩

theorem localConormalClass_equation (r θ : ℂ) :
    localConormalClass r θ (actualSeedEquation r θ) (actualSeedEquation_mem r θ)=
      algebraMap P (ActualLocalCurve r θ) (originalG1 r) • actualConormalBasis r θ 0+
      algebraMap P (ActualLocalCurve r θ) originalG2 • actualConormalBasis r θ 1+
      algebraMap P (ActualLocalCurve r θ) (thetaK θ) • actualConormalBasis r θ 2 := by
  simpa only [localConormalClass,actualConormalBasis_apply] using
    (baseChangedConormal_relation (S := ActualLocalCurve r θ) r θ)

theorem localConormalClass_section (r θ : ℂ) :
    localConormalClass r θ (thetaH θ) (curveEquation_mem r θ 2)=
      actualConormalBasis r θ 2 := by
  rw [actualConormalBasis_apply]
  rfl

/-- Evaluate an actual normal homomorphism on the two actual equation
classes. Identifying the target with the full two-equation normal module
additionally uses its conormal basis, as constructed on a g1-unit chart. -/
def actualEquationNormalMap (r θ : ℂ) :
    (ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) →ₗ[ActualLocalCurve r θ]
      (Fin 2 → ActualLocalCurve r θ) where
  toFun φ := ![
    φ (localConormalClass r θ (actualSeedEquation r θ) (actualSeedEquation_mem r θ)),
    φ (localConormalClass r θ (thetaH θ) (curveEquation_mem r θ 2))]
  map_add' φ ψ := by ext i; fin_cases i <;> rfl
  map_smul' c φ := by ext i; fin_cases i <;> rfl

/-- The previously checked equation-normal matrix is exactly evaluation
on the actual (F,h) classes, in the proved source conormal basis. -/
theorem actualEquationNormalMap_eq (r θ : ℂ)
    (φ : ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) :
    actualEquationNormalMap r θ φ=
      equationMap
        (algebraMap P (ActualLocalCurve r θ) (originalG1 r))
        (algebraMap P (ActualLocalCurve r θ) originalG2)
        (algebraMap P (ActualLocalCurve r θ) (thetaK θ))
        (actualNormalCoordinates r θ φ) := by
  ext i
  fin_cases i
  · change φ (localConormalClass r θ (actualSeedEquation r θ) _) = _
    rw [localConormalClass_equation,map_add,map_add,map_smul,map_smul,map_smul]
    rfl
  · change φ (localConormalClass r θ (thetaH θ) _)=_
    rw [localConormalClass_section]
    rfl

/-- The explicit Jacobian open contains an actual complex point for every
nonzero r, including r=57.  Its conormal basis is not vacuous. -/
theorem exists_point_in_jacobian_open (r θ : ℂ) (hr : r≠0) :
    ∃ x : Fin 5 → ℂ,
      (∀ i : Fin 3, eval x (curveEquations r θ i)=0) ∧
      eval x (jacobianMinor r)≠0 := by
  let c : ℂ := (Complex.I-1)^((3:ℂ)⁻¹)
  have hc : c^3=Complex.I-1 := Complex.cpow_nat_inv_pow _ (by norm_num)
  have hi : Complex.I-1≠0 := by
    intro hh
    have him := congrArg Complex.im hh
    norm_num at him
  have hc0 : c≠0 := by
    intro hh
    apply hi
    simpa [hh] using hc.symm
  refine ⟨![0,0,c,1,-c^2],?_,?_⟩
  · intro j
    fin_cases j <;>
      simp [curveEquations,originalF1,originalF2,thetaH,originalH,originalB,hc] <;> ring
  · have he : eval ![0,0,c,1,-c^2] (jacobianMinor r)= -3*r*c^2 := by
      simp [jacobianMinor,firstPivot,secondPivot] <;> ring
    rw [he]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hr) (pow_ne_zero _ hc0)

end ActualLocalization
end CycleQ2ConormalJacobian

#print axioms CycleQ2ConormalJacobian.actualConormalBasis
#print axioms CycleQ2ConormalJacobian.surfaceConormalBasisOnFirstOpen
#print axioms CycleQ2ConormalJacobian.actualEquationNormalMap_eq
#print axioms CycleQ2ConormalJacobian.exists_point_in_jacobian_open
end
end


/- Component: continuation_20261111/SeedCurveGradient.lean -/
section
/-! The exact polynomial certificate binds to the literal r=57 curve
f1=h=0 after eliminating w=-x2^2.  Every relevant prime admits a
nonzero two-column normal Jacobian minor. This is the algebraic cover
needed before applying a geometric smoothness/Jacobian theorem. -/

noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace CycleQ2SeedCurveGradient
open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations

def quadric : Poly ℂ := X 0^2 - C 57*X 1*X 3

def minor (j k : Fin 4) : Poly ℂ :=
  pderiv j.castSucc quadric * pderiv k.castSucc (smoothH Complex.I) -
    pderiv k.castSucc quadric * pderiv j.castSucc (smoothH Complex.I)

def minorPairs : Fin 6 → Fin 4 × Fin 4 :=
  ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

def generators : Fin 8 → Poly ℂ :=
  ![quadric, smoothH Complex.I, minor 0 1, minor 0 2, minor 0 3,
    minor 1 2, minor 1 3, minor 2 3]

theorem quadric_derivative (j : Fin 4) :
    pderiv j.castSucc quadric =
      ![2*X 0, -C 57*X 3, 0, -C 57*X 1] j := by
  fin_cases j <;> simp [quadric, Derivation.leibniz, Fin.castSucc] <;> ring

theorem generators_binding (j : Fin 8) :
    CycleQ2SeedCurveGradientArithmetic.generators
      (C Complex.I) (X 0) (X 1) (X 2) (X 3) j = generators j := by
  have hc : (C (57 : ℂ) : Poly ℂ) = 57 := map_ofNat _ _
  have hn (k : Fin 5) : pderiv k (57 : Poly ℂ) = 0 := by
    rw [←hc]
    exact pderiv_C
  fin_cases j <;>
    simp [CycleQ2SeedCurveGradientArithmetic.generators, generators, minor,
      quadric, smoothH, smoothB, smoothA, map_ofNat, hn] <;>
    ring

theorem coordinate_power_identity (j : Fin 4) :
    (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ) * X j.castSucc^6 =
      ∑ k, CycleQ2SeedCurveGradientArithmetic.numerators j
        (C Complex.I) (X 0) (X 1) (X 2) (X 3) k * generators k := by
  have hi : (C Complex.I : Poly ℂ)^2+1=0 := by
    rw [←map_pow, Complex.I_sq, map_neg, map_one]
    ring
  simp_rw [←generators_binding]
  fin_cases j
  · exact CycleQ2SeedCurveGradientArithmetic.identity0 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity1 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity2 _ _ _ _ _ hi
  · exact CycleQ2SeedCurveGradientArithmetic.identity3 _ _ _ _ _ hi

theorem denominator_ne_zero (j : Fin 4) :
    (CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ) ≠ 0 := by
  fin_cases j <;> norm_num [CycleQ2SeedCurveGradientArithmetic.denominator]

def jacobianIdeal : Ideal (Poly ℂ) := Ideal.span (Set.range generators)

/-- Four actual coordinate sixth powers lie in the actual curve Jacobian
ideal over the complex numbers. -/
theorem coordinate_power_mem_jacobian (j : Fin 4) :
    (X j.castSucc : Poly ℂ)^6 ∈ jacobianIdeal := by
  have hsum : (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ)*
      X j.castSucc^6 ∈ jacobianIdeal := by
    rw [coordinate_power_identity]
    apply Ideal.sum_mem
    intro k _
    apply Ideal.mul_mem_left
    exact Ideal.subset_span (Set.mem_range_self k)
  have h := Ideal.mul_mem_left jacobianIdeal
    (C ((CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ)⁻¹)) hsum
  have hc : C ((CycleQ2SeedCurveGradientArithmetic.denominator j : ℂ)⁻¹)*
      (CycleQ2SeedCurveGradientArithmetic.denominator j : Poly ℂ)=1 := by
    rw [←map_natCast C, ←map_mul, inv_mul_cancel₀ (denominator_ne_zero j), map_one]
  simpa only [←mul_assoc, hc, one_mul] using h

/-- The curve Jacobian minors cover all relevant primes of the literal
quadric-cubic curve. -/
theorem prime_minor_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (hf : quadric ∈ P) (hh : smoothH Complex.I ∈ P)
    (hx : ∃ j : Fin 4, X j.castSucc ∉ P) :
    ∃ j : Fin 6, minor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  by_contra! hzero
  have hgen (j : Fin 8) : generators j ∈ P := by
    fin_cases j
    · exact hf
    · exact hh
    · exact hzero 0
    · exact hzero 1
    · exact hzero 2
    · exact hzero 3
    · exact hzero 4
    · exact hzero 5
  have hle : jacobianIdeal ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact hgen j
  obtain ⟨j,hj⟩ := hx
  exact hj ((inferInstance : P.IsPrime).mem_of_pow_mem _
    (hle (coordinate_power_mem_jacobian j)))

/-- The same nonzero minor statement over every extension of the actual
complex coefficients. -/
theorem field_minor_cover {K : Type*} [Field K] (φ : Poly ℂ →+* K)
    (hf : φ quadric=0) (hh : φ (smoothH Complex.I)=0)
    (hx : ∃ j : Fin 4, φ (X j.castSucc) ≠ 0) :
    ∃ j : Fin 6, φ (minor (minorPairs j).1 (minorPairs j).2) ≠ 0 := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  exact prime_minor_cover (RingHom.ker φ) hf hh hx


/-- Restore the eliminated weight-two coordinate. -/
def weightedEquation : Poly ℂ := X 4 + X 2^2

def curveEquations : Fin 3 → Poly ℂ := ![quadric, smoothH Complex.I, weightedEquation]

def normalMinor (j k : Fin 4) : Poly ℂ :=
  Matrix.det (fun a b : Fin 3 =>
    pderiv (![j.castSucc, k.castSucc, (4 : Fin 5)] b) (curveEquations a))

theorem normalMinor_eq (j k : Fin 4) : normalMinor j k = minor j k := by
  have hf : pderiv (4 : Fin 5) quadric=0 := by simp [quadric, Derivation.leibniz]
  have hh : pderiv (4 : Fin 5) (smoothH Complex.I : Poly ℂ)=0 := by
    simp [smoothH, smoothB, smoothA, Derivation.leibniz]
  have hw : pderiv (4 : Fin 5) weightedEquation=1 := by
    simp [weightedEquation]
  unfold normalMinor
  rw [Matrix.det_fin_three]
  simp [curveEquations, hf, hh, hw, minor]

theorem base_coordinate_of_weighted_equation (P : Ideal (Poly ℂ))
    (hw : weightedEquation ∈ P) (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j : Fin 4, X j.castSucc ∉ P := by
  by_contra! hbase
  have hfour : (X (4 : Fin 5) : Poly ℂ) ∈ P := by
    have hx2 : (X (2 : Fin 5) : Poly ℂ)^2 ∈ P :=
      Ideal.pow_mem_of_mem P (hbase 2) 2 (by decide)
    have he : X (4 : Fin 5) = weightedEquation-X 2^2 := by
      unfold weightedEquation
      ring
    rw [he]
    exact P.sub_mem hw hx2
  obtain ⟨j,hj⟩ := hx
  fin_cases j
  · exact hj (hbase 0)
  · exact hj (hbase 1)
  · exact hj (hbase 2)
  · exact hj (hbase 3)
  · exact hj hfour

/-- Actual three-equation normal Jacobian cover for the weighted seed
curve f1=h=(w+x2^2)=0, including all projective coordinate charts. -/
theorem weighted_prime_normal_cover (P : Ideal (Poly ℂ)) [P.IsPrime]
    (he : ∀ a : Fin 3, curveEquations a ∈ P)
    (hx : ∃ j : Fin 5, X j ∉ P) :
    ∃ j : Fin 6, normalMinor (minorPairs j).1 (minorPairs j).2 ∉ P := by
  have hbase := base_coordinate_of_weighted_equation P (he 2) hx
  obtain ⟨j,hj⟩ := prime_minor_cover P (he 0) (he 1) hbase
  exact ⟨j, by simpa only [normalMinor_eq] using hj⟩

theorem weighted_field_normal_cover {K : Type*} [Field K]
    (φ : Poly ℂ →+* K) (he : ∀ a : Fin 3, φ (curveEquations a)=0)
    (hx : ∃ j : Fin 5, φ (X j) ≠ 0) :
    ∃ j : Fin 6, IsUnit (φ (normalMinor (minorPairs j).1 (minorPairs j).2)) := by
  letI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨j,hj⟩ := weighted_prime_normal_cover (RingHom.ker φ) he hx
  exact ⟨j, isUnit_iff_ne_zero.mpr hj⟩

end CycleQ2SeedCurveGradient

#print axioms CycleQ2SeedCurveGradient.prime_minor_cover
#print axioms CycleQ2SeedCurveGradient.field_minor_cover

#print axioms CycleQ2SeedCurveGradient.weighted_prime_normal_cover
#print axioms CycleQ2SeedCurveGradient.weighted_field_normal_cover
end
end


/- Component: continuation_20261111/SurfaceLocalDerivations.lean -/
section
/-!
# Actual local lifts of a deformation derivation on a complete intersection

For F=h=0 the inverse of a two-by-two Jacobian minor gives a literal
correction of the coefficient derivation.  It annihilates both defining
equations, preserves their ideal, and descends to the actual quotient ring.
The localization constructor below supplies the ambient derivations on the
minor open; no tangent derivation or quotient compatibility is assumed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2SurfaceLocalDerivations

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]

def minor (Da Db : Derivation K R R) (F h : R) : R :=
  Da F * Db h - Db F * Da h

/-- Cramer's rule, with signs chosen so D(F)=D(h)=0. -/
def corrected (D Da Db : Derivation K R R) (F h : R) (u : Rˣ) :
    Derivation K R R :=
  D + ((Db F * D h - Db h * D F) * (↑(u⁻¹) : R)) • Da +
    ((Da h * D F - Da F * D h) * (↑(u⁻¹) : R)) • Db

theorem corrected_F (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    corrected D Da Db F h u F = 0 := by
  have hi := u.mul_inv
  rw [hu] at hi
  dsimp [minor] at hi
  simp only [corrected, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
  linear_combination -(D F) * hi

theorem corrected_h (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    corrected D Da Db F h u h = 0 := by
  have hi := u.mul_inv
  rw [hu] at hi
  dsimp [minor] at hi
  simp only [corrected, Derivation.add_apply, Derivation.smul_apply, smul_eq_mul]
  linear_combination -(D h) * hi

theorem corrected_on_constants (D Da Db : Derivation K R R) (F h c : R) (u : Rˣ)
    (ha : Da c = 0) (hb : Db c = 0) :
    corrected D Da Db F h u c = D c := by
  simp [corrected, ha, hb]

def equationIdeal (F h : R) : Ideal R := Ideal.span ({F, h} : Set R)

theorem preserves_equationIdeal (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) (a : R) (ha : a ∈ equationIdeal F h) :
    E a ∈ equationIdeal F h := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      rcases hx with hx | hx
      · rw [hx, hF]; exact Ideal.zero_mem _
      · rw [Set.mem_singleton_iff.mp hx, hh]; exact Ideal.zero_mem _
  | zero => simpa only [map_zero] using (Ideal.zero_mem (equationIdeal F h))
  | add x y hx hy hdx hdy =>
      rw [map_add]
      exact Ideal.add_mem _ hdx hdy
  | smul a x hx hdx =>
      change E (a * x) ∈ equationIdeal F h
      rw [Derivation.leibniz]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ a hdx)
        (Ideal.mul_mem_right (E a) _ hx)

/-- A derivation annihilating the equations descends to the actual quotient. -/
def quotientDerivation (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) :
    Derivation K (R ⧸ equationIdeal F h) (R ⧸ equationIdeal F h) :=
  Derivation.liftOfSurjective (Ideal.Quotient.mkₐ_surjective K (equationIdeal F h))
    (d := E) (by
      intro x hx
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (preserves_equationIdeal E F h hF hh x (Ideal.Quotient.eq_zero_iff_mem.mp hx)))

@[simp] theorem quotientDerivation_mk (E : Derivation K R R) (F h : R)
    (hF : E F = 0) (hh : E h = 0) (a : R) :
    quotientDerivation E F h hF hh (Ideal.Quotient.mk (equationIdeal F h) a) =
      Ideal.Quotient.mk (equationIdeal F h) (E a) := by
  unfold quotientDerivation
  exact Derivation.liftOfSurjective_apply _ _ a

/-- The local lift is constructed from the ambient coefficient motion and
two ambient coordinate derivations by the proved Cramer's correction. -/
def localLift (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) :
    Derivation K (R ⧸ equationIdeal F h) (R ⧸ equationIdeal F h) :=
  quotientDerivation (corrected D Da Db F h u) F h
    (corrected_F D Da Db F h u hu) (corrected_h D Da Db F h u hu)

theorem localLift_mk (D Da Db : Derivation K R R) (F h : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) (a : R) :
    localLift D Da Db F h u hu (Ideal.Quotient.mk (equationIdeal F h) a) =
      Ideal.Quotient.mk (equationIdeal F h)
        (D a + (Db F * D h - Db h * D F) * (↑(u⁻¹) : R) * Da a +
          (Da h * D F - Da F * D h) * (↑(u⁻¹) : R) * Db a) := by
  rw [localLift, quotientDerivation_mk]
  rfl

theorem localLift_on_constants (D Da Db : Derivation K R R) (F h c : R) (u : Rˣ)
    (hu : (u : R) = minor Da Db F h) (ha : Da c = 0) (hb : Db c = 0) :
    localLift D Da Db F h u hu (Ideal.Quotient.mk (equationIdeal F h) c) =
      Ideal.Quotient.mk (equationIdeal F h) (D c) := by
  rw [localLift, quotientDerivation_mk, corrected_on_constants D Da Db F h c u ha hb]

section Localization

variable (D Da Db : Derivation K R R) (F h : R)

abbrev MinorOpen := Localization.Away (minor Da Db F h)

def openDerivation (E : Derivation K R R) :
    Derivation K (MinorOpen Da Db F h) (MinorOpen Da Db F h) :=
  CycleQ2LocalizationDerivation.extend (Submonoid.powers (minor Da Db F h)) E

theorem openDerivation_map (E : Derivation K R R) (a : R) :
    openDerivation Da Db F h E (algebraMap R (MinorOpen Da Db F h) a) =
      algebraMap R (MinorOpen Da Db F h) (E a) :=
  CycleQ2LocalizationDerivation.extend_map _ E a

theorem open_minor :
    minor (openDerivation Da Db F h Da) (openDerivation Da Db F h Db)
      (algebraMap R (MinorOpen Da Db F h) F) (algebraMap R (MinorOpen Da Db F h) h) =
      algebraMap R (MinorOpen Da Db F h) (minor Da Db F h) := by
  simp only [minor, openDerivation_map, map_sub, map_mul]

/-- The actual localization makes the required Jacobian minor a unit. -/
def minorUnit : (MinorOpen Da Db F h)ˣ :=
  (IsLocalization.map_units (MinorOpen Da Db F h)
    ⟨minor Da Db F h, Submonoid.mem_powers _⟩).unit

theorem minorUnit_val :
    (minorUnit Da Db F h : MinorOpen Da Db F h) =
      minor (openDerivation Da Db F h Da) (openDerivation Da Db F h Db)
        (algebraMap R (MinorOpen Da Db F h) F) (algebraMap R (MinorOpen Da Db F h) h) := by
  rw [open_minor]
  exact IsUnit.unit_spec _

abbrev LocalSurface := (MinorOpen Da Db F h) ⧸
  equationIdeal (algebraMap R (MinorOpen Da Db F h) F)
    (algebraMap R (MinorOpen Da Db F h) h)

/-- A local derivation on the literal minor-localized surface, produced
without assuming a coordinate lift or quotient stability. -/
def surfaceDerivation : Derivation K (LocalSurface Da Db F h) (LocalSurface Da Db F h) :=
  localLift (openDerivation Da Db F h D) (openDerivation Da Db F h Da)
    (openDerivation Da Db F h Db) _ _ (minorUnit Da Db F h) (minorUnit_val Da Db F h)

/-- The actual local lift induces the original motion on every coefficient
annihilated by the chosen coordinate derivations. -/
theorem surfaceDerivation_on_constants (c : R) (ha : Da c = 0) (hb : Db c = 0) :
    surfaceDerivation D Da Db F h
      (Ideal.Quotient.mk _ (algebraMap R (MinorOpen Da Db F h) c)) =
      Ideal.Quotient.mk _ (algebraMap R (MinorOpen Da Db F h) (D c)) := by
  unfold surfaceDerivation
  rw [localLift_on_constants (openDerivation Da Db F h D)
    (openDerivation Da Db F h Da) (openDerivation Da Db F h Db) _ _ _
    (minorUnit Da Db F h) (minorUnit_val Da Db F h)
    (by rw [openDerivation_map, ha, map_zero])
    (by rw [openDerivation_map, hb, map_zero]), openDerivation_map]

end Localization
end CycleQ2SurfaceLocalDerivations

#print axioms CycleQ2SurfaceLocalDerivations.localLift_mk
#print axioms CycleQ2SurfaceLocalDerivations.localLift_on_constants
#print axioms CycleQ2SurfaceLocalDerivations.surfaceDerivation
#print axioms CycleQ2SurfaceLocalDerivations.surfaceDerivation_on_constants
end
end


/- Component: continuation_20261111/IncidenceLocalDerivations.lean -/
section
/-!
# Local deformation lifts for the actual finite trace family

The coefficient motion is the already constructed derivative on the actual
finite extension of the trace parameter field.  The two equations are the
actual specialized invariant sextic and cubic, not independent model
equations.  The sextic is fixed by this motion.  On every two-by-two Jacobian
minor open, a derivation on the actual quotient is constructed explicitly.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CycleQ2IncidenceLocalDerivations

open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceMonomials
  CycleQ2IncidenceUniversalChart CycleQ2IncidencePolynomialJacobianBinding
  CycleQ2SegreFullJacobianBounds CycleQ2IncidenceTraceFamily
  CycleQ2IncidenceTraceFieldDerivation CycleQ2IncidenceTraceGeometry
  CycleQ2IncidenceGenericPointSemantics CycleQ2SurfaceLocalDerivations
  CycleQ2PolynomialCoefficientDerivation CycleQ2PolynomialAffineSlice
open CycleQ2IncidenceCompatibleGenericPoint (SquareIndex)

variable {L : Type} [Field L] [Algebra TraceField L]
  [Algebra TraceRing L] [IsScalarTower TraceRing TraceField L]
  [Algebra ℂ L] [IsScalarTower ℂ TraceRing L] [FiniteDimensional TraceField L]

def timePolynomial : Derivation ℂ (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L) :=
  coefficientDerivation (timeDerivation (L := L))

def coordinateDerivation (j : Fin 5) :
    Derivation ℂ (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L) :=
  (pderiv j : Derivation L (MvPolynomial (Fin 5) L) (MvPolynomial (Fin 5) L)).restrictScalars ℂ

theorem time_fullInvariantPolynomial (d : ℕ) (c : FullInvariantIndex d → L) :
    timePolynomial (fullInvariantPolynomial d c) =
      fullInvariantPolynomial d (fun j => timeDerivation (c j)) := by
  unfold fullInvariantPolynomial timePolynomial
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientDerivation_monomial _ _ _

def actualF (B : Matrix FixedSexticParameters SquareIndex ℂ) (z : SquareIndex → L) :
    MvPolynomial (Fin 5) L :=
  fullInvariantPolynomial 6 (pointSextic (tracePointValue B z))

def actualH (B : Matrix FixedSexticParameters SquareIndex ℂ) (z : SquareIndex → L) :
    MvPolynomial (Fin 5) L :=
  fullInvariantPolynomial 3 (pointCubic (tracePointValue B z))

theorem actualF_eq_specialized (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) :
    actualF B z = MvPolynomial.map
      (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
      CycleQ2IncidenceBasepointOpen.familyF :=
  (CycleQ2IncidenceImageLine.pointMap_familyF (tracePointValue B z)).symm

theorem actualH_eq_specialized (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) :
    actualH B z = MvPolynomial.map
      (CycleQ2IncidenceImageLine.pointMap (tracePointValue B z))
      CycleQ2IncidenceBasepointOpen.familyH :=
  (CycleQ2IncidenceImageLine.pointMap_familyH (tracePointValue B z)).symm

/-- The actual family keeps the sextic fixed under its trace parameter. -/
theorem time_actualF (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) : timePolynomial (actualF B z) = 0 := by
  rw [actualF, time_fullInvariantPolynomial]
  have hc (j : FullInvariantIndex 6) :
      timeDerivation (pointSextic (tracePointValue B z) j) = 0 := by
    change timeDerivation
      (pointValue (algebraMap TraceRing L) centre (directions B) z
        (Sum.inr (Sum.inl j))) = 0
    rw [sextic_coordinate_fixed, timeDerivation_sexticParameter]
  simp only [hc, fullInvariantPolynomial, map_zero, Finset.sum_const_zero]

theorem coordinateDerivation_C (j : Fin 5) (c : L) :
    coordinateDerivation j (C c) = 0 := by
  exact pderiv_C

abbrev ActualLocalSurface (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) :=
  LocalSurface (coordinateDerivation i) (coordinateDerivation j) (actualF B z) (actualH B z)

/-- This derivation exists on the actual minor-localized quotient without
assuming a tangent lift or its compatibility with either defining equation.
A separate Jacobian-cover theorem is needed to cover the surface by these
opens; this constructor alone does not assert that an open is nonempty. -/
def actualLocalTime (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) :
    Derivation ℂ (ActualLocalSurface B z i j) (ActualLocalSurface B z i j) :=
  surfaceDerivation timePolynomial (coordinateDerivation i) (coordinateDerivation j)
    (actualF B z) (actualH B z)

/-- Every constructed local lift restricts to the same actual derivation
of the finite coefficient field. -/
theorem actualLocalTime_coefficients (B : Matrix FixedSexticParameters SquareIndex ℂ)
    (z : SquareIndex → L) (i j : Fin 5) (c : L) :
    actualLocalTime B z i j
      (Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 5) L)
        (MinorOpen (coordinateDerivation i) (coordinateDerivation j)
          (actualF B z) (actualH B z)) (C c))) =
      Ideal.Quotient.mk _ (algebraMap (MvPolynomial (Fin 5) L)
        (MinorOpen (coordinateDerivation i) (coordinateDerivation j)
          (actualF B z) (actualH B z)) (C (timeDerivation c))) := by
  unfold actualLocalTime
  rw [surfaceDerivation_on_constants _ _ _ _ _ (C c)
    (coordinateDerivation_C i c) (coordinateDerivation_C j c)]
  rw [timePolynomial, coefficientDerivation_C]

end CycleQ2IncidenceLocalDerivations

#print axioms CycleQ2IncidenceLocalDerivations.time_actualF
#print axioms CycleQ2IncidenceLocalDerivations.actualLocalTime
#print axioms CycleQ2IncidenceLocalDerivations.actualLocalTime_coefficients
end
end


/- Component: continuation_20261111/SeedConormalCover.lean -/
section
/-! The exact seed Jacobian certificate supplies actual conormal bases at
every relevant prime of the curve, including nonclosed primes. -/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ConormalCover
open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2ConormalJacobian

abbrev I : Ideal P := ambientCurveIdeal 57 1
abbrev Q := ActualCurve 57 1

def generatorOrder : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

theorem gradient_generator_eq (j : Fin 3) :
    CycleQ2SeedCurveGradient.curveEquations j=
      curveEquations 57 1 (generatorOrder j) := by
  fin_cases j <;>
    simp [CycleQ2SeedCurveGradient.curveEquations,CycleQ2SeedCurveGradient.quadric,
      CycleQ2SeedCurveGradient.weightedEquation,curveEquations,generatorOrder,
      Equiv.swap_apply_def,originalF1,originalF2,←smoothH_eq_thetaH]

theorem gradient_span_eq :
    Ideal.span (Set.range CycleQ2SeedCurveGradient.curveEquations)=I := by
  unfold I ambientCurveIdeal
  congr 1
  ext p
  constructor
  · rintro ⟨j,rfl⟩
    exact ⟨generatorOrder j,(gradient_generator_eq j).symm⟩
  · rintro ⟨j,rfl⟩
    refine ⟨generatorOrder.symm j,?_⟩
    simpa using gradient_generator_eq (generatorOrder.symm j)

variable (q : Ideal Q) [q.IsPrime]

abbrev PrimeCurve := Localization.AtPrime q

def primeMap : P →+* PrimeCurve q :=
  (algebraMap Q (PrimeCurve q)).comp (Ideal.Quotient.mk I)

instance primeScalarTower : IsScalarTower ℂ P (PrimeCurve q) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := P) (A := PrimeCurve q)
    fun _ => rfl

theorem primeMap_ideal (p : P) (hp : p∈I) :
    algebraMap P (PrimeCurve q) p=0 := by
  change algebraMap Q (PrimeCurve q) (Ideal.Quotient.mk I p)=0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp,map_zero]

def minorCoordinates (j : Fin 6) : Fin 3 → Fin 5 :=
  ![(CycleQ2SeedCurveGradient.minorPairs j).1.castSucc,
    (CycleQ2SeedCurveGradient.minorPairs j).2.castSucc,4]

theorem mapped_minor_det (j : Fin 6) :
    (derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))).det=
      algebraMap P (PrimeCurve q)
        (CycleQ2SeedCurveGradient.normalMinor
          (CycleQ2SeedCurveGradient.minorPairs j).1
          (CycleQ2SeedCurveGradient.minorPairs j).2) := by
  let A : Matrix (Fin 3) (Fin 3) P := fun a b =>
    pderiv (minorCoordinates j b) (CycleQ2SeedCurveGradient.curveEquations a)
  have hm : derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))=
        ((algebraMap P (PrimeCurve q)).mapMatrix A).transpose := by
    ext a b
    rfl
  rw [hm,Matrix.det_transpose,←RingHom.map_det]
  rfl

/-- The ideal cotangent module localized at every relevant prime has the
actual three equation classes as a basis. The Jacobian-unit premise has
been discharged by the exact coordinate-power certificate. -/
theorem exists_actual_conormal_basis
    (hx : ∃ j : Fin 5, Ideal.Quotient.mk I (X j)∉q) :
    ∃ b : Module.Basis (Fin 3) (PrimeCurve q) (PrimeCurve q ⊗[P] I.Cotangent),
      ∀ i, b i=(1:PrimeCurve q) ⊗ₜ[P] conormalGenerator 57 1 i := by
  let p : Ideal P := q.comap (Ideal.Quotient.mk I)
  have he (a : Fin 3) : CycleQ2SeedCurveGradient.curveEquations a∈p := by
    change Ideal.Quotient.mk I (CycleQ2SeedCurveGradient.curveEquations a)∈q
    have ha : CycleQ2SeedCurveGradient.curveEquations a∈I :=
      gradient_span_eq ▸ Ideal.subset_span ⟨a,rfl⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact q.zero_mem
  obtain ⟨j,hj⟩ := CycleQ2SeedCurveGradient.weighted_prime_normal_cover p he hx
  have hu : IsUnit (algebraMap P (PrimeCurve q)
      (CycleQ2SeedCurveGradient.normalMinor
        (CycleQ2SeedCurveGradient.minorPairs j).1
        (CycleQ2SeedCurveGradient.minorPairs j).2)) :=
    IsLocalization.map_units (M := q.primeCompl) (PrimeCurve q) ⟨_,hj⟩
  have hd : IsUnit (derivationMatrix CycleQ2SeedCurveGradient.curveEquations
      (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i))).det := by
    rwa [mapped_minor_det]
  let b := conormalBasisOfJacobian I (primeMap_ideal q)
    CycleQ2SeedCurveGradient.curveEquations gradient_span_eq
    (fun i => mappedPartial (S := PrimeCurve q) (minorCoordinates j i)) hd
  refine ⟨b.reindex generatorOrder,?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  dsimp [b]
  rw [conormalBasisOfJacobian_apply]
  simp only [generator,conormalGenerator,gradient_generator_eq,Equiv.apply_symm_apply]

end CycleQ2ConormalCover

#print axioms CycleQ2ConormalCover.exists_actual_conormal_basis
end
end

/- Component: continuation_20261111/SeedNaturalNormalMap.lean -/
section
/-!
# The natural conormal map and the actual normal matrix

For the literal seed ideals J=(F,h) and I=(f1,f2,h), the inclusion J <= I
induces the actual map J/J^2 -> I/I^2. Scalar extension and dualization give
an S-linear map between the genuine normal modules. Evaluation on the
actual equation classes identifies this dual map with the existing normal
matrix, and with the existing actualEquationNormalMap on its seed chart.

The local basis comparison uses the already constructed source derivative
duals and a unit value of g1. Both coordinate identifications are therefore
actual conormal bases. The graded global normal sequence and its connecting
class require further chart compatibility and gluing.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2NaturalNormalMap

open CycleQ2ConormalJacobian CycleQ2NormalConnecting CycleQ2SeedTrace

/-- The literal natural map J/J^2 -> I/I^2, with J=(F,h), I=(f1,f2,h).
The algebra homomorphism is the identity of the actual polynomial ring. -/
def naturalCotangentMap (r θ : ℂ) :
    (surfaceIdeal r θ).Cotangent →ₗ[P] (ambientCurveIdeal r θ).Cotangent :=
  Ideal.mapCotangent (surfaceIdeal r θ) (ambientCurveIdeal r θ)
    (AlgHom.id P P) (by
      intro x hx
      change x ∈ ambientCurveIdeal r θ
      exact surfaceIdeal_le_curveIdeal r θ hx)

/-- This is the identity-homomorphism instance of
Ideal.mapCotangent_toCotangent, whose proof in mathlib is also rfl. -/
@[simp] theorem naturalCotangentMap_toCotangent (r θ : ℂ)
    (x : surfaceIdeal r θ) :
    naturalCotangentMap r θ ((surfaceIdeal r θ).toCotangent x) =
      (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩ := by
  rfl

section ScalarExtension

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

/-- Scalar extension of the actual natural cotangent map. -/
def baseChangedNaturalCotangentMap (r θ : ℂ) :
    S ⊗[P] (surfaceIdeal r θ).Cotangent →ₗ[S]
      S ⊗[P] (ambientCurveIdeal r θ).Cotangent :=
  (naturalCotangentMap r θ).baseChange S

@[simp] theorem baseChangedNaturalCotangentMap_toCotangent (r θ : ℂ)
    (s : S) (x : surfaceIdeal r θ) :
    baseChangedNaturalCotangentMap (S := S) r θ
        (s ⊗ₜ[P] (surfaceIdeal r θ).toCotangent x) =
      s ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩ := by
  simp only [baseChangedNaturalCotangentMap, LinearMap.baseChange_tmul,
    naturalCotangentMap_toCotangent]

/-- The normal map is dualization of the genuine, base-changed natural
cotangent map. No choice of equation coordinates enters this definition. -/
def naturalNormalMap (r θ : ℂ) :
    (S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) →ₗ[S]
      (S ⊗[P] (surfaceIdeal r θ).Cotangent →ₗ[S] S) :=
  (baseChangedNaturalCotangentMap (S := S) r θ).dualMap

@[simp] theorem naturalNormalMap_toCotangent (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S)
    (s : S) (x : surfaceIdeal r θ) :
    naturalNormalMap r θ φ (s ⊗ₜ[P] (surfaceIdeal r θ).toCotangent x) =
      φ (s ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
        ⟨(x : P), surfaceIdeal_le_curveIdeal r θ x.property⟩) := by
  simp only [naturalNormalMap, LinearMap.dualMap_apply,
    baseChangedNaturalCotangentMap_toCotangent]

/-- On every scalar extension, the equation values of the actual dual
natural map are exactly the previously proved normal matrix. This theorem
does not require either equation family to have been proved a basis. -/
theorem naturalNormalMap_equation_coordinates (r θ : ℂ)
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    (fun j : Fin 2 => naturalNormalMap r θ φ
        (generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (fun i => φ ((1 : S) ⊗ₜ[P] conormalGenerator r θ i)) := by
  calc
    (fun j : Fin 2 => naturalNormalMap r θ φ
        (generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) =
        ![φ ((1 : S) ⊗ₜ[P] (ambientCurveIdeal r θ).toCotangent
              ⟨actualSeedEquation r θ, actualSeedEquation_mem r θ⟩),
          φ ((1 : S) ⊗ₜ[P] conormalGenerator r θ 2)] := by
      funext j
      fin_cases j <;> rfl
    _ = _ := baseChangedNormalMap_eq r θ φ

/-- With the already constructed source and target conormal bases, the
same identity is an identity in coordinates on both genuine normal modules.
The hypotheses are the existing local source derivation duals and a g1 unit;
no assumed normal presentation or normal-map comparison is introduced. -/
theorem naturalNormalMap_in_equation_bases (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S (originalG1 r))
    (φ : S ⊗[P] (ambientCurveIdeal r θ).Cotangent →ₗ[S] S) :
    ((surfaceConormalBasisOnFirstOpen r θ hI d hd u hu).constr S).symm
        (naturalNormalMap r θ φ) =
      equationMap (algebraMap P S (originalG1 r))
        (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
        (((conormalBasis (ambientCurveIdeal r θ) hI
          (curveEquations r θ) rfl d hd).constr S).symm φ) := by
  change (fun j => naturalNormalMap r θ φ
      (surfaceConormalBasisOnFirstOpen r θ hI d hd u hu j)) =
    equationMap (algebraMap P S (originalG1 r))
      (algebraMap P S originalG2) (algebraMap P S (thetaK θ))
      (fun i => φ (conormalBasis (ambientCurveIdeal r θ) hI
        (curveEquations r θ) rfl d hd i))
  simpa only [surfaceConormalBasisOnFirstOpen, conormalBasis_apply,
    generator, conormalGenerator] using
      naturalNormalMap_equation_coordinates (S := S) r θ φ

end ScalarExtension

/-- Direct binding to the existing actualEquationNormalMap on its literal
nonempty Jacobian chart. This identifies the local evaluation map with the natural dual map. -/
theorem actualEquationNormalMap_eq_naturalNormalMap (r θ : ℂ)
    (φ : ActualConormal r θ →ₗ[ActualLocalCurve r θ] ActualLocalCurve r θ) :
    actualEquationNormalMap r θ φ =
      (fun j : Fin 2 => naturalNormalMap (S := ActualLocalCurve r θ) r θ φ
        (generator (S := ActualLocalCurve r θ)
          (surfaceIdeal r θ) (surfaceEquations r θ) rfl j)) := by
  funext j
  fin_cases j <;> rfl

end CycleQ2NaturalNormalMap

#print axioms CycleQ2NaturalNormalMap.naturalNormalMap_equation_coordinates
#print axioms CycleQ2NaturalNormalMap.naturalNormalMap_in_equation_bases
#print axioms CycleQ2NaturalNormalMap.actualEquationNormalMap_eq_naturalNormalMap

end
end

/- Preserved entry-point body; the sole admission follows all helpers. -/


/- Component: continuation_20261112/ConormalRegularSequence.lean -/
section
/-! Genuine conormal coordinates from relations among ideal generators.
The finite-relation criterion below is proved for regular sequences of
length two and three. It does not require the ambient quotient to be smooth.
-/

noncomputable section
open scoped BigOperators TensorProduct
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2ConormalRegular

section Finite
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Fintype ι] [DecidableEq ι]
variable (I : Ideal R) (f : ι → R) (hf : Ideal.span (Set.range f) = I)

include hf in
theorem coefficients_exist (x : I) : ∃ c : ι → R, ∑ i, c i * f i = (x : R) := by
  have hx : (x : R) ∈ Submodule.span R (Set.range f) := hf.symm ▸ x.property
  simpa only [smul_eq_mul] using
    (Submodule.mem_span_range_iff_exists_fun (R := R)).mp hx

def coefficients (x : I) : ι → R := Classical.choose (coefficients_exist I f hf x)

theorem coefficients_spec (x : I) : ∑ i, coefficients I f hf x i * f i = (x : R) :=
  Classical.choose_spec (coefficients_exist I f hf x)

variable (hI : ∀ x ∈ I, algebraMap R S x = 0)
variable (hrel : ∀ c : ι → R, (∑ i, c i * f i) = 0 → ∀ i, c i ∈ I)

include hI hrel in
theorem coefficient_maps_unique (c d : ι → R)
    (h : (∑ i, c i * f i) = ∑ i, d i * f i) (i : ι) :
    algebraMap R S (c i) = algebraMap R S (d i) := by
  have hz : (∑ j, (c j - d j) * f j) = 0 := by
    simp only [sub_mul, Finset.sum_sub_distrib, h, sub_self]
  have hh := hI _ (hrel (fun j => c j - d j) hz i)
  simpa only [map_sub, sub_eq_zero] using hh

/-- The chosen polynomial coefficients give a canonical linear functional
after passing to any algebra that annihilates the ideal. -/
def idealCoordinate (i : ι) : I →ₗ[R] S where
  toFun x := algebraMap R S (coefficients I f hf x i)
  map_add' x y := by
    have hh := coefficient_maps_unique I f hI hrel
      (coefficients I f hf (x+y))
      (fun j => coefficients I f hf x j + coefficients I f hf y j) (by
        simp only [add_mul, Finset.sum_add_distrib, coefficients_spec]
        rfl) i
    simpa only [map_add] using hh
  map_smul' a x := by
    have hh := coefficient_maps_unique I f hI hrel
      (coefficients I f hf (a • x))
      (fun j => a * coefficients I f hf x j) (by
        simp only [mul_assoc, ← Finset.mul_sum, coefficients_spec]
        rfl) i
    simpa only [map_mul, Algebra.smul_def, RingHom.id_apply] using hh

theorem idealCoordinate_generator (i j : ι) :
    idealCoordinate I f hf hI hrel i
      ⟨f j, hf ▸ Ideal.subset_span ⟨j,rfl⟩⟩ = if i=j then 1 else 0 := by
  have hh := coefficient_maps_unique I f hI hrel
    (coefficients I f hf ⟨f j, hf ▸ Ideal.subset_span ⟨j,rfl⟩⟩)
    (Pi.single j 1) (by simp [coefficients_spec, Pi.single_apply]) i
  simpa [idealCoordinate, Pi.single_apply, eq_comm] using hh

theorem idealCoordinate_product (i : ι) (x y : I) :
    idealCoordinate I f hf hI hrel i (x*y) = 0 := by
  change idealCoordinate I f hf hI hrel i ((x:R) • y) = 0
  rw [map_smul, Algebra.smul_def, hI _ x.property, zero_mul]

def conormalCoordinate (i : ι) : S ⊗[R] I.Cotangent →ₗ[S] S :=
  (Ideal.Cotangent.lift (idealCoordinate I f hf hI hrel i)
    (idealCoordinate_product I f hf hI hrel i)).liftBaseChange S

@[simp] theorem conormalCoordinate_generator (i j : ι) :
    conormalCoordinate I f hf hI hrel i
      (CycleQ2ConormalJacobian.generator (S := S) I f hf j) =
      if i=j then 1 else 0 := by
  simp [conormalCoordinate, CycleQ2ConormalJacobian.generator,
    idealCoordinate_generator]

include hI hrel in
theorem generators_independent : LinearIndependent S
    (CycleQ2ConormalJacobian.generator (S := S) I f hf) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := congrArg (conormalCoordinate I f hf hI hrel i) hc
  simp only [map_sum, map_smul, map_zero, conormalCoordinate_generator] at hh
  simpa using hh

/-- The actual base-changed ideal cotangent module is free on the given
equation classes whenever all relations have coefficients in the ideal. -/
def conormalBasis : Module.Basis ι S (S ⊗[R] I.Cotangent) :=
  Module.Basis.mk (generators_independent I f hf hI hrel)
    (by rw [CycleQ2ConormalJacobian.generators_span I f hf])

@[simp] theorem conormalBasis_apply (i : ι) :
    conormalBasis I f hf hI hrel i =
      CycleQ2ConormalJacobian.generator (S := S) I f hf i :=
  Module.Basis.mk_apply _ _ _

end Finite

section Regular
variable {R : Type*} [CommRing R]

/-- Degree-one regular-sequence consequence for two equations. The second
hypothesis is precisely cancellation modulo the first equation. -/
theorem pair_relation_coefficients (a b : R)
    (ha : ∀ x : R, a*x=0 → x=0)
    (hb : ∀ x : R, b*x ∈ Ideal.span ({a}:Set R) → x ∈ Ideal.span ({a}:Set R))
    (u v : R) (h : a*u+b*v=0) :
    u ∈ Ideal.span ({a,b}:Set R) ∧ v ∈ Ideal.span ({a,b}:Set R) := by
  have hv : v ∈ Ideal.span ({a}:Set R) := hb v (by
    rw [Ideal.mem_span_singleton']
    exact ⟨-u, by linear_combination -h⟩)
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hv
  have hu : u+b*t=0 := ha _ (by linear_combination h + b*ht)
  constructor
  · exact Ideal.mem_span_pair.mpr ⟨0,-t,by linear_combination -hu⟩
  · exact Ideal.mem_span_pair.mpr ⟨t,0,by simpa using ht⟩

/-- Degree-one regular-sequence consequence for three equations. -/
theorem triple_relation_coefficients (a b c : R)
    (ha : ∀ x : R, a*x=0 → x=0)
    (hb : ∀ x : R, b*x ∈ Ideal.span ({a}:Set R) → x ∈ Ideal.span ({a}:Set R))
    (hc : ∀ x : R, c*x ∈ Ideal.span ({a,b}:Set R) → x ∈ Ideal.span ({a,b}:Set R))
    (u v w : R) (h : a*u+b*v+c*w=0) :
    u ∈ Ideal.span ({a,b,c}:Set R) ∧
    v ∈ Ideal.span ({a,b,c}:Set R) ∧ w ∈ Ideal.span ({a,b,c}:Set R) := by
  have hw : w ∈ Ideal.span ({a,b}:Set R) := hc w (by
    exact Ideal.mem_span_pair.mpr ⟨-u,-v,by linear_combination -h⟩)
  obtain ⟨s,t,hst⟩ := Ideal.mem_span_pair.mp hw
  have hp : a*(u+c*s)+b*(v+c*t)=0 := by
    linear_combination h + c*hst
  obtain ⟨hu,hv⟩ := pair_relation_coefficients a b ha hb (u+c*s) (v+c*t) hp
  have hab : Ideal.span ({a,b}:Set R) ≤ Ideal.span ({a,b,c}:Set R) :=
    Ideal.span_mono (by intro x hx; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at *; tauto)
  have hcm : c ∈ Ideal.span ({a,b,c}:Set R) := Ideal.subset_span (by simp)
  refine ⟨?_,?_,hab hw⟩
  · simpa using (Ideal.span ({a,b,c}:Set R)).sub_mem (hab hu)
      ((Ideal.span ({a,b,c}:Set R)).mul_mem_right s hcm)
  · simpa using (Ideal.span ({a,b,c}:Set R)).sub_mem (hab hv)
      ((Ideal.span ({a,b,c}:Set R)).mul_mem_right t hcm)

end Regular
end CycleQ2ConormalRegular

#print axioms CycleQ2ConormalRegular.conormalBasis
#print axioms CycleQ2ConormalRegular.triple_relation_coefficients
end
end


/- Component: continuation_20261112/SeedRegularLeading.lean -/
section
/-!
# Leading terms of the actual seed equations

The auxiliary weights on (x0,x1,x2,x3,w) are (3,1,4,1,9).
They give pairwise disjoint monic leading terms x0^2, w, x2^3 for
the actual three curve equations, and w^3, x2^3 for the two surface
equations.  Every statement holds for arbitrary complex r and theta;
there is no Jacobian localization or cube-root restriction.

The standalone algebraic dependency chain supplies the definitions and
earlier lemmas.  No admitted declaration is used by these proofs.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedRegularLeading

open MvPolynomial CycleQ2SeedTrace CycleQ2NormalConnecting
  CycleQ2IncidenceNormalForm
open scoped BigOperators MonomialOrder

abbrev Exponent := Fin 5 →₀ ℕ

def exponent (a b c d e : ℕ) : Exponent :=
  Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 c +
    Finsupp.single 3 d + Finsupp.single 4 e

def auxiliaryWeight : Exponent →+ ℕ where
  toFun e := 3 * e 0 + e 1 + 4 * e 2 + e 3 + 9 * e 4
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def auxiliaryOrder : MonomialOrder (Fin 5) :=
  weightedOrder MonomialOrder.lex auxiliaryWeight

@[simp] theorem auxiliaryWeight_exponent (a b c d e : ℕ) :
    auxiliaryWeight (exponent a b c d e) = 3*a+b+4*c+d+9*e := by
  norm_num [auxiliaryWeight, exponent, Finsupp.single_apply, Fin.ext_iff]

theorem monomial_exponent (a b c d e : ℕ) (z : ℂ) :
    monomial (exponent a b c d e) z =
      C z * X 0^a * X 1^b * X 2^c * X 3^d * X 4^e := by
  simp only [exponent, monomial_add_single, ←C_mul_X_pow_eq_monomial]

theorem f1_shape (r : ℂ) :
    originalF1 r = monomial (exponent 2 0 0 0 0) 1 +
      ∑ _i : Fin 1, monomial (exponent 0 1 0 1 0) (-r) := by
  simp only [Fin.sum_univ_one, monomial_exponent]
  simp [originalF1, sub_eq_add_neg]

theorem f2_shape :
    originalF2 = monomial (exponent 0 0 0 0 1) 1 +
      ∑ _i : Fin 1, monomial (exponent 0 0 2 0 0) 1 := by
  simp only [Fin.sum_univ_one, monomial_exponent]
  simp [originalF2]

def cubicTailExponent (i : Fin 6) : Exponent :=
  ![exponent 0 0 0 3 0, exponent 0 1 1 1 0, exponent 1 0 1 1 0,
    exponent 1 2 0 0 0, exponent 0 3 0 0 0, exponent 3 0 0 0 0] i

def hTailCoefficient (θ : ℂ) (i : Fin 6) : ℂ :=
  ![1-Complex.I, 1, 1, 1, -Complex.I, θ] i

def kTailCoefficient (θ : ℂ) (i : Fin 6) : ℂ :=
  ![1+Complex.I, 1, 1, 1, Complex.I, θ] i

theorem h_shape (θ : ℂ) :
    thetaH θ = monomial (exponent 0 0 3 0 0) 1 +
      ∑ i : Fin 6, monomial (cubicTailExponent i) (hTailCoefficient θ i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cubicTailExponent,
    hTailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [thetaH, originalH, originalB]
  ring

theorem k_shape (θ : ℂ) :
    thetaK θ = monomial (exponent 0 0 3 0 0) 1 +
      ∑ i : Fin 6, monomial (cubicTailExponent i) (kTailCoefficient θ i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, cubicTailExponent,
    kTailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [thetaK, originalK, originalB]
  ring

def g1TailExponent (i : Fin 2) : Exponent :=
  ![exponent 2 1 0 1 0, exponent 0 2 0 2 0] i

def g1TailCoefficient (r : ℂ) (i : Fin 2) : ℂ := ![r,r^2] i

theorem g1_shape (r : ℂ) :
    originalG1 r = monomial (exponent 4 0 0 0 0) 1 +
      ∑ i : Fin 2, monomial (g1TailExponent i) (g1TailCoefficient r i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, g1TailExponent,
    g1TailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [originalG1]
  ring

def g2TailExponent (i : Fin 2) : Exponent :=
  ![exponent 0 0 2 0 1, exponent 0 0 4 0 0] i

def g2TailCoefficient (i : Fin 2) : ℂ := ![-1,1] i

theorem g2_shape :
    originalG2 = monomial (exponent 0 0 0 0 2) 1 +
      ∑ i : Fin 2, monomial (g2TailExponent i) (g2TailCoefficient i) := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, g2TailExponent,
    g2TailCoefficient, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons, monomial_exponent]
  norm_num [originalG2]
  ring

theorem f1_leading_data (r : ℂ) :
    auxiliaryOrder.degree (originalF1 r) = Finsupp.single 0 2 ∧
      auxiliaryOrder.Monic (originalF1 r) := by
  rw [f1_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 2 0 0 0 0)
    (fun _i : Fin 1 => exponent 0 1 0 1 0) (fun _ => -r) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff])
  simpa [exponent] using h

theorem f2_leading_data :
    auxiliaryOrder.degree originalF2 = Finsupp.single 4 1 ∧
      auxiliaryOrder.Monic originalF2 := by
  rw [f2_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 0 0 1)
    (fun _i : Fin 1 => exponent 0 0 2 0 0) (fun _ => (1 : ℂ)) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff])
  simpa [exponent] using h

private theorem cubic_tail_lt (i : Fin 6) :
    cubicTailExponent i ≺[auxiliaryOrder] exponent 0 0 3 0 0 := by
  apply weightedOrder_lt_of_weight_lt
  fin_cases i <;> norm_num [auxiliaryWeight, cubicTailExponent, exponent,
    Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff]

theorem h_leading_data (θ : ℂ) :
    auxiliaryOrder.degree (thetaH θ) = Finsupp.single 2 3 ∧
      auxiliaryOrder.Monic (thetaH θ) := by
  rw [h_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 3 0 0)
    cubicTailExponent (hTailCoefficient θ) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) cubic_tail_lt
  simpa [exponent] using h

theorem k_leading_data (θ : ℂ) :
    auxiliaryOrder.degree (thetaK θ) = Finsupp.single 2 3 ∧
      auxiliaryOrder.Monic (thetaK θ) := by
  rw [k_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 3 0 0)
    cubicTailExponent (kTailCoefficient θ) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) cubic_tail_lt
  simpa [exponent] using h

theorem g1_leading_data (r : ℂ) :
    auxiliaryOrder.degree (originalG1 r) = Finsupp.single 0 4 ∧
      auxiliaryOrder.Monic (originalG1 r) := by
  rw [g1_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 4 0 0 0 0)
    g1TailExponent (g1TailCoefficient r) (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      fin_cases i <;> norm_num [auxiliaryWeight, g1TailExponent, exponent,
        Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff])
  simpa [exponent] using h

theorem g2_leading_data :
    auxiliaryOrder.degree originalG2 = Finsupp.single 4 2 ∧
      auxiliaryOrder.Monic originalG2 := by
  rw [g2_shape]
  have h := degree_monic_add_sum auxiliaryOrder (exponent 0 0 0 0 2)
    g2TailExponent g2TailCoefficient (by
      apply weightedOrder_lt_of_weight_lt
      norm_num [auxiliaryWeight, exponent, Fin.ext_iff]) (by
      intro i
      apply weightedOrder_lt_of_weight_lt
      fin_cases i <;> norm_num [auxiliaryWeight, g2TailExponent, exponent,
        Matrix.cons_val_succ, Fin.reduceSucc, Fin.ext_iff])
  simpa [exponent] using h

theorem F_leading_data (r θ : ℂ) :
    auxiliaryOrder.degree (actualSeedEquation r θ) = Finsupp.single 4 3 ∧
      auxiliaryOrder.Monic (actualSeedEquation r θ) := by
  have hA : auxiliaryOrder.degree (originalF1 r * originalG1 r) =
      Finsupp.single 0 6 := by
    rw [auxiliaryOrder.degree_mul (f1_leading_data r).2.ne_zero
      (g1_leading_data r).2.ne_zero, (f1_leading_data r).1,
      (g1_leading_data r).1, ←Finsupp.single_add]
  have hB : auxiliaryOrder.degree (originalF2 * originalG2) =
      Finsupp.single 4 3 := by
    rw [auxiliaryOrder.degree_mul f2_leading_data.2.ne_zero
      g2_leading_data.2.ne_zero, f2_leading_data.1,
      g2_leading_data.1, ←Finsupp.single_add]
  have hC : auxiliaryOrder.degree (thetaH θ * thetaK θ) =
      Finsupp.single 2 6 := by
    rw [auxiliaryOrder.degree_mul (h_leading_data θ).2.ne_zero
      (k_leading_data θ).2.ne_zero, (h_leading_data θ).1,
      (k_leading_data θ).1, ←Finsupp.single_add]
  have hAB : auxiliaryOrder.degree (originalF1 r * originalG1 r) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2) := by
    rw [hA,hB]
    apply weightedOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight, Fin.ext_iff]
  have hCB : auxiliaryOrder.degree (thetaH θ * thetaK θ) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2) := by
    rw [hC,hB]
    apply weightedOrder_lt_of_weight_lt
    norm_num [auxiliaryWeight, Fin.ext_iff]
  have hBA := auxiliaryOrder.degree_add_of_lt hAB
  have hCBA : auxiliaryOrder.degree (thetaH θ * thetaK θ) ≺[auxiliaryOrder]
      auxiliaryOrder.degree (originalF2 * originalG2 + originalF1 r * originalG1 r) := by
    rw [hBA]
    exact hCB
  unfold actualSeedEquation
  rw [add_comm (originalF1 r * originalG1 r) (originalF2 * originalG2)]
  exact ⟨(auxiliaryOrder.degree_add_of_lt hCBA).trans (hBA.trans hB),
    ((f2_leading_data.2.mul g2_leading_data.2).add_of_lt hAB).add_of_lt hCBA⟩

theorem f1_f2_coprime (r : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (originalF1 r) i = 0 ∨
      auxiliaryOrder.degree originalF2 i = 0 := by
  rw [(f1_leading_data r).1, f2_leading_data.1]
  fin_cases i <;> simp

theorem f1_h_coprime (r θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (originalF1 r) i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [(f1_leading_data r).1, (h_leading_data θ).1]
  fin_cases i <;> simp

theorem f2_h_coprime (θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree originalF2 i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [f2_leading_data.1, (h_leading_data θ).1]
  fin_cases i <;> simp

theorem F_h_coprime (r θ : ℂ) (i : Fin 5) :
    auxiliaryOrder.degree (actualSeedEquation r θ) i = 0 ∨
      auxiliaryOrder.degree (thetaH θ) i = 0 := by
  rw [(F_leading_data r θ).1, (h_leading_data θ).1]
  fin_cases i <;> simp

end CycleQ2SeedRegularLeading

#print axioms CycleQ2SeedRegularLeading.f1_leading_data
#print axioms CycleQ2SeedRegularLeading.f2_leading_data
#print axioms CycleQ2SeedRegularLeading.h_leading_data
#print axioms CycleQ2SeedRegularLeading.F_leading_data
#print axioms CycleQ2SeedRegularLeading.F_h_coprime
end
end


/- Component: continuation_20261112/LocalizationBoundaryClearing.lean -/
section
/-! Denominator clearing for two genuine localization restriction maps.
No domain or injectivity hypothesis on any localization map is used.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000

namespace CycleQ2LocalizationBoundary

section TwoOpens
variable {R S T U : Type*} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
  [Algebra R S] [Algebra R T] [Algebra R U]

/-- An arbitrary boundary on two principal opens has a polynomial
denominator-clearing witness. The extra common-product factor coming
from equality in the overlap localization is retained explicitly. -/
theorem clear_two_open_boundary (x y : R)
    [IsLocalization.Away x S] [IsLocalization.Away y T]
    [IsLocalization.Away (x*y) U]
    (f : S →+* U) (g : T →+* U)
    (hf : ∀ a, f (algebraMap R S a) = algebraMap R U a)
    (hg : ∀ a, g (algebraMap R T a) = algebraMap R U a)
    (a : S) (b : T) (p : R) (n m : ℕ)
    (h : (f a + g b) * algebraMap R U x ^ n * algebraMap R U y ^ m =
      algebraMap R U p) :
    ∃ (N M : ℕ) (q s : R), n ≤ N ∧ m ≤ M ∧
      p*x^(N-n)*y^(M-m) = q*x^N+s*y^M := by
  obtain ⟨na, a0, ha⟩ := IsLocalization.Away.surj x a
  obtain ⟨nb, b0, hb⟩ := IsLocalization.Away.surj y b
  have ha' : f a * algebraMap R U x ^ na = algebraMap R U a0 := by
    simpa only [map_mul, map_pow, hf] using congrArg f ha
  have hb' : g b * algebraMap R U y ^ nb = algebraMap R U b0 := by
    simpa only [map_mul, map_pow, hg] using congrArg g hb
  have heq : algebraMap R U (p*x^na*y^nb) =
      algebraMap R U (a0*x^n*y^(m+nb)+b0*x^(n+na)*y^m) := by
    simp only [map_mul, map_add, map_pow, pow_add]
    rw [← h, ← ha', ← hb']
    ring
  obtain ⟨k, hk⟩ := IsLocalization.Away.exists_of_eq (x*y) heq
  refine ⟨n+na+k, m+nb+k, b0*y^(m+k), a0*x^(n+k), by omega, by omega, ?_⟩
  have hn : n+na+k-n=na+k := by omega
  have hm : m+nb+k-m=nb+k := by omega
  rw [hn,hm]
  simp only [mul_pow,pow_add] at hk ⊢
  linear_combination hk

end TwoOpens

section UnitPowers
variable {R : Type*} [CommRing R]

/-- Removing unit factors from the two denominator generators does not
change whether a numerator has an unrestricted boundary witness. -/
theorem unscale_boundary (a b p q s : R) (u v : Rˣ) (d e N M : ℕ)
    (hN : 1 ≤ N) (hM : 1 ≤ M)
    (h : p*((u:R)*a^d)^(N-1)*((v:R)*b^e)^(M-1) =
      q*((u:R)*a^d)^N+s*((v:R)*b^e)^M) :
    ∃ q' s' : R, p*a^(d*(N-1))*b^(e*(M-1)) =
      q'*a^(d*N)+s'*b^(e*M) := by
  refine ⟨q*(u:R)*((v⁻¹:Rˣ):R)^(M-1),
    s*(v:R)*((u⁻¹:Rˣ):R)^(N-1), ?_⟩
  have hu : (u:R)^(N-1)*((u⁻¹:Rˣ):R)^(N-1)=1 := by
    rw [← mul_pow, u.mul_inv, one_pow]
  have hv : (v:R)^(M-1)*((v⁻¹:Rˣ):R)^(M-1)=1 := by
    rw [← mul_pow, v.mul_inv, one_pow]
  have hNe : N=(N-1)+1 := by omega
  have hMe : M=(M-1)+1 := by omega
  have huN : (u:R)^N = (u:R)^(N-1)*(u:R) := by
    conv_lhs => rw [hNe,pow_succ]
  have hvM : (v:R)^M = (v:R)^(M-1)*(v:R) := by
    conv_lhs => rw [hMe,pow_succ]
  simp only [mul_pow, ← pow_mul] at h
  rw [huN,hvM] at h
  linear_combination ((u⁻¹:Rˣ):R)^(N-1)*((v⁻¹:Rˣ):R)^(M-1)*h -
    p*a^(d*(N-1))*b^(e*(M-1))*((v:R)^(M-1)*((v⁻¹:Rˣ):R)^(M-1))*hu -
    p*a^(d*(N-1))*b^(e*(M-1))*hv +
    q*a^(d*N)*(u:R)*((v⁻¹:Rˣ):R)^(M-1)*hu +
    s*b^(e*M)*(v:R)*((u⁻¹:Rˣ):R)^(N-1)*hv

end UnitPowers
end CycleQ2LocalizationBoundary

#print axioms CycleQ2LocalizationBoundary.clear_two_open_boundary
#print axioms CycleQ2LocalizationBoundary.unscale_boundary
end
end


/- Component: continuation_20261112/HomogeneousPrimeCoverOpen.lean -/
section
/-! A relevant-prime cover at the actual seed persists on an actual
polynomial open, via radical membership and finite homogeneous coefficient
maps. This does not invoke geometric smoothness as an assumed conclusion.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2HomogeneousPrimeCoverOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousIdealOpen
open scoped BigOperators

section HighDegree
variable {K : Type*} [CommRing K]

theorem coordinate_powers_of_prime_cover (I : Ideal (Poly K))
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime], I ≤ P →
      ∀ j : Fin 5, X j ∈ P) :
    ∃ n : Fin 5 → ℕ, ∀ j, (X j : Poly K)^n j ∈ I := by
  classical
  have hj (j : Fin 5) : (X j : Poly K) ∈ I.radical := by
    rw [Ideal.radical_eq_sInf, Ideal.mem_sInf]
    intro P hP
    letI : P.IsPrime := hP.2
    exact hcover P hP.1 j
  choose n hn using hj
  exact ⟨n,hn⟩

theorem high_degree_monomial_mem (I : Ideal (Poly K)) (n : Fin 5 → ℕ)
    (hn : ∀ j, (X j : Poly K)^n j ∈ I) (T : ℕ)
    (hT : (∑ j, n j) < T) (e : FullInvariantIndex (6*T)) :
    (monomial (fullExponentOf e.val) 1 : Poly K) ∈ I := by
  classical
  have hdvd : ∃ j : Fin 5, n j ≤ fullExponentOf e.val j := by
    by_contra h
    push_neg at h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have hd := e.property.1
    simp only [fullExponentOf_apply] at h0 h1 h2 h3 h4
    simp only [fullDegree] at hd
    simp [Fin.sum_univ_succ] at hT
    omega
  obtain ⟨j,hj⟩ := hdvd
  have he : Finsupp.single j (n j) ≤ fullExponentOf e.val :=
    Finsupp.single_le_iff.mpr hj
  have hm : (monomial (fullExponentOf e.val) 1 : Poly K) =
      X j^n j * monomial (fullExponentOf e.val-Finsupp.single j (n j)) 1 := by
    rw [X_pow_eq_monomial,monomial_mul,one_mul,add_tsub_cancel_of_le he]
  rw [hm]
  exact Ideal.mul_mem_right _ _ (hn j)

theorem high_degree_homogeneous_mem (I : Ideal (Poly K)) (n : Fin 5 → ℕ)
    (hn : ∀ j, (X j : Poly K)^n j ∈ I) (T : ℕ)
    (hT : (∑ j, n j) < T) (p : Poly K) (hp : HG p (6*T,0)) : p ∈ I := by
  rw [← fullInvariantPolynomial_of_homogeneous hp]
  apply Ideal.sum_mem
  intro e _
  simpa only [C_mul_monomial,mul_one] using
    Ideal.mul_mem_left I (C (p.coeff (fullExponentOf e.val)))
      (high_degree_monomial_mem I n hn T hT e)

theorem coordinate_power_homogeneous (T : ℕ) (j : Fin 5) :
    HG ((X j : Poly K)^(if j=4 then 3*T else 6*T)) (6*T,0) := by
  rw [X_pow_eq_monomial]
  apply isWeightedHomogeneous_monomial
  rw [Finsupp.weight_single]
  have h6 : (6 : ZMod 3)=0 := by decide
  fin_cases j <;> simp [fullGrading, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat,h6]
  <;> ring

end HighDegree

section CoefficientOpen
variable {R K : Type*} [CommRing R] [CommRing K]
  {ι : Type*} [Fintype ι]

/-- A seed cover by a finite homogeneous ideal gives a polynomial open
where the same ideal contains powers of every projective coordinate. -/
theorem exists_prime_cover_open (f : R →+* K) (c : K →+* R)
    (hfc : ∀ x, f (c x)=x) (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0))
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime],
      generatorIdeal (fun j => map f (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P) :
    ∃ s : R, f s=1 ∧
      ∀ (S : Type*) [CommRing S] (φ : R →+* S), IsUnit (φ s) →
        ∀ (P : Ideal (Poly S)) [P.IsPrime],
          generatorIdeal (fun j => map φ (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P := by
  classical
  obtain ⟨n,hn⟩ := coordinate_powers_of_prime_cover
    (generatorIdeal (fun j => map f (g j))) hcover
  let T := (∑ j, n j) + (∑ j, degree j) + 1
  have hT : (∑ j, n j) < T := by dsimp [T]; omega
  have hle (j : ι) : degree j ≤ 6*T := by
    have hj : degree j ≤ ∑ i : ι, degree i :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (degree i)) (Finset.mem_univ j)
    dsimp [T]
    omega
  have hseed (p : Poly K) (hp : HG p (6*T,0)) :
      p ∈ generatorIdeal (fun j => map f (g j)) :=
    high_degree_homogeneous_mem _ n hn T hT p hp
  obtain ⟨s,hs,hspec⟩ := exists_homogeneous_open f c hfc g degree hgen (6*T) hle hseed
  refine ⟨s,hs,?_⟩
  intro S _ φ hφ P _ hP j
  have hj := hspec S φ hφ _ (coordinate_power_homogeneous (K := S) T j)
  exact (inferInstance : P.IsPrime).mem_of_pow_mem _ (hP hj)

/-- Pointedness forces every open containing the seed to remain a unit
over the generic field, so the actual projective prime cover persists. -/
theorem prime_cover_of_pointed {L : Type*} [Field L]
    (f : R →+* K) (c : K →+* R) (hfc : ∀ x, f (c x)=x)
    (g : ι → Poly R) (degree : ι → ℕ)
    (hgen : ∀ j, HG (g j) (degree j,0)) [Nontrivial K]
    (hcover : ∀ (P : Ideal (Poly K)) [P.IsPrime],
      generatorIdeal (fun j => map f (g j)) ≤ P → ∀ j : Fin 5, X j ∈ P)
    (φ : R →+* L) (hpointed : ∀ a, φ a=0 → f a=0)
    (P : Ideal (Poly L)) [P.IsPrime]
    (hP : generatorIdeal (fun j => map φ (g j)) ≤ P) :
    ∀ j : Fin 5, X j ∈ P := by
  obtain ⟨s,hs,hopen⟩ := exists_prime_cover_open f c hfc g degree hgen hcover
  have hu : IsUnit (φ s) := by
    apply isUnit_iff_ne_zero.mpr
    intro hz
    exact one_ne_zero (hs.symm.trans (hpointed s hz))
  exact hopen L φ hu P hP

end CoefficientOpen
end CycleQ2HomogeneousPrimeCoverOpen

#print axioms CycleQ2HomogeneousPrimeCoverOpen.exists_prime_cover_open
#print axioms CycleQ2HomogeneousPrimeCoverOpen.prime_cover_of_pointed
end
end


/- Component: continuation_20261112/SeedGenuineNormalConnecting.lean -/
section
/-!
# Genuine normal lifts and their overlap coefficient

The map throughout this file is the dual of the actual natural cotangent
map for J=(F,h) contained in I=(f1,f2,h). A basis of the source conormal
module is required to consist of the actual equation classes. Such bases
are already constructed on the seed Jacobian charts and at every relevant
prime. The statements are also ready for a global equation-class basis.

The second denominator chart receives its genuine target conormal basis.
Both local splitting formulas are realized as actual normal homomorphisms,
their difference is in the kernel of the natural map, and its canonical
kernel coordinate is the existing overlapCoefficient. The final identities
describe changes of lifts; graded sheaf gluing is a separate construction.
-/

noncomputable section
open scoped TensorProduct BigOperators
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2GenuineNormalConnecting

open CycleQ2ConormalJacobian CycleQ2NaturalNormalMap
  CycleQ2NormalConnecting CycleQ2SeedTrace

variable {S : Type*} [CommRing S] [Algebra P S] [Algebra ℂ S]
  [IsScalarTower ℂ P S]

abbrev CurveConormal (r θ : ℂ) := S ⊗[P] (ambientCurveIdeal r θ).Cotangent
abbrev SurfaceConormal (r θ : ℂ) := S ⊗[P] (surfaceIdeal r θ).Cotangent
abbrev CurveNormal (r θ : ℂ) := CurveConormal (S := S) r θ →ₗ[S] S
abbrev SurfaceNormal (r θ : ℂ) := SurfaceConormal (S := S) r θ →ₗ[S] S

def curveClass (r θ : ℂ) (i : Fin 3) : CurveConormal (S := S) r θ :=
  (1 : S) ⊗ₜ[P] conormalGenerator r θ i

def surfaceClass (r θ : ℂ) (j : Fin 2) : SurfaceConormal (S := S) r θ :=
  generator (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl j

theorem curveNormal_ext (r θ : ℂ) {φ ψ : CurveNormal (S := S) r θ}
    (h : ∀ i, φ (curveClass r θ i) = ψ (curveClass r θ i)) : φ = ψ := by
  apply LinearMap.ext_on_range
    (generators_span (S := S) (ambientCurveIdeal r θ) (curveEquations r θ) rfl)
  exact h

theorem surfaceNormal_ext (r θ : ℂ) {φ ψ : SurfaceNormal (S := S) r θ}
    (h : ∀ j, φ (surfaceClass r θ j) = ψ (surfaceClass r θ j)) : φ = ψ := by
  apply LinearMap.ext_on_range
    (generators_span (S := S) (surfaceIdeal r θ) (surfaceEquations r θ) rfl)
  exact h

section SecondChart

def secondSurfaceDuals (d : Fin 3 → Derivation ℂ P S) (u : Sˣ) (k : S) :
    Fin 2 → Derivation ℂ P S :=
  ![(↑(u⁻¹) : S) • d 1, d 2 - (k * (↑(u⁻¹) : S)) • d 1]

theorem secondSurfaceDuals_equations (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S originalG2) (i j : Fin 2) :
    secondSurfaceDuals d u (algebraMap P S (thetaK θ)) i
      (surfaceEquations r θ j) = if i = j then 1 else 0 := by
  have hF1 := sourceDual_F r θ hI d hd 1
  have hF2 := sourceDual_F r θ hI d hd 2
  change d 1 (actualSeedEquation r θ) = algebraMap P S originalG2 at hF1
  change d 2 (actualSeedEquation r θ) = algebraMap P S (thetaK θ) at hF2
  have hh1 : d 1 (thetaH θ) = 0 := by simpa [curveEquations] using hd 1 2
  have hh2 : d 2 (thetaH θ) = 1 := by simpa [curveEquations] using hd 2 2
  rw [← hu] at hF1
  fin_cases i <;> fin_cases j <;>
    simp [secondSurfaceDuals, surfaceEquations, Derivation.smul_apply,
      Derivation.sub_apply, hF1, hF2, hh1, hh2, smul_eq_mul, mul_assoc]

/-- The actual target conormal basis on a source Jacobian chart where g2
is a unit. It complements surfaceConormalBasisOnFirstOpen. -/
def surfaceConormalBasisOnSecondOpen (r θ : ℂ)
    (hI : ∀ p ∈ ambientCurveIdeal r θ, algebraMap P S p = 0)
    (d : Fin 3 → Derivation ℂ P S)
    (hd : ∀ i j, d i (curveEquations r θ j) = if i = j then 1 else 0)
    (u : Sˣ) (hu : (u : S) = algebraMap P S originalG2) :
    Module.Basis (Fin 2) S (SurfaceConormal (S := S) r θ) :=
  conormalBasis (surfaceIdeal r θ)
    (fun p hp => hI p (surfaceIdeal_le_curveIdeal r θ hp))
    (surfaceEquations r θ) rfl
    (secondSurfaceDuals d u (algebraMap P S (thetaK θ)))
    (secondSurfaceDuals_equations r θ hI d hd u hu)

end SecondChart

section ActualLifts

variable (r θ : ℂ)
variable (b : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
variable (hb : ∀ i, b i = curveClass r θ i)

def fromCoordinates : (Fin 3 → S) ≃ₗ[S] CurveNormal (S := S) r θ := b.constr S

include hb in
@[simp] theorem fromCoordinates_class (v : Fin 3 → S) (i : Fin 3) :
    fromCoordinates r θ b v (curveClass r θ i) = v i := by
  rw [← hb i]
  exact b.constr_basis S v i

include hb in
@[simp] theorem fromCoordinates_symm_class (φ : CurveNormal (S := S) r θ) (i : Fin 3) :
    (fromCoordinates r θ b).symm φ i = φ (curveClass r θ i) := by
  change φ (b i) = _
  rw [hb i]

include hb in
/-- The coordinate constructor does not depend on a choice of derivative
duals or of a basis construction once its equation values are fixed. -/
theorem fromCoordinates_unique
    (b' : Module.Basis (Fin 3) S (CurveConormal (S := S) r θ))
    (hb' : ∀ i, b' i = curveClass r θ i) (v : Fin 3 → S) :
    fromCoordinates r θ b v = fromCoordinates r θ b' v := by
  apply curveNormal_ext r θ
  intro i
  rw [fromCoordinates_class r θ b hb, fromCoordinates_class r θ b' hb']

include hb in
theorem naturalNormalMap_fromCoordinates (v : Fin 3 → S) :
    (fun j => naturalNormalMap r θ (fromCoordinates r θ b v) (surfaceClass r θ j)) =
      equationMap (algebraMap P S (originalG1 r)) (algebraMap P S originalG2)
        (algebraMap P S (thetaK θ)) v := by
  calc
    _ = equationMap (algebraMap P S (originalG1 r)) (algebraMap P S originalG2)
        (algebraMap P S (thetaK θ))
        (fun i => fromCoordinates r θ b v (curveClass r θ i)) :=
      naturalNormalMap_equation_coordinates r θ (fromCoordinates r θ b v)
    _ = _ := by
      congr 1
      funext i
      exact fromCoordinates_class r θ b hb v i

def firstGenuineLift (u : Sˣ) (A L : S) : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b (firstLift u (algebraMap P S (thetaK θ)) A L)

def secondGenuineLift (u : Sˣ) (A L : S) : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b (secondLift u (algebraMap P S (thetaK θ)) A L)

def genuineKernelGenerator : CurveNormal (S := S) r θ :=
  fromCoordinates r θ b
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))

include hb in
theorem firstGenuineLift_equations (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (A L : S) :
    (fun j => naturalNormalMap r θ (firstGenuineLift r θ b u A L) (surfaceClass r θ j)) =
      ![-A, -L] := by
  rw [firstGenuineLift, naturalNormalMap_fromCoordinates r θ b hb, ← hu]
  exact equationMap_firstLift u _ _ A L

include hb in
theorem secondGenuineLift_equations (u : Sˣ)
    (hu : (u : S) = algebraMap P S originalG2) (A L : S) :
    (fun j => naturalNormalMap r θ (secondGenuineLift r θ b u A L) (surfaceClass r θ j)) =
      ![-A, -L] := by
  rw [secondGenuineLift, naturalNormalMap_fromCoordinates r θ b hb, ← hu]
  exact equationMap_secondLift u _ _ A L

include hb in
/-- These are two lifts of the same genuine target normal homomorphism,
not merely solutions of an independently specified coordinate matrix. -/
theorem genuineLifts_same_image (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    naturalNormalMap r θ (firstGenuineLift r θ b u A L) =
      naturalNormalMap r θ (secondGenuineLift r θ b v A L) := by
  apply surfaceNormal_ext r θ
  intro j
  exact congrFun ((firstGenuineLift_equations r θ b hb u hu A L).trans
    (secondGenuineLift_equations r θ b hb v hv A L).symm) j

include hb in
theorem genuineKernelGenerator_mem :
    naturalNormalMap r θ (genuineKernelGenerator r θ b) = 0 := by
  apply surfaceNormal_ext r θ
  intro j
  have h := congrFun (naturalNormalMap_fromCoordinates r θ b hb
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))) j
  simpa only [equationMap_kernelVector, Pi.zero_apply, LinearMap.zero_apply,
    genuineKernelGenerator] using h

/-- The literal scalar in the genuine kernel is the existing normal
connecting coefficient, with first-chart-minus-second-chart sign. -/
theorem genuineLift_difference (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    firstGenuineLift r θ b u A L - secondGenuineLift r θ b v A L =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L •
        genuineKernelGenerator r θ b := by
  rw [firstGenuineLift, secondGenuineLift, ← map_sub, local_lift_difference, map_smul]
  rw [hu, hv]
  rfl

/-- The first-chart scalar coordinate of a genuine normal homomorphism.
On the kernel it is inverse to c |-> c * genuineKernelGenerator. -/
def kernelCoefficient (u : Sˣ) : CurveNormal (S := S) r θ →ₗ[S] S where
  toFun φ := -(φ (curveClass r θ 1) * (↑(u⁻¹) : S))
  map_add' φ ψ := by simp [add_mul, add_comm]
  map_smul' c φ := by simp [smul_eq_mul, mul_assoc]

include hb in
theorem kernelCoefficient_generator (u : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r)) (c : S) :
    kernelCoefficient r θ u (c • genuineKernelGenerator r θ b) = c := by
  change -((c * fromCoordinates r θ b
    (kernelVector (algebraMap P S (originalG1 r)) (algebraMap P S originalG2))
      (curveClass r θ 1)) * (↑(u⁻¹) : S)) = c
  rw [fromCoordinates_class r θ b hb]
  change -(c * (-algebraMap P S (originalG1 r)) * (↑(u⁻¹) : S)) = c
  rw [← hu]
  simp [mul_assoc]

include hb in
theorem genuineLift_difference_coefficient (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S) :
    kernelCoefficient r θ u
        (firstGenuineLift r θ b u A L - secondGenuineLift r θ b v A L) =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L := by
  rw [genuineLift_difference r θ b u v hu hv,
    kernelCoefficient_generator r θ b hb u hu]

include hb in
/-- Changing the two local lifts changes the connecting coordinate by
the difference of their kernel coordinates, the Cech coboundary formula. -/
theorem changed_lifts_coefficient (u v : Sˣ)
    (hu : (u : S) = algebraMap P S (originalG1 r))
    (hv : (v : S) = algebraMap P S originalG2) (A L : S)
    (a b' : CurveNormal (S := S) r θ) :
    kernelCoefficient r θ u
      ((firstGenuineLift r θ b u A L + a) - (secondGenuineLift r θ b v A L + b')) =
      overlapCoefficient u v (algebraMap P S (thetaK θ)) A L +
        kernelCoefficient r θ u a - kernelCoefficient r θ u b' := by
  have h := genuineLift_difference_coefficient r θ b hb u v hu hv A L
  rw [map_sub] at h
  simp only [map_sub, map_add]
  rw [show kernelCoefficient r θ u (firstGenuineLift r θ b u A L) +
      kernelCoefficient r θ u a -
      (kernelCoefficient r θ u (secondGenuineLift r θ b v A L) + kernelCoefficient r θ u b') =
      (kernelCoefficient r θ u (firstGenuineLift r θ b u A L) -
        kernelCoefficient r θ u (secondGenuineLift r θ b v A L)) +
        kernelCoefficient r θ u a - kernelCoefficient r θ u b' by abel]
  rw [h]

end ActualLifts
end CycleQ2GenuineNormalConnecting

#print axioms CycleQ2GenuineNormalConnecting.surfaceConormalBasisOnSecondOpen
#print axioms CycleQ2GenuineNormalConnecting.genuineLifts_same_image
#print axioms CycleQ2GenuineNormalConnecting.genuineLift_difference_coefficient
#print axioms CycleQ2GenuineNormalConnecting.changed_lifts_coefficient
end
end


/- Component: continuation_20261112/SeedBoundaryProjection.lean -/
section
/-!
# Homogeneous extraction from arbitrary seed Cech boundary coefficients

For the actual theta-family curve ideal, an arbitrary polynomial boundary
witness for a homogeneous degree-one fraction can be projected to the
correct homogeneous numerator degrees. Thus unbounded and initially
inhomogeneous numerator coefficients introduce no additional boundaries
for the checked derivative fraction. Localization denominator clearing is
a separate input to this purely polynomial step.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedBoundaryProjection

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
  CycleQ2HomogeneousComponent
open CycleQ2SeedCech (curveA curveB)

theorem curveA_homogeneous : curveA.IsHomogeneous 2 := by
  simpa [curveA] using (isHomogeneous_X ℂ (1 : Fin 4)).mul (isHomogeneous_X ℂ (3 : Fin 4))

theorem curveB_homogeneous : curveB.IsHomogeneous 1 := by
  exact isHomogeneous_X ℂ (2 : Fin 4)

/-- Homogeneous projection of arbitrary denominator-clearing coefficients.
The bound on N,M permits every higher pole order needed by localization. -/
theorem boundary_of_unrestricted_witness (r θ : ℂ) (p : Poly)
    (hp : p.IsHomogeneous 9) (N M : ℕ) (q s : Poly)
    (hn : 2 ≤ N) (hm : 4 ≤ M)
    (hmem : p * curveA ^ (N - 2) * curveB ^ (M - 4) -
      (q * curveA ^ N + s * curveB ^ M) ∈ curveIdeal r θ) :
    CechBoundary r θ p 2 4 := by
  let D := 2 * N + M + 1
  have hD2 : 2 ≤ D := by dsimp [D]; omega
  have hD3 : 3 ≤ D := by dsimp [D]; omega
  have hAN : (curveA ^ N).IsHomogeneous (2 * N) := curveA_homogeneous.pow N
  have hBM : (curveB ^ M).IsHomogeneous M := by simpa using curveB_homogeneous.pow M
  have hp' : (p * curveA ^ (N - 2) * curveB ^ (M - 4)).IsHomogeneous D := by
    convert (hp.mul (curveA_homogeneous.pow (N - 2))).mul
      (curveB_homogeneous.pow (M - 4)) using 1 <;> dsimp [D] <;> omega
  obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.mp hmem
  have hh := congrArg (homogeneousComponent D) huv
  have hF : (relation r 0).IsHomogeneous 2 := CycleQ2SeedCech.curveF1_homogeneous r
  rw [map_add, component_mul_of_homogeneous _ _ hF hD2,
    component_mul_of_homogeneous _ _ (curveH_homogeneous θ) hD3,
    map_sub, map_add, homogeneousComponent_eq_self hp',
    component_mul_of_homogeneous _ _ hAN (by dsimp [D]; omega),
    component_mul_of_homogeneous _ _ hBM (by dsimp [D]; omega)] at hh
  have hDA : D - 2 * N = M + 1 := by dsimp [D]; omega
  have hDB : D - M = 2 * N + 1 := by dsimp [D]; omega
  rw [hDA, hDB] at hh
  refine ⟨N, M, homogeneousComponent (M + 1) q,
    homogeneousComponent (2 * N + 1) s, hn, hm,
    homogeneousComponent_isHomogeneous _ _, homogeneousComponent_isHomogeneous _ _, ?_⟩
  apply Ideal.mem_span_pair.mpr
  exact ⟨homogeneousComponent (D - 2) u, homogeneousComponent (D - 3) v, hh⟩

theorem cubicColumn_homogeneous (j : Fin 9) : (cubicColumn j).IsHomogeneous 3 := by
  have hm (a b c d : ℕ) (hd : a + b + c + d = 3) : (mon a b c d).IsHomogeneous 3 := by
    simpa only [hd] using CycleQ2SeedCech.mon_homogeneous a b c d
  fin_cases j
  · simpa [cubicColumn] using (hm 0 0 2 1 (by omega)).neg
  · simpa [cubicColumn] using hm 0 0 0 3 (by omega)
  · simpa [cubicColumn] using hm 0 0 3 0 (by omega)
  · simpa [cubicColumn] using hm 0 1 1 1 (by omega)
  · simpa [cubicColumn] using hm 0 3 0 0 (by omega)
  · simpa [cubicColumn] using hm 1 0 1 1 (by omega)
  · simpa [cubicColumn] using hm 1 2 0 0 (by omega)
  · simpa [cubicColumn] using hm 2 1 0 0 (by omega)
  · simpa [cubicColumn] using hm 3 0 0 0 (by omega)

theorem cubicDeformation_homogeneous (v : Fin 9 → ℂ) :
    (cubicDeformation v).IsHomogeneous 3 := by
  show (∑ j : Fin 9, C (v j) * cubicColumn j) ∈ homogeneousSubmodule (Fin 4) ℂ 3
  apply Submodule.sum_mem
  intro j hj
  exact (cubicColumn_homogeneous j).C_mul (v j)

theorem derivativeNumerator_homogeneous (v : Fin 9 → ℂ) :
    (derivativeNumerator (cubicDeformation v)).IsHomogeneous 9 := by
  exact (((isHomogeneous_X_pow (2 : Fin 4) 3).neg).mul
    (isHomogeneous_X_pow (3 : Fin 4) 3)).mul (cubicDeformation_homogeneous v)

/-- The actual nonzero trace excludes arbitrary polynomial boundary
coefficients once denominators have been cleared. -/
theorem no_unrestricted_boundary (r θ : ℂ) (hr : r ≠ 0)
    (v : Fin 9 → ℂ) (hv : derivativeTrace θ v ≠ 0)
    (N M : ℕ) (q s : Poly) (hn : 2 ≤ N) (hm : 4 ≤ M) :
    derivativeNumerator (cubicDeformation v) * curveA ^ (N - 2) * curveB ^ (M - 4) -
      (q * curveA ^ N + s * curveB ^ M) ∉ curveIdeal r θ := by
  intro hmem
  exact nonboundary_of_derivativeTrace_ne_zero r θ hr v hv
    (boundary_of_unrestricted_witness r θ _ (derivativeNumerator_homogeneous v)
      N M q s hn hm hmem)

end CycleQ2SeedBoundaryProjection

#print axioms CycleQ2SeedBoundaryProjection.boundary_of_unrestricted_witness
#print axioms CycleQ2SeedBoundaryProjection.no_unrestricted_boundary
end
end


/- Component: continuation_20261112/SeedTwoOpenCover.lean -/
section
/-!
# The two denominator opens cover the actual projective seed curve

On a prime of the curve, simultaneous vanishing of g1 and g2 forces
x1*x3 and x2 to vanish. The quadratic then forces x0 to vanish, and the
literal cubic with coefficients -i and 1-i forces both remaining
coordinates to vanish. Thus D(g1),D(g2) contain every relevant prime.
The statement applies to the weighted five-variable presentation as well.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedTwoOpenCover

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta CycleQ2NormalConnecting
open CycleQ2SeedCech (curveA curveB)

private theorem mem_of_C_mul (Q : Ideal Poly) (c : ℂ) (hc : c ≠ 0) (p : Poly)
    (hp : C c * p ∈ Q) : p ∈ Q := by
  have hh := Q.mul_mem_left (C (c⁻¹)) hp
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel₀ hc, map_one, one_mul] using hh

private theorem one_sub_I_ne_zero : (1 - Complex.I : ℂ) ≠ 0 := by
  intro hzero
  have hh := congrArg Complex.im hzero
  norm_num at hh

/-- The two small homogeneous functions have no common relevant prime
on the literal theta-family curve. -/
theorem coordinates_mem_of_A_B (r θ : ℂ) (Q : Ideal Poly) [Q.IsPrime]
    (hcurve : curveIdeal r θ ≤ Q) (hA : curveA ∈ Q) (hB : curveB ∈ Q) :
    ∀ j : Fin 4, X j ∈ Q := by
  have hF : relation r 0 ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hH : curveH θ ∈ Q := hcurve (Ideal.subset_span (by simp))
  have hx0sq : (X (0 : Fin 4)) ^ 2 ∈ Q := by
    have hh := Q.add_mem hF (Q.mul_mem_left (C r) hA)
    simpa [relation, curveA, mul_assoc] using hh
  have hx0 : (X (0 : Fin 4)) ∈ Q :=
    (inferInstance : Q.IsPrime).mem_of_pow_mem 2 hx0sq
  have hx2 : (X (2 : Fin 4)) ∈ Q := hB
  have hrest : X (2 : Fin 4) * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
      X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2) ∈ Q :=
    Q.add_mem (Q.mul_mem_right _ hx2) (Q.mul_mem_right _ hx0)
  have hshape : curveH θ =
      (C (1 - Complex.I) * X 3 ^ 3 - C Complex.I * X 1 ^ 3) +
        (X 2 * (X 2 ^ 2 + X 1 * X 3 + X 0 * X 3) +
          X 0 * (X 1 ^ 2 + C θ * X 0 ^ 2)) := by
    simp [curveH, h, b, map_sub]
    ring
  have htail : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 -
      C Complex.I * X 1 ^ 3 ∈ Q := by
    have hh := Q.sub_mem hH hrest
    simpa only [hshape, add_sub_cancel_right] using hh
  have h13 : X (1 : Fin 4) ∈ Q ∧ X (3 : Fin 4) ∈ Q := by
    rcases (inferInstance : Q.IsPrime).mem_or_mem hA with hx1 | hx3
    · have hx1pow := Q.pow_mem_of_mem hx1 3 (by decide)
      have hh := Q.add_mem htail (Q.mul_mem_left (C Complex.I) hx1pow)
      have hc : C (1 - Complex.I) * X (3 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_add_cancel] using hh
      exact ⟨hx1, (inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ one_sub_I_ne_zero _ hc)⟩
    · have hx3pow := Q.pow_mem_of_mem hx3 3 (by decide)
      have hh := Q.sub_mem (Q.mul_mem_left (C (1 - Complex.I)) hx3pow) htail
      have hc : C Complex.I * X (1 : Fin 4) ^ 3 ∈ Q := by
        simpa only [sub_sub_cancel] using hh
      exact ⟨(inferInstance : Q.IsPrime).mem_of_pow_mem 3
        (mem_of_C_mul Q _ Complex.I_ne_zero _ hc), hx3⟩
  intro j
  fin_cases j
  · exact hx0
  · exact h13.1
  · exact hx2
  · exact h13.2

/-- If both denominator functions lie in a prime of the actual curve,
then all four ordinary homogeneous coordinates lie in that prime. -/
theorem coordinates_mem_of_denominators (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (h1 : curveG1 r θ ∈ Q) (h2 : curveG2 r θ ∈ Q) :
    ∀ j : Fin 4, curveMap r θ (X j) ∈ Q := by
  let T : Ideal Poly := Q.comap (curveMap r θ)
  letI : T.IsPrime := Ideal.comap_isPrime _ _
  have hcurve : curveIdeal r θ ≤ T := by
    intro p hp
    change curveMap r θ p ∈ Q
    have hz : curveMap r θ p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hp
    rw [hz]
    exact Q.zero_mem
  have hg1 : C (3 * r ^ 2) * curveA ^ 2 ∈ T := by
    change curveMap r θ (C (3 * r ^ 2) * curveA ^ 2) ∈ Q
    rw [← ambientCurveMap_g1]
    exact h1
  have hg2 : C 3 * curveB ^ 4 ∈ T := by
    change curveMap r θ (C 3 * curveB ^ 4) ∈ Q
    rw [← ambientCurveMap_g2]
    exact h2
  have hA : curveA ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 2
    (mem_of_C_mul T _ (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) _ hg1)
  have hB : curveB ∈ T := (inferInstance : T.IsPrime).mem_of_pow_mem 4
    (mem_of_C_mul T _ (by norm_num) _ hg2)
  exact coordinates_mem_of_A_B r θ T hcurve hA hB

/-- The actual denominator opens cover every relevant prime of the
ordinary homogeneous curve presentation. -/
theorem relevant_prime_cover (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (hx : ∃ j : Fin 4, curveMap r θ (X j) ∉ Q) :
    curveG1 r θ ∉ Q ∨ curveG2 r θ ∉ Q := by
  by_contra! hbad
  obtain ⟨j, hj⟩ := hx
  exact hj (coordinates_mem_of_denominators r θ hr Q hbad.1 hbad.2 j)

/-- The same cover on the literal weighted curve: w=-x2² introduces no
additional relevant prime outside the two opens. -/
theorem weighted_relevant_prime_cover (r θ : ℂ) (hr : r ≠ 0)
    (Q : Ideal (CurveRing r θ)) [Q.IsPrime]
    (hx : ∃ j : Fin 5, ambientCurveMap r θ (X j) ∉ Q) :
    curveG1 r θ ∉ Q ∨ curveG2 r θ ∉ Q := by
  by_contra! hbad
  have hc := coordinates_mem_of_denominators r θ hr Q hbad.1 hbad.2
  have hw : ∀ j : Fin 5, ambientCurveMap r θ (X j) ∈ Q := by
    intro j
    fin_cases j
    · simpa [ambientCurveMap, substitute] using hc 0
    · simpa [ambientCurveMap, substitute] using hc 1
    · simpa [ambientCurveMap, substitute] using hc 2
    · simpa [ambientCurveMap, substitute] using hc 3
    · simpa [ambientCurveMap, substitute] using
        Q.neg_mem (Q.pow_mem_of_mem (hc 2) 2 (by decide))
  obtain ⟨j, hj⟩ := hx
  exact hj (hw j)

end CycleQ2SeedTwoOpenCover

#print axioms CycleQ2SeedTwoOpenCover.relevant_prime_cover
#print axioms CycleQ2SeedTwoOpenCover.weighted_relevant_prime_cover
end
end


/- Component: continuation_20261112/UniversalSurfaceFiniteFree.lean -/
section
/-!
# The normalized universal incidence surface is finite free over three coordinates

The two equations are the actual full invariant cubic and sextic, with their
distinguished coefficients normalized to one.  No seed specialization, smoothness,
or cohomological flatness is assumed.  The nine basis vectors are the original
classes of x0^a*w^b.  This supplies the missing relative input for the explicit
three-coordinate Cech calculation.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2UniversalSurface

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2SeedQuotientFiniteFree
open scoped MonomialOrder

variable (R : Type*) [CommRing R]

def selectedExponent (e : Fin 5 →₀ ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (e 0) + Finsupp.single 1 (e 4)

def remainingExponent (e : Fin 5 →₀ ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (e 1) + Finsupp.single 1 (e 2) + Finsupp.single 2 (e 3)

theorem regroup_monomial (e : Fin 5 →₀ ℕ) (c : R) :
    regroup R (monomial e c) =
      monomial (selectedExponent e) (monomial (remainingExponent e) c) := by
  simp only [MvPolynomial.monomial_eq]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_succ, selectedExponent, remainingExponent, Fin.reduceSucc]
  ring

def nestedWeight : (Fin 2 →₀ ℕ) →+ ℕ where
  toFun e := 3 * e 0 + 7 * e 1
  map_zero' := by simp
  map_add' a b := by simp only [Finsupp.add_apply]; omega

def nestedOrder : MonomialOrder (Fin 2) :=
  weightedOrder MonomialOrder.lex nestedWeight

def nestedCubic (hcoeff : FullCubicTailIndex → R) : Nested R :=
  monomial (Finsupp.single 0 3) 1 +
    ∑ e, monomial (selectedExponent (fullExponentOf e.val.val))
      (monomial (remainingExponent (fullExponentOf e.val.val)) (hcoeff e))

def nestedSextic (Fcoeff : FullSexticTailIndex → R) : Nested R :=
  monomial (Finsupp.single 1 3) 1 +
    ∑ e, monomial (selectedExponent (fullExponentOf e.val.val))
      (monomial (remainingExponent (fullExponentOf e.val.val)) (Fcoeff e))

theorem regroup_cubic (hcoeff : FullCubicTailIndex → R) :
    regroup R (normalizedFullCubic hcoeff) = nestedCubic R hcoeff := by
  simp only [normalizedFullCubic, map_add, map_sum, regroup_monomial, nestedCubic]
  congr 1
  simp [selectedExponent, remainingExponent, Finsupp.single_apply]

theorem regroup_sextic (Fcoeff : FullSexticTailIndex → R) :
    regroup R (normalizedFullSextic Fcoeff) = nestedSextic R Fcoeff := by
  simp only [normalizedFullSextic, map_add, map_sum, regroup_monomial, nestedSextic]
  congr 1
  simp [selectedExponent, remainingExponent, Finsupp.single_apply]

theorem nestedCubic_leading [Nontrivial R] (hcoeff : FullCubicTailIndex → R) :
    nestedOrder.degree (nestedCubic R hcoeff) = Finsupp.single 0 3 ∧
      nestedOrder.Monic (nestedCubic R hcoeff) := by
  apply degree_monic_add_sum nestedOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [nestedWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have hc := e.val.property.2
    have h0 := e.property
    simp only [fullDegree, fullCharacter] at hd hc
    simp only [nestedWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      selectedExponent, Finsupp.add_apply, Finsupp.single_apply,
      fullExponentOf_apply]
    norm_num
    have h4 : (e.val.val 4).val ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h4 with h4 | h4
    · omega
    · have hc_lt : 2 * (e.val.val 0).val + 2 * (e.val.val 1).val +
          (e.val.val 2).val < 3 := by omega
      rw [Nat.mod_eq_of_lt hc_lt] at hc
      omega

theorem nestedSextic_leading [Nontrivial R] (Fcoeff : FullSexticTailIndex → R) :
    nestedOrder.degree (nestedSextic R Fcoeff) = Finsupp.single 1 3 ∧
      nestedOrder.Monic (nestedSextic R Fcoeff) := by
  apply degree_monic_add_sum nestedOrder
  · apply weightedOrder_lt_of_weight_lt
    norm_num [nestedWeight]
  · intro e
    apply weightedOrder_lt_of_weight_lt
    have hd := e.val.property.1
    have h4 := e.property
    simp only [fullDegree] at hd
    simp only [nestedWeight, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      selectedExponent, Finsupp.add_apply, Finsupp.single_apply,
      fullExponentOf_apply]
    norm_num
    omega

def surfaceIdeal (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Ideal (Poly R) :=
  equationsIdeal (normalizedFullCubic hcoeff) (normalizedFullSextic Fcoeff)

abbrev SurfaceRing (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) := Poly R ⧸ surfaceIdeal R hcoeff Fcoeff

instance surfaceModule (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Module (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  (inferInstance : Algebra (Base R) (SurfaceRing R hcoeff Fcoeff)).toModule

def nestedIdeal (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) : Ideal (Nested R) :=
  equationsIdeal (nestedCubic R hcoeff) (nestedSextic R Fcoeff)

theorem nestedIdeal_map (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    nestedIdeal R hcoeff Fcoeff =
      (surfaceIdeal R hcoeff Fcoeff).map (regroupOverBase R).toRingHom := by
  simp only [nestedIdeal, surfaceIdeal, equationsIdeal, Ideal.map_span,
    Set.image_insert_eq, Set.image_singleton]
  change Ideal.span {nestedCubic R hcoeff, nestedSextic R Fcoeff} =
    Ideal.span {regroup R (normalizedFullCubic hcoeff),
      regroup R (normalizedFullSextic Fcoeff)}
  rw [regroup_cubic, regroup_sextic]

def quotientRegroup (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    SurfaceRing R hcoeff Fcoeff ≃ₐ[Base R]
      (Nested R ⧸ nestedIdeal R hcoeff Fcoeff) :=
  Ideal.quotientEquivAlg _ _ (regroupOverBase R) (nestedIdeal_map R hcoeff Fcoeff)

theorem nested_coprime [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    ∀ j, nestedOrder.degree (nestedCubic R hcoeff) j = 0 ∨
      nestedOrder.degree (nestedSextic R Fcoeff) j = 0 := by
  intro j
  rw [(nestedCubic_leading R hcoeff).1, (nestedSextic_leading R Fcoeff).1]
  fin_cases j <;> simp

def nestedExponentEquiv [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    reducedExponents nestedOrder (nestedCubic R hcoeff) (nestedSextic R Fcoeff) ≃
      Fin 3 × Fin 3 where
  toFun d :=
    (⟨d.val 0, by
      have hd := d.property.1
      rw [(nestedCubic_leading R hcoeff).1, single_three_le_iff] at hd
      omega⟩,
     ⟨d.val 1, by
      have hd := d.property.2
      rw [(nestedSextic_leading R Fcoeff).1, single_three_le_iff] at hd
      omega⟩)
  invFun ij := ⟨Finsupp.single 0 ij.1.val + Finsupp.single 1 ij.2.val, by
    constructor
    · rw [(nestedCubic_leading R hcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.1.isLt
    · rw [(nestedSextic_leading R Fcoeff).1, single_three_le_iff]
      simpa using Nat.not_le_of_lt ij.2.isLt⟩
  left_inv d := by
    apply Subtype.ext
    ext j
    fin_cases j <;> simp
  right_inv ij := by
    apply Prod.ext <;> apply Fin.ext <;> simp

def nestedBasis [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (Nested R ⧸ nestedIdeal R hcoeff Fcoeff) :=
  (quotientBasis nestedOrder (nestedCubic R hcoeff) (nestedSextic R Fcoeff)
    (nestedCubic_leading R hcoeff).2 (nestedSextic_leading R Fcoeff).2
    (nested_coprime R hcoeff Fcoeff)).reindex
      (nestedExponentEquiv R hcoeff Fcoeff)

theorem nestedBasis_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : Fin 3 × Fin 3) :
    nestedBasis R hcoeff Fcoeff ab = Ideal.Quotient.mk (nestedIdeal R hcoeff Fcoeff)
      (X 0 ^ ab.1.val * X 1 ^ ab.2.val) := by
  unfold nestedBasis
  erw [Module.Basis.reindex_apply, quotientBasis_apply]
  congr 1
  change monomial (Finsupp.single 0 ab.1.val + Finsupp.single 1 ab.2.val) 1 = _
  rw [MvPolynomial.monomial_single_add, ← MvPolynomial.X_pow_eq_monomial]

def surfaceBasis [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Basis (Fin 3 × Fin 3) (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  (nestedBasis R hcoeff Fcoeff).map (quotientRegroup R hcoeff Fcoeff).symm.toLinearEquiv

theorem surfaceBasis_apply [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) (ab : Fin 3 × Fin 3) :
    surfaceBasis R hcoeff Fcoeff ab = Ideal.Quotient.mk (surfaceIdeal R hcoeff Fcoeff)
      ((X 0 : Poly R) ^ ab.1.val * X 4 ^ ab.2.val) := by
  apply (quotientRegroup R hcoeff Fcoeff).injective
  simp only [surfaceBasis, Module.Basis.map_apply, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.apply_symm_apply, nestedBasis_apply]
  change Ideal.Quotient.mk _ (X 0 ^ ab.1.val * X 1 ^ ab.2.val) =
    Ideal.Quotient.mk _ (regroup R ((X 0 : Poly R) ^ ab.1.val * X 4 ^ ab.2.val))
  simp

theorem surfaceQuotient_free [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Free (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  Module.Free.of_basis (surfaceBasis R hcoeff Fcoeff)

theorem surfaceQuotient_finite [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.Finite (Base R) (SurfaceRing R hcoeff Fcoeff) :=
  Module.Finite.of_basis (surfaceBasis R hcoeff Fcoeff)

theorem surfaceQuotient_rank_nine [Nontrivial R] (hcoeff : FullCubicTailIndex → R)
    (Fcoeff : FullSexticTailIndex → R) :
    Module.finrank (Base R) (SurfaceRing R hcoeff Fcoeff) = 9 := by
  rw [Module.finrank_eq_card_basis (surfaceBasis R hcoeff Fcoeff)]
  decide

end CycleQ2UniversalSurface

#print axioms CycleQ2UniversalSurface.surfaceBasis_apply
#print axioms CycleQ2UniversalSurface.surfaceQuotient_rank_nine
end
end


/- Component: continuation_20261112/CharacterTopCech.lean -/
section
/-!
# Top Cech coordinates in all three characters

The degree remains zero.  The character is retained as an explicit parameter,
so the ambient-test character-one piece is computed rather than identified
with the previously checked character-zero piece.  Their respective ranks
are eight and seven.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2CharacterTopCech

open CycleQ2SeedCechThreeOpen
open CycleQ2SeedCechTopCohomology (SmallExponents topExponent topExponent_negative
  topExponent_injective)
open scoped BigOperators

section Indices
variable (χ : ZMod 3)

abbrev TopIndex :=
  {q : ShiftIndex × SmallExponents // shiftedGrade q.1 (topExponent q.2) = (0,χ)}

theorem topIndex_count : Fintype.card (TopIndex χ) = if χ=0 then 7 else 8 := by
  fin_cases χ <;> decide

def topCoordinate (q : TopIndex χ) : ShiftIndex × LaurentExponent :=
  (q.val.1, topExponent q.val.2)

theorem topCoordinate_injective : Function.Injective (topCoordinate χ) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q : ShiftIndex × LaurentExponent => q.1) hab
  · exact topExponent_injective
      (congrArg (fun q : ShiftIndex × LaurentExponent => q.2) hab)

/-- The finite exponent bound uses degree zero and is uniform in the character. -/
theorem exists_topIndex (ab : ShiftIndex) (e : LaurentExponent)
    (he : ∀ i, e i < 0) (hg : shiftedGrade ab e = (0,χ)) :
    ∃ q : TopIndex χ, topCoordinate χ q = (ab,e) := by
  have hd := congrArg Prod.fst hg
  change (ab.1.val : ℤ) + 2 * ab.2.val + ∑ i, e i = 0 at hd
  rw [Fin.sum_univ_three] at hd
  have ha := ab.1.isLt
  have hb := ab.2.isLt
  have h0 := he 0
  have h1 := he 1
  have h2 := he 2
  have bounds (i : Fin 3) : (-e i - 1).toNat < 4 := by
    fin_cases i
    · change (-e 0 - 1).toNat < 4; omega
    · change (-e 1 - 1).toNat < 4; omega
    · change (-e 2 - 1).toNat < 4; omega
  let v : SmallExponents :=
    (⟨(-e 0 - 1).toNat, bounds 0⟩,
     ⟨(-e 1 - 1).toNat, bounds 1⟩,
     ⟨(-e 2 - 1).toNat, bounds 2⟩)
  have hv : topExponent v = e := by
    ext i
    fin_cases i
    · change -(((-e 0 - 1).toNat : ℤ) + 1) = e 0; omega
    · change -(((-e 1 - 1).toNat : ℤ) + 1) = e 1; omega
    · change -(((-e 2 - 1).toNat : ℤ) + 1) = e 2; omega
  refine ⟨⟨(ab,v), ?_⟩, ?_⟩
  · simpa only [hv] using hg
  · exact Prod.ext rfl hv

end Indices

variable (R : Type*) [CommRing R] (χ : ZMod 3)

abbrev Family := ShiftIndex → Laurent (R := R)

def gradedFamilies : Submodule R (Family R) where
  carrier := {p | ∀ ab, HasGrade ab (0,χ) (p ab)}
  zero_mem' := by intro ab e he; simp
  add_mem' hp hq ab := hasGrade_add ab (0,χ) (hp ab) (hq ab)
  smul_mem' c p hp ab := by
    intro e he
    simp [AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, hp ab e he]

def topProjection : gradedFamilies R χ →ₗ[R] ((TopIndex χ) →₀ R) where
  toFun p := Finsupp.equivFunOnFinite.symm
    (fun q ↦ (p.val q.val.1).coeff (topExponent q.val.2))
  map_add' p q := by ext i; simp [AddMonoidAlgebra.coeff_add]
  map_smul' c p := by ext i; simp [AddMonoidAlgebra.coeff_smul]

@[simp] theorem topProjection_apply (p : gradedFamilies R χ) (q : (TopIndex χ)) :
    topProjection R χ p q = (p.val q.val.1).coeff (topExponent q.val.2) := rfl

def basisFamily (q : (TopIndex χ)) : Family R := fun ab ↦
  if ab = q.val.1 then AddMonoidAlgebra.single (topExponent q.val.2) 1 else 0

@[simp] theorem basisFamily_coeff (q : (TopIndex χ)) (ab : ShiftIndex) (e : LaurentExponent) :
    (basisFamily R χ q ab).coeff e = if topCoordinate χ q = (ab, e) then 1 else 0 := by
  classical
  by_cases ha : ab = q.val.1
  · subst ab
    by_cases he : e = topExponent q.val.2
    · subst e; simp [basisFamily, topCoordinate]
    · simp [basisFamily, topCoordinate, he, Ne.symm he]
  · have ha' : q.val.1 ≠ ab := Ne.symm ha
    simp [basisFamily, topCoordinate, ha, ha']

def basisSection (q : (TopIndex χ)) : gradedFamilies R χ := ⟨basisFamily R χ q, by
  intro ab e he
  rw [basisFamily_coeff]
  split
  · next h =>
      have ha : q.val.1 = ab := congrArg Prod.fst h
      have h_exp : topExponent q.val.2 = e := congrArg Prod.snd h
      exact False.elim (he (ha ▸ h_exp ▸ q.property))
  · rfl⟩

@[simp] theorem topProjection_basisSection (q : (TopIndex χ)) :
    topProjection R χ (basisSection R χ q) = Finsupp.single q 1 := by
  ext j
  change (basisFamily R χ q j.val.1).coeff (topExponent j.val.2) = _
  rw [basisFamily_coeff]
  change (if topCoordinate χ q = topCoordinate χ j then 1 else 0) = _
  simp only [(topCoordinate_injective χ).eq_iff, Finsupp.single_apply]

theorem topProjection_surjective : Function.Surjective (topProjection R χ) := by
  intro p
  refine ⟨∑ q : (TopIndex χ), p q • basisSection R χ q, ?_⟩
  ext q
  simp

def poleSubmodule (s : Finset (Fin 3)) : Submodule R (gradedFamilies R χ) where
  carrier := {p | ∀ ab, HasPoles s (p.val ab)}
  zero_mem' := by intro ab e i hi hneg; simp
  add_mem' hp hq := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_add, hp ab e i hi hneg, hq ab e i hi hneg]
  smul_mem' c p hp := by
    intro ab e i hi hneg
    simp [AddMonoidAlgebra.coeff_smul, hp ab e i hi hneg]

/-- The sum of the three pair-open images in the triple-open graded space. -/
def topBoundary : Submodule R (gradedFamilies R χ) :=
  poleSubmodule R χ {0, 1} ⊔ poleSubmodule R χ {0, 2} ⊔ poleSubmodule R χ {1, 2}

theorem topProjection_zero_iff (p : gradedFamilies R χ) :
    topProjection R χ p = 0 ↔
      ∀ ab e, (∀ i, e i < 0) → (p.val ab).coeff e = 0 := by
  constructor
  · intro hp ab e he
    by_cases hg : shiftedGrade ab e = (0,χ)
    · obtain ⟨q, hq⟩ := exists_topIndex χ ab e he hg
      have ha : q.val.1 = ab := congrArg Prod.fst hq
      have hx : topExponent q.val.2 = e := congrArg Prod.snd hq
      have hh := congrArg (fun f : (TopIndex χ) →₀ R ↦ f q) hp
      simpa only [topProjection_apply, ha, hx, Finsupp.zero_apply] using hh
    · exact p.property ab e hg
  · intro hp
    ext q
    exact hp q.val.1 (topExponent q.val.2) (topExponent_negative q.val.2)

theorem poleSubmodule_le_ker (s : Finset (Fin 3)) (i : Fin 3) (hi : i ∉ s) :
    poleSubmodule R χ s ≤ LinearMap.ker (topProjection R χ) := by
  intro p hp
  rw [LinearMap.mem_ker, topProjection_zero_iff]
  intro ab e he
  exact hp ab e i hi (he i)

theorem topBoundary_le_ker : topBoundary R χ ≤ LinearMap.ker (topProjection R χ) :=
  sup_le (sup_le (poleSubmodule_le_ker R χ {0, 1} 2 (by decide))
    (poleSubmodule_le_ker R χ {0, 2} 1 (by decide)))
      (poleSubmodule_le_ker R χ {1, 2} 0 (by decide))

def filterSection (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) : gradedFamilies R χ :=
  ⟨fun ab ↦ AddMonoidAlgebra.ofCoeff ((p.val ab).coeff.filter P), by
    intro ab e he
    change (if P e then (p.val ab).coeff e else 0) = 0
    split <;> simp [p.property ab e he]⟩

@[simp] theorem filterSection_coeff (P : LaurentExponent → Prop) [DecidablePred P]
    (p : gradedFamilies R χ) (ab : ShiftIndex) (e : LaurentExponent) :
    ((filterSection R χ P p).val ab).coeff e = if P e then (p.val ab).coeff e else 0 := rfl

theorem filterSection_mem_poleSubmodule (P : LaurentExponent → Prop) [DecidablePred P]
    (s : Finset (Fin 3))
    (hP : ∀ e, P e → ∀ i, i ∉ s → 0 ≤ e i) (p : gradedFamilies R χ) :
    filterSection R χ P p ∈ poleSubmodule R χ s := by
  intro ab e i hi hneg
  rw [filterSection_coeff]
  split
  · next he => exact False.elim ((not_le.mpr hneg) (hP e he i hi))
  · rfl

/-- Projection onto negative exponents loses exactly the three pair-open images. -/
theorem topBoundary_eq_ker : topBoundary R χ = LinearMap.ker (topProjection R χ) := by
  apply le_antisymm (topBoundary_le_ker R χ)
  intro p hp
  have hz := (topProjection_zero_iff R χ p).mp hp
  let p01 := filterSection R χ (fun e ↦ 0 ≤ e 2) p
  let p02 := filterSection R χ (fun e ↦ e 2 < 0 ∧ 0 ≤ e 1) p
  let p12 := filterSection R χ (fun e ↦ e 2 < 0 ∧ e 1 < 0 ∧ 0 ≤ e 0) p
  have h01 : p01 ∈ poleSubmodule R χ {0, 1} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · simp at hi
    · exact he
  have h02 : p02 ∈ poleSubmodule R χ {0, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · simp at hi
    · exact he.2
    · simp at hi
  have h12 : p12 ∈ poleSubmodule R χ {1, 2} := by
    apply filterSection_mem_poleSubmodule
    intro e he i hi
    fin_cases i
    · exact he.2.2
    · simp at hi
    · simp at hi
  have heq : p = p01 + p02 + p12 := by
    apply Subtype.ext
    funext ab
    apply AddMonoidAlgebra.ext
    ext e
    change (p.val ab).coeff e =
      ((p01.val ab + p02.val ab + p12.val ab).coeff e)
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply,
      p01, p02, p12, filterSection_coeff]
    by_cases h2 : 0 ≤ e 2
    · simp [h2, not_lt.mpr h2]
    · by_cases h1 : 0 ≤ e 1
      · simp [lt_of_not_ge h2, h1, not_lt.mpr h1]
      · by_cases h0 : 0 ≤ e 0
        · simp [h2, h1, lt_of_not_ge h2, lt_of_not_ge h1, h0]
        · have hn : ∀ i, e i < 0 := by
            intro i
            fin_cases i
            · exact lt_of_not_ge h0
            · exact lt_of_not_ge h1
            · exact lt_of_not_ge h2
          simp [lt_of_not_ge h2, lt_of_not_ge h1, h0, hz ab e hn]
  rw [heq]
  apply Submodule.add_mem
  · apply Submodule.add_mem
    · exact (show poleSubmodule R χ {0, 1} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_left) h01
    · exact (show poleSubmodule R χ {0, 2} ≤ topBoundary R χ from
        le_sup_of_le_left le_sup_right) h02
  · exact (show poleSubmodule R χ {1, 2} ≤ topBoundary R χ from le_sup_right) h12

abbrev TopCechQuotient := gradedFamilies R χ ⧸ topBoundary R χ

def topCechEquiv : TopCechQuotient R χ ≃ₗ[R] ((TopIndex χ) →₀ R) :=
  (Submodule.quotEquivOfEq _ _ (topBoundary_eq_ker R χ)).trans
    ((topProjection R χ).quotKerEquivOfSurjective (topProjection_surjective R χ))

@[simp] theorem topCechEquiv_mk (p : gradedFamilies R χ) :
    topCechEquiv R χ (Submodule.Quotient.mk p) = topProjection R χ p := by
  simp [topCechEquiv]

def topCechBasis : Module.Basis (TopIndex χ) R (TopCechQuotient R χ) :=
  Finsupp.basisSingleOne.map (topCechEquiv R χ).symm

@[simp] theorem topCechBasis_apply (q : (TopIndex χ)) :
    topCechBasis R χ q = Submodule.Quotient.mk (basisSection R χ q) := by
  apply (topCechEquiv R χ).injective
  simp [topCechBasis]

theorem topCech_rank [Nontrivial R] : Module.finrank R (TopCechQuotient R χ) = if χ=0 then 7 else 8 := by
  rw [Module.finrank_eq_card_basis (topCechBasis R χ), topIndex_count χ]

end CycleQ2CharacterTopCech

#print axioms CycleQ2CharacterTopCech.topIndex_count
#print axioms CycleQ2CharacterTopCech.topCechBasis_apply
#print axioms CycleQ2CharacterTopCech.topCech_rank
end
end


/- Component: continuation_20261112/SeedSurfaceBranchSparseBase.lean -/
section
/-! A kernel-checkable sparse polynomial identity checker over Gaussian integers.

All executable definitions use natural-number tuples, lists, and structural
recursion. The checker is sound for arbitrary term lists; sortedness only
improves its ability to combine equal monomials and is never a proof premise.
No external arithmetic result or evaluator axiom is used.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 20000
set_option Elab.async false

namespace CycleQ2SeedSurfaceSparsePolynomial

abbrev Exponent := ℕ × ℕ × ℕ × ℕ × ℕ
abbrev Term := Exponent × GaussianInt
abbrev Sparse := List Term

def exponentAdd (a b : Exponent) : Exponent :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1, a.2.2.2.1+b.2.2.2.1,
    a.2.2.2.2+b.2.2.2.2)

def code (e : Exponent) : ℕ :=
  e.1 + 32*(e.2.1 + 32*(e.2.2.1 + 32*(e.2.2.2.1 + 32*e.2.2.2.2)))

def termProduct (a b : Term) : Term :=
  (exponentAdd a.1 b.1, a.2*b.2)

/-- Fuel exhaustion preserves every term. Equality of exponent tuples is
checked before combining; the numeric sorting key need not be injective. -/
def addFuel : ℕ → Sparse → Sparse → Sparse
  | 0, p, q => p ++ q
  | _+1, [], q => q
  | _+1, p, [] => p
  | n+1, a::p, b::q =>
      if a.1 = b.1 then (a.1, a.2+b.2) :: addFuel n p q
      else if code a.1 ≤ code b.1 then a :: addFuel n p (b::q)
      else b :: addFuel n (a::p) q

def add (p q : Sparse) : Sparse := addFuel (p.length+q.length+1) p q

def mul (p q : Sparse) : Sparse :=
  p.foldr (fun a acc => add (q.map (termProduct a)) acc) []

def neg (p : Sparse) : Sparse := p.map (fun a => (a.1, -a.2))
def checkZero (p : Sparse) : Bool := p.all (fun a => decide (a.2 = 0))

section Soundness
variable {R : Type*} [CommRing R]
variable (φ : GaussianInt →+* R)

def monomial (x : Fin 5 → R) (e : Exponent) : R :=
  x 0 ^ e.1 * x 1 ^ e.2.1 * x 2 ^ e.2.2.1 *
    x 3 ^ e.2.2.2.1 * x 4 ^ e.2.2.2.2

def termValue (φ : GaussianInt →+* R) (x : Fin 5 → R) (a : Term) : R := φ a.2 * monomial x a.1
def eval (φ : GaussianInt →+* R) (x : Fin 5 → R) (p : Sparse) : R := (p.map (termValue φ x)).sum

@[simp] theorem eval_nil (x : Fin 5 → R) : eval φ x [] = 0 := rfl
@[simp] theorem eval_cons (x : Fin 5 → R) (a : Term) (p : Sparse) :
    eval φ x (a::p) = termValue φ x a + eval φ x p := rfl

theorem eval_append (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (p ++ q) = eval φ x p + eval φ x q := by simp [eval]

theorem eval_addFuel (x : Fin 5 → R) (n : ℕ) (p q : Sparse) :
    eval φ x (addFuel n p q) = eval φ x p + eval φ x q := by
  induction n generalizing p q with
  | zero => exact eval_append φ x p q
  | succ n ih =>
    cases p with
    | nil => simp [addFuel]
    | cons a p =>
      cases q with
      | nil => simp [addFuel]
      | cons b q =>
        by_cases he : a.1 = b.1
        · simp only [addFuel, if_pos he, eval_cons, ih, termValue,
            map_add]
          rw [he]
          ring
        · simp only [addFuel, if_neg he]
          split <;> simp only [eval_cons, ih] <;> ring

@[simp] theorem eval_add (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (add p q) = eval φ x p + eval φ x q := eval_addFuel φ x _ p q

theorem monomial_exponentAdd (x : Fin 5 → R) (a b : Exponent) :
    monomial x (exponentAdd a b) = monomial x a * monomial x b := by
  simp only [monomial, exponentAdd, pow_add]
  ring

theorem termValue_product (x : Fin 5 → R) (a b : Term) :
    termValue φ x (termProduct a b) = termValue φ x a * termValue φ x b := by
  simp only [termValue, termProduct, map_mul,
    monomial_exponentAdd]
  ring

theorem eval_mul (x : Fin 5 → R) (p q : Sparse) :
    eval φ x (mul p q) = eval φ x p * eval φ x q := by
  induction p with
  | nil => simp [mul]
  | cons a p ih =>
    change eval φ x (add (q.map (termProduct a)) (mul p q)) = _
    rw [eval_add, ih, eval_cons]
    have h : eval φ x (q.map (termProduct a)) = termValue φ x a * eval φ x q := by
      simp only [eval, List.map_map, Function.comp_def, termValue_product,
        List.sum_map_mul_left]
    rw [h]
    ring

theorem termValue_neg (x : Fin 5 → R) (a : Term) :
    termValue φ x (a.1, -a.2) = -termValue φ x a := by
  simp only [termValue, map_neg, neg_mul]

theorem eval_neg (x : Fin 5 → R) (p : Sparse) :
    eval φ x (neg p) = -eval φ x p := by
  simp only [neg, eval, List.map_map, Function.comp_def, termValue_neg]
  simpa only [List.map_map, Function.comp_def] using (List.sum_neg (p.map (termValue φ x))).symm

theorem eval_zero_of_all (x : Fin 5 → R) (p : Sparse)
    (h : p.all (fun a => decide (a.2 = 0)) = true) : eval φ x p = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [eval_cons, ih h.2, add_zero]
    unfold termValue
    rw [h.1, map_zero, zero_mul]

/-- A literal zero check yields the polynomial identity under every Gaussian-integer ring homomorphism. Concrete checks use ordinary kernel reduction. -/
theorem eval_eq_zero_of_check (x : Fin 5 → R) (p : Sparse)
    (h : checkZero p = true) : eval φ x p = 0 := eval_zero_of_all φ x p h

end Soundness
end CycleQ2SeedSurfaceSparsePolynomial

#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_eq_zero_of_check
#print axioms CycleQ2SeedSurfaceSparsePolynomial.eval_mul

/-! The literal r=57 branch certificate in exact Gaussian sparse form.
All coefficient pairs come unchanged from the stored characteristic-zero
certificate. Small generators are the first argument of sparse multiplication.
-/

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000
set_option Elab.async false
namespace CycleQ2SeedSurfaceBranchSparse
open CycleQ2SeedSurfaceSparsePolynomial
open scoped BigOperators

def generators : Fin 8 → Sparse :=
  ![[((6,0,0,0,0),⟨1,0⟩),
    ((0,0,6,0,0),⟨1,0⟩),
    ((0,3,0,3,0),⟨-185193,0⟩)],
    [((3,0,0,0,0),⟨1,0⟩),
    ((1,2,0,0,0),⟨1,0⟩),
    ((0,3,0,0,0),⟨0,-1⟩),
    ((0,0,3,0,0),⟨1,0⟩),
    ((1,0,1,1,0),⟨1,0⟩),
    ((0,1,1,1,0),⟨1,0⟩),
    ((0,0,0,3,0),⟨1,-1⟩)],
    [((6,1,0,0,0),⟨12,0⟩),
    ((5,2,0,0,0),⟨0,-18⟩),
    ((5,0,1,1,0),⟨6,0⟩),
    ((2,2,0,3,0),⟨1666737,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩),
    ((0,2,1,4,0),⟨555579,0⟩)],
    [((5,0,2,0,0),⟨18,0⟩),
    ((2,0,5,0,0),⟨-18,0⟩),
    ((0,2,5,0,0),⟨-6,0⟩),
    ((6,0,0,1,0),⟨6,0⟩),
    ((5,1,0,1,0),⟨6,0⟩),
    ((0,0,6,1,0),⟨-6,0⟩)],
    [((6,0,1,0,0),⟨6,0⟩),
    ((5,1,1,0,0),⟨6,0⟩),
    ((5,0,0,2,0),⟨18,-18⟩),
    ((2,3,0,2,0),⟨1666737,0⟩),
    ((0,5,0,2,0),⟨555579,0⟩),
    ((0,3,1,3,0),⟨555579,0⟩)],
    [((1,1,5,0,0),⟨-12,0⟩),
    ((0,2,5,0,0),⟨0,18⟩),
    ((0,0,6,1,0),⟨-6,0⟩),
    ((0,2,2,3,0),⟨-1666737,0⟩),
    ((1,2,0,4,0),⟨-555579,0⟩),
    ((0,3,0,4,0),⟨-555579,0⟩)],
    [((1,4,0,2,0),⟨1111158,0⟩),
    ((0,5,0,2,0),⟨0,-1666737⟩),
    ((1,2,1,3,0),⟨-555579,0⟩),
    ((0,2,0,5,0),⟨-1666737,1666737⟩)],
    [((1,0,6,0,0),⟨6,0⟩),
    ((0,1,6,0,0),⟨6,0⟩),
    ((0,3,2,2,0),⟨1666737,0⟩),
    ((0,0,5,2,0),⟨18,-18⟩),
    ((1,3,0,3,0),⟨555579,0⟩),
    ((0,4,0,3,0),⟨555579,0⟩)]]

def combine (g n : Fin 8 → Sparse) : Sparse :=
  add (mul (g 0) (n 0)) (add (mul (g 1) (n 1))
    (add (mul (g 2) (n 2)) (add (mul (g 3) (n 3))
    (add (mul (g 4) (n 4)) (add (mul (g 5) (n 5))
    (add (mul (g 6) (n 6)) (mul (g 7) (n 7))))))))

theorem eval_combine {R : Type*} [CommRing R] (φ : GaussianInt →+* R)
    (x : Fin 5 → R) (g n : Fin 8 → Sparse) :
    eval φ x (combine g n) = ∑ k, eval φ x (g k) * eval φ x (n k) := by
  simp only [combine,eval_add,eval_mul,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,Fin.reduceSucc]

end CycleQ2SeedSurfaceBranchSparse
end


/- Component: continuation_20261112/MonicRegularConormal.lean -/
section
/-! Conormal bases for two or three monic equations with disjoint leading
monomials. All polynomial and cotangent modules are the actual modules.
-/

noncomputable section
open MvPolynomial
open scoped BigOperators TensorProduct MonomialOrder
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2MonicRegular
open CycleQ2IncidenceNormalForm

variable {σ R : Type*} [CommRing R]

theorem mul_monic_ne_zero (m : MonomialOrder σ) {p q : MvPolynomial σ R}
    (hp : p ≠ 0) (hq : m.Monic q) : p*q ≠ 0 := by
  have hc : m.leadingCoeff p * m.leadingCoeff q ≠ 0 := by
    simpa [hq.leadingCoeff_eq_one] using m.leadingCoeff_ne_zero_iff.mpr hp
  intro hz
  have he := m.leadingCoeff_mul_of_mul_leadingCoeff_ne_zero hc
  rw [hz] at he
  exact hc (by simpa using he.symm)

theorem monic_regular (m : MonomialOrder σ) {p : MvPolynomial σ R}
    (hp : m.Monic p) (x : MvPolynomial σ R) (hx : p*x=0) : x=0 := by
  by_contra hn
  exact mul_monic_ne_zero m hn hp (by simpa [mul_comm] using hx)

/-- Cancellation of the second monic equation modulo the first. -/
theorem pair_regular_mod_first (m : MonomialOrder σ) {h F : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i=0 ∨ m.degree F i=0)
    (x : MvPolynomial σ R) (hFx : F*x ∈ Ideal.span ({h}:Set _)) :
    x ∈ Ideal.span ({h}:Set _) := by
  obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hFx
  obtain ⟨q,r,hx,_,hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff h) by rw [hh.leadingCoeff_eq_one]; exact isUnit_one) x
  have hp : r*F=(a-q*F)*h := by linear_combination -ha-F*hx
  have hr0 : r=0 := by
    by_contra hn
    have hs : a-q*F≠0 := by
      intro hz
      apply mul_monic_ne_zero m hn hF
      simpa [hz] using hp
    have hd := congrArg m.degree hp
    rw [degree_mul_monic m hn hF, degree_mul_monic m hs hh] at hd
    have hle : m.degree h ≤ m.degree r+m.degree F := by
      rw [hd]
      intro i
      simp only [Finsupp.add_apply]
      omega
    apply hr (m.degree r) (m.degree_mem_support hn)
    intro i
    rcases hcop i with hi | hi
    · simp [hi]
    · simpa only [Finsupp.add_apply,hi,add_zero] using hle i
  apply Ideal.mem_span_singleton'.mpr
  exact ⟨q,by simpa [hr0] using hx.symm⟩

/-- The concrete two-equation Groebner consequence needed for the third
regularity step: a nonzero element of the ideal has divisible leading term. -/
theorem leading_of_pair_representation
    (m : MonomialOrder σ) {h F p a b : MvPolynomial σ R}
    (hh : m.Monic h) (hF : m.Monic F)
    (hcop : ∀ i, m.degree h i=0 ∨ m.degree F i=0)
    (hp0 : p≠0) (heq : p=a*h+b*F) :
    m.degree h ≤ m.degree p ∨ m.degree F ≤ m.degree p := by
  obtain ⟨q,r,ha,_,hr⟩ := m.div_single
    (show IsUnit (m.leadingCoeff F) by rw [hF.leadingCoeff_eq_one]; exact isUnit_one) a
  let s := b+q*h
  have hp : p=r*h+s*F := by rw [heq,ha]; dsimp [s]; ring
  by_cases hr0 : r=0
  · have hs0 : s≠0 := by intro hz; apply hp0; simpa [hr0,hz] using hp
    right
    rw [hp,hr0,zero_mul,zero_add,degree_mul_monic m hs0 hF]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hrd : m.degree (r*h)=m.degree r+m.degree h := degree_mul_monic m hr0 hh
  have hrn : ¬ m.degree F ≤ m.degree (r*h) := by
    intro hd
    apply hr (m.degree r) (m.degree_mem_support hr0)
    rw [hrd] at hd
    intro i
    rcases hcop i with hi | hi
    · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
    · simp [hi]
  have hhd : m.degree h ≤ m.degree (r*h) := by
    rw [hrd]
    intro i
    simp only [Finsupp.add_apply]
    omega
  by_cases hs0 : s=0
  · left
    simpa only [hp,hs0,zero_mul,add_zero] using hhd
  have hFd : m.degree F ≤ m.degree (s*F) := by
    rw [degree_mul_monic m hs0 hF]
    intro i
    simp only [Finsupp.add_apply]
    omega
  have hne : m.toSyn (m.degree (r*h))≠m.toSyn (m.degree (s*F)) := by
    intro he
    apply hrn
    rwa [m.toSyn.injective he]
  rcases lt_or_gt_of_ne hne with hd | hd
  · right
    rwa [hp,m.degree_add_eq_right_of_lt hd]
  · left
    rwa [hp,m.degree_add_of_lt hd]

/-- Cancellation of a third monic equation modulo the first two. -/
theorem triple_regular_mod_pair (m : MonomialOrder σ)
    {a b c : MvPolynomial σ R} (ha : m.Monic a) (hb : m.Monic b) (hc : m.Monic c)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (hac : ∀ i, m.degree a i=0 ∨ m.degree c i=0)
    (hbc : ∀ i, m.degree b i=0 ∨ m.degree c i=0)
    (x : MvPolynomial σ R) (hcx : c*x ∈ Ideal.span ({a,b}:Set _)) :
    x ∈ Ideal.span ({a,b}:Set _) := by
  obtain ⟨u,v,huv⟩ := Ideal.mem_span_pair.mp hcx
  obtain ⟨q,t,r,hx,hr⟩ := exists_reduced_representation m a b x ha hb
  have hp : r*c=(u-q*c)*a+(v-t*c)*b := by linear_combination -huv-c*hx
  have hr0 : r=0 := by
    by_contra hn
    have hd := leading_of_pair_representation m ha hb hab
      (mul_monic_ne_zero m hn hc) hp
    rw [degree_mul_monic m hn hc] at hd
    have hred := hr (m.degree r) (m.degree_mem_support hn)
    rcases hd with hd | hd
    · apply hred.1
      intro i
      rcases hac i with hi | hi
      · simp [hi]
      · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
    · apply hred.2
      intro i
      rcases hbc i with hi | hi
      · simp [hi]
      · simpa only [Finsupp.add_apply,hi,add_zero] using hd i
  exact Ideal.mem_span_pair.mpr ⟨q,t,by simpa [hr0] using hx.symm⟩

theorem pair_relation_coefficients (m : MonomialOrder σ) (a b : MvPolynomial σ R)
    (ha : m.Monic a) (hb : m.Monic b)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (v : Fin 2 → MvPolynomial σ R) (hv : (∑ i, v i * (![a,b] i))=0) :
    ∀ i, v i ∈ Ideal.span (Set.range ![a,b]) := by
  have hset : Set.range ![a,b] = ({a,b}:Set _) := by
    ext x
    simp [Set.mem_range,Fin.exists_fin_succ,eq_comm,or_comm]
  rw [hset]
  have hp := CycleQ2ConormalRegular.pair_relation_coefficients a b
    (monic_regular m ha) (pair_regular_mod_first m ha hb hab) (v 0) (v 1)
    (by simpa [Fin.sum_univ_two,mul_comm] using hv)
  intro i
  fin_cases i
  · exact hp.1
  · exact hp.2

theorem triple_relation_coefficients (m : MonomialOrder σ) (a b c : MvPolynomial σ R)
    (ha : m.Monic a) (hb : m.Monic b) (hc : m.Monic c)
    (hab : ∀ i, m.degree a i=0 ∨ m.degree b i=0)
    (hac : ∀ i, m.degree a i=0 ∨ m.degree c i=0)
    (hbc : ∀ i, m.degree b i=0 ∨ m.degree c i=0)
    (v : Fin 3 → MvPolynomial σ R) (hv : (∑ i, v i * (![a,b,c] i))=0) :
    ∀ i, v i ∈ Ideal.span (Set.range ![a,b,c]) := by
  have hset : Set.range ![a,b,c] = ({a,b,c}:Set _) := by
    ext x
    simp [Set.mem_range,Fin.exists_fin_succ,eq_comm,or_assoc,or_comm,or_left_comm]
  rw [hset]
  have hp := CycleQ2ConormalRegular.triple_relation_coefficients a b c
    (monic_regular m ha) (pair_regular_mod_first m ha hb hab)
    (triple_regular_mod_pair m ha hb hc hab hac hbc) (v 0) (v 1) (v 2)
    (by simpa [Fin.sum_univ_three,mul_comm,add_assoc] using hv)
  intro i
  fin_cases i
  · exact hp.1
  · exact hp.2.1
  · exact hp.2.2

end CycleQ2MonicRegular

#print axioms CycleQ2MonicRegular.pair_relation_coefficients
#print axioms CycleQ2MonicRegular.triple_relation_coefficients
end
end


/- Component: continuation_20261112/SeedLocalizationBoundary.lean -/
section
/-! Actual seed localization boundaries give unrestricted polynomial
boundary witnesses. In particular no fixed pole-order bound is imposed.
-/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2SeedLocalizationBoundary
open MvPolynomial CycleQ2SeedTrace CycleQ2SeedCechTheta
  CycleQ2NormalConnecting CycleQ2LocalizationBoundary
open CycleQ2SeedCech (curveA curveB)

theorem paired_denominator_identity (r θ : ℂ) (p : Poly) :
    pairedNormalOverlap r θ p *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ) *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ) =
      algebraMap (CurveRing r θ) (Overlap r θ) (-curveMap r θ (derivativeNumerator p)) := by
  have hp : overlapAmbient r θ derivativeA *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p) =
      algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ (derivativeNumerator p)) := by
    change algebraMap (CurveRing r θ) (Overlap r θ)
        (curveMap r θ (substitute derivativeA)) * _ = _
    rw [← map_mul, ← map_mul, substitute_derivativeA]
  rw [← coe_firstOverlapUnit, ← coe_secondOverlapUnit]
  simp only [pairedNormalOverlap,normalOverlapCoefficient,overlapCoefficient,
    map_zero,mul_zero,zero_sub,map_neg]
  calc
    _ = -(overlapAmbient r θ derivativeA *
        algebraMap (CurveRing r θ) (Overlap r θ) (curveMap r θ p)) *
        (((firstOverlapUnit r θ)⁻¹ : (Overlap r θ)ˣ) : Overlap r θ) *
        (firstOverlapUnit r θ : Overlap r θ) *
        (((secondOverlapUnit r θ)⁻¹ : (Overlap r θ)ˣ) : Overlap r θ) *
        (secondOverlapUnit r θ : Overlap r θ) := by ring
    _ = _ := by
      rw [mul_assoc _ _ (firstOverlapUnit r θ : Overlap r θ),
        (firstOverlapUnit r θ).inv_mul,mul_one,
        mul_assoc _ _ (secondOverlapUnit r θ : Overlap r θ),
        (secondOverlapUnit r θ).inv_mul,mul_one,hp]

/-- Actual first- and second-open sections, of arbitrary pole order and
without any homogeneity restriction, clear to the polynomial boundary
relation used by the residue obstruction. -/
theorem paired_boundary_witness (r θ : ℂ) (hr : r ≠ 0) (p : Poly)
    (a : FirstOpen r θ) (b : SecondOpen r θ)
    (h : pairedNormalOverlap r θ p = firstRestriction r θ a + secondRestriction r θ b) :
    ∃ (N M : ℕ) (q s : Poly), 2 ≤ N ∧ 4 ≤ M ∧
      derivativeNumerator p * curveA^(N-2)*curveB^(M-4) -
        (q*curveA^N+s*curveB^M) ∈ curveIdeal r θ := by
  have hnum := paired_denominator_identity r θ p
  rw [h] at hnum
  have hnum' : (firstRestriction r θ a + secondRestriction r θ b) *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG1 r θ)^1 *
      algebraMap (CurveRing r θ) (Overlap r θ) (curveG2 r θ)^1 =
      algebraMap (CurveRing r θ) (Overlap r θ) (-curveMap r θ (derivativeNumerator p)) := by
    simpa only [pow_one] using hnum
  obtain ⟨N,M,q,s,hN,hM,hclear⟩ := clear_two_open_boundary
    (curveG1 r θ) (curveG2 r θ) (firstRestriction r θ) (secondRestriction r θ)
    (fun z => IsLocalization.Away.awayToAwayRight_eq _ _ z)
    (fun z => IsLocalization.Away.awayToAwayLeft_eq _ _ z) a b
    (-curveMap r θ (derivativeNumerator p)) 1 1 hnum'
  let u : (CurveRing r θ)ˣ := Units.map ((curveMap r θ).comp C).toMonoidHom
    (Units.mk0 (3*r^2) (mul_ne_zero (by norm_num) (pow_ne_zero _ hr)))
  let v : (CurveRing r θ)ˣ := Units.map ((curveMap r θ).comp C).toMonoidHom
    (Units.mk0 3 (by norm_num))
  have hg1 : curveG1 r θ = (u:CurveRing r θ)*(curveMap r θ curveA)^2 := by
    rw [curveG1,ambientCurveMap_g1,map_mul,map_pow]
    rfl
  have hg2 : curveG2 r θ = (v:CurveRing r θ)*(curveMap r θ curveB)^4 := by
    rw [curveG2,ambientCurveMap_g2,map_mul,map_pow]
    rfl
  rw [hg1,hg2] at hclear
  obtain ⟨q',s',heq⟩ := unscale_boundary (curveMap r θ curveA) (curveMap r θ curveB)
    (-curveMap r θ (derivativeNumerator p)) q s u v 2 4 N M hN hM hclear
  obtain ⟨qP,hqP⟩ := Ideal.Quotient.mk_surjective (-q')
  obtain ⟨sP,hsP⟩ := Ideal.Quotient.mk_surjective (-s')
  refine ⟨2*N,4*M,qP,sP,by omega,by omega,?_⟩
  have hNe : 2*N-2=2*(N-1) := by omega
  have hMe : 4*M-4=4*(M-1) := by omega
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change curveMap r θ (_ - _) = 0
  simp only [map_sub,map_add,map_mul,map_pow,hNe,hMe]
  change curveMap r θ (derivativeNumerator p) * (curveMap r θ curveA)^(2*(N-1)) *
      (curveMap r θ curveB)^(4*(M-1)) -
      (Ideal.Quotient.mk (curveIdeal r θ) qP * (curveMap r θ curveA)^(2*N) +
       Ideal.Quotient.mk (curveIdeal r θ) sP * (curveMap r θ curveB)^(4*M)) = 0
  rw [hqP,hsP]
  linear_combination -heq

end CycleQ2SeedLocalizationBoundary

#print axioms CycleQ2SeedLocalizationBoundary.paired_denominator_identity
#print axioms CycleQ2SeedLocalizationBoundary.paired_boundary_witness
end
end


/- Component: continuation_20261112/SurfaceJacobianGrading.lean -/
section
/-! Homogeneous Jacobian-minor generators of the actual surface family,
with exact coefficient-map and literal seed bindings. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

namespace CycleQ2IncidenceSurfaceGradientOpen
open MvPolynomial Matrix CycleQ2IncidenceNormalForm CycleQ2IncidenceEquations
  CycleQ2HomogeneousIdealArithmetic CycleQ2HomogeneousPrimeCoverOpen
open CycleQ2IncidenceBasepointOpen (Coeff familyF familyH seedEvaluation)

def minor {R : Type*} [CommRing R] (F h : Poly R) (j k : Fin 5) : Poly R :=
  pderiv j F * pderiv k h - pderiv k F * pderiv j h

abbrev Index := Fin 2 ⊕ (Fin 5 × Fin 5)

def generators : Index → Poly Coeff
  | Sum.inl j => ![familyF,familyH] j
  | Sum.inr (j,k) => minor familyF familyH j k ^ 3

def degree : Index → ℕ
  | Sum.inl j => ![6,3] j
  | Sum.inr (j,k) => 3*(9-(fullGrading j).1-(fullGrading k).1)

theorem pderiv_homogeneous {R : Type*} [CommRing R] {p : Poly R}
    (d : ℕ) (hd : 2 ≤ d) (hp : HG p (d,0)) (j : Fin 5) :
    HG (pderiv j p) (d-(fullGrading j).1,-(fullGrading j).2) := by
  apply hp.pderiv
  apply Prod.ext
  · have hj : (fullGrading j).1 ≤ 2 := by fin_cases j <;> decide
    simp only [Prod.fst_add]
    omega
  · simp

theorem minor_homogeneous {R : Type*} [CommRing R] {F h : Poly R}
    (hF : HG F (6,0)) (hh : HG h (3,0)) (j k : Fin 5) :
    HG (minor F h j k)
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
  have h1 := (pderiv_homogeneous 6 (by decide) hF j).mul
    (pderiv_homogeneous 3 (by decide) hh k)
  have h2 := (pderiv_homogeneous 6 (by decide) hF k).mul
    (pderiv_homogeneous 3 (by decide) hh j)
  have hj : (fullGrading j).1 ≤ 2 := by fin_cases j <;> decide
  have hk : (fullGrading k).1 ≤ 2 := by fin_cases k <;> decide
  have hgrade1 : (6-(fullGrading j).1,-(fullGrading j).2) +
      (3-(fullGrading k).1,-(fullGrading k).2) =
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
    apply Prod.ext
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add,sub_eq_add_neg]
  have hgrade2 : (6-(fullGrading k).1,-(fullGrading k).2) +
      (3-(fullGrading j).1,-(fullGrading j).2) =
      (9-(fullGrading j).1-(fullGrading k).1,
        -(fullGrading j).2-(fullGrading k).2) := by
    apply Prod.ext
    · simp only [Prod.fst_add]; omega
    · simp only [Prod.snd_add,sub_eq_add_neg]; abel
  rw [hgrade1] at h1
  rw [hgrade2] at h2
  exact h1.sub h2

theorem generators_homogeneous (i : Index) : HG (generators i) (degree i,0) := by
  cases i with
  | inl j =>
    fin_cases j
    · exact fullInvariantPolynomial_homogeneous 6 _
    · exact fullInvariantPolynomial_homogeneous 3 _
  | inr jk =>
    rcases jk with ⟨j,k⟩
    have hh := (minor_homogeneous (R := Coeff) (F := familyF) (h := familyH)
      (fullInvariantPolynomial_homogeneous 6 _)
      (fullInvariantPolynomial_homogeneous 3 _) j k).pow 3
    change HG (minor familyF familyH j k ^ 3)
      (3*(9-(fullGrading j).1-(fullGrading k).1),0)
    convert hh using 1
    apply Prod.ext
    · simp [nsmul_eq_mul]
    · have h3 : (3 : ZMod 3) = 0 := by decide
      simp [nsmul_eq_mul,h3]

theorem minor_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (F h : Poly R) (j k : Fin 5) :
    map φ (minor F h j k) = minor (map φ F) (map φ h) j k := by
  simp only [minor,map_sub,map_mul,←pderiv_map]

theorem familyF_seed : map seedEvaluation familyF =
    CycleQ2IncidenceEquations.smoothF (57:ℂ) Complex.I := by
  have h := congrFun CycleQ2IncidenceBasepointOpen.seed_universalGenerators (10:Fin 11)
  simpa [CycleQ2IncidenceBasepointOpen.universalGenerators,
    CycleQ2IncidenceBasepointOpen.generators,CycleQ2IncidenceBasepointOpen.seedFamilyGenerators,
    familyF,Matrix.cons_val_succ',Matrix.cons_val_zero'] using h

theorem familyH_seed : map seedEvaluation familyH =
    CycleQ2IncidenceEquations.smoothH Complex.I := by
  have h := congrFun CycleQ2IncidenceBasepointOpen.seed_universalGenerators (9:Fin 11)
  simpa [CycleQ2IncidenceBasepointOpen.universalGenerators,
    CycleQ2IncidenceBasepointOpen.generators,CycleQ2IncidenceBasepointOpen.seedFamilyGenerators,
    familyH,Matrix.cons_val_succ',Matrix.cons_val_zero'] using h

end CycleQ2IncidenceSurfaceGradientOpen

#print axioms CycleQ2IncidenceSurfaceGradientOpen.generators_homogeneous
#print axioms CycleQ2IncidenceSurfaceGradientOpen.familyF_seed
#print axioms CycleQ2IncidenceSurfaceGradientOpen.familyH_seed
end
end


