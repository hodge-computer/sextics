import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.BilinearMap
import Proposal.GeometricTarget11Part04

/-!
# The paired graded Higgs model at the actual Fermat quotient

Source-only continuation of Part III.1 of the written geometric argument.
No elaboration, compilation, or kernel replay has been run for this file.

The upper piece is the existing degree-six, character-one submodule of the
actual Fermat Jacobian quotient. Complementary monomials give a basis of
the actual degree-twelve, character-one piece, and the socle trace is
proved to identify that lower piece with the dual of the upper piece.
On their 66-dimensional direct sum this file constructs the canonical
nondegenerate alternating pairing and the Higgs operators. Actual quotient
multiplication is proved to intertwine with those operators under the
socle-duality equivalence. Their matrix entries are the existing finite
Higgs data.

The dual action of a grading-preserving self-adjoint endomorphism is
derived from the pairing. Commutation with the constructed Higgs operators
then gives the actual trace-pairing equations. The existing finite scalar
calculation therefore proves that a compatible idempotent on this whole
paired graded model is zero or the identity.

This constructs a concrete graded linear-algebra object at the Fermat
point. It does not define a geometric variation of Hodge structure over
the parameter space, a flat connection, a Hodge metric, or a geometric
residue comparison. In particular it does not identify the canonical
alternating pairing below with a geometric polarization. Those remaining
comparisons must be proved before applying this result to a subvariation.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2FermatVariationAlgebra

open CycleQ2FermatJacobian CycleQ2GeometricBridgeAlgebra

/-- The actual degree-six character-one quotient component. -/
abbrev Upper := InvariantHodgeModel

/-- The dual graded component in the paired model. The actual lower
Jacobian piece is identified with it by `lowerDualEquiv` below. -/
abbrev Lower := Module.Dual ℂ Upper

abbrev Total := Upper × Lower
abbrev Tangent := InvariantTangentModel

local instance : Module.Finite ℂ Upper :=
  Module.Finite.of_basis degreeSixCharacterOneBasis

theorem total_finrank : Module.finrank ℂ Total = 66 := by
  change Module.finrank ℂ (Upper × Module.Dual ℂ Upper) = 66
  rw [Module.finrank_prod, Subspace.dual_finrank_eq]
  have h : Module.finrank ℂ Upper = 33 := degreeSixCharacterOne_finrank
  rw [h]

/-- The canonical alternating pairing on the actual upper component and
its linear dual. This is a constructed bilinear form. -/
def pairing : Total →ₗ[ℂ] Total →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun := fun y => y.2 x.1 - x.2 y.1
      map_add' y z := by
        change (y.2 + z.2) x.1 - x.2 (y.1 + z.1) =
          (y.2 x.1 - x.2 y.1) + (z.2 x.1 - x.2 z.1)
        simp only [LinearMap.add_apply, map_add]
        ring
      map_smul' c y := by
        change (c • y.2) x.1 - x.2 (c • y.1) =
          c * (y.2 x.1 - x.2 y.1)
        simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_sub] }
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change z.2 (x.1 + y.1) - (x.2 + y.2) z.1 =
      (z.2 x.1 - x.2 z.1) + (z.2 y.1 - y.2 z.1)
    simp only [LinearMap.add_apply, map_add]
    ring
  map_smul' c x := by
    apply LinearMap.ext
    intro y
    change y.2 (c • x.1) - (c • x.2) y.1 =
      c * (y.2 x.1 - x.2 y.1)
    simp only [LinearMap.smul_apply, map_smul, smul_eq_mul, mul_sub]

@[simp] theorem pairing_apply (x y : Total) :
    pairing x y = y.2 x.1 - x.2 y.1 := rfl

theorem pairing_alternating (x : Total) : pairing x x = 0 :=
  sub_self _

theorem pairing_skew (x y : Total) : pairing x y = -pairing y x := by
  simp only [pairing_apply]
  ring

/-- Nondegeneracy is proved from actual dual separation, rather than
supplied as a hypothesis about an unnamed polarization. -/
theorem pairing_left_nondegenerate (x : Total)
    (hx : ∀ y : Total, pairing x y = 0) : x = 0 := by
  have hupper : x.1 = 0 := by
    apply (Module.forall_dual_apply_eq_zero_iff ℂ x.1).mp
    intro φ
    simpa only [pairing_apply, map_zero, sub_zero] using hx (0, φ)
  have hlower : x.2 = 0 := by
    apply LinearMap.ext
    intro u
    have h := hx (u, 0)
    simpa only [pairing_apply, LinearMap.zero_apply, zero_sub, neg_eq_zero]
      using h
  exact Prod.ext hupper hlower

theorem pairing_right_nondegenerate (y : Total)
    (hy : ∀ x : Total, pairing x y = 0) : y = 0 := by
  apply pairing_left_nondegenerate y
  intro x
  rw [pairing_skew, hy x, neg_zero]

/-- The Higgs operator is built from multiplication and trace in the
actual Fermat derivative quotient. -/
def higgs (t : Tangent) : Module.End ℂ Total :=
  (LinearMap.inr ℂ Upper Lower).comp
    ((actualTracePairing t).comp (LinearMap.fst ℂ Upper Lower))

@[simp] theorem higgs_apply (t : Tangent) (x : Total) :
    higgs t x = (0, actualTracePairing t x.1) := rfl

theorem higgs_add (s t : Tangent) : higgs (s + t) = higgs s + higgs t := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp [higgs_apply]
  · apply LinearMap.ext
    intro v
    change socleTrace ((x.1 : JacobianRing) * (v : JacobianRing) *
        ((s : JacobianRing) + (t : JacobianRing))) =
      socleTrace ((x.1 : JacobianRing) * (v : JacobianRing) * (s : JacobianRing)) +
        socleTrace ((x.1 : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
    rw [mul_add, map_add]

theorem higgs_smul (c : ℂ) (t : Tangent) : higgs (c • t) = c • higgs t := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · simp only [higgs_apply, LinearMap.smul_apply, Prod.smul_fst, smul_zero]
  · apply LinearMap.ext
    intro v
    change socleTrace ((x.1 : JacobianRing) * (v : JacobianRing) *
        (c • (t : JacobianRing))) =
      c • socleTrace ((x.1 : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
    rw [mul_smul_comm, map_smul]

/-- The whole 35-dimensional tangent-to-endomorphism Higgs family. -/
def higgsFamily : Tangent →ₗ[ℂ] Module.End ℂ Total where
  toFun := higgs
  map_add' := higgs_add
  map_smul' := higgs_smul

/-- The constructed operators have exactly the existing finite matrices. -/
theorem higgs_basis_matrix (m : Fin 35) (i j : Fin 33) :
    (higgs (degreeSixCharacterZeroBasis m)
      (degreeSixCharacterOneBasis i, 0)).2 (degreeSixCharacterOneBasis j) =
      CycleQ2FermatHiggs.higgsMatrix ℂ m i j :=
  actualTracePairing_basis m i j

/-- Successive Higgs operators vanish for this two-step graded model. -/
theorem higgs_mul_higgs (s t : Tangent) : higgs s * higgs t = 0 := by
  apply LinearMap.ext
  intro x
  change (0, actualTracePairing s 0) = (0, 0)
  rw [map_zero]

theorem higgs_commute (s t : Tangent) : Commute (higgs s) (higgs t) := by
  change higgs s * higgs t = higgs t * higgs s
  rw [higgs_mul_higgs, higgs_mul_higgs]

/-- The actual symmetric trace forms give the infinitesimal alternating
pairing compatibility of the constructed Higgs operators. -/
theorem higgs_pairing_compatibility (t : Tangent) (x y : Total) :
    pairing (higgs t x) y + pairing x (higgs t y) = 0 := by
  simp only [pairing_apply, higgs_apply, map_zero, zero_sub, sub_zero]
  rw [actualTracePairing_symmetric t y.1 x.1]
  exact neg_add_cancel _

/-- The induced paired endomorphism with its dual block. -/
def pairedEnd (P : Module.End ℂ Upper) : Module.End ℂ Total :=
  P.prodMap P.dualMap

@[simp] theorem pairedEnd_apply (P : Module.End ℂ Upper) (x : Total) :
    pairedEnd P x = (P x.1, P.dualMap x.2) := rfl

@[simp] theorem pairedEnd_zero : pairedEnd 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro u
    change x.2 0 = 0
    exact map_zero x.2

@[simp] theorem pairedEnd_one : pairedEnd 1 = 1 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · rfl
  · apply LinearMap.ext
    intro u
    rfl

def upperBlock (e : Module.End ℂ Total) : Module.End ℂ Upper :=
  (LinearMap.fst ℂ Upper Lower).comp (e.comp (LinearMap.inl ℂ Upper Lower))

def lowerBlock (e : Module.End ℂ Total) : Module.End ℂ Lower :=
  (LinearMap.snd ℂ Upper Lower).comp (e.comp (LinearMap.inr ℂ Upper Lower))

/-- Preservation of the two actual summands in the constructed grading. -/
def PreservesGrading (e : Module.End ℂ Total) : Prop :=
  (∀ u : Upper, (e (u, 0)).2 = 0) ∧
    ∀ φ : Lower, (e (0, φ)).1 = 0

def PairingSelfAdjoint (e : Module.End ℂ Total) : Prop :=
  ∀ x y : Total, pairing (e x) y = pairing x (e y)

/-- Self-adjointness determines the actual lower block from the upper
block. The transpose relationship is proved, not postulated. -/
theorem lowerBlock_eq_dual (e : Module.End ℂ Total)
    (he : PairingSelfAdjoint e) : lowerBlock e = (upperBlock e).dualMap := by
  apply LinearMap.ext
  intro φ
  apply LinearMap.ext
  intro u
  have h := he (u, 0) (0, φ)
  simpa only [pairing_apply, map_zero, LinearMap.zero_apply, sub_zero,
    upperBlock, lowerBlock, LinearMap.comp_apply, LinearMap.inl_apply,
    LinearMap.inr_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    LinearMap.dualMap_apply] using h.symm

theorem eq_pairedEnd_of_grading_selfAdjoint
    (e : Module.End ℂ Total) (hgrading : PreservesGrading e)
    (hself : PairingSelfAdjoint e) : e = pairedEnd (upperBlock e) := by
  apply LinearMap.ext
  rintro ⟨u, φ⟩
  calc
    e (u, φ) = e (u, 0) + e (0, φ) := by
      rw [← map_add]
      congr 1
      simp only [Prod.mk_add_mk, add_zero, zero_add]
    _ = pairedEnd (upperBlock e) (u, φ) := by
      apply Prod.ext
      · change (e (u, 0)).1 + (e (0, φ)).1 = (e (u, 0)).1
        rw [hgrading.2 φ, add_zero]
      · change (e (u, 0)).2 + lowerBlock e φ = (upperBlock e).dualMap φ
        rw [hgrading.1 u, zero_add, lowerBlock_eq_dual e hself]

/-- Commutation with the actual Higgs operators gives exactly the trace
equations used by the established finite scalar calculation. -/
theorem trace_compatibility_of_higgs_commutation
    (P : Module.End ℂ Upper)
    (hcommute : ∀ t : Tangent, pairedEnd P * higgs t = higgs t * pairedEnd P) :
    ∀ (t : Tangent) (u v : Upper),
      actualTracePairing t (P u) v = actualTracePairing t u (P v) := by
  intro t u v
  have h := congrArg (fun e : Module.End ℂ Total => (e (u, 0)).2 v) (hcommute t)
  simpa only [Module.End.mul_apply, pairedEnd_apply, higgs_apply,
    LinearMap.dualMap_apply] using h.symm

/-- The actual scalar Higgs calculation forces every compatible
idempotent on the entire 66-dimensional paired model to be trivial. -/
theorem compatible_graded_projector_trivial
    (e : Module.End ℂ Total) (hgrading : PreservesGrading e)
    (hself : PairingSelfAdjoint e)
    (hcommute : ∀ t : Tangent, e * higgs t = higgs t * e)
    (hidempotent : e * e = e) : e = 0 ∨ e = 1 := by
  let P : Module.End ℂ Upper := upperBlock e
  have he : e = pairedEnd P := eq_pairedEnd_of_grading_selfAdjoint e hgrading hself
  have hP : P * P = P := by
    apply LinearMap.ext
    intro u
    have h := congrArg (fun f : Module.End ℂ Total => (f (u, 0)).1) hidempotent
    simpa only [he, Module.End.mul_apply, pairedEnd_apply] using h
  have htrace : ∀ (t : Tangent) (u v : Upper),
      actualTracePairing t (P u) v = actualTracePairing t u (P v) := by
    apply trace_compatibility_of_higgs_commutation P
    intro t
    simpa only [he] using hcommute t
  rcases actual_trace_selfAdjoint_projector_trivial P htrace hP with hzero | hone
  · left
    rw [he, hzero, pairedEnd_zero]
  · right
    rw [he, hone, pairedEnd_one]

theorem compatible_graded_projector_range
    (e : Module.End ℂ Total) (hgrading : PreservesGrading e)
    (hself : PairingSelfAdjoint e)
    (hcommute : ∀ t : Tangent, e * higgs t = higgs t * e)
    (hidempotent : e * e = e) :
    LinearMap.range e = ⊥ ∨ LinearMap.range e = ⊤ := by
  rcases compatible_graded_projector_trivial e hgrading hself hcommute hidempotent with
    hzero | hone
  · left
    rw [hzero]
    simp
  · right
    rw [hone]
    simp [Module.End.one_eq_id]

section ActualLowerPiece

open CycleQ2FermatHiggs MvPolynomial

/-- Complementary exponents for the actual degree-six monomial basis. -/
def lowerExponent (i : Fin 33) (k : Fin 5) : ℕ :=
  socle k - basisMonomial i k

theorem lowerExponent_properties : ∀ i : Fin 33,
    weightedDegree (lowerExponent i) = 12 ∧ character (lowerExponent i) = 1 ∧
      ∀ k, lowerExponent i k ≤ socle k := by
  intro i
  have h0 : basisMonomial i 0 ≤ 4 := by
    simpa [socle] using (basis_properties i).2.2 0
  have h1 : basisMonomial i 1 ≤ 4 := by
    simpa [socle] using (basis_properties i).2.2 1
  have h2 : basisMonomial i 2 ≤ 4 := by
    simpa [socle] using (basis_properties i).2.2 2
  have h3 : basisMonomial i 3 ≤ 4 := by
    simpa [socle] using (basis_properties i).2.2 3
  have h4 : basisMonomial i 4 ≤ 1 := by
    simpa [socle] using (basis_properties i).2.2 4
  constructor
  · have h := (basis_properties i).1
    simp only [weightedDegree] at h
    norm_num [weightedDegree, lowerExponent, socle]
    omega
  · constructor
    · have h := (basis_properties i).2.1
      simp only [character] at h
      norm_num [character, lowerExponent, socle]
      omega
    · intro k
      exact Nat.sub_le _ _

def lowerIndex (i : Fin 33) : BoundedExp :=
  ⟨exponent (lowerExponent i), (lowerExponent_properties i).2.2⟩

theorem lowerIndex_injective : Function.Injective lowerIndex := by
  intro i j hij
  apply basis_injective
  funext k
  have h := congrArg (fun d : BoundedExp => d.val k) hij
  change socle k - basisMonomial i k = socle k - basisMonomial j k at h
  have hi := (basis_properties i).2.2 k
  have hj := (basis_properties j).2.2 k
  omega

/-- The complementary monomials span the full actual degree-twelve
character-one component, not an abstract subspace of the right dimension. -/
theorem lower_complete_bounded (d : Exp) (hb : d ∈ bounded)
    (hn : weightedDegree d = 12) (hc : character d = 1) :
    ∃ i : Fin 33, exponent (lowerExponent i) = d := by
  have h0 : d 0 ≤ 4 := by simpa [socle] using hb 0
  have h1 : d 1 ≤ 4 := by simpa [socle] using hb 1
  have h2 : d 2 ≤ 4 := by simpa [socle] using hb 2
  have h3 : d 3 ≤ 4 := by simpa [socle] using hb 3
  have h4 : d 4 ≤ 1 := by simpa [socle] using hb 4
  let a : Exp := exponent (fun k => socle k - d k)
  have ha : a ∈ bounded := by
    intro k
    exact Nat.sub_le _ _
  have han : weightedDegree a = 6 := by
    change weightedDegree (fun k => socle k - d k) = 6
    simp only [weightedDegree] at hn
    norm_num [weightedDegree, socle]
    omega
  have hac : character a = 1 := by
    change character (fun k => socle k - d k) = 1
    simp only [character] at hc
    norm_num [character, socle]
    omega
  obtain ⟨i, hi⟩ := basis_complete_bounded a ha han hac
  refine ⟨i, ?_⟩
  ext k
  have hik := congrArg (fun e : Exp => e k) hi
  change basisMonomial i k = socle k - d k at hik
  change socle k - basisMonomial i k = d k
  have hk := hb k
  omega

theorem lowerMonomials_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 33 => monomialClass (lowerExponent i)) :=
  boundedMonomials_linearIndependent.comp lowerIndex lowerIndex_injective

theorem lowerPiece_eq_span :
    gradedPiece 12 1 = Submodule.span ℂ
      (Set.range fun i : Fin 33 => monomialClass (lowerExponent i)) :=
  gradedPiece_eq_span_of_enumeration lowerExponent 12 1
    (fun i => ⟨(lowerExponent_properties i).1, (lowerExponent_properties i).2.1⟩)
    lower_complete_bounded

abbrev ActualLower := gradedPiece 12 1

def lowerBasis : Module.Basis (Fin 33) ℂ ActualLower :=
  (Module.Basis.span lowerMonomials_linearIndependent).map
    (LinearEquiv.ofEq _ _ lowerPiece_eq_span.symm)

theorem lowerBasis_coe (i : Fin 33) :
    (lowerBasis i : JacobianRing) = monomialClass (lowerExponent i) := by
  simp [lowerBasis]

theorem actualLower_finrank : Module.finrank ℂ ActualLower = 33 := by
  rw [Module.finrank_eq_card_basis lowerBasis]
  rfl

/-- The socle trace gives a concrete map from the lower Jacobian piece to
the dual of the upper piece. -/
def lowerToDual : ActualLower →ₗ[ℂ] Lower where
  toFun z :=
    { toFun := fun u => socleTrace ((u : JacobianRing) * (z : JacobianRing))
      map_add' u v := by simp [add_mul]
      map_smul' c u := by simp [smul_mul_assoc] }
  map_add' z w := by
    apply LinearMap.ext
    intro u
    simp [mul_add]
  map_smul' c z := by
    apply LinearMap.ext
    intro u
    simp [mul_smul_comm]

@[simp] theorem lowerToDual_apply (z : ActualLower) (u : Upper) :
    lowerToDual z u = socleTrace ((u : JacobianRing) * (z : JacobianRing)) := rfl

theorem socleTrace_pair_monomial (a b : Fin 5 → ℕ) :
    socleTrace (monomialClass a * monomialClass b) =
      if (∀ k, a k + b k = socle k) then 1 else 0 := by
  classical
  rw [monomialClass, monomialClass, ← map_mul, socleTrace_mk,
    monomial_mul, one_mul, coeff_monomial]
  congr 1
  apply propext
  constructor
  · intro h k
    exact congrArg (fun d : Exp => d k) h
  · intro h
    ext k
    exact h k

theorem lowerToDual_basis_apply (i j : Fin 33) :
    lowerToDual (lowerBasis i) (degreeSixCharacterOneBasis j) =
      if j = i then 1 else 0 := by
  rw [lowerToDual_apply, degreeSixCharacterOneBasis_coe, lowerBasis_coe,
    socleTrace_pair_monomial]
  congr 1
  apply propext
  constructor
  · intro h
    apply basis_injective
    funext k
    have hk := h k
    have hi := (basis_properties i).2.2 k
    change basisMonomial j k + (socle k - basisMonomial i k) = socle k at hk
    omega
  · intro h k
    rw [h]
    change basisMonomial i k + (socle k - basisMonomial i k) = socle k
    exact Nat.add_sub_of_le ((basis_properties i).2.2 k)

theorem lowerToDual_basis (i : Fin 33) :
    lowerToDual (lowerBasis i) = degreeSixCharacterOneBasis.dualBasis i := by
  apply degreeSixCharacterOneBasis.ext
  intro j
  rw [lowerToDual_basis_apply, Module.Basis.dualBasis_apply_self]

/-- The actual complementary Jacobian piece is the dual through the socle
pairing. The equivalence is constructed on the complementary monomial bases. -/
def lowerDualEquiv : ActualLower ≃ₗ[ℂ] Lower :=
  lowerBasis.equiv degreeSixCharacterOneBasis.dualBasis (Equiv.refl (Fin 33))

theorem lowerDualEquiv_toLinearMap : lowerDualEquiv.toLinearMap = lowerToDual := by
  apply lowerBasis.ext
  intro i
  change lowerBasis.equiv degreeSixCharacterOneBasis.dualBasis
    (Equiv.refl (Fin 33)) (lowerBasis i) = lowerToDual (lowerBasis i)
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, lowerToDual_basis]

theorem lowerDualEquiv_apply (z : ActualLower) (u : Upper) :
    lowerDualEquiv z u = socleTrace ((u : JacobianRing) * (z : JacobianRing)) :=
  congrArg (fun f : ActualLower →ₗ[ℂ] Lower => f z u) lowerDualEquiv_toLinearMap

/-- Multiplication by an actual invariant tangent class lands in the
actual complementary Jacobian component. -/
theorem upper_mul_tangent_mem (u : Upper) (t : Tangent) :
    (u : JacobianRing) * (t : JacobianRing) ∈ gradedPiece 12 1 := by
  have hbasis (i : Fin 33) (m : Fin 35) :
      monomialClass (basisMonomial i) * monomialClass (tangentMonomial m) ∈
        gradedPiece 12 1 := by
    let d : Exp := exponent (basisMonomial i) + exponent (tangentMonomial m)
    have hn : weightedDegree d = 12 := by
      have hi := (basis_properties i).1
      have hm := (tangent_properties m).1
      simp only [weightedDegree] at hi hm
      change basisMonomial i 0 + tangentMonomial m 0 +
        (basisMonomial i 1 + tangentMonomial m 1) +
        (basisMonomial i 2 + tangentMonomial m 2) +
        (basisMonomial i 3 + tangentMonomial m 3) +
        2 * (basisMonomial i 4 + tangentMonomial m 4) = 12
      omega
    have hc : character d = 1 := by
      have hi := (basis_properties i).2.1
      have hm := (tangent_properties m).2.1
      simp only [character] at hi hm
      change (2 * (basisMonomial i 0 + tangentMonomial m 0) +
        2 * (basisMonomial i 1 + tangentMonomial m 1) +
        (basisMonomial i 2 + tangentMonomial m 2)) % 3 = 1
      omega
    rw [monomialClass, monomialClass, ← map_mul, monomial_mul, one_mul]
    rw [gradedPiece, restrictSupport_eq_span, Submodule.map_span, Set.image_image]
    apply Submodule.subset_span
    exact ⟨d, ⟨hn, hc⟩, rfl⟩
  change (gradedPiece 6 1).subtype u * (gradedPiece 6 0).subtype t ∈ _
  rw [← degreeSixCharacterOneBasis.sum_repr u,
    ← degreeSixCharacterZeroBasis.sum_repr t]
  simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum,
    smul_mul_assoc, mul_smul_comm, smul_smul]
  apply (gradedPiece 12 1).sum_mem
  intro i hi
  apply (gradedPiece 12 1).smul_mem
  apply (gradedPiece 12 1).sum_mem
  intro m hm
  apply (gradedPiece 12 1).smul_mem
  change (degreeSixCharacterOneBasis m : JacobianRing) *
    (degreeSixCharacterZeroBasis i : JacobianRing) ∈ gradedPiece 12 1
  simpa only [degreeSixCharacterOneBasis_coe, degreeSixCharacterZeroBasis_coe] using
    hbasis m i

/-- The lower Higgs component is actual multiplication in the quotient. -/
def actualHiggsLower (t : Tangent) : Upper →ₗ[ℂ] ActualLower where
  toFun u := ⟨(u : JacobianRing) * (t : JacobianRing), upper_mul_tangent_mem u t⟩
  map_add' u v := by
    apply Subtype.ext
    change ((u : JacobianRing) + (v : JacobianRing)) * (t : JacobianRing) = _
    exact add_mul _ _ _
  map_smul' c u := by
    apply Subtype.ext
    change (c • (u : JacobianRing)) * (t : JacobianRing) =
      c • ((u : JacobianRing) * (t : JacobianRing))
    exact smul_mul_assoc _ _ _

theorem lowerDualEquiv_actualHiggsLower (t : Tangent) (u : Upper) :
    lowerDualEquiv (actualHiggsLower t u) = actualTracePairing t u := by
  apply LinearMap.ext
  intro v
  rw [lowerDualEquiv_apply]
  change socleTrace ((v : JacobianRing) *
      ((u : JacobianRing) * (t : JacobianRing))) =
    socleTrace ((u : JacobianRing) * (v : JacobianRing) * (t : JacobianRing))
  congr 1
  ring

abbrev JacobianTotal := Upper × ActualLower

/-- Both graded pieces are now actual submodules of the Fermat quotient. -/
def jacobianTotalEquiv : JacobianTotal ≃ₗ[ℂ] Total :=
  LinearEquiv.prodCongr (LinearEquiv.refl ℂ Upper) lowerDualEquiv

def actualJacobianHiggs (t : Tangent) : Module.End ℂ JacobianTotal :=
  (LinearMap.inr ℂ Upper ActualLower).comp
    ((actualHiggsLower t).comp (LinearMap.fst ℂ Upper ActualLower))

/-- The concrete multiplication operators intertwine with the paired
Higgs model under the proved socle-duality equivalence. -/
theorem jacobianTotalEquiv_intertwines_higgs (t : Tangent) (x : JacobianTotal) :
    jacobianTotalEquiv (actualJacobianHiggs t x) =
      higgs t (jacobianTotalEquiv x) := by
  change (0, lowerDualEquiv (actualHiggsLower t x.1)) =
    (0, actualTracePairing t x.1)
  rw [lowerDualEquiv_actualHiggsLower]

theorem actual_total_finrank : Module.finrank ℂ JacobianTotal = 66 :=
  jacobianTotalEquiv.finrank_eq.trans total_finrank

/-- The pairing on the two actual quotient components, transported by the
proved socle-duality equivalence. Its explicit socle formula is below. -/
def actualPairing : JacobianTotal →ₗ[ℂ] JacobianTotal →ₗ[ℂ] ℂ :=
  pairing.compl₁₂ jacobianTotalEquiv.toLinearMap jacobianTotalEquiv.toLinearMap

theorem actualPairing_eq (x y : JacobianTotal) :
    actualPairing x y = pairing (jacobianTotalEquiv x) (jacobianTotalEquiv y) := rfl

/-- Both factors in each product are actual classes in the Fermat
Jacobian quotient. No geometric polarization is assumed here. -/
theorem actualPairing_apply (x y : JacobianTotal) :
    actualPairing x y =
      socleTrace ((x.1 : JacobianRing) * (y.2 : JacobianRing)) -
        socleTrace ((y.1 : JacobianRing) * (x.2 : JacobianRing)) := by
  change lowerDualEquiv y.2 x.1 - lowerDualEquiv x.2 y.1 = _
  rw [lowerDualEquiv_apply, lowerDualEquiv_apply]

theorem actualPairing_alternating (x : JacobianTotal) : actualPairing x x = 0 :=
  pairing_alternating (jacobianTotalEquiv x)

theorem actualPairing_left_nondegenerate (x : JacobianTotal)
    (hx : ∀ y : JacobianTotal, actualPairing x y = 0) : x = 0 := by
  have h : jacobianTotalEquiv x = 0 := by
    apply pairing_left_nondegenerate
    intro y
    obtain ⟨z, rfl⟩ := jacobianTotalEquiv.surjective y
    exact hx z
  apply jacobianTotalEquiv.injective
  simpa only [map_zero] using h

theorem actualJacobianHiggs_pairing_compatibility (t : Tangent) (x y : JacobianTotal) :
    actualPairing (actualJacobianHiggs t x) y +
      actualPairing x (actualJacobianHiggs t y) = 0 := by
  rw [actualPairing_eq, actualPairing_eq,
    jacobianTotalEquiv_intertwines_higgs, jacobianTotalEquiv_intertwines_higgs]
  exact higgs_pairing_compatibility t (jacobianTotalEquiv x) (jacobianTotalEquiv y)

/-- Preservation of the actual degree-six and degree-twelve components. -/
def ActualPreservesGrading (e : Module.End ℂ JacobianTotal) : Prop :=
  (∀ u : Upper, (e (u, 0)).2 = 0) ∧
    ∀ z : ActualLower, (e (0, z)).1 = 0

/-- The scalar calculation now applies directly to endomorphisms of the
two actual Jacobian components. All forms and multiplication operators in
the hypotheses are the concrete constructions above. -/
theorem actual_compatible_graded_projector_trivial
    (e : Module.End ℂ JacobianTotal) (hgrading : ActualPreservesGrading e)
    (hself : ∀ x y : JacobianTotal, actualPairing (e x) y = actualPairing x (e y))
    (hcommute : ∀ t : Tangent,
      e * actualJacobianHiggs t = actualJacobianHiggs t * e)
    (hidempotent : e * e = e) : e = 0 ∨ e = 1 := by
  let e' : Module.End ℂ Total := jacobianTotalEquiv.conjRingEquiv e
  have htransport (x : JacobianTotal) :
      e' (jacobianTotalEquiv x) = jacobianTotalEquiv (e x) := by
    change jacobianTotalEquiv
      (e (jacobianTotalEquiv.symm (jacobianTotalEquiv x))) = jacobianTotalEquiv (e x)
    rw [LinearEquiv.symm_apply_apply]
  have hupper (u : Upper) : jacobianTotalEquiv (u, 0) = (u, 0) := by
    change (u, lowerDualEquiv 0) = (u, 0)
    rw [map_zero]
  have hlower (φ : Lower) :
      jacobianTotalEquiv (0, lowerDualEquiv.symm φ) = (0, φ) := by
    change (0, lowerDualEquiv (lowerDualEquiv.symm φ)) = (0, φ)
    rw [LinearEquiv.apply_symm_apply]
  have hgrading' : PreservesGrading e' := by
    constructor
    · intro u
      rw [← hupper u, htransport]
      change lowerDualEquiv ((e (u, 0)).2) = 0
      rw [hgrading.1 u, map_zero]
    · intro φ
      rw [← hlower φ, htransport]
      change (e (0, lowerDualEquiv.symm φ)).1 = 0
      exact hgrading.2 (lowerDualEquiv.symm φ)
  have hself' : PairingSelfAdjoint e' := by
    intro x y
    obtain ⟨x, rfl⟩ := jacobianTotalEquiv.surjective x
    obtain ⟨y, rfl⟩ := jacobianTotalEquiv.surjective y
    rw [htransport, htransport]
    exact hself x y
  have hcommute' : ∀ t : Tangent, e' * higgs t = higgs t * e' := by
    intro t
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := jacobianTotalEquiv.surjective x
    change e' (higgs t (jacobianTotalEquiv z)) = higgs t (e' (jacobianTotalEquiv z))
    rw [← jacobianTotalEquiv_intertwines_higgs t z, htransport, htransport,
      ← jacobianTotalEquiv_intertwines_higgs t (e z)]
    exact congrArg (fun f : Module.End ℂ JacobianTotal => jacobianTotalEquiv (f z))
      (hcommute t)
  have hidempotent' : e' * e' = e' := by
    change jacobianTotalEquiv.conjRingEquiv e * jacobianTotalEquiv.conjRingEquiv e =
      jacobianTotalEquiv.conjRingEquiv e
    rw [← map_mul, hidempotent]
  rcases compatible_graded_projector_trivial e' hgrading' hself' hcommute' hidempotent'
    with hzero | hone
  · left
    apply jacobianTotalEquiv.conjRingEquiv.injective
    simpa only [e', map_zero] using hzero
  · right
    apply jacobianTotalEquiv.conjRingEquiv.injective
    simpa only [e', map_one] using hone

end ActualLowerPiece

end CycleQ2FermatVariationAlgebra

end
