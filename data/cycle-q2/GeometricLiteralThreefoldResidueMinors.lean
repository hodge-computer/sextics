import Proposal.GeometricLiteralThreefoldResidueFrame
import Mathlib.LinearAlgebra.Alternating.Curry
import Proposal.GeometricSurfaceResidueOverlap

/-!
# Residue three-forms on the gradient opens of the fixed sextic

In the four affine variables of each original weight-one chart, the
residue divided by a Jacobian partial is the signed wedge of the other
three coordinate differentials. The hypersurface equation identifies
these forms on double gradient opens.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueMinors

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralAbelJacobiMovingNormal CycleQ2GeometricAffineOverlap
  CycleQ2ExteriorSectionNaturality CycleQ2LiteralThreefoldResidueFrame

variable {S S' : Type} [CommRing S] [CommRing S'] [Algebra ℂ S] [Algebra ℂ S']

/-- The order is the normal coordinate z followed by the remaining three linear coordinates. -/
abbrev coordIndex := _root_.finSuccEquiv 3

def coord (i j : Fin 4) : T i := Ideal.Quotient.mk _ (X (coordIndex j))

theorem differential_polynomial (f : P →ₐ[ℂ] S) (p : P) :
    KaehlerDifferential.D ℂ S (f p) =
      ∑ j : Option (Fin 3), f (pderiv j p) • KaehlerDifferential.D ℂ S (f (X j)) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq =>
      simp only [map_add, hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X q j hq =>
      simp only [map_mul, Derivation.leibniz, hq, smul_eq_mul, map_add,
        pderiv_X, add_smul, Finset.sum_add_distrib, mul_smul]
      simp [Pi.single_apply, Finset.smul_sum]

def coordinateForm (i : Fin 4) (f : T i →ₐ[ℂ] S) (j : Fin 4) :=
  KaehlerDifferential.D ℂ S (f (coord i j))

theorem gradient_relation (i : Fin 4) (f : T i →ₐ[ℂ] S) :
    ∑ j, f (gradient i j) • coordinateForm i f j = 0 := by
  let g := f.comp (Ideal.Quotient.mkₐ ℂ (fixedIdeal i))
  have h : g (seedF i) = 0 := by
    change f (Ideal.Quotient.mk (fixedIdeal i) (seedF i)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)), map_zero]
  calc
    _ = ∑ j : Option (Fin 3), g (pderiv j (seedF i)) • KaehlerDifferential.D ℂ S (g (X j)) :=
      Equiv.sum_comp coordIndex _
    _ = KaehlerDifferential.D ℂ S (g (seedF i)) := (differential_polynomial g _).symm
    _ = 0 := by rw [h, map_zero]

section Omitted

variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
private def wedge₃ (A : Type*) [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (x y z : M) : ⋀[A]^3 M :=
  exteriorPower.ιMulti A 3 ![x,y,z]

/-- The signed wedge of the three rows remaining after erasing the indicated row. -/
def signedOmitted (A : Type*) [CommRing A] {M : Type*} [AddCommGroup M]
    [Module A M] (e : Fin 4 → M) (j : Fin 4) : ⋀[A]^3 M :=
  (-1 : A) ^ j.val • exteriorPower.ιMulti A 3 (e ∘ j.succAbove)

private theorem signedOmitted_values (e : Fin 4 → M) :
    signedOmitted A e =
      ![wedge₃ A (e 1) (e 2) (e 3), -wedge₃ A (e 0) (e 2) (e 3),
        wedge₃ A (e 0) (e 1) (e 3), -wedge₃ A (e 0) (e 1) (e 2)] := by
  have h0 : e ∘ Fin.succ = ![e 1, e 2, e 3] := by funext i; fin_cases i <;> rfl
  have h1 : e ∘ (1 : Fin 4).succAbove = ![e 0, e 2, e 3] := by funext i; fin_cases i <;> rfl
  have h2 : e ∘ (2 : Fin 4).succAbove = ![e 0, e 1, e 3] := by funext i; fin_cases i <;> rfl
  have h3 : e ∘ (3 : Fin 4).succAbove = ![e 0, e 1, e 2] := by funext i; fin_cases i <;> rfl
  funext j
  fin_cases j <;> simp [signedOmitted, wedge₃, h0, h1, h2, h3, pow_succ] <;> exact neg_one_smul (M := (⋀[A]^3 M)) A _

private theorem wedge₃_swap12 (x y z : M) :
    wedge₃ A y x z = -wedge₃ A x y z := by
  have h := (exteriorPower.ιMulti A 3).map_swap ![x,y,z] (show (0 : Fin 3) ≠ 1 by decide)
  have hv : ![x,y,z] ∘ Equiv.swap (0 : Fin 3) 1 = ![y,x,z] := by
    funext t; fin_cases t <;> rfl
  rw [hv] at h
  exact h

private theorem wedge₃_swap23 (x y z : M) :
    wedge₃ A x z y = -wedge₃ A x y z := by
  have h := (exteriorPower.ιMulti A 3).map_swap ![x,y,z] (show (1 : Fin 3) ≠ 2 by decide)
  have hv : ![x,y,z] ∘ Equiv.swap (1 : Fin 3) 2 = ![x,z,y] := by
    funext t; fin_cases t <;> rfl
  rw [hv] at h
  exact h

@[simp] private theorem wedge₃_repeat1 (x y : M) : wedge₃ A x x y = 0 :=
  (exteriorPower.ιMulti A 3).map_eq_zero_of_eq ![x,x,y] (i := 0) (j := 1) rfl (by decide)

@[simp] private theorem wedge₃_repeat2 (x y : M) : wedge₃ A x y x = 0 :=
  (exteriorPower.ιMulti A 3).map_eq_zero_of_eq ![x,y,x] (i := 0) (j := 2) rfl (by decide)

private theorem triple_relation (a : Fin 4 → A) (e : Fin 4 → M)
    (h : ∑ i, a i • e i = 0) (x y : M) :
    a 0 • wedge₃ A (e 0) x y + a 1 • wedge₃ A (e 1) x y +
    a 2 • wedge₃ A (e 2) x y + a 3 • wedge₃ A (e 3) x y = 0 := by
  let f := (exteriorPower.ιMulti (M := M) A 3).curryLeft
  have hf := congrArg f h
  simp only [Fin.sum_univ_four, map_smul, map_add, map_zero] at hf
  exact congrArg (fun g : M [⋀^Fin 2]→ₗ[A] (⋀[A]^3 M) => g ![x,y]) hf

private theorem wedge₃_rotate (x y z : M) : wedge₃ A z x y = wedge₃ A x y z := by
  rw [wedge₃_swap12 x z y, wedge₃_swap23 x y z, neg_neg]

theorem signedOmitted_cross (a : Fin 4 → A) (e : Fin 4 → M)
    (h : ∑ i, a i • e i = 0) (j k : Fin 4) :
    a k • signedOmitted A e j = a j • signedOmitted A e k := by
  have h01 := triple_relation a e h (e 2) (e 3)
  have h02 := triple_relation a e h (e 1) (e 3)
  have h03 := triple_relation a e h (e 1) (e 2)
  have h12 := triple_relation a e h (e 0) (e 3)
  have h13 := triple_relation a e h (e 0) (e 2)
  have h23 := triple_relation a e h (e 0) (e 1)
  simp only [wedge₃_repeat1, wedge₃_repeat2, smul_zero, add_zero, zero_add] at h01 h02 h03 h12 h13 h23
  rw [wedge₃_swap12 (e 1) (e 2) (e 3), smul_neg] at h02
  rw [wedge₃_rotate (e 1) (e 2) (e 3)] at h03
  rw [wedge₃_swap12 (e 0) (e 1) (e 3), wedge₃_swap12 (e 0) (e 2) (e 3), smul_neg, smul_neg] at h12
  rw [wedge₃_swap12 (e 0) (e 1) (e 2), wedge₃_rotate (e 0) (e 2) (e 3), smul_neg] at h13
  rw [wedge₃_rotate (e 0) (e 1) (e 2), wedge₃_rotate (e 0) (e 1) (e 3)] at h23
  simp only [add_eq_zero_iff_eq_neg, neg_neg, neg_inj] at h01 h02 h03 h12 h13 h23
  have h12' := congrArg Neg.neg h12
  simp only [neg_neg] at h12'
  rw [signedOmitted_values]
  fin_cases j <;> fin_cases k <;> simp [h01, h02, h03, h12', h13, h23]

end Omitted

/-- The hypersurface residue on a gradient patch. -/
def residue (i : Fin 4) (f : T i →ₐ[ℂ] S) (j : Fin 4) (h : IsUnit (f (gradient i j))) :
    ⋀[S]^3 (KaehlerDifferential ℂ S) :=
  (↑h.unit⁻¹ : S) • signedOmitted S (coordinateForm i f) j

theorem gradient_smul_residue (i : Fin 4) (f : T i →ₐ[ℂ] S) (j : Fin 4)
    (h : IsUnit (f (gradient i j))) :
    f (gradient i j) • residue i f j h = signedOmitted S (coordinateForm i f) j := by
  unfold residue
  have hu : f (gradient i j) * (↑h.unit⁻¹ : S) = 1 := by
    simpa only [h.unit_spec] using h.unit.mul_inv
  rw [smul_smul, hu, one_smul]

theorem residue_natural (i : Fin 4) (f : T i →ₐ[ℂ] S) (g : S →ₐ[ℂ] S') (j : Fin 4)
    (h : IsUnit (f (gradient i j))) :
    exteriorDifferentialMap g 3 (residue i f j h) =
      residue i (g.comp f) j (h.map g.toMonoidHom) := by
  apply (IsUnit.smul_left_cancel (h.map g.toMonoidHom)).mp
  calc
    _ = exteriorDifferentialMap g 3 (f (gradient i j) • residue i f j h) :=
      ((exteriorDifferentialMap g 3).map_smulₛₗ _ _).symm
    _ = signedOmitted S' (coordinateForm i (g.comp f)) j := by
      rw [gradient_smul_residue, signedOmitted, map_smulₛₗ, exteriorDifferentialMap_wedge]
      simp only [RingHom.map_pow, map_neg, map_one]
      unfold signedOmitted coordinateForm
      simp only [Function.comp_apply, differentialMap_D, AlgHom.comp_apply]
      rfl
    _ = _ := (gradient_smul_residue i (g.comp f) j _).symm

def patchResidue (i j : Fin 4) := residue i (IsScalarTower.toAlgHom ℂ (T i) (Patch i j)) j
  (IsLocalization.Away.algebraMap_isUnit (S := Patch i j) (gradient i j))


/-- The normalized choice is independent of the chosen invertible partial. -/
theorem residue_eq (i : Fin 4) (f : T i →ₐ[ℂ] S) (j k : Fin 4)
    (hj : IsUnit (f (gradient i j))) (hk : IsUnit (f (gradient i k))) :
    residue i f j hj = residue i f k hk := by
  apply (IsUnit.smul_left_cancel hj).mp
  apply (IsUnit.smul_left_cancel hk).mp
  rw [gradient_smul_residue, smul_comm (f (gradient i k)) (f (gradient i j)),
    gradient_smul_residue]
  exact signedOmitted_cross _ _ (gradient_relation i f) j k

/-- Every three-form on the literal principal open has a unique coefficient in this frame. -/
theorem patchResidue_frame (i j : Fin 4)
    (w : ⋀[Patch i j]^3 (KaehlerDifferential ℂ (Patch i j))) :
    ∃! c : Patch i j, c • patchResidue i j = w := residue_frame i j w

abbrev DoublePatch (i j k : Fin 4) := Localization.Away (gradient i j * gradient i k)

private def doubleMap (i j k : Fin 4) : T i →ₐ[ℂ] DoublePatch i j k :=
  IsScalarTower.toAlgHom ℂ (T i) _

private theorem doubleLeftUnit (i j k : Fin 4) :
    IsUnit (doubleMap i j k (gradient i j)) :=
  IsLocalization.Away.isUnit_of_dvd (gradient i j * gradient i k) (dvd_mul_right _ _)

private theorem doubleRightUnit (i j k : Fin 4) :
    IsUnit (doubleMap i j k (gradient i k)) :=
  IsLocalization.Away.isUnit_of_dvd (gradient i j * gradient i k) (dvd_mul_left _ _)

/-- Canonical restriction from a gradient patch along a chart map inverting its gradient. -/
def patchLift (i j : Fin 4) (f : T i →ₐ[ℂ] S) (h : IsUnit (f (gradient i j))) :
    Patch i j →ₐ[ℂ] S := IsLocalization.Away.liftAlgHom _ h

theorem patchLift_residue (i j : Fin 4) (f : T i →ₐ[ℂ] S) (h : IsUnit (f (gradient i j))) :
    exteriorDifferentialMap (patchLift i j f h) 3 (patchResidue i j) = residue i f j h := by
  let l := IsScalarTower.toAlgHom ℂ (T i) (Patch i j)
  have hl : (patchLift i j f h).comp l = f := by
    ext x
    exact IsLocalization.Away.lift_eq (gradient i j) h x
  unfold patchResidue
  rw [residue_natural]
  change residue i ((patchLift i j f h).comp l) j _ = residue i f j h
  congr 1

/-- The actual restrictions from both gradient patches coincide on their intersection. -/
theorem patchResidue_overlap (i j k : Fin 4) :
    exteriorDifferentialMap (patchLift i j (doubleMap i j k) (doubleLeftUnit i j k)) 3
      (patchResidue i j) =
    exteriorDifferentialMap (patchLift i k (doubleMap i j k) (doubleRightUnit i j k)) 3
      (patchResidue i k) := by
  rw [patchLift_residue, patchLift_residue]
  exact residue_eq i _ j k _ _

end CycleQ2LiteralThreefoldResidueMinors
end

#print axioms CycleQ2LiteralThreefoldResidueMinors.gradient_relation
#print axioms CycleQ2LiteralThreefoldResidueMinors.residue_natural

#print axioms CycleQ2LiteralThreefoldResidueMinors.patchResidue_frame
#print axioms CycleQ2LiteralThreefoldResidueMinors.patchResidue_overlap
