import Proposal.GeometricFormalInputs03Part02

/-!
# Derivations of the normalized affine hypersurface chart

For a hypersurface equation in four coordinates, a vector field is uniquely
determined by its values on the coordinates. The sole relation on these
four values is contraction with the gradient of the equation. Polynomial
lifts of any tuple satisfying this relation give a derivation preserving the
equation ideal, which descends to the original quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeEulerChartDerivations

open MvPolynomial
open scoped KaehlerDifferential

variable {K : Type*} [CommRing K]
abbrev Poly (K : Type*) [CommRing K] := MvPolynomial (Fin 4) K

abbrev Hyp (F : Poly K) := Poly K ⧸ Ideal.span ({F} : Set (Poly K))

def mk (F : Poly K) : Poly K →ₐ[K] Hyp F := Ideal.Quotient.mkₐ K _

@[simp] theorem mk_equation (F : Poly K) : mk F F = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self F)

def gradient (F : Poly K) : (Fin 4 → Hyp F) →ₗ[Hyp F] Hyp F :=
  ∑ j : Fin 4, mk F (pderiv j F) • LinearMap.proj j

theorem gradient_apply (F : Poly K) (v : Fin 4 → Hyp F) :
    gradient F v = ∑ j : Fin 4, mk F (pderiv j F) * v j := by
  simp [gradient]

private def coordinates (F : Poly K) :
    Derivation K (Hyp F) (Hyp F) →ₗ[Hyp F] (Fin 4 → Hyp F) where
  toFun D j := D (mk F (X j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem chain (F : Poly K) (D : Derivation K (Hyp F) (Hyp F)) (p : Poly K) :
    D (mk F p) = ∑ j : Fin 4, mk F (pderiv j p) * coordinates F D j :=
  CycleQ2PolynomialChainRule.apply (mk F) D p

private def toKernel (F : Poly K) :
    Derivation K (Hyp F) (Hyp F) →ₗ[Hyp F] (gradient F).ker :=
  (coordinates F).codRestrict _ (fun D => by
    rw [LinearMap.mem_ker, gradient_apply, ← chain F D, mk_equation, map_zero])

private theorem kernel_injective (F : Poly K) : Function.Injective (toKernel F) := by
  intro D E h
  have he : coordinates F D = coordinates F E := congrArg Subtype.val h
  ext a
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  change D (mk F p) = E (mk F p)
  rw [chain F D, chain F E, he]

private def liftCoordinates (F : Poly K) (v : Fin 4 → Hyp F) (j : Fin 4) : Poly K :=
  Function.surjInv (Ideal.Quotient.mkₐ_surjective K (Ideal.span ({F} : Set (Poly K)))) (v j)

private theorem mk_liftCoordinates (F : Poly K) (v : Fin 4 → Hyp F) (j : Fin 4) :
    mk F (liftCoordinates F v j) = v j :=
  Function.rightInverse_surjInv (Ideal.Quotient.mkₐ_surjective K _) _

private def polyDerivation (F : Poly K) (v : Fin 4 → Hyp F) : Derivation K (Poly K) (Poly K) :=
  mkDerivation K (liftCoordinates F v)

private theorem mk_polyDerivation (F : Poly K) (v : Fin 4 → Hyp F) (p : Poly K) :
    mk F (polyDerivation F v p) = ∑ j : Fin 4, mk F (pderiv j p) * v j := by
  have hc := CycleQ2PolynomialChainRule.apply (AlgHom.id K (Poly K)) (polyDerivation F v) p
  change polyDerivation F v p = ∑ j : Fin 4, pderiv j p * polyDerivation F v (X j) at hc
  rw [hc, map_sum]
  simp only [polyDerivation, mkDerivation_X, map_mul, mk_liftCoordinates]

private theorem preserves_equation (F : Poly K) (v : (gradient F).ker) (p : Poly K)
    (hp : mk F p = 0) : mk F (polyDerivation F v.val p) = 0 := by
  obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have ht : mk F (polyDerivation F v.val F) = 0 := by
    rw [mk_polyDerivation, ← gradient_apply]
    exact v.property
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
    ht, mk_equation, mul_zero, zero_mul, zero_add]

private def descend (F : Poly K) (v : (gradient F).ker) : Derivation K (Hyp F) (Hyp F) :=
  Derivation.liftOfSurjective (f := mk F) (Ideal.Quotient.mkₐ_surjective K _)
    (d := polyDerivation F v.val) (preserves_equation F v)

private theorem descend_apply (F : Poly K) (v : (gradient F).ker) (p : Poly K) :
    descend F v (mk F p) = mk F (polyDerivation F v.val p) :=
  Derivation.liftOfSurjective_apply (f := mk F) (Ideal.Quotient.mkₐ_surjective K _)
    (preserves_equation F v) p

/-- Coordinate values of the actual quotient derivations, with their full relation. -/
def derivationEquiv (F : Poly K) :
    Derivation K (Hyp F) (Hyp F) ≃ₗ[Hyp F] (gradient F).ker :=
  LinearEquiv.ofBijective (toKernel F) ⟨kernel_injective F, fun v => by
    refine ⟨descend F v, Subtype.ext (funext fun j => ?_)⟩
    change descend F v (mk F (X j)) = v.val j
    rw [descend_apply, polyDerivation, mkDerivation_X, mk_liftCoordinates]⟩

@[simp] theorem derivationEquiv_apply (F : Poly K) (D : Derivation K (Hyp F) (Hyp F)) (j : Fin 4) :
    (derivationEquiv F D).val j = D (mk F (X j)) := rfl

/-- The dual of the actual Kähler module has the same gradient presentation. -/
def cotangentDualEquiv (F : Poly K) :
    (Ω[Hyp F⁄K] →ₗ[Hyp F] Hyp F) ≃ₗ[Hyp F] (gradient F).ker :=
  (KaehlerDifferential.linearMapEquivDerivation K (Hyp F)).trans (derivationEquiv F)

theorem cotangentDualEquiv_apply (F : Poly K) (l : Ω[Hyp F⁄K] →ₗ[Hyp F] Hyp F) (j : Fin 4) :
    (cotangentDualEquiv F l).val j = l (KaehlerDifferential.D K (Hyp F) (mk F (X j))) := rfl

end CycleQ2HodgeEulerChartDerivations
end

#print axioms CycleQ2HodgeEulerChartDerivations.derivationEquiv
#print axioms CycleQ2HodgeEulerChartDerivations.cotangentDualEquiv_apply
