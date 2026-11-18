import Proposal.GeometricHodgeEulerChartDerivations
import Mathlib.Tactic.Module

/-!
# The actual cotangent presentation of a hypersurface chart

The four coordinate differentials generate the Kähler module of the
original affine hypersurface quotient. Their sole relation is the
gradient of its actual equation. The inverse is constructed by descending
the polynomial derivation to the quotient by that gradient relation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCotangentChartPresentation

open MvPolynomial CycleQ2HodgeEulerChartDerivations
open scoped KaehlerDifferential

variable {K : Type} [CommRing K] (F : Poly K)

abbrev Tuple := Fin 4 → Hyp F

def gradientVector : Tuple F := fun j => mk F (pderiv j F)

def relation : Submodule (Hyp F) (Tuple F) :=
  (LinearMap.toSpanSingleton (Hyp F) (Tuple F) (gradientVector F)).range

abbrev Presented := Tuple F ⧸ relation F

def coordinateMap : Tuple F →ₗ[Hyp F] Ω[Hyp F⁄K] :=
  ∑ j : Fin 4, (LinearMap.proj j).smulRight
    (KaehlerDifferential.D K (Hyp F) (mk F (X j)))

theorem coordinateMap_apply (v : Tuple F) :
    coordinateMap F v = ∑ j, v j • KaehlerDifferential.D K (Hyp F) (mk F (X j)) := by
  simp [coordinateMap]

private theorem polynomial_chain {M : Type} [AddCommGroup M]
    [Module (Poly K) M] [Module K M] [IsScalarTower K (Poly K) M]
    (d : Derivation K (Poly K) M) (p : Poly K) :
    d p = ∑ j : Fin 4, pderiv j p • d (X j) := by
  exact CycleQ2PolynomialChainRule.apply (AlgHom.id K (Poly K)) d p

private theorem coordinateMap_gradient : coordinateMap F (gradientVector F) = 0 := by
  have h := polynomial_chain ((KaehlerDifferential.D K (Hyp F)).compAlgebraMap (Poly K)) F
  change KaehlerDifferential.D K (Hyp F) (mk F F) = _ at h
  rw [mk_equation, map_zero] at h
  rw [coordinateMap_apply]
  exact h.symm

def toCotangent : Presented F →ₗ[Hyp F] Ω[Hyp F⁄K] :=
  (relation F).liftQ (coordinateMap F) (by
    rintro _ ⟨a,rfl⟩
    change coordinateMap F (a • gradientVector F) = 0
    rw [map_smul, coordinateMap_gradient, smul_zero])

private def polynomialD : Derivation K (Poly K) (Presented F) :=
  mkDerivation K (fun j => (relation F).mkQ (Pi.single j 1))

private theorem polynomialD_equation : polynomialD F F = 0 := by
  rw [polynomial_chain (polynomialD F) F]
  simp only [polynomialD, mkDerivation_X]
  change ∑ j : Fin 4, mk F (pderiv j F) • (relation F).mkQ (Pi.single j 1) = 0
  simp only [← map_smul]
  rw [← map_sum]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨1, ?_⟩
  simp only [LinearMap.toSpanSingleton_apply, one_smul]
  classical
  ext j
  simp [gradientVector, Pi.single_apply]

private theorem polynomialD_kills (p : Poly K) (hp : mk F p = 0) : polynomialD F p = 0 := by
  obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  rw [Derivation.leibniz, polynomialD_equation, smul_zero, add_zero]
  change mk F F • polynomialD F q = 0
  rw [mk_equation]
  exact zero_smul (Hyp F) (polynomialD F q)

private def representative : Hyp F → Poly K :=
  Function.surjInv (Ideal.Quotient.mkₐ_surjective K (Ideal.span ({F} : Set (Poly K))))

private theorem representative_spec (x : Hyp F) : mk F (representative F x) = x :=
  Function.rightInverse_surjInv (Ideal.Quotient.mkₐ_surjective K _) x

private theorem same_d (p q : Poly K) (h : mk F p = mk F q) : polynomialD F p = polynomialD F q :=
  sub_eq_zero.mp (by rw [← map_sub]; exact polynomialD_kills F (p-q) (by rw [map_sub,h,sub_self]))

private def quotientD : Derivation K (Hyp F) (Presented F) where
  toFun x := polynomialD F (representative F x)
  map_add' x y := by
    rw [same_d F _ (representative F x + representative F y) (by simp [representative_spec])]
    exact map_add _ _ _
  map_smul' c x := by
    rw [same_d F _ (c • representative F x) (by simp [representative_spec])]
    exact (polynomialD F).map_smul c _
  map_one_eq_zero' := by
    change polynomialD F (representative F 1) = 0
    rw [same_d F _ 1 (by simp [representative_spec])]
    exact (polynomialD F).map_one_eq_zero
  leibniz' x y := by
    change polynomialD F (representative F (x*y)) =
      x • polynomialD F (representative F y) + y • polynomialD F (representative F x)
    rw [same_d F _ (representative F x * representative F y) (by simp [representative_spec])]
    rw [Derivation.leibniz]
    change mk F (representative F x) • polynomialD F (representative F y) +
      mk F (representative F y) • polynomialD F (representative F x) = _
    rw [representative_spec, representative_spec]

private theorem quotientD_mk (p : Poly K) : quotientD F (mk F p) = polynomialD F p :=
  same_d F _ p (representative_spec F _)

def fromCotangent : Ω[Hyp F⁄K] →ₗ[Hyp F] Presented F := (quotientD F).liftKaehlerDifferential

theorem fromCotangent_coordinate (j : Fin 4) :
    fromCotangent F (KaehlerDifferential.D K (Hyp F) (mk F (X j))) =
      (relation F).mkQ (Pi.single j 1) := by
  rw [fromCotangent, Derivation.liftKaehlerDifferential_comp_D, quotientD_mk]
  exact mkDerivation_X K _ j

theorem from_to (z : Presented F) : fromCotangent F (toCotangent F z) = z := by
  obtain ⟨v,rfl⟩ := (relation F).mkQ_surjective z
  change fromCotangent F (coordinateMap F v) = (relation F).mkQ v
  rw [coordinateMap_apply, map_sum]
  simp only [map_smul, fromCotangent_coordinate]
  simp only [← map_smul, ← map_sum]
  apply congrArg (relation F).mkQ
  classical
  ext j
  simp [Pi.single_apply]

theorem to_from (z : Ω[Hyp F⁄K]) : toCotangent F (fromCotangent F z) = z := by
  have hd : ((toCotangent F).comp (fromCotangent F)).compDer (KaehlerDifferential.D K (Hyp F)) =
      (LinearMap.id : Ω[Hyp F⁄K] →ₗ[Hyp F] Ω[Hyp F⁄K]).compDer (KaehlerDifferential.D K (Hyp F)) := by
    have hp : (((toCotangent F).comp (fromCotangent F)).compDer
        (KaehlerDifferential.D K (Hyp F))).compAlgebraMap (Poly K) =
        ((KaehlerDifferential.D K (Hyp F)).compAlgebraMap (Poly K)) := by
      apply MvPolynomial.derivation_ext
      intro j
      change toCotangent F (fromCotangent F (KaehlerDifferential.D K (Hyp F) (mk F (X j)))) = _
      rw [fromCotangent_coordinate]
      change coordinateMap F (Pi.single j 1) = KaehlerDifferential.D K (Hyp F) (mk F (X j))
      rw [coordinateMap_apply]
      classical
      rw [Finset.sum_eq_single j]
      · rw [Pi.single_eq_same]
        change (1 : Hyp F) •
          KaehlerDifferential.D K (Hyp F) (mk F (X j)) =
            KaehlerDifferential.D K (Hyp F) (mk F (X j))
        exact one_smul (Hyp F) (KaehlerDifferential.D K (Hyp F) (mk F (X j)))
      · intro b _ hbj
        rw [Pi.single_eq_of_ne hbj]
        exact zero_smul (Hyp F) (KaehlerDifferential.D K (Hyp F) (mk F (X b)))
      · simp
    ext a
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective a
    exact Derivation.congr_fun hp p
  exact LinearMap.congr_fun (Derivation.liftKaehlerDifferential_unique _ _ hd) z

/-- The original Kähler module, with the actual equation's single gradient relation. -/
def cotangentEquiv : Presented F ≃ₗ[Hyp F] Ω[Hyp F⁄K] where
  __ := toCotangent F
  invFun := fromCotangent F
  left_inv := from_to F
  right_inv := to_from F

theorem coordinateMap_surjective : Function.Surjective (coordinateMap F) := by
  intro z
  obtain ⟨p,rfl⟩ := (cotangentEquiv F).surjective z
  obtain ⟨v,rfl⟩ := (relation F).mkQ_surjective p
  exact ⟨v,rfl⟩

/-- No extra chart relation can be hidden by a dualization or dimension count. -/
theorem coordinateMap_eq_zero_iff (v : Tuple F) :
    coordinateMap F v = 0 ↔ ∃ a : Hyp F, a • gradientVector F = v := by
  change cotangentEquiv F ((relation F).mkQ v) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

end CycleQ2HodgeCotangentChartPresentation
end

#print axioms CycleQ2HodgeCotangentChartPresentation.fromCotangent_coordinate
#print axioms CycleQ2HodgeCotangentChartPresentation.cotangentEquiv
#print axioms CycleQ2HodgeCotangentChartPresentation.coordinateMap_surjective
#print axioms CycleQ2HodgeCotangentChartPresentation.coordinateMap_eq_zero_iff
