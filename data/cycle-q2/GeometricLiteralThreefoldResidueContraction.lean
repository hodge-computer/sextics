import Proposal.GeometricLiteralThreefoldKodairaSpencer
import Proposal.GeometricExteriorSheaf
import Proposal.GeometricLiteralThreefoldChartVolumeFrame
import Proposal.GeometricHodgeTwistTorus
import Proposal.GeometricHodgeThreefoldCubicChart
import Proposal.GeometricHodgeThreefoldLiteral
import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin

/-!
# The two-form associated to a threefold deformation

Contracting a three-form by the actual Jacobian-chart Kodaira–Spencer
differences gives two-forms satisfying the additive cocycle identity.
The construction uses interior multiplication on exterior powers and
commutes with semilinear restriction of the covector and the form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldResidueContraction

open CycleQ2GeometricExteriorSheaf CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2GeometricSurfaceFirstOrder

section Exterior

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- Interior multiplication, with sign positive in the first slot. -/
def interior (n : ℕ) (v : M →ₗ[R] R) : (⋀[R]^(n+1) M) →ₗ[R] (⋀[R]^n M) :=
  exteriorPower.alternatingMapLinearEquiv <|
    AlternatingMap.alternatizeUncurryFin (v.smulRight (exteriorPower.ιMulti R n))

theorem interior_wedge (n : ℕ) (v : M →ₗ[R] R) (m : Fin (n+1) → M) :
    interior n v (exteriorPower.ιMulti R (n+1) m) =
      ∑ j : Fin (n+1), (-1 : ℤ) ^ (j : ℕ) •
        (v (m j) • exteriorPower.ιMulti R n (j.removeNth m)) := by
  simp [interior, AlternatingMap.alternatizeUncurryFin_apply]

theorem interior_add (n : ℕ) (v w : M →ₗ[R] R) :
    interior n (v+w) = interior n v + interior n w := by
  have h : (v + w).smulRight (exteriorPower.ιMulti R n (M := M)) =
      v.smulRight (exteriorPower.ιMulti R n (M := M)) + w.smulRight (exteriorPower.ιMulti R n (M := M)) := by
    apply LinearMap.ext
    intro x
    simp [add_smul]
  unfold interior
  rw [h, AlternatingMap.alternatizeUncurryFin_add, map_add]

variable {S N : Type} [CommRing S] [AddCommGroup N] [Module S N]

theorem interior_natural (φ : R →+* S) (f : M →ₛₗ[φ] N) (v : M →ₗ[R] R)
    (u : N →ₗ[S] S) (hvu : ∀ x, u (f x) = φ (v x)) (n : ℕ) (ω : ⋀[R]^(n+1) M) :
    interior n u (exteriorMap φ f (n+1) ω) = exteriorMap φ f n (interior n v ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [exteriorMap_wedge, interior_wedge, interior_wedge, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hvu, map_zsmul, map_smulₛₗ, exteriorMap_wedge]
      rfl
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, RingHom.id_apply, hx]

end Exterior

abbrev Chart (i : Fin 4) (s : Finset Index) := Closed (localF i s)
abbrev Forms (i : Fin 4) (s : Finset Index) (n : ℕ) := ⋀[Chart i s]^n (KaehlerDifferential ℂ (Chart i s))

/-- The two-form obtained from the normalized splitting difference on an
actual fixed-sextic Jacobian intersection and a three-form on that chart. -/
def twoForm (i : Fin 4) (s : Finset Index) (j k : Index) (hj : j ∈ s) (hk : k ∈ s)
    (ω : Forms i s 3) : Forms i s 2 :=
  interior 2 (tangent i s j k hj hk).liftKaehlerDifferential ω

private theorem lift_tangents_add {R : Type} [CommRing R] [Algebra ℂ R]
    (x y : Derivation ℂ R R) :
    (x+y).liftKaehlerDifferential = x.liftKaehlerDifferential + y.liftKaehlerDifferential :=
  (KaehlerDifferential.linearMapEquivDerivation ℂ R (M := R)).symm.map_add x y

private theorem interior_tangents_add {R : Type} [CommRing R] [Algebra ℂ R]
    (x y : Derivation ℂ R R) (ω : ⋀[R]^3 (KaehlerDifferential ℂ R)) :
    interior 2 (x+y).liftKaehlerDifferential ω =
      interior 2 x.liftKaehlerDifferential ω + interior 2 y.liftKaehlerDifferential ω := by
  rw [lift_tangents_add x y, interior_add]
  rfl

theorem twoForm_cocycle (i : Fin 4) (s : Finset Index) (j k l : Index)
    (hj : j ∈ s) (hk : k ∈ s) (hl : l ∈ s) (ω : Forms i s 3) :
    twoForm i s j l hj hl ω = twoForm i s j k hj hk ω + twoForm i s k l hk hl ω := by
  exact (congrArg (fun δ : Derivation ℂ (Chart i s) (Chart i s) =>
    interior 2 δ.liftKaehlerDifferential ω) (tangent_cocycle i s j k l hj hk hl)).trans
      (interior_tangents_add _ _ ω)

end CycleQ2LiteralThreefoldResidueContraction
end

#print axioms CycleQ2LiteralThreefoldResidueContraction.interior_natural
#print axioms CycleQ2LiteralThreefoldResidueContraction.twoForm_cocycle

/-! Native coordinate wedges on a localized fixed threefold chart.
These are the six actual two-form generators to which the cubic trace
identities apply; no free cotangent basis on the whole torus is assumed. -/

noncomputable section
namespace CycleQ2LiteralThreefoldTorusForms

open Module MvPolynomial
open CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiEquations
  CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldResidueMinors
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralThreefoldChartVolumeFrame
  CycleQ2ExteriorSectionNaturality

section LocalizedGenerators

variable (i : Fin 4) (M : Submonoid (T i)) (B : Type) [CommRing B]
  [Algebra ℂ B] [Algebra (T i) B] [IsScalarTower ℂ (T i) B] [IsLocalization M B]

/-- The original four coordinate differentials still generate after an
arbitrary localization of the actual fixed chart. -/
theorem coordinateForms_span_localized :
    Submodule.span B (Set.range
      (coordinateForm i (IsScalarTower.toAlgHom ℂ (T i) B))) = ⊤ := by
  let f := IsScalarTower.toAlgHom ℂ (T i) B
  let Q := Submodule.span B (Set.range (coordinateForm i f))
  have hbase (a : T i) : KaehlerDifferential.D ℂ B (algebraMap (T i) B a) ∈ Q := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
    change KaehlerDifferential.D ℂ B ((f.comp mk) p) ∈ Q
    rw [differential_polynomial]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨coordIndex.symm j, ?_⟩
    simpa only [coordinateForm, coord, Equiv.apply_symm_apply, AlgHom.comp_apply]
  have hall (a : B) : KaehlerDifferential.D ℂ B a ∈ Q := by
    obtain ⟨⟨r,s⟩,hs⟩ := IsLocalization.surj M a
    have hd := congrArg (KaehlerDifferential.D ℂ B) hs
    rw [Derivation.leibniz] at hd
    have he : algebraMap (T i) B s • KaehlerDifferential.D ℂ B a =
        KaehlerDifferential.D ℂ B (algebraMap (T i) B r) -
          a • KaehlerDifferential.D ℂ B (algebraMap (T i) B s) :=
      eq_sub_of_add_eq (by simpa only [add_comm] using hd)
    have hm : algebraMap (T i) B s • KaehlerDifferential.D ℂ B a ∈ Q := by
      rw [he]
      exact Q.sub_mem (hbase r) (Q.smul_mem a (hbase s))
    let u := (IsLocalization.map_units B s).unit
    have hu : (↑u⁻¹ : B) * algebraMap (T i) B s = 1 := by
      rw [← (IsLocalization.map_units B s).unit_spec]
      exact Units.inv_mul u
    have hx := Q.smul_mem (↑u⁻¹ : B) hm
    simpa only [smul_smul, hu, one_smul] using hx
  change Q = ⊤
  rw [eq_top_iff, ← KaehlerDifferential.span_range_derivation ℂ B, Submodule.span_le]
  rintro _ ⟨a,rfl⟩
  exact hall a

/-- The exterior square is spanned by the six ordered pairs of these
four genuine coordinate differentials. -/
theorem coordinateTwo_span_localized :
    Submodule.span B (Set.range (exteriorPower.ιMulti_family B 2
      (coordinateForm i (IsScalarTower.toAlgHom ℂ (T i) B)))) = ⊤ :=
  exteriorPower.ιMulti_family_span_of_span (n := 2) B
    (coordinateForms_span_localized i M B)

end LocalizedGenerators

section WedgeCoefficients

variable {B N : Type} [CommRing B] [AddCommGroup N] [Module B N]

private def three (x y z : N) : ⋀[B]^3 N := exteriorPower.ιMulti B 3 ![x,y,z]

private def firstLinear (y z : N) : N →ₗ[B] (⋀[B]^3 N) where
  toFun x := three x y z
  map_add' x x' := (exteriorPower.ιMulti B 3).map_vecCons_add ![y,z] x x'
  map_smul' r x := (exteriorPower.ιMulti B 3).map_vecCons_smul ![y,z] r x

private theorem first_sum (v : Fin 4 → B) (e : Fin 4 → N) (y z : N) :
    three (∑ j, v j • e j) y z = ∑ j, v j • three (e j) y z := by
  change firstLinear y z (∑ j, v j • e j) = _
  rw [map_sum]
  simp only [map_smul]

@[simp] private theorem repeat12 (x y : N) : three (B := B) x x y = 0 :=
  (exteriorPower.ιMulti B 3).map_eq_zero_of_eq ![x,x,y] (i := 0) (j := 1) rfl (by decide)

@[simp] private theorem repeat13 (x y : N) : three (B := B) x y x = 0 :=
  (exteriorPower.ιMulti B 3).map_eq_zero_of_eq ![x,y,x] (i := 0) (j := 2) rfl (by decide)

@[simp] private theorem repeat23 (x y : N) : three (B := B) x y y = 0 :=
  (exteriorPower.ιMulti B 3).map_eq_zero_of_eq ![x,y,y] (i := 1) (j := 2) rfl (by decide)

private theorem swap12 (x y z : N) : three (B := B) y x z = -three x y z := by
  have h := (exteriorPower.ιMulti B 3).map_swap ![x,y,z] (show (0 : Fin 3) ≠ 1 by decide)
  have he : ![x,y,z] ∘ Equiv.swap (0 : Fin 3) 1 = ![y,x,z] := by
    funext j; fin_cases j <;> rfl
  rw [he] at h
  exact h

private theorem swap23 (x y z : N) : three (B := B) x z y = -three x y z := by
  have h := (exteriorPower.ιMulti B 3).map_swap ![x,y,z] (show (1 : Fin 3) ≠ 2 by decide)
  have he : ![x,y,z] ∘ Equiv.swap (1 : Fin 3) 2 = ![x,z,y] := by
    funext j; fin_cases j <;> rfl
  rw [he] at h
  exact h

private theorem rotate (x y z : N) : three (B := B) z x y = three x y z := by
  rw [swap12 x z y, swap23 x y z, neg_neg]

def pairLeft : Fin 6 → Fin 4 := ![0,0,0,1,1,2]
def pairRight : Fin 6 → Fin 4 := ![1,2,3,2,3,3]

/-- The ordered pairs are (0,1), (0,2), (0,3), (1,2), (1,3), (2,3),
with coordinate zero the original normal variable. -/
def pairCoefficient (g v : Fin 4 → B) : Fin 6 → B :=
  ![v 3*g 2-v 2*g 3, v 1*g 3-v 3*g 1, v 2*g 1-v 1*g 2,
    v 3*g 0-v 0*g 3, v 0*g 2-v 2*g 0, v 1*g 0-v 0*g 1]

private theorem expand_pair (e : Fin 4 → N) (g v : Fin 4 → B) (ω : ⋀[B]^3 N)
    (h012 : three (e 0) (e 1) (e 2) = -(g 3 • ω))
    (h013 : three (e 0) (e 1) (e 3) = g 2 • ω)
    (h023 : three (e 0) (e 2) (e 3) = -(g 1 • ω))
    (h123 : three (e 1) (e 2) (e 3) = g 0 • ω) (p : Fin 6) :
    three (∑ j, v j • e j) (e (pairLeft p)) (e (pairRight p)) =
      pairCoefficient g v p • ω := by
  rw [first_sum, Fin.sum_univ_four]
  fin_cases p <;> dsimp only [pairLeft, pairRight, pairCoefficient]
  all_goals simp only [repeat12, repeat13, repeat23, smul_zero, zero_add, add_zero]
  · rw [rotate (e 0) (e 1) (e 2), rotate (e 0) (e 1) (e 3), h012, h013]
    simp only [smul_neg, smul_smul, sub_smul]; abel
  · rw [swap12 (e 0) (e 1) (e 2), rotate (e 0) (e 2) (e 3), h012, h023]
    simp only [neg_neg, smul_neg, smul_smul, sub_smul]; abel
  · rw [swap12 (e 0) (e 1) (e 3), swap12 (e 0) (e 2) (e 3), h013, h023]
    simp only [neg_neg, smul_neg, smul_smul, sub_smul]; abel
  · rw [rotate (e 1) (e 2) (e 3), h012, h123]
    simp only [smul_neg, smul_smul, sub_smul]; abel
  · rw [swap12 (e 1) (e 2) (e 3), h013, h123]
    simp only [smul_neg, smul_smul, sub_smul]; abel
  · rw [h023, h123]
    simp only [smul_neg, smul_smul, sub_smul]; abel

end WedgeCoefficients

section Native

variable {B : Type} [CommRing B] [Algebra ℂ B]
  (i : Fin 4) (f : T i →ₐ[ℂ] B)

theorem coordinate_triple (j : Fin 4) :
    exteriorPower.ιMulti B 3 (coordinateForm i f ∘ j.succAbove) =
      ((-1 : B)^j.val*f (gradient i j)) • exteriorDifferentialMap f 3 (chartVolume i) := by
  have h := congrArg (fun ω : ⋀[B]^3 (KaehlerDifferential ℂ B) => (-1 : B)^j.val • ω)
    (gradient_smul_chartVolume i f j)
  simpa only [signedOmitted, smul_smul, ← mul_pow, neg_mul_neg, one_mul, one_pow,
    one_smul] using h.symm

/-- Reading an actual triple wedge in the original affine residue frame
gives precisely the six gradient cross-coefficients. -/
theorem coordinate_wedge (v : Fin 4 → B) (p : Fin 6) :
    exteriorPower.ιMulti B 3 ![∑ j, v j • coordinateForm i f j,
      coordinateForm i f (pairLeft p), coordinateForm i f (pairRight p)] =
        pairCoefficient (fun j => f (gradient i j)) v p •
          exteriorDifferentialMap f 3 (chartVolume i) := by
  let e := coordinateForm i f
  let g := fun j => f (gradient i j)
  let ω := exteriorDifferentialMap f 3 (chartVolume i)
  have h0 : e ∘ (0 : Fin 4).succAbove = ![e 1,e 2,e 3] := by
    funext j; fin_cases j <;> rfl
  have h1 : e ∘ (1 : Fin 4).succAbove = ![e 0,e 2,e 3] := by
    funext j; fin_cases j <;> rfl
  have h2 : e ∘ (2 : Fin 4).succAbove = ![e 0,e 1,e 3] := by
    funext j; fin_cases j <;> rfl
  have h3 : e ∘ (3 : Fin 4).succAbove = ![e 0,e 1,e 2] := by
    funext j; fin_cases j <;> rfl
  have he (j : Fin 4) : exteriorPower.ιMulti B 3 (e ∘ j.succAbove) =
      ((-1 : B)^j.val*g j) • ω := coordinate_triple i f j
  apply expand_pair e g v ω
  · simpa only [h3, show (3 : Fin 4).val = 3 from rfl,
      pow_succ, pow_zero, mul_one, neg_mul_neg, one_mul, neg_one_mul, neg_smul] using he 3
  · simpa only [h2, show (2 : Fin 4).val = 2 from rfl,
      neg_one_sq, one_mul] using he 2
  · simpa only [h1, Fin.val_one, pow_one, neg_one_mul, neg_smul] using he 1
  · simpa only [h0, Fin.val_zero, pow_zero, one_mul] using he 0

theorem polynomial_differential (q : P) :
    let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
    KaehlerDifferential.D ℂ B (f (mk q)) =
      ∑ j : Fin 4, f (mk (pderiv (coordIndex j) q)) • coordinateForm i f j := by
  dsimp only
  let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
  have h := differential_polynomial (f.comp mk) q
  change KaehlerDifferential.D ℂ B (f (mk q)) = _ at h
  refine h.trans ?_
  exact (Equiv.sum_comp coordIndex (fun j =>
    (f.comp mk) (pderiv j q) • KaehlerDifferential.D ℂ B ((f.comp mk) (X j)))).symm

/-- This computes the differential of every polynomial multiple of each
coordinate two-wedge, in the genuine Kähler module and genuine volume.
The equality remains valid under every further chart localization. -/
theorem polynomial_coordinate_wedge (q : P) (p : Fin 6) :
    let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
    exteriorPower.ιMulti B 3 ![KaehlerDifferential.D ℂ B (f (mk q)),
      coordinateForm i f (pairLeft p), coordinateForm i f (pairRight p)] =
      pairCoefficient (fun j => f (gradient i j))
        (fun j => f (mk (pderiv (coordIndex j) q))) p •
          exteriorDifferentialMap f 3 (chartVolume i) := by
  dsimp only
  rw [polynomial_differential]
  exact coordinate_wedge i f _ p

/-- The same native wedge formula for an actual fraction. The inverse
used here is the unit of its specified denominator, so this applies to
the polynomial fractions on the original coordinate torus. -/
theorem fraction_coordinate_wedge (q r : P) (a : B)
    (ha : a * f ((Ideal.Quotient.mkₐ ℂ (fixedIdeal i)) r) =
      f ((Ideal.Quotient.mkₐ ℂ (fixedIdeal i)) q))
    (hr : IsUnit (f ((Ideal.Quotient.mkₐ ℂ (fixedIdeal i)) r))) (p : Fin 6) :
    let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
    exteriorPower.ιMulti B 3 ![KaehlerDifferential.D ℂ B a,
      coordinateForm i f (pairLeft p), coordinateForm i f (pairRight p)] =
      pairCoefficient (fun j => f (gradient i j))
        (fun j => (↑hr.unit⁻¹ : B) *
          (f (mk (pderiv (coordIndex j) q)) - a * f (mk (pderiv (coordIndex j) r)))) p •
          exteriorDifferentialMap f 3 (chartVolume i) := by
  dsimp only
  let mk := Ideal.Quotient.mkₐ ℂ (fixedIdeal i)
  let z : B := ↑hr.unit⁻¹
  have hu : z * f (mk r) = 1 := by
    rw [← hr.unit_spec]
    exact Units.inv_mul hr.unit
  have hd := congrArg (KaehlerDifferential.D ℂ B) ha
  rw [Derivation.leibniz] at hd
  have he : f (mk r) • KaehlerDifferential.D ℂ B a =
      KaehlerDifferential.D ℂ B (f (mk q)) -
        a • KaehlerDifferential.D ℂ B (f (mk r)) :=
    eq_sub_of_add_eq (by simpa only [add_comm] using hd)
  have hv : KaehlerDifferential.D ℂ B a =
      ∑ j : Fin 4, (z * (f (mk (pderiv (coordIndex j) q)) -
        a * f (mk (pderiv (coordIndex j) r)))) • coordinateForm i f j := by
    calc
      _ = z • (f (mk r) • KaehlerDifferential.D ℂ B a) := by
        rw [smul_smul, hu, one_smul]
      _ = _ := by
        rw [he, polynomial_differential, polynomial_differential]
        simp only [smul_sub, Finset.smul_sum, smul_smul, mul_sub, sub_smul,
          Finset.sum_sub_distrib, mul_assoc]
  rw [hv]
  exact coordinate_wedge i f _ p

end Native

end CycleQ2LiteralThreefoldTorusForms
end

#print axioms CycleQ2LiteralThreefoldTorusForms.coordinateTwo_span_localized
#print axioms CycleQ2LiteralThreefoldTorusForms.polynomial_coordinate_wedge
#print axioms CycleQ2LiteralThreefoldTorusForms.fraction_coordinate_wedge

/-! The literal shifted normal coordinate and the original cubic root.
This is an equivalence of the actual fixed chart algebras, with every
coordinate recorded explicitly. -/

noncomputable section
namespace CycleQ2LiteralThreefoldCubicCoordinates

open MvPolynomial
open CycleQ2IncidenceDehomogenizedChart
open CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
open CycleQ2LiteralThreefoldResidueMinors
open CycleQ2LiteralAmbientChartCoordinates (representative)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literal_vertex_unit)
open CycleQ2GeometricHodgeThreefoldCubic

def unshiftHom (i : Fin 4) : P →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  (CycleQ2HodgeEuler.dehom i).comp (representative i)

theorem unshiftHom_linear (i k : Fin 4) :
    unshiftHom i (linearCoordinate i k) = CycleQ2HodgeEuler.dehom i (X k.castSucc) := by
  refine Fin.succAboveCases i ?_ (fun j => ?_) k
  · rw [linearCoordinate_self, map_one, CycleQ2HodgeEuler.dehom_X_self]
  · rw [linearCoordinate_succAbove, unshiftHom, AlgHom.comp_apply,
      representative, aeval_X]

theorem unshiftHom_dehomogenize (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    unshiftHom i (dehomogenize i p) = CycleQ2HodgeEuler.dehom i p := by
  have he : (unshiftHom i).comp (dehomogenize i) = CycleQ2HodgeEuler.dehom i := by
    apply MvPolynomial.algHom_ext
    intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [AlgHom.comp_apply, dehomogenize_last, map_sub, map_pow,
        unshiftHom_linear]
      rw [unshiftHom, AlgHom.comp_apply, representative, aeval_X, map_add, map_pow]
      exact add_sub_cancel_right _ _
    · rw [AlgHom.comp_apply, dehomogenize_castSucc, unshiftHom_linear]
  exact AlgHom.congr_fun he p

private def shiftHom (i : Fin 4) : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] P :=
  aeval fun j => dehomogenize i (X (i.castSucc.succAbove j))

private theorem shiftHom_dehom (i : Fin 4) (p : MvPolynomial (Fin 5) ℂ) :
    shiftHom i (CycleQ2HodgeEuler.dehom i p) = dehomogenize i p := by
  have he : (shiftHom i).comp (CycleQ2HodgeEuler.dehom i) = dehomogenize i := by
    apply MvPolynomial.algHom_ext
    intro j
    refine Fin.succAboveCases i.castSucc ?_ (fun k => ?_) j
    · simp only [AlgHom.comp_apply, CycleQ2HodgeEuler.dehom_X_self, map_one,
        dehomogenize_self]
    · rw [AlgHom.comp_apply, CycleQ2HodgeEuler.dehom_X_succAbove, shiftHom, aeval_X]
  exact AlgHom.congr_fun he p

def unshiftEquiv (i : Fin 4) : P ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  AlgEquiv.ofAlgHom (unshiftHom i) (shiftHom i) (by
    apply MvPolynomial.algHom_ext
    intro j
    rw [AlgHom.comp_apply, shiftHom, aeval_X, unshiftHom_dehomogenize,
      CycleQ2HodgeEuler.dehom_X_succAbove]
    rfl) (by
    apply MvPolynomial.algHom_ext
    intro j
    change shiftHom i (unshiftHom i (X j)) = X j
    cases j with
    | none => rw [← dehomogenize_normal i, unshiftHom_dehomogenize, shiftHom_dehom]
    | some k => rw [← dehomogenize_succAbove i k, unshiftHom_dehomogenize, shiftHom_dehom])

theorem unshift_seedF (i : Fin 4) :
    unshiftEquiv i (seedF i) = CycleQ2HodgeEuler.F literalEval i := by
  change unshiftHom i (dehomogenize i _) = _
  rw [unshiftHom_dehomogenize]
  exact congrArg (CycleQ2HodgeEuler.dehom i)
    (CycleQ2GeometricHodgeThreefoldIncidence.equation_eq
      CycleQ2LiteralAmbientCylinder.point).symm

def chartEquiv (i : Fin 4) : T i ≃ₐ[ℂ] CycleQ2HodgeEuler.chart literalEval i :=
  Ideal.quotientEquivAlg (fixedIdeal i)
    (Ideal.span {CycleQ2HodgeEuler.F literalEval i}) (unshiftEquiv i) (by
      rw [fixedIdeal, Ideal.map_span, Set.image_singleton]
      exact congrArg (fun p => Ideal.span {p}) (unshift_seedF i).symm)

/-- The native chart used for residue contraction is the original monic
cubic chart, not a replacement hypersurface. -/
def cubicEquiv (i : Fin 4) : T i ≃ₐ[ℂ] Stage literalEval i literal_vertex_unit :=
  (chartEquiv i).trans (chartEquivAdjoinRoot literalEval i literal_vertex_unit)

theorem cubicEquiv_polynomial (i : Fin 4) (p : P) :
    cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i) p) =
      AdjoinRoot.mk (cubic literalEval i literal_vertex_unit) (pack (unshiftHom i p)) := rfl

theorem cubicEquiv_weightOne (i k : Fin 4) :
    cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i) (linearCoordinate i k)) =
      algebraMap (Base ℂ) (Stage literalEval i literal_vertex_unit) (baseValue i k) := by
  rw [cubicEquiv_polynomial, unshiftHom_linear, pack_dehom]
  simp only [expand, aeval_X, Fin.snoc_castSucc, AdjoinRoot.mk_C]

theorem cubicEquiv_weightTwo (i : Fin 4) :
    cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i)
      (dehomogenize i (X (Fin.last 4)))) =
      AdjoinRoot.root (cubic literalEval i literal_vertex_unit) := by
  rw [cubicEquiv_polynomial, unshiftHom_dehomogenize, pack_dehom]
  simp only [expand, aeval_X, Fin.snoc_last, AdjoinRoot.mk_X]

theorem cubicEquiv_coordinate (i : Fin 4) (j : Fin 3) :
    cubicEquiv i (coord i j.succ) =
      algebraMap (Base ℂ) (Stage literalEval i literal_vertex_unit) (X j) := by
  change cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i) (X (some j))) = _
  have h := cubicEquiv_weightOne i (i.succAbove j)
  simpa only [linearCoordinate_succAbove, baseValue, Fin.insertNth_apply_succAbove] using h

/-- The native normal variable z is exactly w+x₂² in the unshifted
power basis; no localization at the cubic discriminant is involved. -/
theorem cubicEquiv_normal (i : Fin 4) :
    cubicEquiv i (coord i 0) =
      AdjoinRoot.root (cubic literalEval i literal_vertex_unit) +
        (algebraMap (Base ℂ) (Stage literalEval i literal_vertex_unit) (baseValue i 2))^2 := by
  change cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i) (X none)) = _
  have h := congrArg
    (fun p => cubicEquiv i (Ideal.Quotient.mk (fixedIdeal i) p))
    (dehomogenize_normal (S := ℂ) i)
  simpa only [map_add, map_pow, dehomogenize_castSucc, cubicEquiv_weightTwo,
    cubicEquiv_weightOne] using h.symm

abbrev LocalBase (S : Finset (Fin 3)) :=
  CycleQ2TorusCubicTrace.Coefficients (R := ℂ) S

abbrev LocalCubic (i : Fin 4) (S : Finset (Fin 3)) :=
  CycleQ2TorusCubicTrace.Cubic literalEval i literal_vertex_unit S

/-- The same native chart map into the actual cubic localization used
by the Laurent coefficient computation. -/
def localizedMap (i : Fin 4) (S : Finset (Fin 3)) : T i →ₐ[ℂ] LocalCubic i S :=
  (IsScalarTower.toAlgHom ℂ (Stage literalEval i literal_vertex_unit)
    (LocalCubic i S)).comp (cubicEquiv i).toAlgHom

def shiftCoefficient (i : Fin 4) (S : Finset (Fin 3)) : LocalBase S :=
  algebraMap (Base ℂ) (LocalBase S) ((baseValue i 2)^2)

theorem localizedMap_coordinate (i : Fin 4) (S : Finset (Fin 3)) (j : Fin 3) :
    localizedMap i S (coord i j.succ) =
      algebraMap (LocalBase S) (LocalCubic i S)
        (algebraMap (Base ℂ) (LocalBase S) (X j)) := by
  change algebraMap (Stage literalEval i literal_vertex_unit) (LocalCubic i S)
    (cubicEquiv i (coord i j.succ)) = _
  rw [cubicEquiv_coordinate]
  simp only [← IsScalarTower.algebraMap_apply]

theorem localizedMap_normal (i : Fin 4) (S : Finset (Fin 3)) :
    localizedMap i S (coord i 0) =
      CycleQ2TorusCubicTrace.root literalEval i literal_vertex_unit S +
        algebraMap (LocalBase S) (LocalCubic i S) (shiftCoefficient i S) := by
  simpa only [CycleQ2TorusCubicTrace.root, shiftCoefficient, map_add, map_pow,
    ← IsScalarTower.algebraMap_apply] using
    congrArg (algebraMap (Stage literalEval i literal_vertex_unit) (LocalCubic i S))
      (cubicEquiv_normal i)

/-- Every element of the actual localized cubic has a quadratic normal
form in the original native z coordinate. -/
theorem exists_native_normal (i : Fin 4) (S : Finset (Fin 3)) (x : LocalCubic i S) :
    ∃ a : Fin 3 → LocalBase S,
      CycleQ2CubicCoefficientTrace.normal (localizedMap i S (coord i 0)) a = x := by
  rw [localizedMap_normal]
  exact CycleQ2CubicCoefficientTrace.exists_translated_normal
    (CycleQ2TorusCubicTrace.powerBasis literalEval i literal_vertex_unit S)
    (CycleQ2TorusCubicTrace.root literalEval i literal_vertex_unit S)
    (CycleQ2TorusCubicTrace.powerBasis_apply literalEval i literal_vertex_unit S)
    (shiftCoefficient i S) x

/-- The Laurent trace's original power-basis functional reads the native
z² coefficient without a change of scale or sign. -/
theorem topCoefficient_native_normal (i : Fin 4) (S : Finset (Fin 3))
    (a : Fin 3 → LocalBase S) :
    CycleQ2TorusCubicTrace.topCoefficient literalEval i literal_vertex_unit S
      (CycleQ2CubicCoefficientTrace.normal (localizedMap i S (coord i 0)) a) = a 2 := by
  rw [localizedMap_normal]
  exact CycleQ2CubicCoefficientTrace.top_translated_normal
    (CycleQ2TorusCubicTrace.powerBasis literalEval i literal_vertex_unit S)
    (CycleQ2TorusCubicTrace.root literalEval i literal_vertex_unit S)
    (CycleQ2TorusCubicTrace.powerBasis_apply literalEval i literal_vertex_unit S)
    (shiftCoefficient i S) a

end CycleQ2LiteralThreefoldCubicCoordinates
end

#print axioms CycleQ2LiteralThreefoldCubicCoordinates.cubicEquiv
#print axioms CycleQ2LiteralThreefoldCubicCoordinates.cubicEquiv_normal
#print axioms CycleQ2LiteralThreefoldCubicCoordinates.topCoefficient_native_normal

/-! The four original polynomial gradients in the same translated cubic
coordinates.  The identity is proved before taking the hypersurface
quotient, so it retains the native equation and all four partials. -/

noncomputable section
namespace CycleQ2LiteralThreefoldCubicCoordinates

open MvPolynomial
open CycleQ2IncidenceDehomogenizedChart
open CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
open CycleQ2LiteralThreefoldResidueMinors
open CycleQ2LiteralThreefoldResidueFrame (gradient)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literal_vertex_unit)
open CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2CubicCoefficientTrace (normal)

private def nativePack (i : Fin 4) : P ≃ₐ[ℂ] Polynomial (Base ℂ) :=
  (unshiftEquiv i).trans pack

private theorem nativePack_coordinate (i : Fin 4) (j : Fin 3) :
    nativePack i (X (some j)) = Polynomial.C (X j : Base ℂ) := by
  change pack (unshiftHom i (X (some j))) = _
  rw [← linearCoordinate_succAbove i j, unshiftHom_linear, pack_dehom]
  simp only [expand, aeval_X, Fin.snoc_castSucc, baseValue,
    Fin.insertNth_apply_succAbove]

private theorem nativePack_normal (i : Fin 4) :
    nativePack i (X none) =
      Polynomial.X + Polynomial.C ((baseValue i 2 : Base ℂ)^2) := by
  change pack (unshiftHom i (X none)) = _
  rw [unshiftHom, AlgHom.comp_apply,
    CycleQ2LiteralAmbientChartCoordinates.representative, aeval_X, pack_dehom]
  simp only [map_add, map_pow, expand, aeval_X, Fin.snoc_last, Fin.snoc_castSucc]

private theorem nativePack_base (i : Fin 4) (p : Base ℂ) :
    nativePack i (rename Option.some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa only [rename_C] using (nativePack i).commutes a
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
      simp only [map_mul, rename_X, hp, nativePack_coordinate]

private theorem literal_vertex_value :
    literalEval CycleQ2GeometricHodgeThreefold.vertexCoefficient = 1 := by
  change aeval (CycleQ2IncidenceGenericPointSemantics.pointSextic
    CycleQ2LiteralAmbientCylinder.point)
      (X CycleQ2IncidenceNormalForm.fullSexticLeadingIndex) = 1
  rw [aeval_X]
  change CycleQ2IncidenceEquations.seedSexticCoefficients (57 : ℂ) Complex.I
    CycleQ2IncidenceNormalForm.fullSexticLeadingIndex = 1
  rw [CycleQ2IncidenceEquations.seedSexticCoefficients,
    CycleQ2IncidenceNormalForm.fullSexticLeadingIndex_exponent,
    CycleQ2IncidenceEquations.smoothF_leading_coefficient]

private theorem nativePack_seedF (i : Fin 4) :
    nativePack i (seedF i) = cubic literalEval i literal_vertex_unit := by
  change pack (unshiftEquiv i (seedF i)) = _
  rw [unshift_seedF, pack_F, literal_vertex_value, map_one, map_one, one_mul]

/-- The actual lower coefficients after substituting w=z-x₂². -/
def nativeBaseCoefficients (i : Fin 4) : Fin 3 → Base ℂ :=
  let c := fun j : Fin 3 => (cubic literalEval i literal_vertex_unit).coeff j.val
  let u : Base ℂ := (baseValue i 2)^2
  ![c 0-u*c 1+u^2*c 2-u^3, c 1-2*u*c 2+3*u^2, c 2-3*u]

def nativeCoefficients (i : Fin 4) (S : Finset (Fin 3)) (j : Fin 3) : LocalBase S :=
  algebraMap (Base ℂ) (LocalBase S) (nativeBaseCoefficients i j)

theorem nativeCoefficients_eq_translated (i : Fin 4) (S : Finset (Fin 3)) :
    nativeCoefficients i S =
      let c := CycleQ2TorusCubicTrace.coefficients literalEval i literal_vertex_unit S
      let u := shiftCoefficient i S
      ![c 0-u*c 1+u^2*c 2-u^3, c 1-2*u*c 2+3*u^2, c 2-3*u] := by
  funext j
  fin_cases j <;>
    simp only [nativeCoefficients, nativeBaseCoefficients,
      CycleQ2TorusCubicTrace.coefficients, shiftCoefficient,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      map_sub, map_add, map_mul, map_pow, map_ofNat]

private theorem cubic_decomposition (i : Fin 4) :
    cubic literalEval i literal_vertex_unit = Polynomial.X^3 +
      Polynomial.C ((cubic literalEval i literal_vertex_unit).coeff 0) +
      Polynomial.C ((cubic literalEval i literal_vertex_unit).coeff 1) * Polynomial.X +
      Polynomial.C ((cubic literalEval i literal_vertex_unit).coeff 2) * Polynomial.X^2 := by
  let p := cubic literalEval i literal_vertex_unit
  have h3 : p.coeff 3 = 1 := by
    have hm := (cubic_monic literalEval i literal_vertex_unit).leadingCoeff
    change p.coeff p.natDegree = 1 at hm
    simpa only [p, cubic_natDegree] using hm
  have hp : p = ∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val := by
    rw [Fin.sum_univ_eq_sum_range (fun j => Polynomial.C (p.coeff j) * Polynomial.X^j)]
    exact p.as_sum_range_C_mul_X_pow' (by
      rw [show p.natDegree = 3 from cubic_natDegree literalEval i literal_vertex_unit]
      decide)
  calc
    p = ∑ j : Fin 4, Polynomial.C (p.coeff j.val) * Polynomial.X^j.val := hp
    _ = _ := by
      rw [Fin.sum_univ_four]
      simp only [Fin.val_zero, Fin.val_one, show (2 : Fin 4).val = 2 from rfl,
        show (3 : Fin 4).val = 3 from rfl, h3, map_one, pow_zero, pow_one,
        one_mul, mul_one]
      ring

/-- This is an equality of the original chart polynomials, before
passing to the equation quotient or any coordinate localization. -/
theorem seedF_native_cubic (i : Fin 4) :
    seedF i = (X none : P)^3 + rename Option.some (nativeBaseCoefficients i 0) +
      rename Option.some (nativeBaseCoefficients i 1) * X none +
      rename Option.some (nativeBaseCoefficients i 2) * X none^2 := by
  apply (nativePack i).injective
  rw [nativePack_seedF]
  simp only [map_add, map_mul, map_pow, nativePack_base, nativePack_normal]
  conv_lhs => rw [cubic_decomposition]
  simp only [nativeBaseCoefficients, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, map_sub, map_add, map_mul, map_pow, map_ofNat]
  ring

private theorem pderiv_base_normal (p : Base ℂ) :
    pderiv none (rename Option.some p) = 0 := by
  apply MvPolynomial.pderiv_eq_zero_of_notMem_vars
  intro h
  obtain ⟨j, _, hj⟩ := MvPolynomial.mem_vars_rename Option.some p h
  cases hj

private theorem pderiv_base_coordinate (p : Base ℂ) (j : Fin 3) :
    pderiv (some j) (rename Option.some p) = rename Option.some (pderiv j p) :=
  MvPolynomial.pderiv_rename (Option.some_injective (Fin 3)) j p

theorem pderiv_seedF_normal (i : Fin 4) :
    pderiv none (seedF i) = rename Option.some (nativeBaseCoefficients i 1) +
      2 * rename Option.some (nativeBaseCoefficients i 2) * X none + 3 * X none^2 := by
  rw [seedF_native_cubic]
  simp only [map_add, pderiv_pow, pderiv_mul, pderiv_X_self, pderiv_base_normal]
  norm_num <;> ring

theorem pderiv_seedF_coordinate (i : Fin 4) (j : Fin 3) :
    pderiv (some j) (seedF i) = rename Option.some (pderiv j (nativeBaseCoefficients i 0)) +
      rename Option.some (pderiv j (nativeBaseCoefficients i 1)) * X none +
      rename Option.some (pderiv j (nativeBaseCoefficients i 2)) * X none^2 := by
  have hn : pderiv (some j) (X none : P) = 0 := pderiv_X_of_ne (by simp)
  rw [seedF_native_cubic]
  simp only [map_add, pderiv_pow, pderiv_mul, pderiv_base_coordinate, hn,
    mul_zero, add_zero, zero_add]

private def nativeEval (i : Fin 4) (S : Finset (Fin 3)) : P →ₐ[ℂ] LocalCubic i S :=
  (localizedMap i S).comp (Ideal.Quotient.mkₐ ℂ (fixedIdeal i))

private theorem nativeEval_normal (i : Fin 4) (S : Finset (Fin 3)) :
    nativeEval i S (X none) = localizedMap i S (coord i 0) := rfl

private theorem nativeEval_base (i : Fin 4) (S : Finset (Fin 3)) (p : Base ℂ) :
    nativeEval i S (rename Option.some p) =
      algebraMap (LocalBase S) (LocalCubic i S)
        (algebraMap (Base ℂ) (LocalBase S) p) := by
  change algebraMap (Stage literalEval i literal_vertex_unit) (LocalCubic i S)
    (AdjoinRoot.mk (cubic literalEval i literal_vertex_unit)
      (nativePack i (rename Option.some p))) = _
  rw [nativePack_base, AdjoinRoot.mk_C]
  simp only [← IsScalarTower.algebraMap_apply]

/-- The original normal partial is the derivative of this same cubic
in z, with its original monic leading coefficient. -/
theorem localizedMap_gradient_normal (i : Fin 4) (S : Finset (Fin 3)) :
    localizedMap i S (gradient i 0) = normal (localizedMap i S (coord i 0))
      ![nativeCoefficients i S 1, 2*nativeCoefficients i S 2, 3] := by
  change nativeEval i S (pderiv none (seedF i)) = _
  rw [pderiv_seedF_normal]
  simp only [map_add, map_mul, map_pow, map_ofNat, nativeEval_base,
    nativeEval_normal, normal, nativeCoefficients,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- Each original retained-coordinate partial differentiates the actual
three cubic coefficients while fixing the native z coordinate. -/
theorem localizedMap_gradient_coordinate (i : Fin 4) (S : Finset (Fin 3)) (j : Fin 3) :
    localizedMap i S (gradient i j.succ) = normal (localizedMap i S (coord i 0))
      ((CycleQ2TorusLogDerivatives.localizedPartial ℂ S j) ∘ nativeCoefficients i S) := by
  change nativeEval i S (pderiv (some j) (seedF i)) = _
  rw [pderiv_seedF_coordinate]
  simp only [map_add, map_mul, map_pow, nativeEval_base, nativeEval_normal,
    normal, nativeCoefficients, Function.comp_apply,
    CycleQ2TorusLogDerivatives.localizedPartial_algebraMap]

/-- The translated root relation belongs to the same actual localized
chart, including where the original normal partial vanishes. -/
theorem native_root_relation (i : Fin 4) (S : Finset (Fin 3)) :
    (localizedMap i S (coord i 0))^3 =
      -normal (localizedMap i S (coord i 0)) (nativeCoefficients i S) := by
  have hq : Ideal.Quotient.mk (fixedIdeal i) (seedF i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp [fixedIdeal]))
  have hz : nativeEval i S (seedF i) = 0 := by
    change localizedMap i S (Ideal.Quotient.mk (fixedIdeal i) (seedF i)) = 0
    rw [hq, map_zero]
  rw [seedF_native_cubic] at hz
  simp only [map_add, map_mul, map_pow, nativeEval_normal, nativeEval_base] at hz
  simp only [normal, nativeCoefficients]
  linear_combination hz

end CycleQ2LiteralThreefoldCubicCoordinates
end

#print axioms CycleQ2LiteralThreefoldCubicCoordinates.seedF_native_cubic
#print axioms CycleQ2LiteralThreefoldCubicCoordinates.localizedMap_gradient_normal
#print axioms CycleQ2LiteralThreefoldCubicCoordinates.localizedMap_gradient_coordinate
#print axioms CycleQ2LiteralThreefoldCubicCoordinates.native_root_relation
