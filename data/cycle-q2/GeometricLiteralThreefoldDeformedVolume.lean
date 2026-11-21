import Proposal.GeometricLiteralThreefoldChartVolume
import Proposal.GeometricLiteralThreefoldLiftDifference
import Proposal.GeometricLiteralThreefoldLiftTransition

/-! The relative adjunction three-form evaluated at a lifted point of the
first-order sextic. Its reduction is the original regular hypersurface residue.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldDeformedVolume

open MvPolynomial CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldChartLift CycleQ2LiteralThreefoldKodairaSpencer
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldResidueMinors CycleQ2LiteralThreefoldChartVolume
  CycleQ2GeometricExteriorSheaf CycleQ2ExteriorSectionNaturality

abbrev Dual := Jet ℂ
abbrev epsilon (S : Type) [CommRing S] : Jet S := TrivSqZeroExt.inr 1

variable {S : Type} [CommRing S] [Algebra ℂ S] {i : Fin 4}

def scalarMap : Dual →ₐ[ℂ] Jet S := jetMap (Algebra.ofId ℂ S)
@[reducible] local instance dualAlgebra : Algebra Dual (Jet S) := (scalarMap (S := S)).toRingHom.toAlgebra
local instance dualTower : IsScalarTower ℂ Dual (Jet S) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := Dual) (A := Jet S) fun c =>
    ((scalarMap (S := S)).commutes c).symm

abbrev Forms (S : Type) [CommRing S] [Algebra ℂ S] (n : ℕ) :=
  ⋀[Jet S]^n (KaehlerDifferential Dual (Jet S))

def gradient (x : Lift i S) (j : Fin 4) : Jet S :=
  aeval x.x (pderiv (coordIndex j) (seedF i)) -
    epsilon S * aeval x.x (pderiv (coordIndex j) (test i))

theorem gradient_fst (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) (j : Fin 4) :
    (gradient x j).fst = f (CycleQ2LiteralThreefoldResidueFrame.gradient i j) := by
  change (aeval x.x _).fst - 0 * _ = _
  rw [zero_mul, sub_zero]
  exact eval_fst x f hx _

theorem gradient_bezout (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) :
    ∃ c : Fin 4 → Jet S, ∑ j, c j * gradient x j = 1 := by
  obtain ⟨c,hc⟩ := chartBezout i
  let a : Fin 4 → Jet S := fun j => TrivSqZeroExt.inl (f (c j))
  let z := ∑ j, a j * gradient x j
  have hz : z.fst = 1 := by
    change (TrivSqZeroExt.fstHom ℂ S S) (∑ j, a j * gradient x j) = 1
    simp only [map_sum, map_mul, TrivSqZeroExt.fstHom_apply, a, TrivSqZeroExt.fst_inl,
      gradient_fst x f hx]
    simpa only [map_sum, map_mul, map_one] using congrArg f hc
  have hu : IsUnit z := TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (hz.symm ▸ isUnit_one)
  refine ⟨fun j => (↑hu.unit⁻¹ : Jet S) * a j, ?_⟩
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  change (↑hu.unit⁻¹ : Jet S) * z = 1
  exact hu.val_inv_mul

def coordinateDifferential (x : Lift i S) (j : Fin 4) :=
  KaehlerDifferential.D Dual (Jet S) (x.x (coordIndex j))

private theorem relative_chain (x : Lift i S) (p : P) :
    KaehlerDifferential.D Dual (Jet S) (aeval x.x p) =
      ∑ j, aeval x.x (pderiv (coordIndex j) p) • coordinateDifferential x j := by
  have h := congrArg (KaehlerDifferential.map ℂ Dual (Jet S) (Jet S))
    (differential_polynomial (aeval x.x) p)
  simp only [KaehlerDifferential.map_D, Algebra.algebraMap_self, RingHom.id_apply, map_sum,
    map_smul, aeval_X] at h
  exact h.trans (Equiv.sum_comp coordIndex _).symm

theorem conormal (x : Lift i S) : ∑ j, gradient x j • coordinateDifferential x j = 0 := by
  have h := congrArg (KaehlerDifferential.D Dual (Jet S)) x.equation
  have he : KaehlerDifferential.D Dual (Jet S) (epsilon S) = 0 := by
    have hmap : algebraMap Dual (Jet S) (epsilon ℂ) = epsilon S := by
      apply TrivSqZeroExt.ext
      · exact map_zero (Algebra.ofId ℂ S)
      · exact map_one (Algebra.ofId ℂ S)
    rw [← hmap, Derivation.map_algebraMap]
  change KaehlerDifferential.D Dual (Jet S) (aeval x.x (seedF i)) =
    KaehlerDifferential.D Dual (Jet S) (epsilon S * aeval x.x (test i)) at h
  rw [Derivation.leibniz, he, smul_zero, add_zero, relative_chain, relative_chain] at h
  rw [← sub_eq_zero] at h
  rw [← h, Finset.smul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change (_ - epsilon S * _) • _ = _
  let a := aeval x.x (pderiv (coordIndex j) (seedF i))
  let b := aeval x.x (pderiv (coordIndex j) (test i))
  let m := coordinateDifferential x j
  exact (sub_smul a (epsilon S * b) m).trans
    (congrArg (fun z => a • m - z) (mul_smul (epsilon S) b m))

/-- The relative hypersurface residue pulled back to the dual-number point.
The four deformed partials generate the unit ideal even at a nonreduced point. -/
def volume (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) : Forms S 3 :=
  ∑ j, (gradient_bezout x f hx).choose j • signedOmitted (Jet S) (coordinateDifferential x) j

theorem gradient_smul_volume (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) (k : Fin 4) :
    gradient x k • volume x f hx = signedOmitted (Jet S) (coordinateDifferential x) k := by
  let c := (gradient_bezout x f hx).choose
  let z := signedOmitted (Jet S) (coordinateDifferential x)
  change gradient x k • (∑ j, c j • z j) = z k
  rw [Finset.smul_sum]
  calc
    _ = ∑ j, (c j * gradient x j) • z k := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_comm (gradient x k), signedOmitted_cross _ _ (conormal x) j k, mul_smul]
    _ = z k := by rw [← Finset.sum_smul, (gradient_bezout x f hx).choose_spec, one_smul]

theorem volume_unique (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) (w : Forms S 3)
    (hw : ∀ j, gradient x j • w = signedOmitted (Jet S) (coordinateDifferential x) j) :
    w = volume x f hx := by
  obtain ⟨c, hc⟩ := gradient_bezout x f hx
  have eq (j : Fin 4) := (hw j).trans (gradient_smul_volume x f hx j).symm
  calc
    w = (∑ j, c j * gradient x j) • w := by rw [hc, one_smul]
    _ = (∑ j, c j * gradient x j) • volume x f hx := by
      simp only [Finset.sum_smul, mul_smul, eq]
    _ = _ := by rw [hc, one_smul]

section Restriction
local instance (priority := 2300) : Algebra Dual Dual := Algebra.id Dual
local instance (priority := 2300) : SMul Dual Dual := (Algebra.id Dual).toSMul
local instance : IsScalarTower Dual Dual (Jet S) :=
  IsScalarTower.of_algebraMap_eq (R := Dual) (S := Dual) (A := Jet S) fun _ => rfl
variable {U : Type} [CommRing U] [Algebra ℂ U]

def relativeJetMap (g : S →ₐ[ℂ] U) : Jet S →ₐ[Dual] Jet U where
  __ := (jetMap g).toRingHom
  commutes' c := by
    apply TrivSqZeroExt.ext
    · exact g.commutes c.fst
    · exact g.commutes c.snd

def mapDifferential (g : S →ₐ[ℂ] U) : KaehlerDifferential Dual (Jet S)
    →ₛₗ[(relativeJetMap g).toRingHom] KaehlerDifferential Dual (Jet U) := by
  letI := (relativeJetMap g).toRingHom.toAlgebra
  letI : IsScalarTower Dual (Jet S) (Jet U) := IsScalarTower.of_algHom (relativeJetMap g)
  let F := KaehlerDifferential.map Dual Dual (Jet S) (Jet U)
  exact { toFun := F, map_add' := F.map_add, map_smul' := fun a m =>
    (F.map_smul a m).trans (IsScalarTower.algebraMap_smul (Jet U) a (F m)).symm }

private theorem mapDifferential_D (g : S →ₐ[ℂ] U) (a : Jet S) :
    mapDifferential g (KaehlerDifferential.D Dual (Jet S) a) =
    KaehlerDifferential.D Dual (Jet U) (jetMap g a) := by
  let := (relativeJetMap g).toRingHom.toAlgebra
  let : IsScalarTower Dual (Jet S) (Jet U) := IsScalarTower.of_algHom (relativeJetMap g)
  exact KaehlerDifferential.map_D Dual Dual (Jet S) (Jet U) a

def mapForms (g : S →ₐ[ℂ] U) (n : ℕ) : Forms S n
    →ₛₗ[(relativeJetMap g).toRingHom] Forms U n :=
  exteriorMap _ (mapDifferential g) n

private theorem map_aeval_jet (g : S →ₐ[ℂ] U) (x : Lift i S) (p : P) :
    jetMap g (aeval x.x p) = aeval (mapLift g x).x p := by
  have H : (jetMap g).comp (aeval x.x) = aeval (mapLift g x).x := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply, aeval_X]
    rfl
  exact AlgHom.congr_fun H p

theorem map_gradient (g : S →ₐ[ℂ] U) (x : Lift i S) (j : Fin 4) :
    jetMap g (gradient x j) = gradient (mapLift g x) j := by
  have he : jetMap g (epsilon S) = epsilon U := by
    apply TrivSqZeroExt.ext
    · exact map_zero g
    · exact map_one g
  simp only [gradient, map_sub, map_mul, he, map_aeval_jet]

theorem map_volume (g : S →ₐ[ℂ] U) (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) :
    mapForms g 3 (volume x f hx) =
      volume (mapLift g x) (g.comp f) (fun a => congrArg g (hx a)) := by
  apply volume_unique
  intro j
  rw [← map_gradient g]
  change (relativeJetMap g).toRingHom (gradient x j) • _ = _
  rw [← map_smulₛₗ, gradient_smul_volume]
  simp only [mapForms, signedOmitted, map_smulₛₗ, map_pow, map_neg, map_one, exteriorMap_wedge]
  apply congrArg (fun w => (-1 : Jet U)^j.val • exteriorPower.ιMulti (Jet U) 3 w)
  exact funext fun k => mapDifferential_D g _

end Restriction

section Reduction

@[reducible] local instance : Algebra Dual ℂ := TrivSqZeroExt.algebraBase ℂ ℂ
@[reducible] local instance : Algebra (Jet S) S := TrivSqZeroExt.algebraBase S S
@[reducible] local instance : Algebra Dual S :=
  ((algebraMap ℂ S).comp (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom).toAlgebra
local instance : IsScalarTower Dual ℂ S :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl
local instance (priority := 2200) : SMul Dual (Jet S) := (dualAlgebra (S := S)).toSMul
local instance : IsScalarTower Dual (Jet S) S :=
  IsScalarTower.of_algebraMap_eq (R := Dual) (S := Jet S) (A := S) fun _ => rfl

/-- The canonical reduction of relative differentials modulo the infinitesimal parameter. -/
def reduceDifferential :
    KaehlerDifferential Dual (Jet S) →ₛₗ[(TrivSqZeroExt.fstHom ℂ S S).toRingHom]
      KaehlerDifferential ℂ S where
  toFun := KaehlerDifferential.map Dual ℂ (Jet S) S
  map_add' := map_add _
  map_smul' a m := by
    rw [map_smul]
    exact (IsScalarTower.algebraMap_smul S a _).symm

def reduceForms (n : ℕ) :
    Forms S n →ₛₗ[(TrivSqZeroExt.fstHom ℂ S S).toRingHom] (⋀[S]^n (KaehlerDifferential ℂ S)) :=
  exteriorMap _ reduceDifferential n

theorem reduce_volume (x : Lift i S) (f : T i →ₐ[ℂ] S) (hx : LiesOver x f) :
    reduceForms 3 (volume x f hx) = exteriorDifferentialMap f 3 (chartVolume i) := by
  apply chartVolume_unique i f
  intro j
  rw [← gradient_fst x f hx j]
  change (TrivSqZeroExt.fstHom ℂ S S).toRingHom (gradient x j) • _ = _
  rw [← map_smulₛₗ, gradient_smul_volume]
  simp only [reduceForms, signedOmitted, map_smulₛₗ, map_pow, map_neg, map_one, exteriorMap_wedge]
  apply congrArg (fun w => (-1 : S)^j.val • exteriorPower.ιMulti S 3 w)
  funext k
  change KaehlerDifferential.map Dual ℂ (Jet S) S
    (KaehlerDifferential.D Dual (Jet S) (x.x _)) = KaehlerDifferential.D ℂ S (f _)
  rw [KaehlerDifferential.map_D]
  exact congrArg (KaehlerDifferential.D ℂ S) (hx _)

end Reduction

end CycleQ2LiteralThreefoldDeformedVolume
end

#print axioms CycleQ2LiteralThreefoldDeformedVolume.gradient_smul_volume
#print axioms CycleQ2LiteralThreefoldDeformedVolume.reduce_volume
#print axioms CycleQ2LiteralThreefoldDeformedVolume.map_volume
