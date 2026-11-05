import HodgeComputer.Verify
import Proposal.PExplicitWitnessComplete
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option maxRecDepth 1000
noncomputable section
namespace HodgeComputer.DenseP0
open MvPolynomial HodgeTestbed
abbrev E := HodgeTestbed.ExplicitWitness.D

def cm : SexticPoly →+* Poly := MvPolynomial.map (algebraMap ℚ ℂ)
def F : Poly := cm Frozen.F
def A : Poly := cm Frozen.A
def D : Poly := cm ExplicitWitness.D
def N : Fin 6 → Poly := fun i => cm (ExplicitWitness.N i)
def Q : Poly := cm ExplicitWitness.C

theorem directional_cm (P : SexticPoly) (V : Fin 6 → SexticPoly) :
  directional (cm P) (fun i => cm (V i)) = cm (directional P V) := by
  simp only [directional, cm, pderiv_map, map_sum, map_mul]

theorem divergence_cm (V : Fin 6 → SexticPoly) :
  divergence (fun i => cm (V i)) = cm (divergence V) := by
  simp only [divergence, cm, pderiv_map, map_sum]

theorem equations : Equations F A D N Q where
  e1 := by
    change directional (cm Frozen.F) (fun i => cm (ExplicitWitness.N i)) = _
    rw [directional_cm, ExplicitWitness.certificate.e1, map_mul]
    rfl
  e2 := by
    change cm ExplicitWitness.D * divergence (fun i => cm (ExplicitWitness.N i)) -
      directional (cm ExplicitWitness.D) (fun i => cm (ExplicitWitness.N i)) = _
    rw [divergence_cm, directional_cm, ← map_mul, ← map_sub]
    change cm (divergenceNumerator ExplicitWitness.D ExplicitWitness.N) = _
    rw [ExplicitWitness.certificate.e2, map_mul]
    rfl

def toUni : Poly →+* Polynomial Coeff := MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C) (fun i => if i.val = 0 then (Polynomial.X) else if i.val = 1 then (Polynomial.C (MvPolynomial.X 0)) else if i.val = 2 then (Polynomial.C (MvPolynomial.X 1)) else if i.val = 3 then (Polynomial.C (MvPolynomial.X 2)) else if i.val = 4 then (Polynomial.C (MvPolynomial.X 3)) else (Polynomial.C (MvPolynomial.X 4)))

def fromUni : Polynomial Coeff →+* Poly := Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom MvPolynomial.C (fun i => if i.val = 0 then (MvPolynomial.X 1) else if i.val = 1 then (MvPolynomial.X 2) else if i.val = 2 then (MvPolynomial.X 3) else if i.val = 3 then (MvPolynomial.X 4) else (MvPolynomial.X 5))) (MvPolynomial.X 0)

@[simp] theorem toUni_X0 : toUni (MvPolynomial.X 0) = (Polynomial.X) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X1 : toUni (MvPolynomial.X 1) = (Polynomial.C (MvPolynomial.X 0)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X2 : toUni (MvPolynomial.X 2) = (Polynomial.C (MvPolynomial.X 1)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X3 : toUni (MvPolynomial.X 3) = (Polynomial.C (MvPolynomial.X 2)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X4 : toUni (MvPolynomial.X 4) = (Polynomial.C (MvPolynomial.X 3)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_X5 : toUni (MvPolynomial.X 5) = (Polynomial.C (MvPolynomial.X 4)) := by simp only [toUni,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem toUni_C (c : ℂ) : toUni (MvPolynomial.C c) = Polynomial.C (MvPolynomial.C c) := by simp [toUni]

@[simp] theorem fromUni_w0 : fromUni (Polynomial.C (MvPolynomial.X 0)) = (MvPolynomial.X 1) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w1 : fromUni (Polynomial.C (MvPolynomial.X 1)) = (MvPolynomial.X 2) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w2 : fromUni (Polynomial.C (MvPolynomial.X 2)) = (MvPolynomial.X 3) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w3 : fromUni (Polynomial.C (MvPolynomial.X 3)) = (MvPolynomial.X 4) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_w4 : fromUni (Polynomial.C (MvPolynomial.X 4)) = (MvPolynomial.X 5) := by simp only [fromUni,Polynomial.coe_eval₂RingHom,Polynomial.eval₂_C,MvPolynomial.eval₂Hom_X']; rfl

@[simp] theorem fromUni_t : fromUni Polynomial.X = MvPolynomial.X 0 := by simp [fromUni]

theorem retract : fromUni.comp toUni = RingHom.id Poly := by

  apply MvPolynomial.ringHom_ext

  · intro c; simp [toUni,fromUni]

  · intro i; fin_cases i <;> simp only [RingHom.comp_apply,RingHom.id_apply]

    · change fromUni (toUni (X 0)) = X 0; simp only [toUni_X0,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 1)) = X 1; simp only [toUni_X1,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 2)) = X 2; simp only [toUni_X2,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 3)) = X 3; simp only [toUni_X3,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 4)) = X 4; simp only [toUni_X4,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

    · change fromUni (toUni (X 5)) = X 5; simp only [toUni_X5,map_add,fromUni_t,fromUni_w0,fromUni_w1,fromUni_w2,fromUni_w3,fromUni_w4] <;> ring

def specialize : Coeff →+* ℂ := MvPolynomial.eval (fun _ => 1)
def castUni : Polynomial ℚ →+* Polynomial ℂ := Polynomial.mapRingHom (algebraMap ℚ ℂ)
private theorem lineMap_X0 : ExplicitWitness.lineMap (MvPolynomial.X 0) = Polynomial.X := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
private theorem lineMap_X1 : ExplicitWitness.lineMap (MvPolynomial.X 1) = 1 := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
private theorem lineMap_X2 : ExplicitWitness.lineMap (MvPolynomial.X 2) = 1 := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
private theorem lineMap_X3 : ExplicitWitness.lineMap (MvPolynomial.X 3) = 1 := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
private theorem lineMap_X4 : ExplicitWitness.lineMap (MvPolynomial.X 4) = 1 := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
private theorem lineMap_X5 : ExplicitWitness.lineMap (MvPolynomial.X 5) = 1 := by simp only [ExplicitWitness.lineMap,MvPolynomial.eval₂Hom_X']; rfl
theorem commute : (Polynomial.mapRingHom specialize).comp (toUni.comp cm) =
    castUni.comp ExplicitWitness.lineMap := by
  apply MvPolynomial.ringHom_ext
  · intro c; simp [toUni, cm, castUni, specialize, ExplicitWitness.lineMap]
  · intro i; fin_cases i
    · change (toUni (cm (MvPolynomial.X 0))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 0))
      norm_num [cm,castUni,specialize,lineMap_X0]
    · change (toUni (cm (MvPolynomial.X 1))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 1))
      norm_num [cm,castUni,specialize,lineMap_X1]
    · change (toUni (cm (MvPolynomial.X 2))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 2))
      norm_num [cm,castUni,specialize,lineMap_X2]
    · change (toUni (cm (MvPolynomial.X 3))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 3))
      norm_num [cm,castUni,specialize,lineMap_X3]
    · change (toUni (cm (MvPolynomial.X 4))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 4))
      norm_num [cm,castUni,specialize,lineMap_X4]
    · change (toUni (cm (MvPolynomial.X 5))).map specialize = castUni (ExplicitWitness.lineMap (MvPolynomial.X 5))
      norm_num [cm,castUni,specialize,lineMap_X5]

def fUni : Polynomial Coeff := Polynomial.C ((MvPolynomial.C (14 : ℂ))) * Polynomial.X^6 +
Polynomial.C ((MvPolynomial.C (7 : ℂ)) * (MvPolynomial.X 0)^2 +
    (MvPolynomial.C (21 : ℂ)) * (MvPolynomial.X 2)^2) * Polynomial.X^4 +
Polynomial.C ((MvPolynomial.C (23 : ℂ)) * (MvPolynomial.X 0)^4 +
    (MvPolynomial.C (12 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (23 : ℂ)) * (MvPolynomial.X 2)^4) * Polynomial.X^2 +
Polynomial.C ((MvPolynomial.C (4 : ℂ)) * (MvPolynomial.X 0)^6 +
    (MvPolynomial.C (39 : ℂ)) * (MvPolynomial.X 0)^4 * (MvPolynomial.X 2)^2 +
    (MvPolynomial.C (73 : ℂ)) * (MvPolynomial.X 0)^2 * (MvPolynomial.X 2)^4 +
    (MvPolynomial.C (31 : ℂ)) * (MvPolynomial.X 1)^6 +
    (MvPolynomial.C (37 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 3)^2 +
    (MvPolynomial.C (41 : ℂ)) * (MvPolynomial.X 1)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (43 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^4 +
    (MvPolynomial.C (47 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (53 : ℂ)) * (MvPolynomial.X 1)^2 * (MvPolynomial.X 4)^4 +
    (MvPolynomial.C (8 : ℂ)) * (MvPolynomial.X 2)^6 +
    (MvPolynomial.C (59 : ℂ)) * (MvPolynomial.X 3)^6 +
    (MvPolynomial.C (61 : ℂ)) * (MvPolynomial.X 3)^4 * (MvPolynomial.X 4)^2 +
    (MvPolynomial.C (67 : ℂ)) * (MvPolynomial.X 3)^2 * (MvPolynomial.X 4)^4 +
    (MvPolynomial.C (71 : ℂ)) * (MvPolynomial.X 4)^6) * Polynomial.X^0
theorem toUni_F : toUni F = fUni := by
  norm_num [F, cm, Frozen.F, Frozen.X0, Frozen.X1, Frozen.X2,
    Frozen.Y0, Frozen.Y1, Frozen.Y2, fUni, map_ofNat] <;> polynomial
theorem fUni_degree : fUni.natDegree = 6 := by
  unfold fUni; compute_degree!
theorem fUni_lc : fUni.leadingCoeff = 14 := by
  rw [Polynomial.leadingCoeff, fUni_degree]
  simp only [fUni, Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow]
  norm_num [map_ofNat]

def fFiber : Polynomial ℂ := (Polynomial.C (14 : ℂ)) * Polynomial.X^6 +
    (Polynomial.C (28 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (58 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (634 : ℂ))

def dFiber : Polynomial ℂ := (Polynomial.C (-481499986679670392862224670720 : ℂ)) * Polynomial.X^13 +
    (Polynomial.C (-1100543548755039613457925242880 : ℂ)) * Polynomial.X^11 +
    (Polynomial.C (2405981827067502652967069245440 : ℂ)) * Polynomial.X^9 +
    (Polynomial.C (13984114727676480763218606489600 : ℂ)) * Polynomial.X^7 +
    (Polynomial.C (10194122788303772906793555517440 : ℂ)) * Polynomial.X^5 +
    (Polynomial.C (-20313643691181699333801526394880 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (-37798690365894673291452701368320 : ℂ)) * Polynomial.X

def bezoutF : Polynomial ℂ := (Polynomial.C (222839430337851259244378747720126561214042410761623317283742421 / 539537129600025584667300066798717463109124189930771325618198014588150 : ℂ)) * Polynomial.X^12 +
    (Polynomial.C (179464441262704055876737975108921339049346217301904713038483177 / 269768564800012792333650033399358731554562094965385662809099007294075 : ℂ)) * Polynomial.X^10 +
    (Polynomial.C (855945238695002926662965211423570295322545802539291273372194509 / 269768564800012792333650033399358731554562094965385662809099007294075 : ℂ)) * Polynomial.X^8 +
    (Polynomial.C (-14283374124887367202583135654450971363700383814992302753818872201 / 539537129600025584667300066798717463109124189930771325618198014588150 : ℂ)) * Polynomial.X^6 +
    (Polynomial.C (-27018908051052331732400498155528596417930667993024434428437108709 / 539537129600025584667300066798717463109124189930771325618198014588150 : ℂ)) * Polynomial.X^4 +
    (Polynomial.C (-71279619343216071589333096285376765827961627652169805275476127093 / 539537129600025584667300066798717463109124189930771325618198014588150 : ℂ)) * Polynomial.X^2 +
    (Polynomial.C (1 / 634 : ℂ))

def bezoutD : Polynomial ℂ := (Polynomial.C (60906891307183814845284788570882564672939 / 5071821670121712504059714163929319742813962305090028307635259160493278208000 : ℂ)) * Polynomial.X^5 +
    (Polynomial.C (10088083702004919753062869910825766206801 / 633977708765214063007464270491164967851745288136253538454407395061659776000 : ℂ)) * Polynomial.X^3 +
    (Polynomial.C (518155587984724061476168683233679017688569 / 2535910835060856252029857081964659871406981152545014153817629580246639104000 : ℂ)) * Polynomial.X

theorem fiber_F : (toUni F).map specialize = fFiber := by
  have h := RingHom.congr_fun commute Frozen.F
  change _ = castUni (ExplicitWitness.lineMap Frozen.F) at h
  rw [ExplicitWitness.lineMap_F] at h
  change (toUni F).map specialize = _ at h
  rw [h]
  norm_num [castUni,fFiber,ExplicitWitness.lineF,map_ofNat] <;> polynomial

theorem fiber_D : (toUni D).map specialize = dFiber := by
  have h := RingHom.congr_fun commute ExplicitWitness.D
  change _ = castUni (ExplicitWitness.lineMap ExplicitWitness.D) at h
  rw [ExplicitWitness.lineMap_D] at h
  change (toUni D).map specialize = _ at h
  rw [h]
  norm_num [castUni,dFiber,ExplicitWitness.lineD,map_ofNat] <;> polynomial

theorem fiber_coprime : IsCoprime fFiber dFiber := by
  refine ⟨bezoutF, bezoutD, ?_⟩
  unfold bezoutF bezoutD fFiber dFiber
  polynomial

theorem denominator_legal : IsRelPrime F D := by
  apply relPrime_of_retract toUni fromUni retract
  apply relPrime_of_specialization specialize
  · rw [toUni_F, fUni_lc]
    simpa only [map_ofNat] using
      (isUnit_iff_ne_zero.mpr (by norm_num : (14:ℂ) ≠ 0)).map MvPolynomial.C
  · rw [fiber_F, fiber_D]
    exact fiber_coprime.isRelPrime

theorem denominator_ne_zero : D ≠ 0 := by
  intro h
  have hd := fiber_D
  rw [h, map_zero, Polynomial.map_zero] at hd
  have hc := congrArg (fun p : Polynomial ℂ => p.coeff 1) hd
  norm_num [dFiber] at hc

theorem certificate : Verify F A 1 55 D N Q where
  denominator_ne_zero := denominator_ne_zero
  denominator_homogeneous := ExplicitWitness.D_homogeneous.map (algebraMap ℚ ℂ)
  numerator_homogeneous i := (ExplicitWitness.numerator_homogeneous i).map (algebraMap ℚ ℂ)
  denominator_legal := denominator_legal
  identity := normalized_identity (by simpa using equations.e1) (by simpa using equations.e2)

theorem solved : HasCertificate F A 1 := ⟨55,D,N,Q,certificate⟩
end HodgeComputer.DenseP0
#print axioms HodgeComputer.DenseP0.solved
