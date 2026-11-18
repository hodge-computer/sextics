import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.ResiduePiolaPullback
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! Target-specific mixed-polar physical field audit. Adapted from the accepted
mixed-biweight PhysicalField of fqlx and hodgepodgeconjecture, using the shared
HoldoutCover irreducibility and homogeneous-certificate machinery. Prepared
with Codex assistance. This proves domain and closure conditional on normalized
data; it does not claim such data have yet been constructed. -/
noncomputable section
namespace MixedPolarPhysical
open HoldoutConstruction Polynomial
open scoped BigOperators
abbrev Ambient := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
local notation "w" => (MvPolynomial.X : Fin 5 → Coeff)

def sextic : Ambient :=
  v 0^6+v 1^6+v 2^6+v 3^6+v 4^6+v 5^6+
    MvPolynomial.C (1/2)*(v 0^3*v 1*v 3*v 4+
      v 1^3*v 2*v 4*v 5)+MvPolynomial.C (1/3)*(v 0*v 1*v 3*v 4^3)
def source : Ambient := v 0*v 1*v 2*v 3*v 4*v 5
def equation : Polynomial Coeff :=
  X^6+(C (MvPolynomial.C (1/2)*w 0*w 2*w 3)*X^3+
    C (MvPolynomial.C (1/3)*w 0*w 2*w 3^3)*X^1+
    C (w 0^6+w 1^6+w 2^6+w 3^6+w 4^6+
      MvPolynomial.C (1/2)*w 0^3*w 1*w 3*w 4))

lemma equation_monic : equation.Monic := by
  apply monic_X_pow_add
  apply lt_of_le_of_lt (degree_add_le _ _)
  apply max_lt
  · apply lt_of_le_of_lt (degree_add_le _ _)
    apply max_lt
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 3 _) (by decide)
    · exact lt_of_le_of_lt (degree_C_mul_X_pow_le 1 _) (by decide)
  · exact lt_of_le_of_lt degree_C_le (by decide)

lemma equation_specialization :
    equation.map (holdoutSpecialization Complex.I)=X^6+C ((X+1)^6-1) := by
  have hi : (Complex.I : ℂ)^6 = -1 := by
    rw [show (6:ℕ)=2*3 by decide,pow_mul,Complex.I_sq]
    norm_num
  simp [equation,holdoutSpecialization,← map_pow,hi,sub_eq_add_neg]

lemma equation_irreducible : Irreducible equation := by
  apply equation_monic.irreducible_of_irreducible_map (holdoutSpecialization Complex.I)
  rw [equation_specialization]
  exact irreducible_power_add_constant ((X+1)^6-1 : Polynomial ℂ)
    (by simp [coeff_X_add_one_pow]) (by norm_num [coeff_X_add_one_pow,coeff_one])
    6 (by decide)

lemma sextic_univariate : MvPolynomial.finSuccEquiv ℂ 5 sextic=equation := by
  have he : (Fin.cases (X : Polynomial Coeff) (fun j => C (MvPolynomial.X j))) =
      ![X,C (w 0),C (w 1),C (w 2),C (w 3),C (w 4)] := by
    funext i
    fin_cases i <;> rfl
  simp [sextic,equation,MvPolynomial.finSuccEquiv_apply,he]
  ring

lemma sextic_irreducible : Irreducible sextic := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv ℂ 5)).mp
  rw [sextic_univariate]
  exact equation_irreducible

abbrev CoordinateRing := AdjoinRoot equation
instance coordinate_domain : IsDomain CoordinateRing :=
  AdjoinRoot.isDomain_of_prime equation_irreducible.prime
abbrev FunctionField := FractionRing CoordinateRing
def projection : Ambient →+* CoordinateRing :=
  (AdjoinRoot.mk equation).comp (MvPolynomial.finSuccEquiv ℂ 5).toRingHom
lemma projection_surjective : Function.Surjective projection :=
  (AdjoinRoot.mk_surjective (g := equation)).comp (MvPolynomial.finSuccEquiv ℂ 5).surjective
lemma projection_kernel (p : Ambient) : projection p=0 ↔ sextic ∣ p := by
  change AdjoinRoot.mk equation (MvPolynomial.finSuccEquiv ℂ 5 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← sextic_univariate]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv ℂ 5)
def residueMap : Ambient →+* FunctionField :=
  (algebraMap CoordinateRing FunctionField).comp projection
lemma residueMap_kernel (p : Ambient) : residueMap p=0 ↔ sextic ∣ p := by
  constructor
  · intro h
    apply (projection_kernel p).mp
    apply IsFractionRing.injective CoordinateRing FunctionField
    simpa only [residueMap,RingHom.comp_apply,map_zero] using h
  · intro h
    change algebraMap CoordinateRing FunctionField (projection p)=0
    rw [(projection_kernel p).mpr h,map_zero]

def axis : Ambient →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom C (fun i => if i=0 then X else 0)
lemma axis_sextic : axis sextic=X^6 := by
  norm_num [axis,sextic,
    show (1:Fin 6)≠0 by decide,show (2:Fin 6)≠0 by decide,show (3:Fin 6)≠0 by decide,
    show (4:Fin 6)≠0 by decide,show (5:Fin 6)≠0 by decide]
lemma axis_normal : axis (MvPolynomial.pderiv 0 sextic)=6*X^5 := by
  norm_num [axis,sextic,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_pow,
    Polynomial.C_ofNat,Pi.single_apply,Matrix.cons_val,
    show (1:Fin 6)≠0 by decide,show (2:Fin 6)≠0 by decide,show (3:Fin 6)≠0 by decide,
    show (4:Fin 6)≠0 by decide,show (5:Fin 6)≠0 by decide]
lemma normal_legal : ¬ sextic ∣ MvPolynomial.pderiv 0 sextic := by
  intro h
  have hm := map_dvd axis h
  rw [axis_sextic,axis_normal] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc
lemma normal_ne_zero : residueMap (integerPartial 0 sextic)≠0 := by
  intro h
  exact normal_legal ((residueMap_kernel _).mp h)

local instance : Algebra ℤ FunctionField := Ring.toIntAlgebra _
def tangent (i : Fin 5) : Derivation ℤ FunctionField FunctionField :=
  residueTangent (K := FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) sextic projection_kernel normal_ne_zero
lemma tangent_apply (i : Fin 5) (p : Ambient) :
    tangent i (residueMap p)=residueMap (MvPolynomial.pderiv i.succ p)-
      residueMap (MvPolynomial.pderiv i.succ sextic)/residueMap (MvPolynomial.pderiv 0 sextic)*
        residueMap (MvPolynomial.pderiv 0 p) :=
  residueTangent_apply (K := FunctionField) projection projection_surjective
    (integerPartial 0) (integerPartial i.succ) sextic projection_kernel normal_ne_zero p

lemma sextic_homogeneous : sextic.IsHomogeneous 6 := by
  have hp (i : Fin 6) : (v i^6).IsHomogeneous 6 := MvPolynomial.isHomogeneous_X_pow i 6
  have hc (i j k l : Fin 6) : (v i^3*v j*v k*v l).IsHomogeneous 6 :=
    (((MvPolynomial.isHomogeneous_X_pow i 3).mul (MvPolynomial.isHomogeneous_X ℂ j)).mul
      (MvPolynomial.isHomogeneous_X ℂ k)).mul (MvPolynomial.isHomogeneous_X ℂ l)
  have hdiag := (((((hp 0).add (hp 1)).add (hp 2)).add (hp 3)).add (hp 4)).add (hp 5)
  have hreverse : (v 0*v 1*v 3*v 4^3).IsHomogeneous 6 := by
    rw [show v 0*v 1*v 3*v 4^3=v 4^3*v 0*v 1*v 3 by ring]
    exact hc 4 0 1 3
  exact (hdiag.add ((MvPolynomial.isHomogeneous_C (Fin 6) (1/2 : ℂ)).mul
      ((hc 0 1 3 4).add (hc 1 2 4 5)))).add
      ((MvPolynomial.isHomogeneous_C (Fin 6) (1/3 : ℂ)).mul hreverse)
lemma source_homogeneous : source.IsHomogeneous 6 := by
  exact (((((MvPolynomial.isHomogeneous_X ℂ (0:Fin 6)).mul
    (MvPolynomial.isHomogeneous_X ℂ (1:Fin 6))).mul
    (MvPolynomial.isHomogeneous_X ℂ (2:Fin 6))).mul
    (MvPolynomial.isHomogeneous_X ℂ (3:Fin 6))).mul
    (MvPolynomial.isHomogeneous_X ℂ (4:Fin 6))).mul
    (MvPolynomial.isHomogeneous_X ℂ (5:Fin 6))

lemma ambient_coordinate_ne_zero (i : Fin 6) :
    residueMap (MvPolynomial.X i) ≠ 0 := by
  intro hz
  have hd := (residueMap_kernel _).mp hz
  have hb := MvPolynomial.totalDegree_le_of_dvd_of_isDomain hd (MvPolynomial.X_ne_zero i)
  rw [sextic_homogeneous.totalDegree sextic_irreducible.ne_zero,
    MvPolynomial.totalDegree_X] at hb
  norm_num at hb

/-- Homogeneity and denominator legality create no additional obstruction
once the two normalized identities on this exact physical equation are proved. -/
theorem certificate_of_normalized
    (D : Ambient) (N : Fin 6 → Ambient) (Q : Ambient)
    (legal : IsRelPrime sextic D)
    (normal : HodgeTestbed.directional sextic N=source*D)
    (divergence : HodgeTestbed.divergenceNumerator D N=sextic*Q) :
    HodgeComputer.HasCertificate sextic 1 source :=
  hasCertificate_of_normalized sextic source D N Q sextic_homogeneous source_homogeneous
    sextic_irreducible.prime legal normal divergence 0 normal_legal

/-- Shared residue clearing followed by the legal homogeneous closure. -/
theorem certificate_of_residue_solution
    (vector : Fin 5 → FunctionField)
    (hw : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) vector =
      -(residueMap (MvPolynomial.pderiv 0 source)/residueMap (MvPolynomial.pderiv 0 sextic)-
        residueMap source*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 sextic))/
          (residueMap (MvPolynomial.pderiv 0 sextic))^2)) :
    HodgeComputer.HasCertificate sextic 1 source := by
  have hd : residueDivergence tangent (residueMap (MvPolynomial.pderiv 0 sextic)) vector =
      ∑ i,(tangent i (vector i)-vector i*tangent i (residueMap (MvPolynomial.pderiv 0 sextic))/
        residueMap (MvPolynomial.pderiv 0 sextic)) := by
    simp only [residueDivergence,fieldDivergence,Finset.sum_sub_distrib,Finset.sum_div]
  obtain ⟨D,N₀,N,Q,hD,hlegal,hnormal,hdiv,_⟩ :=
    residue_solution_clearing residueMap (integerPartial 0)
      (fun i : Fin 5 => integerPartial i.succ) tangent sextic source vector
      sextic_irreducible residueMap_kernel normal_ne_zero
      (fun i => integerPartial_commute i.succ 0 sextic) tangent_apply
      (residue_common_representatives projection projection_surjective vector) (by
        rw [hd] at hw
        change (residueMap (MvPolynomial.pderiv 0 source)*residueMap (MvPolynomial.pderiv 0 sextic)-
          residueMap source*residueMap (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 sextic)))/
            (residueMap (MvPolynomial.pderiv 0 sextic))^2+
          ∑ i,(tangent i (vector i)-vector i*tangent i (residueMap (MvPolynomial.pderiv 0 sextic))/
            residueMap (MvPolynomial.pderiv 0 sextic))=0
        rw [hw]
        have hn : residueMap (MvPolynomial.pderiv 0 sextic) ≠ 0 := normal_ne_zero
        field_simp
        ring)
  apply certificate_of_normalized D (Fin.cases N₀ N) Q hlegal
  · simp only [HodgeTestbed.directional,Fin.sum_univ_succ,Fin.cases_zero,
      Fin.cases_succ,mul_comm] at hnormal ⊢
    exact hnormal
  · simp only [HodgeTestbed.divergenceNumerator,HodgeTestbed.divergence,
      HodgeTestbed.directional,residueDivNum,Fin.sum_univ_succ,Fin.cases_zero,
      Fin.cases_succ,mul_comm] at hdiv ⊢
    exact hdiv


end MixedPolarPhysical
#print axioms MixedPolarPhysical.sextic_irreducible
#print axioms MixedPolarPhysical.certificate_of_normalized
#print axioms MixedPolarPhysical.coordinate_domain
#print axioms MixedPolarPhysical.residueMap_kernel
#print axioms MixedPolarPhysical.normal_legal
#print axioms MixedPolarPhysical.normal_ne_zero
#print axioms MixedPolarPhysical.sextic_homogeneous
#print axioms MixedPolarPhysical.source_homogeneous
#print axioms MixedPolarPhysical.ambient_coordinate_ne_zero

#print axioms MixedPolarPhysical.certificate_of_residue_solution
