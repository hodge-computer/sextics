import HodgeComputer.Constructions.HoldoutCover.HomogeneousCertificate
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! The immutable cycle-three equation, its residue field and normal chart.
The Eisenstein specialization and quotient construction adapt the shared
HoldoutCover proofs credited to fqlx and the project collaborators. All three
cyclic couplings are present with their prescribed coefficient one half.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace CyclePhysical
open HoldoutConstruction Polynomial
abbrev Ambient := MvPolynomial (Fin 6) ℂ
abbrev Coeff := MvPolynomial (Fin 5) ℂ
local notation "v" => (MvPolynomial.X : Fin 6 → Ambient)
local notation "w" => (MvPolynomial.X : Fin 5 → Coeff)

def sextic : Ambient :=
  v 0^6+v 1^6+v 2^6+v 3^6+v 4^6+v 5^6+
    MvPolynomial.C (1/2)*(v 0^3*v 1*v 3*v 4+
      v 1^3*v 2*v 4*v 5+v 2^3*v 0*v 5*v 3)
def source : Ambient := v 0^3*v 3^3
def equation : Polynomial Coeff :=
  X^6+(C (MvPolynomial.C (1/2)*w 0*w 2*w 3)*X^3+
    C (MvPolynomial.C (1/2)*w 1^3*w 4*w 2)*X^1+
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
  exact (((((hp 0).add (hp 1)).add (hp 2)).add (hp 3)).add (hp 4)).add (hp 5) |>.add
    (MvPolynomial.isHomogeneous_C (Fin 6) (1/2 : ℂ) |>.mul
      (((hc 0 1 3 4).add (hc 1 2 4 5)).add (hc 2 0 5 3)))
lemma source_homogeneous : source.IsHomogeneous 6 :=
  (MvPolynomial.isHomogeneous_X_pow (0:Fin 6) 3).mul
    (MvPolynomial.isHomogeneous_X_pow (3:Fin 6) 3)

/-- Homogeneity and denominator legality create no additional obstruction
once the two normalized identities on this exact physical equation are proved. -/
theorem certificate_of_normalized
    (D : Ambient) (N : Fin 6 → Ambient) (Q : Ambient)
    (legal : IsRelPrime sextic D)
    (normal : HodgeTestbed.directional sextic N=source*D)
    (divergence : HodgeTestbed.divergenceNumerator D N=sextic*Q) :
    HodgeComputer.HasCertificate sextic source 1 :=
  hasCertificate_of_normalized sextic source D N Q sextic_homogeneous source_homogeneous
    sextic_irreducible.prime legal normal divergence 0 normal_legal

end CyclePhysical
#print axioms CyclePhysical.sextic_irreducible
#print axioms CyclePhysical.certificate_of_normalized
