import Proposal.DeformedDomains
import Proposal.DeformedEquation
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus
import HodgeComputer.Constructions.HoldoutCover.ResidueDerivatives
import HodgeComputer.Constructions.HoldoutCover.ResidueClearing

/-!
The deformed weighted quotient and its genuine tangent derivations.
The quotient/fraction-field descent uses fqlx's shared residue machinery.
The added ternary terms are retained in the equation and every derivative.
Prepared with OpenAI Codex assistance for hodgepodgeconjecture.
-/
noncomputable section
namespace DeformedGeometry
open Polynomial HoldoutConstruction
variable {R : Type*} [CommRing R]

def weightedEquation (d a b : R) : MvPolynomial (Fin 5) R :=
  let x : Fin 5 → MvPolynomial (Fin 5) R := MvPolynomial.X
  x 0^6+x 1^6+x 2^6+x 4*(MvPolynomial.C a*x 0^3*x 1+
    MvPolynomial.C b*x 1^3*x 2)+x 3^3-3*x 3*x 4^2+
    MvPolynomial.C d*(x 0^5*x 1+2*x 1^5*x 2+x 2^5*x 0)

lemma weightedEquation_univariate (d a b : R) :
    MvPolynomial.finSuccEquiv R 4 (weightedEquation d a b)=quotientPolynomial d a b := by
  have he : (Fin.cases (X : (MvPolynomial (Fin 4) R)[X]) (fun j => C (MvPolynomial.X j))) =
      ![X,C (MvPolynomial.X 0),C (MvPolynomial.X 1),C (MvPolynomial.X 2),C (MvPolynomial.X 3)] := by
    funext i
    fin_cases i <;> rfl
  simp [weightedEquation,quotientPolynomial,MvPolynomial.finSuccEquiv_apply,he,Polynomial.C_ofNat]
  ring

lemma weightedEquation_irreducible [IsDomain R] [CharZero R] (d a b : R) :
    Irreducible (weightedEquation d a b) := by
  apply (MulEquiv.irreducible_iff (MvPolynomial.finSuccEquiv R 4)).mp
  rw [weightedEquation_univariate]
  exact quotientPolynomial_irreducible d a b

abbrev QuotientRing (d a b : R) := AdjoinRoot (quotientPolynomial d a b)
abbrev QuotientField (d a b : R) := FractionRing (QuotientRing d a b)
def quotientProjection (d a b : R) : MvPolynomial (Fin 5) R →+* QuotientRing d a b :=
  (AdjoinRoot.mk (quotientPolynomial d a b)).comp
    (MvPolynomial.finSuccEquiv R 4).toRingHom
lemma quotientProjection_surjective (d a b : R) : Function.Surjective (quotientProjection d a b) :=
  (AdjoinRoot.mk_surjective (g := quotientPolynomial d a b)).comp
    (MvPolynomial.finSuccEquiv R 4).surjective
lemma quotientProjection_kernel (d a b : R) (p : MvPolynomial (Fin 5) R) :
    quotientProjection d a b p=0 ↔ weightedEquation d a b ∣ p := by
  change AdjoinRoot.mk (quotientPolynomial d a b) (MvPolynomial.finSuccEquiv R 4 p)=0 ↔ _
  rw [AdjoinRoot.mk_eq_zero,← weightedEquation_univariate d a b]
  exact map_dvd_iff (MvPolynomial.finSuccEquiv R 4)

def axisMap : MvPolynomial (Fin 5) R →+* Polynomial R :=
  MvPolynomial.eval₂Hom C ![X,0,0,0,0]
lemma axisMap_equation (d a b : R) : axisMap (weightedEquation d a b)=X^6 := by
  simp [axisMap,weightedEquation]
lemma axisMap_normal (d a b : R) :
    axisMap (integerPartial 0 (weightedEquation d a b))=6*X^5 := by
  norm_num [axisMap,weightedEquation,integerPartial,MvPolynomial.pderiv_pow,
    MvPolynomial.pderiv_mul,Polynomial.C_ofNat,Pi.single_apply,Fin.ext_iff]

lemma weightedEquation_not_dvd_normal [CharZero R] (d a b : R) :
    ¬ weightedEquation d a b ∣ integerPartial 0 (weightedEquation d a b) := by
  intro h
  have hm := map_dvd (axisMap (R := R)) h
  rw [axisMap_equation,axisMap_normal] at hm
  have hc := (Polynomial.X_pow_dvd_iff.mp hm) 5 (by decide)
  norm_num at hc

section Field
variable [IsDomain R] [CharZero R]
attribute [local instance] quotient_domain

def quotientResidueMap (d a b : R) : MvPolynomial (Fin 5) R →+* QuotientField d a b :=
  (algebraMap (QuotientRing d a b) (QuotientField d a b)).comp (quotientProjection d a b)
lemma quotientResidueMap_kernel (d a b : R) (p : MvPolynomial (Fin 5) R) :
    quotientResidueMap d a b p=0 ↔ weightedEquation d a b ∣ p :=
  residue_fractionMap_kernel (quotientProjection d a b) (weightedEquation d a b)
    (quotientProjection_kernel d a b) p
lemma quotient_normal_ne_zero (d a b : R) :
    quotientResidueMap d a b (integerPartial 0 (weightedEquation d a b)) ≠ 0 := by
  intro h
  exact weightedEquation_not_dvd_normal d a b ((quotientResidueMap_kernel d a b _).mp h)
local instance deformedQuotient_local_1 (d a b : R) : Algebra ℤ (QuotientField d a b) := Ring.toIntAlgebra _
def quotientTangent (d a b : R) (i : Fin 4) :
    Derivation ℤ (QuotientField d a b) (QuotientField d a b) :=
  residueTangent (K := QuotientField d a b) (quotientProjection d a b)
    (quotientProjection_surjective d a b) (integerPartial 0) (integerPartial i.succ)
    (weightedEquation d a b) (quotientProjection_kernel d a b) (quotient_normal_ne_zero d a b)
lemma quotientTangent_apply (d a b : R) (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    quotientTangent d a b i (quotientResidueMap d a b p)=
      quotientResidueMap d a b (integerPartial i.succ p)-
        quotientResidueMap d a b (integerPartial i.succ (weightedEquation d a b))/
          quotientResidueMap d a b (integerPartial 0 (weightedEquation d a b))*
            quotientResidueMap d a b (integerPartial 0 p) :=
  residueTangent_apply (K := QuotientField d a b) (quotientProjection d a b)
    (quotientProjection_surjective d a b) (integerPartial 0) (integerPartial i.succ)
    (weightedEquation d a b) (quotientProjection_kernel d a b) (quotient_normal_ne_zero d a b) p
end Field

section ScaledIdentity
variable {K T : Type*} [Field K] [CharZero K] [CommRing T]
lemma weightedEquation_eval_fourteen (f : K →+* T) (a b : K) (x : Fin 5 → T) :
    14*MvPolynomial.eval₂Hom f x (weightedEquation (14⁻¹) a b)=
      DeformedConic.H (f a) (f b) x := by
  have hi : (14:T)*f ((14:K)⁻¹)=1 := by
    rw [← map_ofNat f 14,← map_mul,mul_inv_cancel₀ (by norm_num : (14:K) ≠ 0),map_one]
  simp only [weightedEquation,DeformedConic.H,map_add,map_sub,map_mul,map_pow,
    map_ofNat,MvPolynomial.eval₂Hom_X',MvPolynomial.eval₂Hom_C]
  linear_combination (x 0^5*x 1+2*x 1^5*x 2+x 2^5*x 0)*hi

lemma weightedEquation_fourteen (a b : K) :
    14*weightedEquation (14⁻¹) a b=
      DeformedConic.H (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X := by
  have h := weightedEquation_eval_fourteen (MvPolynomial.C : K →+* MvPolynomial (Fin 5) K)
    a b MvPolynomial.X
  change 14*MvPolynomial.eval₂ MvPolynomial.C MvPolynomial.X (weightedEquation (14⁻¹) a b)=_ at h
  rwa [MvPolynomial.eval₂_eta] at h

lemma H_integerPartial (a b : R) (i : Fin 5) :
    integerPartial i (DeformedConic.H (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X)=
      DeformedConic.gradient (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X i := by
  have h2 : MvPolynomial.pderiv i (2 : MvPolynomial (Fin 5) R)=0 := Derivation.map_natCast _ 2
  have h3 : MvPolynomial.pderiv i (3 : MvPolynomial (Fin 5) R)=0 := Derivation.map_natCast _ 3
  have h14 : MvPolynomial.pderiv i (14 : MvPolynomial (Fin 5) R)=0 := Derivation.map_natCast _ 14
  simp only [integerPartial_apply,DeformedConic.H,map_add,map_sub,
    MvPolynomial.pderiv_pow,MvPolynomial.pderiv_mul,MvPolynomial.pderiv_C,
    MvPolynomial.pderiv_X,h2,h3,h14]
  fin_cases i <;> norm_num [DeformedConic.gradient,Pi.single_apply,Fin.ext_iff] <;> ring

lemma weightedEquation_partial_fourteen (a b : K) (i : Fin 5) :
    14*integerPartial i (weightedEquation (14⁻¹) a b)=
      DeformedConic.gradient (MvPolynomial.C a) (MvPolynomial.C b) MvPolynomial.X i := by
  have h := congrArg (integerPartial i) (weightedEquation_fourteen a b)
  rw [H_integerPartial] at h
  have hn : integerPartial i (14 : MvPolynomial (Fin 5) K)=0 :=
    (integerPartial i).map_natCast 14
  simpa only [Derivation.leibniz,hn,smul_eq_mul,mul_zero,add_zero] using h

lemma weightedEquation_partial_eval_fourteen (f : K →+* T) (a b : K) (x : Fin 5 → T) (i : Fin 5) :
    14*MvPolynomial.eval₂Hom f x (integerPartial i (weightedEquation (14⁻¹) a b))=
      DeformedConic.gradient (f a) (f b) x i := by
  have h := congrArg (MvPolynomial.eval₂Hom f x) (weightedEquation_partial_fourteen a b i)
  rw [DeformedConic.gradient_map] at h
  simpa only [map_mul,map_ofNat,MvPolynomial.eval₂Hom_C,MvPolynomial.eval₂Hom_X'] using h
end ScaledIdentity

end DeformedGeometry
#print axioms DeformedGeometry.weightedEquation_irreducible
#print axioms DeformedGeometry.quotientTangent_apply
