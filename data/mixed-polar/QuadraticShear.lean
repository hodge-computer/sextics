import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials
import HodgeComputer.Constructions.HoldoutCover.FiniteTrace
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! A finite coefficient extension for eliminating the reverse cubic edge.
The vertical derivation fixes the adjoined shear whenever it fixes a,d,f.
All physical derivations can instead be extended by the shared construction;
their normalized trace is the existing finite-trace descent interface. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace MixedPolarShear
open HoldoutConstruction IntermediateField
universe u
variable (K : Type u) [Field K] [CharZero K]

def discriminant (a d f : K) : K := d^2-3*a*f
def chosenRoot (a d f : K) : AlgebraicClosure K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (discriminant K a d f)) (by decide : 0<2))
lemma chosenRoot_sq (a d f : K) :
    chosenRoot K a d f^2=algebraMap K (AlgebraicClosure K) (discriminant K a d f) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (discriminant K a d f)) (by decide : 0<2))

abbrev Extension (a d f : K) := K⟮chosenRoot K a d f⟯
instance finite_extension (a d f : K) : FiniteDimensional K (Extension K a d f) :=
  IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (chosenRoot K a d f))
def delta (a d f : K) : Extension K a d f :=
  ⟨chosenRoot K a d f,mem_adjoin_simple_self K _⟩
lemma delta_sq (a d f : K) :
    delta K a d f^2=algebraMap K (Extension K a d f) (discriminant K a d f) := by
  apply Subtype.ext
  exact chosenRoot_sq K a d f

def shear (a d f : K) : Extension K a d f :=
  (-algebraMap K _ d+delta K a d f)/(3*algebraMap K _ a)

lemma shear_relation (a d f : K) (ha : a≠0) :
    3*algebraMap K (Extension K a d f) a*shear K a d f^2+
      2*algebraMap K _ d*shear K a d f+algebraMap K _ f=0 := by
  have ha' : algebraMap K (Extension K a d f) a≠0 :=
    by simpa only [map_zero] using (algebraMap K (Extension K a d f)).injective.ne ha
  have hs := delta_sq K a d f
  simp only [discriminant,map_sub,map_pow,map_mul,map_ofNat] at hs
  dsimp only [shear]
  field_simp
  linear_combination hs

lemma transformed_d (a d f : K) (ha : a≠0) :
    algebraMap K (Extension K a d f) d+3*algebraMap K _ a*shear K a d f=
      delta K a d f := by
  have ha' : algebraMap K (Extension K a d f) a≠0 :=
    by simpa only [map_zero] using (algebraMap K (Extension K a d f)).injective.ne ha
  dsimp only [shear]
  field_simp
  ring

lemma delta_ne_zero (a d f : K) (hdisc : discriminant K a d f≠0) :
    delta K a d f≠0 := by
  intro hz
  have h:=delta_sq K a d f
  rw [hz,zero_pow (by decide : (2:ℕ)≠0)] at h
  exact hdisc ((algebraMap K (Extension K a d f)).injective (by simpa using h.symm))

local instance : Algebra ℤ K := Ring.toIntAlgebra K
lemma delta_constant (a d f : K) (D : Derivation ℤ K K)
    (ha : D a=0) (hd : D d=0) (hf : D f=0) :
    extendFiniteDerivation (L:=Extension K a d f) D (delta K a d f)=0 := by
  let E := extendFiniteDerivation (L:=Extension K a d f) D
  have h3 : D (3:K)=0 := D.map_natCast 3
  have hdisc : D (discriminant K a d f)=0 := by
    simp [discriminant,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
      ha,hd,hf,h3,smul_eq_mul,nsmul_eq_mul]
  have h:=congrArg E (delta_sq K a d f)
  simp only [Derivation.leibniz_pow,smul_eq_mul,nsmul_eq_mul,pow_one,
    E,extendFiniteDerivation_apply,hdisc,map_zero] at h
  norm_num at h
  by_cases hz : delta K a d f=0
  · rw [hz,map_zero]
  · exact h.resolve_left hz

lemma shear_constant (a d f : K) (D : Derivation ℤ K K)
    (ha : D a=0) (hd : D d=0) (hf : D f=0) :
    extendFiniteDerivation (L:=Extension K a d f) D (shear K a d f)=0 := by
  have h3 : extendFiniteDerivation (L:=Extension K a d f) D
      (3:Extension K a d f)=0 := (extendFiniteDerivation D).map_natCast 3
  simp [shear,Derivation.leibniz_div,Derivation.leibniz,map_add,map_neg,
    extendFiniteDerivation_apply,delta_constant K a d f D ha hd hf,
    ha,hd,hf,h3,smul_eq_mul]

theorem cubic_shear (a b c d e f : K) (ha : a≠0)
    (x y z : Extension K a d f) :
    let ι := algebraMap K (Extension K a d f)
    let k := shear K a d f
    ι a*(x+k*y)^3+ι b*y^3+ι c*z^3+ι d*(x+k*y)^2*y+
      ι e*y^2*z+ι f*(x+k*y)*y^2 =
    ι a*x^3+(ι b+ι a*k^3+ι d*k^2+ι f*k)*y^3+
      ι c*z^3+(ι d+3*ι a*k)*x^2*y+ι e*y^2*z := by
  dsimp only
  linear_combination x*y^2*shear_relation K a d f ha

theorem residue_solution_descends (a d f : K)
    {ι : Type*} [Fintype ι] (D : ι → Derivation ℤ K K) (g r : K)
    (h : ∃ vector : ι → Extension K a d f,
      residueDivergence (fun i => extendFiniteDerivation (L:=Extension K a d f) (D i))
        (algebraMap K (Extension K a d f) g) vector=
          algebraMap K (Extension K a d f) r) :
    ∃ vector : ι → K,residueDivergence D g vector=r :=
  residue_solution_descends_finite D
    (fun i => extendFiniteDerivation (L:=Extension K a d f) (D i))
    (fun i value => extendFiniteDerivation_apply (D i) value) g r h

end MixedPolarShear
#print axioms MixedPolarShear.shear_relation
#print axioms MixedPolarShear.delta_constant
#print axioms MixedPolarShear.shear_constant
#print axioms MixedPolarShear.cubic_shear
#print axioms MixedPolarShear.residue_solution_descends
