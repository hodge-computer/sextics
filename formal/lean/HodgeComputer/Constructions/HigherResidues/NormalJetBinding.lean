import HodgeComputer.Constructions.HigherResidues.NormalTaylor
import HodgeComputer.Constructions.HoldoutCover.PolynomialCalculus

/- Actual polynomial and rational-source jets for the normal Taylor formula.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
namespace SplitNormalJetBinding
open HoldoutConstruction
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]
abbrev P := MvPolynomial (Fin 5) ℂ

def gradient (π : P →+* K) (A : P) (i : Fin 5) : K := π (integerPartial i A)
def hessian (π : P →+* K) (A : P) : Matrix (Fin 5) (Fin 5) K :=
  fun i j => π (integerPartial j (integerPartial i A))
def third (π : P →+* K) (A : P) (i j k : Fin 5) : K :=
  π (integerPartial k (integerPartial j (integerPartial i A)))

lemma hessian_symm (π : P →+* K) (A : P) : (hessian π A).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  exact congrArg π (integerPartials_commute i j A)

lemma third_cycle (π : P →+* K) (A : P) (i j k : Fin 5) :
    third π A i j k=third π A k i j := by
  unfold third
  rw [integerPartials_commute k j,integerPartials_commute k i]

/-- The first and second jets used by the transgression are the actual
polynomial derivatives, evaluated on the hypersurface. -/
theorem polynomial_source_jets (π : P →+* K) (F A : P)
    (E : Fin 4 → Derivation ℤ K K) (ψ : Fin 5 → K)
    (hg : gradient π F 0≠0)
    (hnormal : (∑ i,gradient π F i*ψ i)=1)
    (hE : ∀ i B,E i (π B)=gradient π B i.succ-
      gradient π F i.succ/gradient π F 0*gradient π B 0) :
    SplitNormalTaylor.firstJet ψ (gradient π A)=
      gradient π A 0/gradient π F 0+
        SplitNormalTaylor.advect E (fun i => ψ i.succ) (π A) ∧
    SplitNormalTaylor.secondJet ψ (hessian π A)=
      (hessian π A 0 0/(gradient π F 0)^2-
        gradient π A 0*hessian π F 0 0/(gradient π F 0)^3)/2+
      SplitNormalTaylor.advect E (fun i => ψ i.succ)
        (gradient π A 0/gradient π F 0)+
      SplitNormalTaylor.restrictedHessian E (fun i => ψ i.succ) (π A)/2+
      SplitNormalTaylor.secondJet ψ (hessian π F)*gradient π A 0/gradient π F 0 := by
  constructor
  · exact SplitNormalTaylor.first_jet_formula E (gradient π F) ψ (gradient π A)
      (π A) hg hnormal (fun i => hE i A)
  · apply SplitNormalTaylor.second_jet_formula E (gradient π F) ψ
      (gradient π A) (π A) (hessian π A) (hessian π F) hg hnormal
      (hessian_symm π A) (hessian_symm π F) (fun i => hE i A)
    · intro i j
      exact hE i (integerPartial j A)
    · intro i j
      exact hE i (integerPartial j F)

def quotientGradient (A g : K) (a z : Fin 5 → K) (j : Fin 5) : K :=
  a j/g-A*z j/g^2
def quotientHessian (A g : K) (a z : Fin 5 → K)
    (aa zz : Matrix (Fin 5) (Fin 5) K) : Matrix (Fin 5) (Fin 5) K :=
  fun j k => aa j k/g-(a j*z k+a k*z j+A*zz j k)/g^2+2*A*z j*z k/g^3

lemma quotientHessian_symm (A g : K) (a z : Fin 5 → K)
    (aa zz : Matrix (Fin 5) (Fin 5) K) (haa : aa.IsSymm) (hzz : zz.IsSymm) :
    (quotientHessian A g a z aa zz).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  unfold quotientHessian
  rw [haa.apply i j,hzz.apply i j]
  ring

lemma quotient_tangent_first (D : Derivation ℤ K K) (A g c : K)
    (a z : Fin 5 → K) (i : Fin 5) (hg : g≠0)
    (hA : D A=a i-c*a 0) (hG : D g=z i-c*z 0) :
    D (A/g)=quotientGradient A g a z i-c*quotientGradient A g a z 0 := by
  simp only [Derivation.leibniz_div,hA,hG,smul_eq_mul,quotientGradient]
  field_simp [hg]
  ring

lemma quotient_tangent_second (D : Derivation ℤ K K) (A g c : K)
    (a z : Fin 5 → K) (aa zz : Matrix (Fin 5) (Fin 5) K)
    (i j : Fin 5) (hg : g≠0)
    (hA : D A=a i-c*a 0) (hG : D g=z i-c*z 0)
    (ha : D (a j)=aa j i-c*aa j 0) (hz : D (z j)=zz j i-c*zz j 0) :
    D (quotientGradient A g a z j)=quotientHessian A g a z aa zz j i-
      c*quotientHessian A g a z aa zz j 0 := by
  have htwo : D (2 : K)=0 := D.map_natCast 2
  simp only [quotientGradient,quotientHessian,map_sub,Derivation.leibniz_div,
    Derivation.leibniz,Derivation.leibniz_pow,hA,hG,ha,hz,smul_eq_mul,nsmul_eq_mul]
  norm_num only
  field_simp [hg]
  ring

lemma quotient_firstJet (A g : K) (ψ a z : Fin 5 → K) (hg : g≠0) :
    SplitNormalTaylor.firstJet ψ (quotientGradient A g a z)=
      SplitNormalTaylor.firstJet ψ a/g-A*SplitNormalTaylor.firstJet ψ z/g^2 := by
  simp only [SplitNormalTaylor.firstJet,quotientGradient,Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp [hg]
  ring

lemma quotient_secondJet (A g : K) (ψ a z : Fin 5 → K)
    (aa zz : Matrix (Fin 5) (Fin 5) K) (hg : g≠0) :
    SplitNormalTaylor.secondJet ψ (quotientHessian A g a z aa zz)=
      SplitNormalTaylor.secondJet ψ aa/g-
        (SplitNormalTaylor.firstJet ψ a*SplitNormalTaylor.firstJet ψ z+
          A*SplitNormalTaylor.secondJet ψ zz)/g^2+
        A*(SplitNormalTaylor.firstJet ψ z)^2/g^3 := by
  simp only [SplitNormalTaylor.firstJet,SplitNormalTaylor.secondJet,quotientHessian,
    Fin.sum_univ_succ,Fin.sum_univ_zero]
  field_simp [hg]
  ring

/-- The rational density A/(∂₀F) satisfies the exact tangent Taylor
identities, with no extension of a normal derivative to the residue field. -/
theorem rational_source_jets (π : P →+* K) (F A : P)
    (E : Fin 4 → Derivation ℤ K K) (ψ : Fin 5 → K)
    (hg : gradient π F 0≠0)
    (hnormal : (∑ i,gradient π F i*ψ i)=1)
    (hE : ∀ i B,E i (π B)=gradient π B i.succ-
      gradient π F i.succ/gradient π F 0*gradient π B 0) :
    let g := gradient π F 0
    let a := gradient π A
    let z := gradient π (integerPartial 0 F)
    let rr := quotientHessian (π A) g a z (hessian π A) (hessian π (integerPartial 0 F))
    let r := quotientGradient (π A) g a z
    SplitNormalTaylor.firstJet ψ r=r 0/g+
        SplitNormalTaylor.advect E (fun i => ψ i.succ) (π A/g) ∧
    SplitNormalTaylor.secondJet ψ rr=(rr 0 0/g^2-
        r 0*hessian π F 0 0/g^3)/2+
      SplitNormalTaylor.advect E (fun i => ψ i.succ) (r 0/g)+
      SplitNormalTaylor.restrictedHessian E (fun i => ψ i.succ) (π A/g)/2+
      SplitNormalTaylor.secondJet ψ (hessian π F)*r 0/g := by
  dsimp only
  have hEA (i : Fin 4) := quotient_tangent_first (E i) (π A) (gradient π F 0)
    (gradient π F i.succ/gradient π F 0) (gradient π A)
    (gradient π (integerPartial 0 F)) i.succ hg (hE i A) (hE i (integerPartial 0 F))
  have hEa (i : Fin 4) (j : Fin 5) := quotient_tangent_second (E i) (π A)
    (gradient π F 0) (gradient π F i.succ/gradient π F 0)
    (gradient π A) (gradient π (integerPartial 0 F))
    (hessian π A) (hessian π (integerPartial 0 F)) i.succ j hg
    (hE i A) (hE i (integerPartial 0 F))
    (hE i (integerPartial j A)) (hE i (integerPartial j (integerPartial 0 F)))
  constructor
  · exact SplitNormalTaylor.first_jet_formula E (gradient π F) ψ _ _ hg hnormal hEA
  · exact SplitNormalTaylor.second_jet_formula E (gradient π F) ψ _ _ _ _ hg hnormal
      (quotientHessian_symm _ _ _ _ _ _ (hessian_symm π A) (hessian_symm π (integerPartial 0 F)))
      (hessian_symm π F) hEA hEa (fun i j => hE i (integerPartial j F))

#print axioms polynomial_source_jets
#print axioms quotient_tangent_second
#print axioms rational_source_jets
end SplitNormalJetBinding
