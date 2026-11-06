import HodgeComputer.Constructions.EllipticCompanions.Kernels
import Proposal.ScalarCalculus

/- Prepared with OpenAI Codex assistance for contributor 1337isnot1337.
See solution.md for the construction, provenance, and prior-work credit. -/

/- Source component: FanoScalarSources. -/
section

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace CrossedFanoElliptic
open HoldoutConstruction CrossedElliptic CrossedFanoAffineData
variable {K : Type*} [Field K] [CharZero K]
local instance : Algebra ℤ (E K) := Ring.toIntAlgebra _

lemma a_ne_zero : a (K:=K)≠0 := by
  intro ha
  apply fermat_a_transcendental (K:=K)
  rw [ha]
  exact isAlgebraic_zero

lemma delta_coboundary : delta ((b (K:=K))^2/a (K:=K))=thetaRatio-a (K:=K)*b (K:=K) := by
  have ha := a_ne_zero (K:=K)
  simp only [Derivation.leibniz_div,Derivation.leibniz_pow,delta_a,delta_b,smul_eq_mul,nsmul_eq_mul,
    thetaRatio]
  norm_num only
  field_simp [ha]
  linear_combination -b (K:=K)*fermat_relation (K:=K)

lemma firstSource_scalar (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) :
    evaluation φ u hu firstSource/(7*(algebraMap K (E K) u)^4)-
      (a (K:=K)*evaluation φ u hu (ambientD 2 firstSource)+
        b (K:=K)*evaluation φ u hu (ambientD 3 firstSource))/(7*(algebraMap K (E K) u)^3)=
    algebraMap K (E K) ((φ (MvPolynomial.X 0))^4*φ (MvPolynomial.X 1)/u^4) := by
  have h7 (i : Fin 4) : MvPolynomial.pderiv (R:=ℂ) i (7 : P4)=0 := (MvPolynomial.pderiv i).map_natCast 7
  simp [firstSource,ambientD,swap,integerPartial_apply,evaluation_X,map_div₀,map_ofNat,h7]
  <;> ring

lemma secondSource_scalar (φ : P2 →+* K) (u : K) (hu : u^3=φ basePolynomial) (hu0 : u≠0) :
    evaluation φ u hu secondSource/(7*(algebraMap K (E K) u)^4)-
      (a (K:=K)*evaluation φ u hu (ambientD 2 secondSource)+
        b (K:=K)*evaluation φ u hu (ambientD 3 secondSource))/(7*(algebraMap K (E K) u)^3)=
    -(algebraMap K (E K) (φ (MvPolynomial.X 0)/u^2))*a (K:=K)*b (K:=K) := by
  have h7 (i : Fin 4) : MvPolynomial.pderiv (R:=ℂ) i (7 : P4)=0 := (MvPolynomial.pderiv i).map_natCast 7
  have hu' : algebraMap K (E K) u≠0 := by simpa only [map_zero] using (algebraMap K (E K)).injective.ne hu0
  simp [secondSource,ambientD,swap,integerPartial_apply,evaluation_X,map_div₀,map_ofNat,h7]
  field_simp [hu']
  ring

theorem first_scalar_primitive (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ basePolynomial)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0) :
    ∃ bf cx cy : E K,
      (delta bf+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) ((φ (MvPolynomial.X 0))^4*φ (MvPolynomial.X 1)/u^4)) ∧
      ∀ D : Derivation ℤ K K,(∀ p,D (φ p)=0) → D u=0 →
        coefficient D bf=0 ∧ coefficient D cx=0 ∧ coefficient D cy=0 := by
  obtain ⟨D,N₀,N,hd,hn,hdiv⟩ := firstSource_data
  obtain ⟨bf,cx,cy,he,hkill⟩ := scalar_primitive_of_data φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy
    firstSource D N₀ N hd hn hdiv
  exact ⟨bf,cx,cy,(firstSource_scalar φ u hu ▸ he),hkill⟩

theorem second_scalar_primitive (φ : P2 →+* K) (hφ : Function.Injective φ)
    (u : K) (hu0 : u≠0) (hu : u^3=φ basePolynomial)
    (Dx Dy : Derivation ℤ K K)
    (hcx : ∀ c,Dx (φ (MvPolynomial.C c))=0)
    (hcy : ∀ c,Dy (φ (MvPolynomial.C c))=0)
    (hxx : ∀ i : Fin 2,Dx (φ (MvPolynomial.X i))=if i=0 then 1 else 0)
    (hyy : ∀ i : Fin 2,Dy (φ (MvPolynomial.X i))=if i=1 then 1 else 0) :
    ∃ bg cx cy : E K,
      (delta bg+coefficient Dx cx+coefficient Dy cy=
        algebraMap K (E K) (φ (MvPolynomial.X 0)/u^2)*thetaRatio) ∧
      ∀ D : Derivation ℤ K K,(∀ p,D (φ p)=0) → D u=0 →
        coefficient D bg=0 ∧ coefficient D cx=0 ∧ coefficient D cy=0 := by
  obtain ⟨D,N₀,N,hd,hn,hdiv⟩ := secondSource_data
  obtain ⟨bf,cx,cy,he,hkill⟩ := scalar_primitive_of_data φ hφ u hu0 hu Dx Dy hcx hcy hxx hyy
    secondSource D N₀ N hd hn hdiv
  rw [secondSource_scalar φ u hu hu0] at he
  let β := algebraMap K (E K) (φ (MvPolynomial.X 0)/u^2)
  refine ⟨-bf+β*((b (K:=K))^2/a (K:=K)),-cx,-cy,?_,?_⟩
  · have hβ : delta β=0 := delta_base _
    simp only [map_add,map_neg,Derivation.leibniz,smul_eq_mul,hβ,mul_zero,add_zero,delta_coboundary]
    dsimp [β] at he ⊢
    linear_combination -he
  · intro Dz hzφ hzu
    obtain ⟨hb,hx,hy⟩ := hkill Dz hzφ hzu
    have hβ : coefficient Dz β=0 := by
      dsimp [β]
      simp only [coefficient_scalar,Derivation.leibniz_div,Derivation.leibniz_pow,hzφ,hzu,
        smul_eq_mul,smul_zero,mul_zero,zero_mul,sub_self,zero_div,map_zero]
    simp only [map_add,map_neg,Derivation.leibniz,Derivation.leibniz_div,Derivation.leibniz_pow,
      coefficient_a,coefficient_b,hβ,hb,hx,hy,smul_eq_mul,smul_zero,mul_zero,zero_mul,sub_self,
      zero_div,zero_add,neg_zero,nsmul_eq_mul,and_self]

end CrossedFanoElliptic
end
end
