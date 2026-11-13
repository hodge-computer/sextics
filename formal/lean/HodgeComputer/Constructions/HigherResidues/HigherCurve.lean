import HodgeComputer.Constructions.HigherResidues.NormalRowJets
import HodgeComputer.Constructions.HigherResidues.SourceDensityAlgebra

/- Polynomial-curve integration for a third-order hypersurface pole.
Prepared with OpenAI Codex assistance for fqlx. -/
noncomputable section
set_option maxRecDepth 100000
namespace SplitHigherResidue
open Polynomial HoldoutConstruction SplitNormalJetBinding
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
lemma firstGradientJet_zero (π : P →+* K) (F : P) (ψ : Fin 5 → K) :
    firstGradientJet π F ψ 0=SplitNormalTaylor.firstJet ψ (gradient π (integerPartial 0 F)) := by
  unfold firstGradientJet SplitNormalTaylor.firstJet hessian gradient
  apply Finset.sum_congr rfl
  intro j hj
  ring

lemma secondGradientJet_zero (π : P →+* K) (F : P) (ψ : Fin 5 → K) :
    secondGradientJet π F ψ 0=SplitNormalTaylor.secondJet ψ (hessian π (integerPartial 0 F)) := by
  unfold secondGradientJet SplitNormalTaylor.secondJet third hessian
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
  ring

lemma source_density_jets (π : P →+* K) (F A : P)
    (E : Fin 4 → Derivation ℤ K K) (ψ : Fin 5 → K)
    (hg : gradient π F 0≠0) (hnormal : ∑ i,gradient π F i*ψ i=1)
    (hE : ∀ i B,E i (π B)=gradient π B i.succ-
      gradient π F i.succ/gradient π F 0*gradient π B 0) :
    let g := gradient π F 0
    let A₁ := SplitNormalTaylor.firstJet ψ (gradient π A)
    let A₂ := SplitNormalTaylor.secondJet ψ (hessian π A)
    let l := firstGradientJet π F ψ 0
    let m := secondGradientJet π F ψ 0
    let r₀ := π A/g
    let r₁ := normalSourceOne (π A) (gradient π A 0) g (hessian π F 0 0)/g
    let r₂ := normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
      g (hessian π F 0 0) (third π F 0 0 0)/g
    A₁=l*r₀+g*(r₁+advect E (fun i => ψ i.succ) r₀) ∧
    A₂=m*r₀+l*(r₁+advect E (fun i => ψ i.succ) r₀)+
      g*(r₂+normalQuadraticJet π F ψ*r₁+
        advect E (fun i => ψ i.succ) r₁+(1/2)*hessianDensity E (fun i => ψ i.succ) r₀) := by
  dsimp only
  obtain ⟨h₁,h₂⟩ := rational_source_jets π F A E ψ hg hnormal hE
  rw [quotient_firstJet _ _ _ _ _ hg] at h₁
  rw [quotient_secondJet _ _ _ _ _ _ _ hg] at h₂
  rw [← firstGradientJet_zero] at h₁ h₂
  rw [← secondGradientJet_zero] at h₂
  have hr₁ : quotientGradient (π A) (gradient π F 0) (gradient π A)
      (gradient π (integerPartial 0 F)) 0/gradient π F 0 =
      normalSourceOne (π A) (gradient π A 0) (gradient π F 0) (hessian π F 0 0)/gradient π F 0 := rfl
  have hr₂ : (quotientHessian (π A) (gradient π F 0) (gradient π A)
      (gradient π (integerPartial 0 F)) (hessian π A) (hessian π (integerPartial 0 F)) 0 0/
        (gradient π F 0)^2-
      quotientGradient (π A) (gradient π F 0) (gradient π A)
        (gradient π (integerPartial 0 F)) 0*hessian π F 0 0/(gradient π F 0)^3)/2 =
      normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
        (gradient π F 0) (hessian π F 0 0) (third π F 0 0 0)/gradient π F 0 := by
    unfold quotientHessian quotientGradient normalSourceTwo gradient hessian third
    field_simp [hg]
    ring
  rw [hr₁] at h₁ h₂
  rw [hr₂,← normalQuadraticJet_eq π F ψ] at h₂
  change _ at h₁
  change _ at h₂
  dsimp only [SplitNormalTaylor.advect,SplitNormalTaylor.restrictedHessian] at h₁ h₂
  have h₀ : π A=gradient π F 0*(π A/gradient π F 0) := by field_simp [hg]
  have h₂' : SplitNormalTaylor.secondJet ψ (hessian π A)/gradient π F 0-
      (SplitNormalTaylor.firstJet ψ (gradient π A)*firstGradientJet π F ψ 0+
        π A*secondGradientJet π F ψ 0)/(gradient π F 0)^2+
      π A*(firstGradientJet π F ψ 0)^2/(gradient π F 0)^3 =
      normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
        (gradient π F 0) (hessian π F 0 0) (third π F 0 0 0)/gradient π F 0+
      normalQuadraticJet π F ψ*(normalSourceOne (π A) (gradient π A 0)
        (gradient π F 0) (hessian π F 0 0)/gradient π F 0)+
      advect E (fun i => ψ i.succ) (normalSourceOne (π A) (gradient π A 0)
        (gradient π F 0) (hessian π F 0 0)/gradient π F 0)+
      hessianDensity E (fun i => ψ i.succ) (π A/gradient π F 0)/2 := by
    calc
      _ = _ := h₂
      _ = _ := by
        rw [mul_div_assoc,hr₁]
        dsimp only [advect,hessianDensity]
        ring
  have hs := SplitSourceDensityAlgebra.source_jets
    (gradient π F 0) (π A) (SplitNormalTaylor.firstJet ψ (gradient π A))
    (SplitNormalTaylor.secondJet ψ (hessian π A))
    (firstGradientJet π F ψ 0) (secondGradientJet π F ψ 0)
    (π A/gradient π F 0)
    (normalSourceOne (π A) (gradient π A 0) (gradient π F 0) (hessian π F 0 0)/gradient π F 0)
    (normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
      (gradient π F 0) (hessian π F 0 0) (third π F 0 0 0)/gradient π F 0)
    (normalQuadraticJet π F ψ)
    (advect E (fun i => ψ i.succ) (π A/gradient π F 0))
    (advect E (fun i => ψ i.succ) (normalSourceOne (π A) (gradient π A 0)
      (gradient π F 0) (hessian π F 0 0)/gradient π F 0))
    (hessianDensity E (fun i => ψ i.succ) (π A/gradient π F 0)) hg h₀ h₁ h₂'
  convert hs using 1
  ring

omit [CharZero K] in
lemma linearMatrix_det_coeff_mem {n : ℕ} (S : Subring K)
    (M₀ M₁ : Matrix (Fin n) (Fin n) K)
    (h₀ : ∀ i j,M₀ i j∈S) (h₁ : ∀ i j,M₁ i j∈S) (k : ℕ) :
    (linearMatrix M₀ M₁).det.coeff k∈S := by
  let A : Matrix (Fin n) (Fin n) S := fun i j => ⟨M₀ i j,h₀ i j⟩
  let B : Matrix (Fin n) (Fin n) S := fun i j => ⟨M₁ i j,h₁ i j⟩
  let L : Matrix (Fin n) (Fin n) S[X] := A.map C+(X : S[X]) • B.map C
  have hm : (Polynomial.mapRingHom S.subtype).mapMatrix L=linearMatrix M₀ M₁ := by
    ext i j
    simp [L,A,B,linearMatrix,Polynomial.mapRingHom,smul_eq_mul]
  have hd := (Polynomial.mapRingHom S.subtype).map_det L
  have hc := congrArg (fun p : K[X] => p.coeff k) hd
  rw [hm] at hc
  change ((L.det).map S.subtype).coeff k=(linearMatrix M₀ M₁).det.coeff k at hc
  rw [Polynomial.coeff_map] at hc
  rw [← hc]
  exact (L.det.coeff k).property

theorem residue_solution_from_polynomial_curve_two
    {R : Type*} [Field R] [CharZero R]
    (π : P →+* K) (F A : P)
    (D E : Fin 4 → Derivation ℤ K K)
    (M N : Matrix (Fin 5) (Fin 5) K) (ψ : Fin 5 → K)
    (φ : R →+* K) (t : K) (tIndex : Fin 4)
    (hconst : ∀ a,D tIndex (φ a)=0) (ht : D tIndex t=1)
    (hg0 : gradient π F 0≠0) (hdet : M.det≠0)
    (hMN : M*N=1) (hNM : N*M=1) (hM : ∀j,M j 0=ψ j)
    (hnormal : ∑j,gradient π F j*ψ j=1) (hF : π F=0)
    (hD : ∀i B,D i (π B)=∑j,π (integerPartial j B)*M j i.succ)
    (hE : ∀i B,E i (π B)=gradient π B i.succ-
      gradient π F i.succ/gradient π F 0*gradient π B 0)
    (chain : ∀j x,E j x=∑i,tangentInverse N (gradient π F) i j*D i x)
    (mixed : ∀i j k : Fin 4,D k (M j.succ i.succ)=D i (M j.succ k.succ))
    (Ecommute : ∀i j,Function.Commute (E i) (E j))
    (hpolyM : ∀i j,M i j∈(Polynomial.eval₂RingHom φ t).range)
    (hpolyψ : ∀j,ψ j∈(Polynomial.eval₂RingHom φ t).range)
    (hpolyπ : ∀B,π B∈(Polynomial.eval₂RingHom φ t).range)
    (hpolyDψ : ∀i j,D i (ψ j)∈(Polynomial.eval₂RingHom φ t).range) :
    ∃w : Fin 4 → K,residueDivergence E (gradient π F 0) w =
      -normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
        (gradient π F 0) (hessian π F 0 0) (third π F 0 0 0) := by
  let g := gradient π F
  let a := normalQuadraticJet π F ψ
  let b := normalCubicJet π F ψ
  let M₁ := normalVariation D ψ
  let J₁ := (linearMatrix M M₁).det.coeff 1
  let J₂ := (linearMatrix M M₁).det.coeff 2
  let A₁ := SplitNormalTaylor.firstJet ψ (gradient π A)
  let A₂ := SplitNormalTaylor.secondJet ψ (hessian π A)
  let r := normalSourceTwo (π A) (gradient π A 0) (hessian π A 0 0)
    (g 0) (hessian π F 0 0) (third π F 0 0 0)
  let Z := normalCorrection E (g 0) (π A) (gradient π A 0) (hessian π F 0 0) a
    (fun i => ψ i.succ)
  let p := A₂*M.det+A₁*J₁+π A*J₂-3*a*(A₁*M.det+π A*J₁)+
    (6*a^2-3*b)*π A*M.det
  have hgM (j : Fin 5) : (∑k,g k*M k j)=if j=0 then 1 else 0 := by
    induction j using Fin.cases with
    | zero => simpa [g,hM] using hnormal
    | succ i =>
      have h := hD i F
      rw [hF,map_zero] at h
      simpa [g,gradient,Fin.succ_ne_zero] using h.symm
  have hN : ∀j,N 0 j=g j := inverse_normal_row M N g hMN hgM
  have htNM := tangentInverse_left M N g hg0 hNM hN
  have htMN := tangentInverse_right M N g ψ hg0 hMN hN hM
  have hfactor (i j : Fin 4) : M₁ i.succ j.succ=
      ∑k : Fin 4,E k (ψ i.succ)*M k.succ j.succ := by
    have h := column_directional D E (M.submatrix Fin.succ Fin.succ)
      (tangentInverse N g) htNM chain j (ψ i.succ)
    simpa only [M₁,normalVariation,Fin.cases_succ,Matrix.submatrix_apply,mul_comm] using h.symm
  have hrow := actual_polynomial_normal_row_jet π F D M ψ hF hM hnormal hD
  have hJ := jacobian_jet_equations D E M N M₁ g ψ (firstGradientJet π F ψ)
    (secondGradientJet π F ψ) a b
    (C ∘ Matrix.vecMul (secondGradientJet π F ψ) M₁) hNM hN hM hg0 hnormal chain hrow hfactor
  have hA := source_density_jets π F A E ψ hg0 hnormal hE
  have hA₀ : π A=g 0*(π A/g 0) := by field_simp [show g 0≠0 from hg0]
  have hjet : p=M.det*(r+residueDivergence E (g 0) Z) := by
    have h := linear_thickening_density_identity E (π A/g 0)
      (normalSourceOne (π A) (gradient π A 0) (g 0) (hessian π F 0 0)/g 0)
      (r/g 0) (π A) A₁ A₂ M.det J₁ J₂ (g 0)
      (firstGradientJet π F ψ 0) (secondGradientJet π F ψ 0) a b
      (fun i => ψ i.succ) hA₀ hA.1 hA.2 hJ.1 hJ.2
    change p=g 0*M.det*secondDensity E _ _ _ _ _ at h
    calc
      p = g 0*M.det*secondDensity E _ _ _ _ _ := h
      _ = M.det*(g 0*secondDensity E _ _ _ _ _) := by ring
      _ = M.det*(r+residueDivergence E (g 0) Z) := by
        rw [weighted_second_transgression E Ecommute _ _ _ _ _ _ _ _ hg0]
  let S : Subring K := (Polynomial.eval₂RingHom φ t).range
  have hhalf : (1/2 : K)∈S := by
    refine ⟨C (1/2 : R),?_⟩
    change (C (1/2 : R)).eval₂ φ t=1/2
    rw [Polynomial.eval₂_C,map_div₀,map_one,map_ofNat]
  have hthird : (1/3 : K)∈S := by
    refine ⟨C (1/3 : R),?_⟩
    change (C (1/3 : R)).eval₂ φ t=1/3
    rw [Polynomial.eval₂_C,map_div₀,map_one,map_ofNat]
  have hM₁ : ∀i j,M₁ i j∈S := by
    intro i j
    induction j using Fin.cases with
    | zero => exact S.zero_mem
    | succ j => exact hpolyDψ j i
  have hJ₁ : J₁∈S := linearMatrix_det_coeff_mem S M M₁ hpolyM hM₁ 1
  have hJ₂ : J₂∈S := linearMatrix_det_coeff_mem S M M₁ hpolyM hM₁ 2
  have hJ₀ : M.det∈S := determinant_mem_subring S M hpolyM
  have hA₁ : A₁∈S := S.sum_mem fun j _ => S.mul_mem (hpolyψ j) (hpolyπ _)
  have hA₂ : A₂∈S := by
    dsimp only [A₂,SplitNormalTaylor.secondJet]
    rw [div_eq_mul_one_div]
    apply S.mul_mem _ hhalf
    apply S.sum_mem
    intro j _
    apply S.sum_mem
    intro k _
    exact S.mul_mem (S.mul_mem (hpolyψ j) (hpolyψ k)) (hpolyπ _)
  have ha : a∈S := by
    apply S.mul_mem hhalf
    apply S.sum_mem
    intro j _
    apply S.sum_mem
    intro k _
    exact S.mul_mem (S.mul_mem (hpolyπ _) (hpolyψ j)) (hpolyψ k)
  have hb : b∈S := by
    apply S.mul_mem hthird
    apply S.sum_mem
    intro j _
    apply S.mul_mem _ (hpolyψ j)
    apply S.mul_mem hhalf
    apply S.sum_mem
    intro k _
    apply S.sum_mem
    intro l _
    exact S.mul_mem (S.mul_mem (hpolyπ _) (hpolyψ k)) (hpolyψ l)
  have hpoly : p∈S := by
    apply S.add_mem
    · apply S.sub_mem
      · exact S.add_mem (S.add_mem (S.mul_mem hA₂ hJ₀) (S.mul_mem hA₁ hJ₁))
          (S.mul_mem (hpolyπ A) hJ₂)
      · exact S.mul_mem (S.mul_mem (natCast_mem S 3) ha)
          (S.add_mem (S.mul_mem hA₁ hJ₀) (S.mul_mem (hpolyπ A) hJ₁))
    · exact S.mul_mem (S.mul_mem
        (S.sub_mem (S.mul_mem (natCast_mem S 6) (S.pow_mem ha 2))
          (S.mul_mem (natCast_mem S 3) hb)) (hpolyπ A)) hJ₀
  exact higher_residue_solution_of_density D E (M.submatrix Fin.succ Fin.succ)
    (tangentInverse N g) (g 0) M.det r p Z φ t tIndex hconst ht hg0 hdet
    (normal_matrix_determinant M g hgM) htMN htNM chain mixed hpoly hjet

#print axioms residue_solution_from_polynomial_curve_two

end SplitHigherResidue
