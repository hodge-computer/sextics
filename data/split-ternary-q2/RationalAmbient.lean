import HodgeComputer.Constructions.HoldoutCover.ResidueClearing
import HodgeComputer.Constructions.HoldoutCover.Piola

/- Polynomial representative data for a rational residue source. Prepared
with OpenAI Codex assistance for fqlx. Every source denominator is required
to be nonzero after hypersurface evaluation. -/
noncomputable section
namespace SplitRationalAmbient
open HoldoutConstruction
open scoped BigOperators
variable {R K ι : Type*} [CommRing R] [Field K] [Fintype ι]

theorem rational_divergence_identity
    (ρ : R →+* K) (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K)
    (A Q D N₀ g₀ : R) (N g : ι → R) (w : ι → K)
    (hg : ρ g₀≠0) (hq : ρ Q≠0)
    (mixed : ∀ i,Δ i g₀=Δ₀ (g i))
    (compatible : ∀ i p,E i (ρ p)=ρ (Δ i p)-ρ (g i)/ρ g₀*ρ (Δ₀ p))
    (representative : ∀ i,ρ (N i)=ρ D*w i)
    (normal : Q*(N₀*g₀+∑ i,N i*g i)=A*D) :
    ρ (residueDivNum Δ₀ Δ D N₀ N)=(ρ D)^2*
      (ρ (Δ₀ A)/(ρ Q*ρ g₀)-ρ A*ρ (Δ₀ Q)/((ρ Q)^2*ρ g₀)-
        ρ A*ρ (Δ₀ g₀)/(ρ Q*(ρ g₀)^2)+residueDivergence E (ρ g₀) w) := by
  have hn : (Q*N₀)*g₀+∑ i,(Q*N i)*g i=A*D := by
    simpa only [mul_add,mul_assoc,Finset.mul_sum] using normal
  have hr (i : ι) : ρ (Q*N i)=ρ D*(ρ Q*w i) := by
    rw [map_mul,representative]
    ring
  have hh := residue_divergence_identity ρ Δ₀ Δ E A D (Q*N₀) g₀
    (fun i => Q*N i) g (fun i => ρ Q*w i) hg mixed compatible hr hn
  have he (i : ι) :
      E i (ρ Q*w i)-(ρ Q*w i)*E i (ρ g₀)/ρ g₀=
      ρ Q*(E i (w i)-w i*E i (ρ g₀)/ρ g₀)+
        w i*(ρ (Δ i Q)-ρ (g i)/ρ g₀*ρ (Δ₀ Q)) := by
    rw [Derivation.leibniz,compatible]
    simp only [smul_eq_mul]
    ring
  simp_rw [he] at hh
  have hsum : (∑ i,(ρ Q*(E i (w i)-w i*E i (ρ g₀)/ρ g₀)+
      w i*(ρ (Δ i Q)-ρ (g i)/ρ g₀*ρ (Δ₀ Q))))=
      ρ Q*residueDivergence E (ρ g₀) w+
        ∑ i,w i*(ρ (Δ i Q)-ρ (g i)/ρ g₀*ρ (Δ₀ Q)) := by
    have hw : residueDivergence E (ρ g₀) w=
        ∑ i,(E i (w i)-w i*E i (ρ g₀)/ρ g₀) := by
      simp only [residueDivergence,fieldDivergence,Finset.sum_sub_distrib,Finset.sum_div]
    rw [hw,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hsum] at hh
  have hnum : residueDivNum Δ₀ Δ D (Q*N₀) (fun i => Q*N i)=
      Q*residueDivNum Δ₀ Δ D N₀ N+D*(N₀*Δ₀ Q+∑ i,N i*Δ i Q) := by
    simp only [residueDivNum,Derivation.leibniz,smul_eq_mul,
      Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
    simp only [mul_assoc,← Finset.mul_sum]
    ring
  rw [hnum,map_add,map_mul,map_mul] at hh
  have hnormal := congrArg ρ normal
  simp only [map_mul,map_add,map_sum,representative] at hnormal
  simp only [mul_assoc,← Finset.mul_sum] at hnormal
  have hterm : ρ D*ρ (N₀*Δ₀ Q+∑ i,N i*Δ i Q)=
      (ρ D)^2*(ρ A*ρ (Δ₀ Q)/(ρ Q*ρ g₀)+
        ∑ i,w i*(ρ (Δ i Q)-ρ (g i)/ρ g₀*ρ (Δ₀ Q))) := by
    have hs : (∑ i,w i*(ρ (Δ i Q)-ρ (g i)/ρ g₀*ρ (Δ₀ Q)))=
        (∑ i,w i*ρ (Δ i Q))-(ρ (Δ₀ Q)/ρ g₀)*(∑ i,w i*ρ (g i)) := by
      simp only [mul_sub,Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs]
    simp only [map_add,map_sum,map_mul,representative,mul_assoc,← Finset.mul_sum]
    field_simp [hg,hq]
    linear_combination (ρ D)*(ρ (Δ₀ Q))*hnormal
  rw [hterm] at hh
  apply mul_left_cancel₀ hq
  linear_combination (norm := ring_nf) hh
  field_simp [hg,hq]
  ring

theorem ambient_data
    (ρ : R →+* K) (Δ₀ : Derivation ℤ R R) (Δ : ι → Derivation ℤ R R)
    (E : ι → Derivation ℤ K K) (f A Q : R) (w : ι → K)
    (hg : ρ (Δ₀ f)≠0) (hq : ρ Q≠0)
    (mixed : ∀ i,Δ i (Δ₀ f)=Δ₀ (Δ i f))
    (compatible : ∀ i p,E i (ρ p)=ρ (Δ i p)-ρ (Δ i f)/ρ (Δ₀ f)*ρ (Δ₀ p))
    (representatives : ∃ d : R,∃ n : ι → R,ρ d≠0 ∧ ∀ i,ρ (n i)=ρ d*w i)
    (equation : residueDivergence E (ρ (Δ₀ f)) w=
      -(ρ (Δ₀ A)/(ρ Q*ρ (Δ₀ f))-ρ A*ρ (Δ₀ Q)/((ρ Q)^2*ρ (Δ₀ f))-
        ρ A*ρ (Δ₀ (Δ₀ f))/(ρ Q*(ρ (Δ₀ f))^2))) :
    ∃ D N₀ : R,∃ N : ι → R,
      ρ D≠0 ∧ Q*(N₀*Δ₀ f+∑ i,N i*Δ i f)=A*D ∧
        ρ (residueDivNum Δ₀ Δ D N₀ N)=0 := by
  obtain ⟨d,n,hd,hn⟩ := representatives
  let D := Δ₀ f*Q*d
  let N₀ := A*d-Q*∑ i,Δ i f*n i
  let N : ι → R := fun i => Q*Δ₀ f*n i
  have hD : ρ D≠0 := by
    dsimp only [D]
    simp only [map_mul]
    exact mul_ne_zero (mul_ne_zero hg hq) hd
  have hN (i : ι) : ρ (N i)=ρ D*w i := by
    simp only [N,D,map_mul,hn]
    ring
  have hnormal : Q*(N₀*Δ₀ f+∑ i,N i*Δ i f)=A*D := by
    dsimp only [N₀,N,D]
    have hs : (∑ i,Q*Δ₀ f*n i*Δ i f)=Q*Δ₀ f*(∑ i,Δ i f*n i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hs]
    ring
  have hdiv := rational_divergence_identity ρ Δ₀ Δ E A Q D N₀ (Δ₀ f) N
    (fun i => Δ i f) w hg hq mixed compatible hN hnormal
  rw [equation] at hdiv
  have hz : ρ (residueDivNum Δ₀ Δ D N₀ N)=0 := by linear_combination hdiv
  exact ⟨D,N₀,N,hD,hnormal,hz⟩

#print axioms rational_divergence_identity
#print axioms ambient_data
end SplitRationalAmbient
