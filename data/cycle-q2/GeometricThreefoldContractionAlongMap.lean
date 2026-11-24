import Proposal.GeometricLiteralThreefoldResidueContraction
import Proposal.GeometricSurfaceResidueOverlap

/-!
# Contraction of forms by a vector along a morphism

If a vector field is defined only along a map, its coefficient in each slot is a
function on the target chart. The remaining slots pull back by the ordinary map
of Kähler differentials. The resulting operation commutes with chart changes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ThreefoldContractionAlongMap

open CycleQ2GeometricExteriorSheaf CycleQ2GeometricAffineOverlap
  CycleQ2ExteriorSectionNaturality CycleQ2LiteralThreefoldResidueContraction

variable {R S : Type} [CommRing R] [CommRing S] [Algebra ℂ R] [Algebra ℂ S]

abbrev Forms (R : Type) [CommRing R] [Algebra ℂ R] (n : ℕ) :=
  ⋀[R]^n (KaehlerDifferential ℂ R)

/-- The first component evaluates the covector and the second pulls back differentials. -/
private def pairMap (φ : R →ₐ[ℂ] S) (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S) :
    KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S × KaehlerDifferential ℂ S where
  toFun α := (v α, differentialMap φ α)
  map_add' _ _ := Prod.ext (map_add v _ _) (map_add _ _ _)
  map_smul' c α := Prod.ext (v.map_smulₛₗ c α) (differentialMap_smul φ c α)

/-- Insert a vector along the morphism in one slot and restrict all remaining slots. -/
def along (n : ℕ) (φ : R →ₐ[ℂ] S) (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S) :
    Forms R (n+1) →ₛₗ[φ.toRingHom] Forms S n :=
  ((exteriorPower.map n (LinearMap.snd S S (KaehlerDifferential ℂ S))).comp
    (interior n (LinearMap.fst S S (KaehlerDifferential ℂ S)))).comp
      (exteriorMap φ.toRingHom (pairMap φ v) (n+1))

theorem along_wedge (n : ℕ) (φ : R →ₐ[ℂ] S) (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S)
    (m : Fin (n+1) → KaehlerDifferential ℂ R) :
    along n φ v (exteriorPower.ιMulti R (n+1) m) =
      ∑ j : Fin (n+1), (-1 : ℤ) ^ (j : ℕ) •
        (v (m j) • exteriorPower.ιMulti S n (fun i => differentialMap φ (j.removeNth m i))) := by
  simp only [along, LinearMap.comp_apply, exteriorMap_wedge, interior_wedge,
    map_sum, map_zsmul, map_smul, exteriorPower.map_apply_ιMulti]
  rfl

theorem along_add (n : ℕ) (φ : R →ₐ[ℂ] S) (v w : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S) :
    along n φ (v + w) = along n φ v + along n φ w := by
  apply LinearMap.ext_on (exteriorPower.ιMulti_span R (n+1) (KaehlerDifferential ℂ R))
  rintro _ ⟨m, rfl⟩
  simp only [LinearMap.add_apply, along_wedge, add_smul, smul_add, Finset.sum_add_distrib]

variable {R' S' : Type} [CommRing R'] [CommRing S'] [Algebra ℂ R'] [Algebra ℂ S']

/-- Naturality for a commuting square of chart maps. It suffices to check the
compatibility of the two vectors on functions. -/
theorem along_natural (n : ℕ) (φ : R →ₐ[ℂ] S) (ψ : R' →ₐ[ℂ] S')
    (a : R →ₐ[ℂ] R') (b : S →ₐ[ℂ] S') (hsq : b.comp φ = ψ.comp a)
    (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S) (u : KaehlerDifferential ℂ R' →ₛₗ[ψ.toRingHom] S')
    (hv : ∀ r, b (v (KaehlerDifferential.D ℂ R r)) = u (KaehlerDifferential.D ℂ R' (a r)))
    (ω : Forms R (n+1)) :
    exteriorDifferentialMap b n (along n φ v ω) =
      along n ψ u (exteriorDifferentialMap a (n+1) ω) := by
  have hs (r : R) : b (φ r) = ψ (a r) := AlgHom.congr_fun hsq r
  have hdu (x : KaehlerDifferential ℂ R) : b (v x) = u (differentialMap a x) := by
    have hx : x ∈ Submodule.span R (Set.range (KaehlerDifferential.D ℂ R)) := by
      rw [KaehlerDifferential.span_range_derivation]
      trivial
    induction hx using Submodule.span_induction with
    | mem _ hx => obtain ⟨r, rfl⟩ := hx; simpa using hv r
    | zero => rw [v.map_zero, map_zero, (differentialMap a).map_zero, u.map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul c x _ hx =>
        rw [v.map_smulₛₗ, differentialMap_smul, u.map_smulₛₗ]
        change b (φ c * v x) = ψ (a c) * u (differentialMap a x)
        rw [map_mul, hs, hx]
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [along_wedge, exteriorDifferentialMap_wedge, along_wedge, map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_zsmul, map_smulₛₗ, exteriorDifferentialMap_wedge]
      change _ • (b (v (m j)) • _) = _ • (u (differentialMap a (m j)) • _)
      rw [hdu]
      congr 3
      funext i
      change differentialMap b (differentialMap φ _) = differentialMap ψ (differentialMap a _)
      simp only [differentialMap_comp, hsq, Fin.removeNth]
  | zero =>
      rw [(along n φ v).map_zero, (exteriorDifferentialMap b n).map_zero,
        (exteriorDifferentialMap a (n+1)).map_zero, (along n ψ u).map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
      rw [(along n φ v).map_smulₛₗ, (exteriorDifferentialMap b n).map_smulₛₗ,
        (exteriorDifferentialMap a (n+1)).map_smulₛₗ, (along n ψ u).map_smulₛₗ, hx]
      exact congrArg (fun c : S' => c • _) (hs c)

private theorem exterior_id (n : ℕ) (ω : Forms R n) :
    exteriorDifferentialMap (AlgHom.id ℂ R) n ω = ω :=
  exteriorMap_identity (AlgHom.id ℂ R).toRingHom (differentialSemilinearMap (AlgHom.id ℂ R))
    (fun _ => rfl) (fun x => differentialMap_id x) n ω

/-- Pulling an ambient form into a common chart before insertion gives the same result
as inserting the composite vector along the original map. -/
theorem along_precomp (n : ℕ) (a : R →ₐ[ℂ] R') (ψ : R' →ₐ[ℂ] S)
    (v : KaehlerDifferential ℂ R →ₛₗ[(ψ.comp a).toRingHom] S)
    (u : KaehlerDifferential ℂ R' →ₛₗ[ψ.toRingHom] S)
    (hv : ∀ r, v (KaehlerDifferential.D ℂ R r) = u (KaehlerDifferential.D ℂ R' (a r)))
    (ω : Forms R (n+1)) :
    along n (ψ.comp a) v ω = along n ψ u (exteriorDifferentialMap a (n+1) ω) := by
  have h := along_natural n (ψ.comp a) ψ a (AlgHom.id ℂ S) (by ext; rfl) v u hv ω
  rwa [exterior_id] at h

/-- Restricting the contracted form is insertion of the restricted vector. -/
theorem along_postcomp (n : ℕ) (φ : R →ₐ[ℂ] S) (b : S →ₐ[ℂ] S')
    (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S)
    (u : KaehlerDifferential ℂ R →ₛₗ[(b.comp φ).toRingHom] S')
    (hv : ∀ r, b (v (KaehlerDifferential.D ℂ R r)) = u (KaehlerDifferential.D ℂ R r))
    (ω : Forms R (n+1)) :
    exteriorDifferentialMap b n (along n φ v ω) = along n (b.comp φ) u ω := by
  have h := along_natural n φ (b.comp φ) (AlgHom.id ℂ R) b (by ext; rfl) v u hv ω
  rwa [exterior_id] at h

/-- An ordinary covector regarded along the identity morphism. -/
def identityCovector (v : KaehlerDifferential ℂ R →ₗ[R] R) :
    KaehlerDifferential ℂ R →ₛₗ[(AlgHom.id ℂ R).toRingHom] R where
  toFun := v
  map_add' := v.map_add
  map_smul' := v.map_smul

/-- On the identity morphism this is ordinary interior multiplication. -/
theorem along_id (n : ℕ) (v : KaehlerDifferential ℂ R →ₗ[R] R) (ω : Forms R (n+1)) :
    along n (AlgHom.id ℂ R) (identityCovector v) ω = interior n v ω := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      rw [along_wedge, interior_wedge]
      simp only [differentialMap_id]
      rfl
  | zero => rw [(along n (AlgHom.id ℂ R) (identityCovector v)).map_zero, (interior n v).map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
      rw [(along n (AlgHom.id ℂ R) (identityCovector v)).map_smulₛₗ, (interior n v).map_smul, hx]
      rfl

/-- If the vector along the morphism comes from the target ring, insertion
equals contraction of the pulled-back ambient form. -/
theorem along_from_target (n : ℕ) (φ : R →ₐ[ℂ] S)
    (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S)
    (u : KaehlerDifferential ℂ S →ₗ[S] S)
    (hv : ∀ r, v (KaehlerDifferential.D ℂ R r) = u (KaehlerDifferential.D ℂ S (φ r)))
    (ω : Forms R (n+1)) :
    along n φ v ω = interior n u (exteriorDifferentialMap φ (n+1) ω) := by
  have h := along_natural n φ (AlgHom.id ℂ S) φ (AlgHom.id ℂ S) rfl
    v (identityCovector u) hv ω
  rwa [exterior_id, along_id] at h

/-- If the vector along the morphism is the restriction of a vector on the
source, insertion equals restriction of the ordinary ambient contraction. -/
theorem along_from_source (n : ℕ) (φ : R →ₐ[ℂ] S)
    (v : KaehlerDifferential ℂ R →ₛₗ[φ.toRingHom] S)
    (u : KaehlerDifferential ℂ R →ₗ[R] R)
    (hv : ∀ r, φ (u (KaehlerDifferential.D ℂ R r)) = v (KaehlerDifferential.D ℂ R r))
    (ω : Forms R (n+1)) :
    along n φ v ω = exteriorDifferentialMap φ n (interior n u ω) := by
  have h := along_natural n (AlgHom.id ℂ R) φ (AlgHom.id ℂ R) φ rfl
    (identityCovector u) v hv ω
  rw [along_id, exterior_id] at h
  exact h.symm

section Derivation
variable [Algebra R S] [IsScalarTower ℂ R S]

/-- The Kähler evaluation functional of a derivation along the given algebra map. -/
def alongCovector (δ : Derivation ℂ R S) :
    KaehlerDifferential ℂ R →ₛₗ[(IsScalarTower.toAlgHom ℂ R S).toRingHom] S where
  toFun := δ.liftKaehlerDifferential
  map_add' := map_add _
  map_smul' c x := (map_smul δ.liftKaehlerDifferential c x).trans (Algebra.smul_def c _)

@[simp] theorem alongCovector_D (δ : Derivation ℂ R S) (r : R) :
    alongCovector δ (KaehlerDifferential.D ℂ R r) = δ r :=
  Derivation.liftKaehlerDifferential_comp_D δ r

def ofDerivation (n : ℕ) (δ : Derivation ℂ R S) :
    Forms R (n+1) →ₛₗ[(IsScalarTower.toAlgHom ℂ R S).toRingHom] Forms S n :=
  along n _ (alongCovector δ)

theorem ofDerivation_add (n : ℕ) (δ ε : Derivation ℂ R S) :
    ofDerivation n (δ + ε) = ofDerivation n δ + ofDerivation n ε := by
  have h : alongCovector (δ+ε) = alongCovector δ + alongCovector ε := by
    apply LinearMap.ext
    intro x
    exact LinearMap.congr_fun
      ((KaehlerDifferential.linearMapEquivDerivation ℂ R (M := S)).symm.map_add δ ε) x
  exact (congrArg (along n _) h).trans (along_add n _ _ _)

end Derivation

end CycleQ2ThreefoldContractionAlongMap
end

#print axioms CycleQ2ThreefoldContractionAlongMap.along_natural
#print axioms CycleQ2ThreefoldContractionAlongMap.ofDerivation_add
